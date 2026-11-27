using System.Text;
using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The generic translation of milestone 3 (docs/milestone3.md): every Lean term gets a set-theoretic meaning computed from
/// its own structure, not looked up in a table.
///
/// - λ x : A, b is the map ( x e. ⟦A⟧ |-> ⟦b⟧ ), and f a is the function value ( ⟦f⟧ ` ⟦a⟧ ).
/// - A non-dependent arrow A → B is the set of functions ( ⟦B⟧ ^m ⟦A⟧ ); a dependent one is X_ x e. ⟦A⟧ ⟦B⟧.
/// - Prop is 2o. Every other sort is the universe U, one Grothendieck universe for every level for now; milestone 4
///   separates the levels.
/// - A constant c is ( lean.c ` U ): each definition is a set.mm definition, lean.c = ( u e. Univ |-> ⟦value⟧ ),
///   a function of the universe.
///
/// Each translated definition comes with its definitional equation as a theorem: lean.c applied to arguments of the
/// right types equals its body with them substituted, by one fvmptd step per argument.
/// </summary>
public sealed partial class Model(Terms t, Environment env, Prover pr, bool dryRun = false, bool tower = true, bool lowered = false)
{
    private const string UniverseVar = "u";
    private static readonly string[] Letters = "x y z w v t s r q p o n m k j i h g f e d c b a".Split(' ');
    /// <summary>
    /// Set variables of our own, for when set.mm's 26 letters run out: xx1, xx2, …: set.mm has no token of the form xx followed by digits.
    /// Each is declared ($v, and $f setvar with label vxxN) in the output the first time a definition or proof uses it.
    /// </summary>
    private static readonly string[] ExtraSetVars = Enumerable.Range(1, 500).Select(i => $"xx{i}").ToArray();
    private static readonly string[] SetVars = [.. Letters, .. ExtraSetVars];
    private static readonly HashSet<string> SetVarSet = [.. SetVars];
    private static readonly string[] ClassVars = "A B C D E F G H I J K L M N O P Q R S T".Split(' ');   // U is the universe, Z a hole
    /// <summary>
    /// Class variables of our own, for statements with more than set.mm's 20 arguments (IO.Error's constructors): AA1, AA2, …
    /// (set.mm has no token AA followed by digits). Each is declared ($v, and $f class with label cAAN) the first time
    /// a statement uses it, like the extra set variables; a $f adds no axiom.
    /// </summary>
    private static readonly string[] ExtraClassVars = Enumerable.Range(1, 80).Select(i => $"AA{i}").ToArray();

    private readonly Ops _ops = new(t);
    private readonly Typing _typing = new(t, env) { Deadline = () => pr.Deadline };   // define-all's time budget
    private readonly Deduction _d = new(pr);
    private readonly HashSet<Name> _defined = new(ReferenceEqualityComparer.Instance);
    private readonly StringBuilder _out = new();
    private ulong _fresh = 1UL << 58;

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>
    /// The set.mm token for a Lean constant: lean. and its name, escaped (NameEscape.cs) so that any Lean name has one.
    /// Never null; the type stays nullable for the callers written when some names had none.
    /// </summary>
    public static string? Token(Name n) => "lean." + NameEscape.Escape(n);

    /// <summary>What this model has written so far: declarations and definitions, in dependency order.</summary>
    public string Declarations => _out.ToString();

    /// <summary>A refusal, with the reason.</summary>
    public sealed class Refused(string why) : Exception(why);

    // ---- terms ----------------------------------------------------------------------------------------------------

    private sealed class Scope(string universe)
    {
        public string Universe { get; } = universe;
        public Dictionary<ulong, string> Vars { get; } = new();
        public Dictionary<ulong, Expr> Types { get; } = new();   // each local's Lean type, for telling proofs from data
        public List<string> Bound { get; } = new();   // every setvar the definition binds (for its $d list)
        public List<string> Active { get; } = new();  // the binders enclosing the current position
        public string WellOrder { get; set; } = "W";   // the well-ordering Classical.choice depends on (ModelBuiltins.cs)
        public bool UsesChoice { get; set; }          // whether the term mentions a constant that depends on it
    }

    /// <summary>⟦e⟧ as a set.mm class, with the universe written as <paramref name="universe"/> and the free variables as bound.</summary>
    public string Class(Expr e, string universe, IReadOnlyDictionary<ulong, string> vars)
    {
        var sc = new Scope(universe);
        foreach (var kv in vars)
        {
            sc.Vars[kv.Key] = kv.Value;
        }
        return Tr(e, sc);
    }

    private string Tr(Expr e, Scope sc)
    {
        using var prof = Prof.Time("Tr");
        // Proof irrelevance: every proof is (/). Types (sorts, Π-types) are never proofs, so they skip the check.
        if (e is not Sort and not Binder { IsPi: true } && _typing.IsProof(e, sc.Types) == true)
        {
            return "(/)";
        }
        switch (e)
        {
            case FVar f:
                return sc.Vars.TryGetValue(f.Id, out string? v) ? v : throw new Refused("a free variable with no translation");
            case Sort s:
                return tower ? TowerSort(s.Level, sc.Universe) : IsZero(s.Level) ? "2o" : sc.Universe;
            case Const c:
                Define(c.Name);
                return ConstTerm(c.Name, sc);   // ModelBuiltins.cs: with the well-ordering when it depends on choice
            case App a when Unwrapped(a) is Expr inner:
                return Tr(inner, sc);
            case App a:
                return $"( {Tr(a.Fn, sc)} ` {Tr(a.Arg, sc)} )";
            case Binder { IsPi: true } pp when tower && _typing.IsProposition(pp, sc.Types) == true:
                return PropPi(pp, sc);
            case Binder b:
                {
                    string dom = Tr(b.Domain, sc);
                    if (b.IsPi && b.Body.LooseBVarRange == 0)
                    {
                        return $"( {Tr(b.Body, sc)} ^m {dom} )";
                    }
                    string x = Fresh(sc, dom);
                    Expr fv = t.FVar(_fresh++);
                    sc.Vars[((FVar)fv).Id] = x;
                    sc.Types[((FVar)fv).Id] = b.Domain;
                    if (!sc.Bound.Contains(x))
                    {
                        sc.Bound.Add(x);
                    }
                    sc.Active.Add(x);
                    string body = Tr(_ops.Instantiate(b.Body, [fv]), sc);
                    sc.Active.RemoveAt(sc.Active.Count - 1);
                    sc.Vars.Remove(((FVar)fv).Id);
                    return b.IsPi ? $"X_ {x} e. {dom} {body}" : $"( {x} e. {dom} |-> {body} )";
                }
            case Let l:
                return Tr(_ops.Instantiate(l.Body, [l.Value]), sc);
            case NatLit lit:
                return NatLiteral(lit.Value);
            case StrLit lit:
                return StringLiteral(lit.Value, sc);
            case Proj p:
                {
                    // A structure's value is <. (/) , fields >. (one constructor, tag (/)): field i of its second part.
                    Define(p.StructName);
                    return Field($"( 2nd ` {Tr(p.Struct, sc)} )", p.Idx);
                }
            default:
                throw new Refused($"not yet in the model: {e.GetType().Name} ({e})");
        }
    }

    private static bool IsZero(Level l) => l is LZero;

    private string Fresh(Scope sc, string domain)
    {
        // A binder's setvar differs from every enclosing binder's, so substituting for one never captures another,
        // and from every variable in its own domain (mptexd, fvmptd3, iunexg and ixpexg need x disjoint from it).
        var inDomain = domain.Split(' ').ToHashSet();
        foreach (string x in SetVars)
        {
            if (!sc.Active.Contains(x) && !sc.Vars.ContainsValue(x) && !inDomain.Contains(x))
            {
                return Declare(x);
            }
        }
        throw new Refused("more nested binders than the model declares set variables");
    }

    private readonly HashSet<string> _declaredVars = new();

    /// <summary>The first count class variables: set.mm's, then ours (declared here when first used).</summary>
    private List<string> ClassVarsFor(int count, string why)
    {
        if (count > ClassVars.Length + ExtraClassVars.Length)
        {
            throw new Refused(why);
        }
        var r = ClassVars.Concat(ExtraClassVars).Take(count).ToList();
        foreach (string x in r.Skip(ClassVars.Length).Where(_declaredVars.Add))
        {
            string text = $"""
                $( A class variable of tenet-zfc's own: set.mm's are used up. $)
                $v {x} $.
                c{x} $f class {x} $.

                """;
            _out.AppendLine(text);
            if (!dryRun)
            {
                pr.Database.Extend(text);
            }
        }
        return r;
    }

    /// <summary>The set variable, declared first in the output when it is one of ours rather than set.mm's.</summary>
    private string Declare(string x)
    {
        if (x.StartsWith("xx", StringComparison.Ordinal) && _declaredVars.Add(x))
        {
            string text = $"""
                $( A set variable of tenet-zfc's own: set.mm's are used up. $)
                $v {x} $.
                v{x} $f setvar {x} $.

                """;
            _out.AppendLine(text);
            if (!dryRun)
            {
                pr.Database.Extend(text);
            }
        }
        return x;
    }

    // ---- definitions --------------------------------------------------------------------------------------------

    private readonly Dictionary<string, string> _values = new();
    private readonly HashSet<string> _intoPropOnly = new();   // recursors of propositions that eliminate only into Prop   // token → its value, with the universe written u

    /// <summary>
    /// Declare lean.c and define it, after the constants its value uses: $c, a syntax axiom, and
    /// df-lean.c $a |- lean.c = ( u e. Univ |-> ⟦value⟧ ) $. The definition's set variables are all bound, and distinct.
    /// Definitions translate their value; an inductive type, its constructors and its recursor are defined together
    /// (see <see cref="DefineInductive"/>).
    /// </summary>
    public void Define(Name n)
    {
        if (_defined.Contains(n))
        {
            return;
        }
        ConstInfo c = env.Find(n) ?? throw new Refused($"{n} is not in the export");
        switch (c.Kind)
        {
            case ConstKind.Definition when c.Value is not null:
            case ConstKind.Opaque when c.OpaqueValue is not null:
                {
                    // An opaque constant is defined by its value, which the kernel checked has its type. Lean can't
                    // unfold it, so a Lean theorem about it uses only its type, and any value of that type is faithful.
                    string tok = Token(n) ?? throw new Refused($"{n}: the name has characters a set.mm token can't");
                    var sc = NewScope();
                    string body = Tr(c.Value ?? c.OpaqueValue!, sc);   // defines what it uses first
                    _defined.Add(n);
                    Emit(n, tok, body, sc, c.Kind == ConstKind.Opaque ? "opaque constant" : "definition");
                    return;
                }
            case ConstKind.Inductive:
                DefineInductive(c);
                return;
            case ConstKind.Constructor when c.Induct is Name ind:
                Define(ind);
                RefuseIfPartial(n, ind);
                return;
            // The inductive type is the recursor's name without its last part. Taken from the name itself, not by
            // reparsing its text, which loses numeric parts (_private.….0.…; found by the Init-wide run).
            case ConstKind.Recursor when n is StrName { Value: "rec" } r:
                Define(r.Prefix);
                RefuseIfPartial(n, r.Prefix);
                return;
            case ConstKind.Recursor when IsAuxRecursorName(n) && n is StrName aux:
                Define(aux.Prefix);   // a nested block's auxiliary recursor, I.rec_k
                RefuseIfPartial(n, aux.Prefix);
                return;
            case ConstKind.Axiom or ConstKind.Quot:
                DefineBuiltin(c);   // ModelBuiltins.cs
                return;
        }
        throw new Refused($"{n} is not a definition but {(c.Kind == ConstKind.Inductive ? "an inductive type" : "a " + c.Kind.ToString().ToLowerInvariant())}; not in the model yet");
    }

    /// <summary>
    /// A type is written before its constructors and recursor, so when one of those was refused (Empty.rec: the empty
    /// type isn't in the model yet) the type counts as defined and they don't. Refuse them again here, rather than fail
    /// later on a definition that was never written (found by the Init-wide run).
    /// </summary>
    private void RefuseIfPartial(Name n, Name ind)
    {
        if (!_defined.Contains(n))
        {
            throw new Refused($"{n} is part of {ind}, which was only partly translated: an earlier refusal stopped it");
        }
    }

    /// <summary>
    /// The type inside an optParam, autoParam, outParam or semiOutParam wrapper, or null. The kernel strips these from
    /// an inductive's locals when it makes the recursor (Recursors.ConsumeAnnotations), so a recursor's binder types
    /// lack them while its constructors' keep them, and a computation rule, which matches hypotheses as text, fails
    /// (HAdd.mk, found by the Init-wide run). Each is the identity on its first argument, so translating through it
    /// changes no value. Like the kernel, only a wrapper the export defines as that identity is looked through.
    /// </summary>
    private Expr? Unwrapped(App a)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        // In tower mode the head is an instance, outParam.{2}: its name is the original's with a level suffix.
        Name? hn = head is Const c ? c.Name is StrName { Value: var lv } inst && NameEscape.IsLevelSuffix(lv) ? inst.Prefix : c.Name : null;
        string n = hn is null ? "" : $"{hn}";
        int arity = n is "optParam" or "autoParam" ? 2 : n is "outParam" or "semiOutParam" ? 1 : 0;
        if (arity == 0 || args.Count != arity || env.Find(((Const)head).Name) is not { Kind: ConstKind.Definition, Value: Expr v })
        {
            return null;
        }
        for (int i = 0; i < arity; i++)
        {
            if (v is not Binder { IsPi: false } lam)
            {
                return null;
            }
            v = lam.Body;
        }
        return v is BVar b && b.Idx == arity - 1 ? args[0] : null;
    }

    private Scope NewScope()
    {
        var sc = new Scope(UniverseVar) { WellOrder = WellOrderHole };
        sc.Bound.Add(UniverseVar);
        sc.Active.Add(UniverseVar);
        return sc;
    }

    /// <summary>The largest definition body written, in symbols: half of mmj2's 32,000, less a margin.</summary>
    private const int MaxDefinitionSymbols = 15_000;

    private void Emit(Name n, string tok, string body, Scope sc, string what)
    {
        EnsureTower();
        body = WellOrderLayer(tok, body, sc);   // ModelBuiltins.cs: ( r e. ~P ( u X. u ) |-> … ) when it depends on choice
        // mmj2's definition check proves |- body = body' for a copy with fresh dummies, and mmj2 can't hold an
        // expression over 32,000 symbols: past that, the check crashes and checks nothing after it (stdNext, 33,685
        // symbols, found by the Init-wide run). Every definition this writes must be checkable, so refuse larger ones.
        int symbols = body.Count(ch => ch == ' ') + 1;
        if (symbols > MaxDefinitionSymbols)
        {
            _defined.Remove(n);   // callers mark it defined first; it isn't, so what uses it must be refused too
            throw new Refused($"{n}'s definition has {symbols} symbols, more than mmj2's definition check can hold ({MaxDefinitionSymbols})");
        }
        string text = $"""
            $( The Lean {what} {NameEscape.CommentText($"{n}")}, translated by the model of docs/milestone3.md. $)
            $c {tok} $.
            c{LabelPart(tok)} $a class {tok} $.
            {"${"}
              {(sc.Bound.Count > 1 ? $"$d {string.Join(' ', sc.Bound)} $." : "")}
              df-{LabelPart(tok)} $a |- {tok} = ( {UniverseVar} e. {UniverseDomain} |-> {body} ) $.
            {"$}"}

            """;
        _out.AppendLine(text);
        _values[tok] = body;
        _tokenNames[tok] = n;
        if (!dryRun)
        {
            pr.Database.Extend(text);
        }
    }

    /// <summary>The first <paramref name="count"/> binders of a Π-type, as ( x e. ⟦A⟧ |-> … ) binders, each bound to a fresh set variable.</summary>
    private List<(string Var, string Dom)> Telescope(ref Expr ty, int count, Scope sc, List<Expr>? fvars = null, IReadOnlyList<Expr>? reuse = null)
    {
        var r = new List<(string, string)>();
        for (int i = 0; i < count; i++)
        {
            if (ty is not Binder { IsPi: true } b)
            {
                throw new Refused($"expected {count} binders, found {i}");
            }
            Expr fv;
            if (reuse is not null && i < reuse.Count)
            {
                // The same parameter as before: same variable, already bound in this scope.
                fv = reuse[i];
                ty = _ops.Instantiate(b.Body, [fv]);
                continue;
            }
            string dom = Tr(b.Domain, sc);
            string x = Fresh(sc, dom);
            fv = t.FVar(_fresh++);
            sc.Vars[((FVar)fv).Id] = x;
            sc.Types[((FVar)fv).Id] = b.Domain;
            if (!sc.Bound.Contains(x))
            {
                sc.Bound.Add(x);
            }
            sc.Active.Add(x);   // a telescope's binders enclose everything after them
            fvars?.Add(fv);
            r.Add((x, dom));
            ty = _ops.Instantiate(b.Body, [fv]);
        }
        return r;
    }

    private static string Maps(IEnumerable<(string Var, string Dom)> binders, string body) =>
        binders.Reverse().Aggregate(body, (acc, b) => $"( {b.Var} e. {b.Dom} |-> {acc} )");

    /// <summary>The fields a1 … ak as nested pairs: <. a1 , <. a2 , … <. ak , (/) >. … >. >.; no fields is (/).</summary>
    private static string Tuple(IReadOnlyList<string> fields) =>
        fields.Reverse().Aggregate("(/)", (acc, f) => $"<. {f} , {acc} >.");

    /// <summary>Constructor i's tag around its fields X: i times <. 1o , … >., then <. (/) , X >.</summary>
    private static string Tag(int i, string x) => i == 0 ? $"<. (/) , {x} >." : $"<. 1o , {Tag(i - 1, x)} >.";

    /// <summary>Field j of a field tuple X: 1st of j applications of 2nd.</summary>
    private static string Field(string x, int j) => j == 0 ? $"( 1st ` {x} )" : Field($"( 2nd ` {x} )", j - 1);

    /// <summary>
    /// An inductive type with no indices, not recursive, not nested and alone in its block, in Type: its values are the
    /// tagged tuples of its constructors (see <see cref="Tag"/>), so the type is the union over its constructors of
    /// U_ a1 e. T1 … { tag(a1, …) }, which is a set by iunexg and snex. A constructor builds the tagged tuple, and the
    /// recursor is case analysis on the tag: if ( ( 1st ` t ) = (/) , minor 0 on the fields , … ). Recursive,
    /// indexed, mutual and nested types, and inductive propositions, are refused for now.
    /// </summary>
    private void DefineInductive(ConstInfo ind)
    {
        Name n = ind.Name;
        string itok = Token(n) ?? throw new Refused($"{n}: the name has characters a set.mm token can't");
        if (IsMutualOrNested(ind, env))
        {
            DefineBlock(ind);   // Model.Mutual.cs
            return;
        }
        if (ind.IsRec)
        {
            if (IsProposition(ind))
            {
                DefineRecursiveProposition(ind, itok);
                return;
            }
            if (ind.NumIndices > 0)
            {
                throw new Refused($"{n} is a recursive indexed inductive type; not in the model yet");
            }
            DefineRecursive(ind, itok);
            return;
        }
        Expr target = ind.Type;
        while (target is Binder { IsPi: true } pb)
        {
            target = pb.Body;
        }
        if (target is Sort { Level: LZero })
        {
            DefineProposition(ind, itok);
            return;
        }
        if (ind.NumIndices > 0)
        {
            throw new Refused($"{n} is an indexed inductive type (not a proposition); not in the model yet");
        }
        List<ConstInfo> ctors = ind.Ctors.Select(c => env.Find(c) ?? throw new Refused($"{c} is not in the export")).ToList();
        ConstInfo rec = env.Find(t.Str(n, "rec")) ?? throw new Refused($"{n}.rec is not in the export");
        foreach (ConstInfo c in ctors.Append(rec))
        {
            _ = Token(c.Name) ?? throw new Refused($"{c.Name}: the name has characters a set.mm token can't");
        }

        // The type: ( p1 e. D1 |-> … ( S0 u. S1 ) … ).
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc, pfv);
            var parts = new List<string>();
            for (int j = 0; j < ctors.Count; j++)
            {
                Expr cty = ctors[j].Type;
                Telescope(ref cty, ind.NumParams, sc, reuse: pfv);
                var fs = Telescope(ref cty, ctors[j].NumFields, sc);
                string part = $"{{ {Tag(j, Tuple(fs.Select(f => f.Var).ToList()))} }}";
                parts.Add(fs.AsEnumerable().Reverse().Aggregate(part, (acc, f) => $"U_ {f.Var} e. {f.Dom} {acc}"));
            }
            string set = parts.Count == 0 ? "(/)" : parts.Skip(1).Aggregate(parts[0], (acc, p) => $"( {acc} u. {p} )");
            _defined.Add(n);
            Emit(n, itok, Maps(ps, set), sc, "inductive type");
        }

        // The constructors: ( p1 e. D1 |-> … ( a1 e. T1 |-> … tag(a1, …) ) ).
        for (int j = 0; j < ctors.Count; j++)
        {
            var sc = NewScope();
            Expr cty = ctors[j].Type;
            var ps = Telescope(ref cty, ind.NumParams, sc);
            var fs = Telescope(ref cty, ctors[j].NumFields, sc);
            _defined.Add(ctors[j].Name);
            Emit(ctors[j].Name, Token(ctors[j].Name)!, Maps(ps.Concat(fs), Tag(j, Tuple(fs.Select(f => f.Var).ToList()))), sc, "constructor");
        }

        // The recursor: ( params |-> ( motive |-> ( minors |-> ( t e. ⟦I params⟧ |-> case analysis on t ) ) ) ).
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bs = Telescope(ref rty, ind.NumParams + rec.NumMotives + rec.NumMinors + 1, sc);
            List<string> minors = bs.Skip(ind.NumParams + rec.NumMotives).Take(rec.NumMinors).Select(b => b.Var).ToList();
            string major = bs[^1].Var;
            string Minor(int j, string x) => Enumerable.Range(0, ctors[j].NumFields).Aggregate(minors[j], (acc, k) => $"( {acc} ` {Field(x, k)} )");
            string Case(int j, string x) => j == ctors.Count - 1
                ? Minor(j, $"( 2nd ` {x} )")
                : $"if ( ( 1st ` {x} ) = (/) , {Minor(j, $"( 2nd ` {x} )")} , {Case(j + 1, $"( 2nd ` {x} )")} )";
            // No constructors (Empty, PEmpty): the type is (/), so the recursor's major premise ranges over nothing,
            // and any value will do: (/).
            _defined.Add(rec.Name);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, ctors.Count == 0 ? "(/)" : Case(0, major)), sc, "recursor");
        }
    }

    /// <summary>
    /// A non-recursive inductive proposition, indexed or not: ( params |-> ( indices |-> if ( φ , 1o , (/) ) ) ), where φ
    /// says some constructor applies: E. fields ( indices = the constructor's indices ). Its constructors build (/)
    /// (every proof is (/)). Its recursor is (/) when it eliminates only into Prop; when it eliminates into any sort
    /// (one constructor whose fields are proofs, like Eq, And, True; or none, like False), it is that constructor's
    /// minor premise applied to (/) for each field, or (/) when there is no constructor.
    /// </summary>
    private void DefineProposition(ConstInfo ind, string itok)
    {
        Name n = ind.Name;
        List<ConstInfo> ctors = ind.Ctors.Select(c => env.Find(c) ?? throw new Refused($"{c} is not in the export")).ToList();
        ConstInfo rec = env.Find(t.Str(n, "rec")) ?? throw new Refused($"{n}.rec is not in the export");
        foreach (ConstInfo c in ctors.Append(rec))
        {
            _ = Token(c.Name) ?? throw new Refused($"{c.Name}: the name has characters a set.mm token can't");
        }

        // The proposition.
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc, pfv);
            var ifv = new List<Expr>();
            var ixs = Telescope(ref ty, ind.NumIndices, sc, ifv);
            var cases = new List<string>();
            foreach (ConstInfo c in ctors)
            {
                Expr cty = c.Type;
                Telescope(ref cty, ind.NumParams, sc, reuse: pfv);
                var fs = Telescope(ref cty, c.NumFields, sc);
                Ops.Spine(cty, out List<Expr> resultArgs);
                var eqs = ixs.Select((ix, i) => $"{ix.Var} = {Tr(resultArgs[ind.NumParams + i], sc)}").ToList();
                string body = eqs.Count == 0 ? "T." : eqs.Skip(1).Aggregate(eqs[0], (acc, e) => $"( {acc} /\\ {e} )");
                cases.Add(fs.AsEnumerable().Reverse().Aggregate(body, (acc, f) => $"E. {f.Var} e. {f.Dom} {acc}"));
            }
            string set = cases.Count == 0 ? "(/)" : $"if ( {cases.Skip(1).Aggregate(cases[0], (acc, c) => $"( {acc} \\/ {c} )")} , 1o , (/) )";
            _defined.Add(n);
            Emit(n, itok, Maps(ps.Concat(ixs), set), sc, "inductive proposition");
        }

        // The constructors: proofs, so (/).
        foreach (ConstInfo c in ctors)
        {
            var sc = NewScope();
            Expr cty = c.Type;
            var bs = Telescope(ref cty, ind.NumParams + c.NumFields, sc);
            _defined.Add(c.Name);
            Emit(c.Name, Token(c.Name)!, Maps(bs, "(/)"), sc, "constructor");
        }

        // The recursor.
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var mfv = new List<Expr>();
            var bs = Telescope(ref rty, ind.NumParams + rec.NumMotives + rec.NumMinors + ind.NumIndices + 1, sc, mfv);
            Expr motive = mfv[ind.NumParams];
            Expr mt = sc.Types[((FVar)motive).Id];
            while (mt is Binder { IsPi: true } mb)
            {
                mt = mb.Body;
            }
            bool large = mt is not Sort { Level: LZero };
            if (!large)
            {
                _intoPropOnly.Add(Token(rec.Name)!);
            }
            string body = "(/)";
            if (large && ctors.Count == 1)
            {
                // Subsingleton elimination: the one minor premise, at (/) for each field. That is right only when
                // every field is a proof. Lean also eliminates into any sort when a data field appears among the
                // result's indices (inductive Foo : Nat → Prop | mk (n : Nat) : Foo n), and there the minor premise
                // must get the index, not (/): refused until the model reads such fields back from the indices.
                {
                    var csc = NewScope();
                    Expr cty = ctors[0].Type;
                    var cfv = new List<Expr>();
                    Telescope(ref cty, ind.NumParams + ctors[0].NumFields, csc, cfv);
                    foreach (Expr f in cfv.Skip(ind.NumParams))
                    {
                        if (_typing.IsProposition(csc.Types[((FVar)f).Id], csc.Types) != true)
                        {
                            throw new Refused($"{n} has a field that is data, and eliminates into any sort; not in the model yet");
                        }
                    }
                }
                string minor = bs[ind.NumParams + rec.NumMotives].Var;
                body = Enumerable.Range(0, ctors[0].NumFields).Aggregate(minor, (acc, _) => $"( {acc} ` (/) )");
            }
            else if (large && ctors.Count > 1)
            {
                throw new Refused($"{n} eliminates into any sort with more than one constructor; not in the model yet");
            }
            _defined.Add(rec.Name);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, body), sc, "recursor");
        }
    }

    // ---- recursive types ------------------------------------------------------------------------------------------

    /// <summary>Set variables frr2 and exse reserve for their own proofs: the recursion's binders must avoid them.</summary>
    private static readonly string[] RecursionPool = "d e i j k m n o p q r s t w".Split(' ');

    private sealed record RecursiveInfo(string StepTok, string CaseTok, List<List<int>> RecFields);
    private readonly Dictionary<string, RecursiveInfo> _recursive = new();   // by the type's token

    /// <summary>
    /// A recursive inductive type with no indices, alone in its block, in Type, whose recursive fields are the type
    /// itself at its own parameters (finitary).
    /// - The type is the union of an ω-chain of stages, U_ n e. _om ( rec ( step , (/) ) ` n ), where the step
    ///   lean.I.-step = ( X e. _V |-> ( X u. F ( X ) ) ) adds every constructor's tagged tuple whose recursive fields
    ///   are in X. The step is a constant of its own so that a stage, substituted into it, doesn't carry the step's
    ///   bound variables into their own scope ($d). Lean names can't contain "-", so its name can't clash.
    /// - Constructors build tagged tuples as for non-recursive types.
    /// - The recursor is well-founded recursion over smaller rank: ( frecs ( RankLt , ⟦I params⟧ , H ) ` t ), where
    ///   H = ( a e. _V , f e. _V |-> case analysis on a, each minor premise given the fields and f at each recursive
    ///   field ). frr2 gives its computation rules (see <see cref="Iota"/>).
    /// </summary>
    private void DefineRecursive(ConstInfo ind, string itok)
    {
        Name n = ind.Name;
        List<ConstInfo> ctors = ind.Ctors.Select(c => env.Find(c) ?? throw new Refused($"{c} is not in the export")).ToList();
        ConstInfo rec = env.Find(t.Str(n, "rec")) ?? throw new Refused($"{n}.rec is not in the export");
        foreach (ConstInfo c in ctors.Append(rec))
        {
            _ = Token(c.Name) ?? throw new Refused($"{c.Name}: the name has characters a set.mm token can't");
        }
        if (ctors.Count == 0)
        {
            throw new Refused($"{n} has no constructors");
        }
        string steptok = itok + ".-step";

        // Which fields are recursive: exactly I at the parameters. Anything else mentioning I isn't finitary.
        bool IsSelf(Expr ty, List<Expr> ps) => Ops.Spine(ty, out List<Expr> a) is Const h && ReferenceEquals(h.Name, n)
            && a.Count == ps.Count && a.Zip(ps).All(z => ReferenceEquals(z.First, z.Second));
        bool Mentions(Expr e) => e switch
        {
            Const c => ReferenceEquals(c.Name, n),
            App a => Mentions(a.Fn) || Mentions(a.Arg),
            Binder b => Mentions(b.Domain) || Mentions(b.Body),
            Let l => Mentions(l.Type) || Mentions(l.Value) || Mentions(l.Body),
            Proj p => Mentions(p.Struct),
            _ => false,
        };

        // The step, over a packed argument w = <. <. u , params >. , X >.: ( w e. _V |-> ( X u. F ( X ) ) ), with u, the
        // parameters and X read from w. A single map over _V, with no universe layer: a definition may be a proper
        // class, but a function value can't, so the step can't be the value of a constant at u and the parameters.
        var recFields = new List<List<int>>();
        var stepBound = new List<string>();
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc, pfv);
            const string hole = "ZZX";
            var parts = new List<string>();
            for (int j = 0; j < ctors.Count; j++)
            {
                Expr cty = ctors[j].Type;
                Telescope(ref cty, ind.NumParams, sc, reuse: pfv);
                var fs = new List<(string Var, string Dom)>();
                var rf = new List<int>();
                for (int k = 0; k < ctors[j].NumFields; k++)
                {
                    var b = (Binder)cty;
                    string dom;
                    if (IsSelf(b.Domain, pfv))
                    {
                        dom = hole;
                        rf.Add(k);
                    }
                    else if (Mentions(b.Domain))
                    {
                        throw new Refused($"{ctors[j].Name} has a recursive field that isn't {n} itself (not finitary); not in the model yet");
                    }
                    else
                    {
                        dom = Tr(b.Domain, sc);
                    }
                    string v = Fresh(sc, dom);
                    Expr fv = t.FVar(_fresh++);
                    sc.Vars[((FVar)fv).Id] = v;
                    sc.Types[((FVar)fv).Id] = b.Domain;
                    if (!sc.Bound.Contains(v))
                    {
                        sc.Bound.Add(v);
                    }
                    sc.Active.Add(v);
                    fs.Add((v, dom));
                    cty = _ops.Instantiate(b.Body, [fv]);
                }
                foreach (var f in fs)
                {
                    sc.Active.Remove(f.Var);
                }
                recFields.Add(rf);
                string part = $"{{ {Tag(j, Tuple(fs.Select(f => f.Var).ToList()))} }}";
                parts.Add(fs.AsEnumerable().Reverse().Aggregate(part, (acc, f) => $"U_ {f.Var} e. {f.Dom} {acc}"));
            }
            string set = parts.Skip(1).Aggregate(parts[0], (acc, p) => $"( {acc} u. {p} )");
            string body = $"( {hole} u. {set} )";
            string w = FirstVar(x => !sc.Bound.Contains(x) && !body.Split(' ').Contains(x) && !ps.Any(q => q.Var == x));
            var packed = new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList();
            body = Unpack(body, packed, $"( 1st ` {w} )");
            body = Subst(body, hole, $"( 2nd ` {w} )");
            stepBound.AddRange(sc.Bound.Where(x => x != UniverseVar && !ps.Any(q => q.Var == x)));
            stepBound.Add(w);
            EmitRaw(t.Of($"{n}.-step"), steptok, $"( {w} e. _V |-> {body} )", stepBound, "inductive type's stage step, over a packed argument");
        }

        // The type: ( params |-> U_ k e. _om ( rec ( ( X e. _V |-> ( step ` <. <. u , params >. , X >. ) ) , (/) ) ` k ) ).
        {
            var sc = NewScope();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc);
            string pack = Tuple(new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList());
            string x = FirstVar(v => !sc.Bound.Contains(v) && !stepBound.Contains(v));
            sc.Bound.Add(x);
            string k = FirstVar(v => !sc.Bound.Contains(v));
            sc.Bound.Add(k);
            string stepf = $"( {x} e. _V |-> ( {steptok} ` <. {pack} , {x} >. ) )";
            _defined.Add(n);
            Emit(n, itok, Maps(ps, $"U_ {k} e. _om ( rec ( {stepf} , (/) ) ` {k} )"), sc, "recursive inductive type");
        }

        // The constructors, as for non-recursive types.
        for (int j = 0; j < ctors.Count; j++)
        {
            var sc = NewScope();
            Expr cty = ctors[j].Type;
            var ps = Telescope(ref cty, ind.NumParams, sc);
            var fs = Telescope(ref cty, ctors[j].NumFields, sc);
            _defined.Add(ctors[j].Name);
            Emit(ctors[j].Name, Token(ctors[j].Name)!, Maps(ps.Concat(fs), Tag(j, Tuple(fs.Select(f => f.Var).ToList()))), sc, "constructor");
        }

        // The case analysis, over a packed argument w = <. <. <. u , params , motive , minors >. , a >. , f >.:
        // ( w e. _V |-> if ( ( 1st ` a ) = (/) , minor0 fields ( f at recursive fields ) , … ) ).
        string casetok = itok + ".-case";
        int nb = ind.NumParams + rec.NumMotives + rec.NumMinors;
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bs = Telescope(ref rty, nb, sc);
            const string ha = "ZZA", hf = "ZZF";
            List<string> minors = bs.Skip(ind.NumParams + rec.NumMotives).Select(b => b.Var).ToList();
            string Minor(int j, string x) =>
                recFields[j].Aggregate(
                    Enumerable.Range(0, ctors[j].NumFields).Aggregate(minors[j], (acc, k) => $"( {acc} ` {Field(x, k)} )"),
                    (acc, k) => $"( {acc} ` ( {hf} ` {Field(x, k)} ) )");
            string Case(int j, string x) => j == ctors.Count - 1
                ? Minor(j, $"( 2nd ` {x} )")
                : $"if ( ( 1st ` {x} ) = (/) , {Minor(j, $"( 2nd ` {x} )")} , {Case(j + 1, $"( 2nd ` {x} )")} )";
            string body = Case(0, ha);
            string w = FirstVar(x => !body.Split(' ').Contains(x) && !bs.Any(q => q.Var == x) && x != UniverseVar);
            var packed = new[] { UniverseVar }.Concat(bs.Select(q => q.Var)).ToList();
            body = Unpack(body, packed, $"( 1st ` ( 1st ` {w} ) )");
            body = Subst(Subst(body, ha, $"( 2nd ` ( 1st ` {w} ) )"), hf, $"( 2nd ` {w} )");
            EmitRaw(t.Of($"{n}.-case"), casetok, $"( {w} e. _V |-> {body} )", [w], "recursor's case analysis, over a packed argument");
        }

        // The recursor: ( params |-> motive |-> minors |-> ( t e. ⟦I params⟧ |->
        //   ( frecs ( RankLt , ⟦I params⟧ , ( a e. _V , f e. _V |-> ( case ` <. <. Q , a >. , f >. ) ) ) ` t ) ) ).
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bs = Telescope(ref rty, nb + 1, sc);
            string major = bs[^1].Var, dom = bs[^1].Dom;
            string q = Tuple(new[] { UniverseVar }.Concat(bs.Take(nb).Select(b => b.Var)).ToList());
            string a = PickRecursionVar(sc), f = PickRecursionVar(sc), rx = PickRecursionVar(sc), ry = PickRecursionVar(sc);
            string rel = $"{{ <. {rx} , {ry} >. | ( rank ` {rx} ) e. ( rank ` {ry} ) }}";
            string g = $"( {a} e. _V , {f} e. _V |-> ( {casetok} ` <. <. {q} , {a} >. , {f} >. ) )";
            _defined.Add(rec.Name);
            _recursive[itok] = new RecursiveInfo(steptok, casetok, recFields);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, $"( frecs ( {rel} , {dom} , {g} ) ` {major} )"), sc, "recursor");
        }
    }

    /// <summary>
    /// A recursive inductive proposition (like Nat.le), indexed or not: the least set of index tuples closed under its
    /// constructors, built in stages as for recursive types, and the proposition true at indices whose tuple is in it:
    /// ( params |-> ( indices |-> if ( <. indices >. e. U_ k e. _om ( rec ( stepf , (/) ) ` k ) , 1o , (/) ) ) ).
    /// The step adds, for each constructor, the tuples of its result indices over its fields, where a recursive premise
    /// I params e⃗ ranges over if ( <. e⃗ >. e. X , 1o , (/) ): it holds when its own indices were in the last stage.
    /// Constructors are (/). A recursor that eliminates only into Prop is (/); others are refused for now.
    /// </summary>
    private void DefineRecursiveProposition(ConstInfo ind, string itok)
    {
        Name n = ind.Name;
        List<ConstInfo> ctors = ind.Ctors.Select(c => env.Find(c) ?? throw new Refused($"{c} is not in the export")).ToList();
        ConstInfo rec = env.Find(t.Str(n, "rec")) ?? throw new Refused($"{n}.rec is not in the export");
        foreach (ConstInfo c in ctors.Append(rec))
        {
            _ = Token(c.Name) ?? throw new Refused($"{c.Name}: the name has characters a set.mm token can't");
        }
        if (NeedsLeastFixedPoint(ind, ctors, rec))
        {
            DefineLeastProposition(ind, itok, ctors, rec);   // Model.Least.cs: Acc, and recursors into any sort
            return;
        }
        string steptok = itok + ".-step";
        bool Mentions(Expr e) => e switch
        {
            Const c => ReferenceEquals(c.Name, n),
            App a => Mentions(a.Fn) || Mentions(a.Arg),
            Binder b => Mentions(b.Domain) || Mentions(b.Body),
            Let l => Mentions(l.Type) || Mentions(l.Value) || Mentions(l.Body),
            Proj p => Mentions(p.Struct),
            _ => false,
        };

        // The step, over w = <. <. u , params >. , X >.
        var stepBound = new List<string>();
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc, pfv);
            const string hole = "ZZX";
            var parts = new List<string>();
            foreach (ConstInfo c in ctors)
            {
                Expr cty = c.Type;
                Telescope(ref cty, ind.NumParams, sc, reuse: pfv);
                var fs = new List<(string Var, string Dom)>();
                for (int k = 0; k < c.NumFields; k++)
                {
                    var b = (Binder)cty;
                    string dom;
                    if (Ops.Spine(b.Domain, out List<Expr> ra) is Const h && ReferenceEquals(h.Name, n))
                    {
                        if (ra.Count != ind.NumParams + ind.NumIndices || !ra.Take(ind.NumParams).Zip(pfv).All(z => ReferenceEquals(z.First, z.Second)))
                        {
                            throw new Refused($"{c.Name} has a recursive premise at other parameters; not in the model yet");
                        }
                        string idx = Tuple(ra.Skip(ind.NumParams).Select(e => Tr(e, sc)).ToList());
                        dom = $"if ( {idx} e. {hole} , 1o , (/) )";
                    }
                    else if (Mentions(b.Domain))
                    {
                        throw new Refused($"{c.Name} has a premise mentioning {n} other than as a premise; not in the model yet");
                    }
                    else
                    {
                        dom = Tr(b.Domain, sc);
                    }
                    string v = Fresh(sc, dom);
                    Expr fv = t.FVar(_fresh++);
                    sc.Vars[((FVar)fv).Id] = v;
                    sc.Types[((FVar)fv).Id] = b.Domain;
                    if (!sc.Bound.Contains(v))
                    {
                        sc.Bound.Add(v);
                    }
                    sc.Active.Add(v);
                    fs.Add((v, dom));
                    cty = _ops.Instantiate(b.Body, [fv]);
                }
                Ops.Spine(cty, out List<Expr> result);
                string tuple = Tuple(result.Skip(ind.NumParams).Select(e => Tr(e, sc)).ToList());
                foreach (var f in fs)
                {
                    sc.Active.Remove(f.Var);
                }
                parts.Add(fs.AsEnumerable().Reverse().Aggregate($"{{ {tuple} }}", (acc, f) => $"U_ {f.Var} e. {f.Dom} {acc}"));
            }
            string set = parts.Count == 0 ? "(/)" : parts.Skip(1).Aggregate(parts[0], (acc, p) => $"( {acc} u. {p} )");
            string body = $"( {hole} u. {set} )";
            string w = FirstVar(x => !sc.Bound.Contains(x) && !body.Split(' ').Contains(x) && !ps.Any(q => q.Var == x));
            var packed = new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList();
            body = Subst(Unpack(body, packed, $"( 1st ` {w} )"), hole, $"( 2nd ` {w} )");
            stepBound.AddRange(sc.Bound.Where(x => x != UniverseVar && !ps.Any(q => q.Var == x)));
            stepBound.Add(w);
            EmitRaw(t.Of($"{n}.-step"), steptok, $"( {w} e. _V |-> {body} )", stepBound, "inductive proposition's stage step, over a packed argument");
        }

        // The proposition.
        {
            var sc = NewScope();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc);
            var ixs = Telescope(ref ty, ind.NumIndices, sc);
            string pack = Tuple(new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList());
            string x = FirstVar(v => !sc.Bound.Contains(v) && !stepBound.Contains(v));
            sc.Bound.Add(x);
            string k = FirstVar(v => !sc.Bound.Contains(v));
            sc.Bound.Add(k);
            string stepf = $"( {x} e. _V |-> ( {steptok} ` <. {pack} , {x} >. ) )";
            string least = $"U_ {k} e. _om ( rec ( {stepf} , (/) ) ` {k} )";
            _defined.Add(n);
            Emit(n, itok, Maps(ps.Concat(ixs), $"if ( {Tuple(ixs.Select(q => q.Var).ToList())} e. {least} , 1o , (/) )"), sc, "recursive inductive proposition");
        }

        // Constructors: proofs, so (/).
        foreach (ConstInfo c in ctors)
        {
            var sc = NewScope();
            Expr cty = c.Type;
            var bs = Telescope(ref cty, ind.NumParams + c.NumFields, sc);
            _defined.Add(c.Name);
            Emit(c.Name, Token(c.Name)!, Maps(bs, "(/)"), sc, "constructor");
        }

        // The recursor: (/) when it eliminates only into Prop.
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var mfv = new List<Expr>();
            var bs = Telescope(ref rty, ind.NumParams + rec.NumMotives + rec.NumMinors + ind.NumIndices + 1, sc, mfv);
            Expr mt = sc.Types[((FVar)mfv[ind.NumParams]).Id];
            while (mt is Binder { IsPi: true } mb)
            {
                mt = mb.Body;
            }
            if (mt is not Sort { Level: LZero })
            {
                throw new Refused($"{rec.Name} eliminates a recursive proposition into any sort; not in the model yet");
            }
            _intoPropOnly.Add(Token(rec.Name)!);
            _defined.Add(rec.Name);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, "(/)"), sc, "recursor");
        }
    }

    /// <summary>
    /// A Nat literal n: ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` n ) ), with n as set.mm's decimal numeral. -ofnum is
    /// the inverse of set.mm's standard isomorphism from _om onto NN0, ( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om ),
    /// and -lit takes the ordinal k to Nat.succ applied k times to Nat.zero, in the model's encoding. So a literal stays
    /// as short as its decimal digits.
    /// </summary>
    private string NatLiteral(System.Numerics.BigInteger value)
    {
        Name nat = t.Of("Nat");
        Define(nat);
        const string lit = "lean.Nat.-lit", ofnum = "lean.Nat.-ofnum";
        if (!_values.ContainsKey(lit))
        {
            ConstInfo ind = env.Find(nat)!;
            int zero = Array.FindIndex(ind.Ctors, c => $"{c}" == "Nat.zero"), succ = Array.FindIndex(ind.Ctors, c => $"{c}" == "Nat.succ");
            if (zero < 0 || succ < 0)
            {
                throw new Refused("Nat's constructors aren't zero and succ");
            }
            EmitRaw(t.Of("Nat.-ofnum"), ofnum, "`' ( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om )", ["y"], "map from decimal numerals to ordinals, for Nat literals");
            EmitRaw(t.Of("Nat.-lit"), lit, $"( rec ( ( x e. _V |-> {Tag(succ, Tuple(["x"]))} ) , {Tag(zero, "(/)")} ) |` _om )", ["x"], "map from ordinals to the model's Nat, for Nat literals");
        }
        return $"( {lit} ` ( {ofnum} ` {Decimal(value)} ) )";
    }

    /// <summary>The first set variable satisfying the condition (set.mm's letters, then ours), or a refusal when all are used up.</summary>
    private string FirstVar(Func<string, bool> ok) =>
        Declare(SetVars.FirstOrDefault(ok) ?? throw new Refused("more set variables needed than the model declares"));

    private static string Decimal(System.Numerics.BigInteger n) => n < 10 ? n.ToString() : $"; {Decimal(n / 10)} {n % 10}";

    /// <summary>Replace each packed variable by its projection from the tuple: the i-th of a Tuple is Field(tuple, i).</summary>
    private static string Unpack(string body, List<string> packed, string tuple)
    {
        for (int i = 0; i < packed.Count; i++)
        {
            body = Subst(body, packed[i], Field(tuple, i));
        }
        return body;
    }

    /// <summary>A definition with no universe layer: df-tok $a |- tok = definiens $. (a map over a packed argument).</summary>
    private void EmitRaw(Name n, string tok, string definiens, IEnumerable<string> bound, string what)
    {
        if (definiens.Split(' ').Contains(WellOrderHole))
        {
            throw new Refused($"{n} depends on Classical.choice inside a packed helper; not in the model yet");
        }
        var b = bound.Distinct().ToList();
        string text = $"""
            $( The {what} of {NameEscape.CommentText($"{n}")}, for the model of docs/milestone3.md. $)
            $c {tok} $.
            c{LabelPart(tok)} $a class {tok} $.
            {"${"}
              {(b.Count > 1 ? $"$d {string.Join(' ', b)} $." : "")}
              df-{LabelPart(tok)} $a |- {tok} = {definiens} $.
            {"$}"}

            """;
        _out.AppendLine(text);
        _values[tok] = definiens;
        if (!dryRun)
        {
            pr.Database.Extend(text);
        }
    }

    /// <summary>A set variable fresh in the whole definition and outside frr2's and exse's reserved names.</summary>
    private string PickRecursionVar(Scope sc)
    {
        // Our own set variables appear in no set.mm proof, so frr2 and exse reserve none of them.
        foreach (string v in Enumerable.Reverse(RecursionPool).Concat(ExtraSetVars))   // not the span Reverse, which returns void
        {
            if (!sc.Bound.Contains(v))
            {
                sc.Bound.Add(v);
                return Declare(v);
            }
        }
        throw new Refused("no set variable left for the recursion");
    }

    private static void RefuseBinders(List<(string Var, string Dom)> fields, Name ctor)
    {
        // A field whose type binds variables would be written with different bound names in the type, the constructor
        // and the recursor; the computation rule matches them as text, so those are refused until it matches up to renaming.
        if (fields.Any(f => f.Dom.Contains(" |-> ", StringComparison.Ordinal) || f.Dom.StartsWith("X_ ", StringComparison.Ordinal) || f.Dom.Contains(" X_ ", StringComparison.Ordinal)))
        {
            throw new Refused($"{ctor} has a field whose type binds a variable; not in the model yet");
        }
    }

    // ---- equations ----------------------------------------------------------------------------------------------

    /// <summary>
    /// ( ph -> ( ( ( tok ` U ) ` a1 ) … ` an ) = value[a1, …] ), one fvmptd step per argument. Each argument's
    /// membership in its domain comes from <paramref name="argIn"/>, given the argument's index and the domain. Also
    /// returns, for the last step, the bound variable and the body before substitution.
    /// </summary>
    private (Proof Eq, string LastVar, string LastBody) Unfold(string ph, string tok, IReadOnlyList<string> args, Func<int, string, Proof> argIn)
    {
        string valueu = _values[tok];
        string valueU = Subst(valueu, UniverseVar, "U");
        Statement dfa = pr.Database["df-" + LabelPart(tok)];
        // The definition, its own variables substituted by themselves (a citation still pushes their syntax).
        Proof df = pr.Apply(dfa.Label, dfa.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!));
        Proof cur = Beta(ph, df, UniverseVar, UniverseDomain, valueu, "U", Hyp(ph, UHyp)!.Value, tok);
        string app = $"( {tok} ` U )", val = valueU, lastVar = UniverseVar, lastBody = valueu;
        for (int i = 0; i < args.Count; i++)
        {
            SyntaxTree m = pr.Parse("class", val.Split(' ')) ?? throw new Refused($"does not parse: {val}");
            if (m.Rule.Label != "cmpt")
            {
                throw new Refused($"expected a map, got {val}");
            }
            string x = pr.Render(m.Children[0]), dom = pr.Render(m.Children[1]), body = pr.Render(m.Children[2]);
            Proof cong = pr.Apply("fveq1d", S(("ph", ph), ("A", args[i]), ("F", app), ("G", val)), cur);
            Proof beta = Beta(ph, pr.Apply("eqid", S(("A", val))), x, dom, body, args[i], argIn(i, dom), val);
            cur = _d.Trans(cong, beta);
            app = $"( {app} ` {args[i]} )";
            val = Eq(beta).R;   // the substituted body, as Beta wrote it (it may rename the map's variables)
            (lastVar, lastBody) = (x, body);
        }
        return (cur, lastVar, lastBody);
    }

    /// <summary>The domains of the first <paramref name="count"/> maps of a value, each after substituting the arguments before it.</summary>
    private List<string> Domains(string tok, IReadOnlyList<string> args, int count)
    {
        string val = Subst(_values[tok], UniverseVar, "U");
        var r = new List<string>();
        for (int i = 0; i < count; i++)
        {
            SyntaxTree m = pr.Parse("class", val.Split(' '))!;
            if (m.Rule.Label != "cmpt")
            {
                throw new Refused($"expected a map, got {val}");
            }
            r.Add(pr.Render(m.Children[1]));
            val = Subst(pr.Render(m.Children[2]), pr.Render(m.Children[0]), args[i]);
        }
        return r;
    }

    private static int Arity(Prover pr, string value)
    {
        int k = 0;
        while (pr.Parse("class", value.Split(' ')) is SyntaxTree { Rule.Label: "cmpt" } m)
        {
            k++;
            value = pr.Render(m.Children[2]);
        }
        return k;
    }

    private static string Conj(IEnumerable<string> hyps) => hyps.Skip(1).Aggregate(hyps.First(), (acc, h) => $"( {acc} /\\ {h} )");

    private string[] DistinctFor(IEnumerable<string> toks, IEnumerable<string> classVars)
    {
        var setvars = new HashSet<string> { UniverseVar };
        foreach (string tok in toks)
        {
            setvars.UnionWith(_values[tok].Split(' ').Where(SetVarSet.Contains));
        }
        setvars.UnionWith(_renamedTo);
        return [string.Join(' ', setvars.Concat(classVars.Where(v => v != "(/)")).Append("U"))];
    }

    /// <summary>
    /// A parameter or field that is a proof is (/) in the model, so the computation rule takes (/) for it rather than a
    /// class variable that the translation would replace by (/) in some places only. This happens at instances that put
    /// Prop where Lean has Sort u (define-all's level 0): Eq.refl.{0}, CoeDep.mk.{0,0}.
    /// </summary>
    private void ProofsAsEmpty(Expr ctorType, int np, List<string> recArgs, List<string> fields)
    {
        var types = new Dictionary<ulong, Expr>();
        Expr ty = ctorType;
        for (int i = 0; i < np + fields.Count && ty is Binder { IsPi: true } b; i++)
        {
            if (_typing.IsProposition(b.Domain, types) == true)
            {
                if (i < np)
                {
                    recArgs[i] = "(/)";
                }
                else
                {
                    fields[i - np] = "(/)";
                }
            }
            Expr fv = t.FVar(_fresh++);
            types[((FVar)fv).Id] = b.Domain;
            ty = _ops.Instantiate(b.Body, [fv]);
        }
    }

    /// <summary>
    /// The definitional equation of a constant c whose value is n maps deep, as a set.mm theorem:
    /// |- ( ( ( U e. Univ /\ A e. D1 ) /\ … ) -> ( ( ( lean.c ` U ) ` A ) … ) = body[A, …] ),
    /// with its proof and the distinct-variable conditions it needs.
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) Equation(Name n)
    {
        Define(n);
        string tok = Token(n)!;
        int arity = Arity(pr, _values[tok]);
        List<string> cv = ClassVarsFor(arity, "more parameters than class variables");
        var args = _choiceDependent.Contains(tok) ? cv.Take(arity - 1).Prepend("W").ToList() : cv;
        List<string> doms = Domains(tok, args, arity);
        var hyps = new List<string> { UHyp };
        hyps.AddRange(args.Select((a, i) => $"{a} e. {doms[i]}"));
        string ph = Conj(hyps);
        (Proof eq, _, _) = Unfold(ph, tok, args, (i, dom) => Hyp(ph, $"{args[i]} e. {dom}") ?? throw new Refused($"no hypothesis {args[i]} e. {dom}"));
        return (eq.Proves, eq.Proof, DistinctFor([tok], args));
    }

    /// <summary>
    /// The computation rule of a constructor c of a type I (Lean's iota reduction), as a set.mm theorem:
    /// I.rec params motive minors (c params fields) = minor_c fields, for arguments of the right types.
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) Iota(Name ctorName)
    {
        Define(ctorName);
        ConstInfo ctor = env.Find(ctorName)!;
        if (ctor.Kind != ConstKind.Constructor)
        {
            throw new Refused($"{ctorName} is not a constructor");
        }
        ConstInfo ind = env.Find(ctor.Induct!)!;
        if (_blocks.ContainsKey(ind.Name))
        {
            return BlockIota(ind.Name, ctorName);   // Model.Mutual.cs
        }
        ConstInfo rec = env.Find(t.Str(ind.Name, "rec"))!;
        if (_choiceDependent.Contains(Token(ind.Name)!) || _choiceDependent.Contains(Token(ctorName)!) || _choiceDependent.Contains(Token(rec.Name)!))
        {
            throw new Refused($"{ind.Name} depends on Classical.choice; its computation rules aren't in the model yet");
        }
        if (IsProposition(ind))
        {
            return PropositionIota(ctor, ind, rec);
        }
        string itok = Token(ind.Name)!, ctok = Token(ctorName)!, rtok = Token(rec.Name)!;
        if (_recursive.ContainsKey(itok))
        {
            return RecursiveIota(ctor, ind, rec);
        }
        int j = Array.FindIndex(ind.Ctors, c => ReferenceEquals(c, ctorName));
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors, nf = ctor.NumFields;
        List<string> cv = ClassVarsFor(nrec + nf, "more arguments than class variables");
        List<string> recArgs = cv.Take(nrec).ToList();
        List<string> fields = cv.Skip(nrec).Take(nf).ToList();
        ProofsAsEmpty(ctor.Type, np, recArgs, fields);
        List<string> ctorArgs = recArgs.Take(np).Concat(fields).ToList();
        string v = ctorArgs.Aggregate($"( {ctok} ` U )", (acc, a) => $"( {acc} ` {a} )");

        // Hypotheses: the recursor's arguments, then the fields, each in its domain.
        var hyps = new List<string> { UHyp };
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        hyps.AddRange(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}"));
        List<string> cdoms = Domains(ctok, ctorArgs, np + nf);
        hyps.AddRange(fields.Select((a, i) => $"{a} e. {cdoms[np + i]}"));
        string ph = Conj(hyps);
        Proof Pick(int _, string h) => Hyp(ph, h) ?? HypUpToRenaming(ph, h, hyps) ?? throw new Refused($"no hypothesis {h}");

        // The constructor's value, and the type at the parameters.
        (Proof eqV, _, _) = Unfold(ph, ctok, ctorArgs, (i, dom) => Pick(i, $"{ctorArgs[i]} e. {dom}"));
        string tag = Rhs(eqV);
        List<string> ps = recArgs.Take(np).ToList();
        (Proof eqT, _, _) = Unfold(ph, itok, ps, (i, dom) => Pick(i, $"{ps[i]} e. {dom}"));
        string iapp = Lhs(eqT), set = Rhs(eqT);

        // The tagged tuple is in the type: through the union to constructor j's part, then down its indexed unions.
        Proof inSet = MemberUnion(ph, tag, set, ind.Ctors.Length, j, fields, Pick);
        Proof iff = pr.Apply("eleq12d", S(("ph", ph), ("A", v), ("B", tag), ("C", iapp), ("D", set)), eqV, eqT);
        Proof inType = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{v} e. {iapp}"), ("ch", $"{tag} e. {set}")), inSet, iff);

        // The recursor at the constructor's value: its case analysis, on the tag, then simplified.
        var allArgs = recArgs.Append(v).ToList();
        (Proof eqR, string lastVar, string lastBody) = Unfold(ph, rtok, allArgs, (i, dom) => i < nrec ? Pick(i, $"{allArgs[i]} e. {dom}") : inType);
        // A recursor whose case analysis doesn't look at its value (one constructor, no fields: PUnit.rec, found by the
        // Init-wide run) needs no rewriting to the tagged tuple.
        string context = Subst(lastBody, lastVar, "Z");
        Proof cur = context.Split(' ').Contains("Z") ? _d.Trans(eqR, _d.Congruence("class", context, "Z", eqV)) : eqR;
        if (Simp(ph, Rhs(cur)) is Proof simp)
        {
            cur = _d.Trans(cur, simp);
        }
        string minor = recArgs[np + rec.NumMotives + j];
        string want = fields.Aggregate(minor, (acc, f) => $"( {acc} ` {f} )");
        if (Rhs(cur) != want)
        {
            throw new InvalidOperationException($"the computation rule came out as {Rhs(cur)}, not {want}");
        }
        return (cur.Proves, cur.Proof, DistinctFor([itok, ctok, rtok], recArgs.Concat(fields)));
    }

    /// <summary>
    /// The computation rule of a constructor of a recursive type:
    /// I.rec params motive minors (c params fields) = minor fields (I.rec params motive minors r) for each recursive r.
    /// 1. The constructor's value is in the type: through the stages (eliun, the step's equation, rdgsuc, ssiun2s),
    ///    proved under only the parameters' and fields' hypotheses (the others mention bound variables).
    /// 2. frr2 unfolds the recursion once, with lean-rankfr for Fr and exse for Se.
    /// 3. The case analysis is evaluated on the tag (ovmpog, then the simplifier).
    /// 4. The recursion at each recursive field r is the recursor at r: r is a predecessor of the value, since it has
    ///    smaller rank (elpredg, brabga, and the rank of a pair's components), so fvres applies.
    /// </summary>
    private (MmExpr Statement, List<string> Proof, string[] Distinct) RecursiveIota(ConstInfo ctor, ConstInfo ind, ConstInfo rec)
    {
        string itok = Token(ind.Name)!, ctok = Token(ctor.Name)!, rtok = Token(rec.Name)!;
        RecursiveInfo info = _recursive[itok];
        int j = Array.FindIndex(ind.Ctors, c => ReferenceEquals(c, ctor.Name));
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors, nf = ctor.NumFields;
        List<int> rf = info.RecFields[j];
        List<string> cv = ClassVarsFor(nrec + nf, "more arguments than class variables");
        List<string> recArgs = cv.Take(nrec).ToList(), ps = recArgs.Take(np).ToList();
        List<string> fields = cv.Skip(nrec).Take(nf).ToList();
        List<string> ctorArgs = ps.Concat(fields).ToList();
        string v = ctorArgs.Aggregate($"( {ctok} ` U )", (acc, a) => $"( {acc} ` {a} )");

        var hyps = new List<string> { UHyp };
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        hyps.AddRange(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}"));
        List<string> cdoms = Domains(ctok, ctorArgs, np + nf);
        RefuseBinders(cdoms.Skip(np).Select(d => ("", d)).ToList(), ctor.Name);
        List<string> fieldHyps = fields.Select((a, i) => $"{a} e. {cdoms[np + i]}").ToList();
        hyps.AddRange(fieldHyps);
        string ph = Conj(hyps);
        Proof Pick(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");

        // 1. Membership, under the parameters' and fields' hypotheses only.
        string small = Conj(new[] { UHyp }.Concat(ps.Select((a, i) => $"{a} e. {rdoms[i]}")).Concat(fieldHyps));
        var extraVars = new List<string>();
        (Proof eqV0, string tag, string iapp, Proof vInSmall) = RecursiveMembership(small, ctok, itok, info, j, ind.Ctors.Length, ps, fields, extraVars);
        Proof inType = _d.Syl(Restrict(ph, small), vInSmall);
        Proof eqV = _d.Syl(Restrict(ph, small), eqV0);

        // 2. frr2.
        (Proof eqR, _, _) = Unfold(ph, rtok, recArgs.Append(v).ToList(), (i, dom) => i < nrec ? Pick(ph, $"{recArgs[i]} e. {dom}") : inType);
        string frApp = Rhs(eqR);
        string fr = Part(frApp, "F");
        string rel = Part(fr, "R"), caseApp = Part(fr, "F");
        string rx = Part(rel, "x"), ry = Part(rel, "y");
        EnsureRankFr();
        Proof frOk = _d.Lift(ph, pr.Apply("lean-rankfr", S(("x", rx), ("y", ry), ("A", iapp))));
        Proof seOk = _d.Syl(Exists(ph, iapp), pr.Apply("exse", S(("A", iapp), ("V", "_V"), ("R", rel))));
        Proof frEq = pr.Apply("eqid", S(("A", fr)));
        Proof once = _d.Syl(_d.Jca(_d.Jca(frOk, seOk), inType),
            pr.Apply("frr2", S(("R", rel), ("A", iapp), ("G", caseApp), ("X", v), ("F", fr)), frEq));
        string g = $"( {fr} |` Pred ( {rel} , {iapp} , {v} ) )";

        // 3. The case analysis at the value: rename the operation's variables away from g (which contains them), apply
        // it (ovmpog), unfold the case analysis at the packed argument, and read the parts back.
        string a0 = Part(caseApp, "x"), f0 = Part(caseApp, "y"), body0 = Part(caseApp, "C");
        var used = (fr + " " + v + " " + ph).Split(' ').ToHashSet();
        string a = FirstVar(x => !used.Contains(x) && x != a0 && x != f0);
        string f = FirstVar(x => !used.Contains(x) && x != a0 && x != f0 && x != a);
        extraVars.AddRange([a, f]);
        string bodyA = Subst(body0, a0, a), body = Subst(bodyA, f0, f);
        string mpo = $"( {a} e. _V , {f} e. _V |-> {body} )";
        Proof ren2 = pr.Apply("cbvmpov", S(("x", a0), ("y", f0), ("z", a), ("w", f), ("A", "_V"), ("B", "_V"), ("C", body0), ("E", bodyA), ("D", body)),
            _d.Congruence("class", Subst(body0, a0, "Z"), "Z", pr.Apply("id", S(("ph", $"{a0} = {a}")))),
            _d.Congruence("class", Subst(bodyA, f0, "Z"), "Z", pr.Apply("id", S(("ph", $"{f0} = {f}")))));
        string atV = Subst(body, a, v), atVg = Subst(atV, f, g);
        Proof toMpo = pr.Apply("oveqd", S(("ph", ph), ("A", caseApp), ("B", mpo), ("C", v), ("D", g)), _d.Lift(ph, ren2));
        Proof h1 = _d.Congruence("class", Subst(body, a, "Z"), "Z", pr.Apply("id", S(("ph", $"{a} = {v}"))));
        Proof h2 = _d.Congruence("class", Subst(atV, f, "Z"), "Z", pr.Apply("id", S(("ph", $"{f} = {g}"))));
        Proof frFn = _d.Syl(_d.Jca(frOk, seOk), pr.Apply("frr1", S(("R", rel), ("A", iapp), ("G", caseApp), ("F", fr)), frEq));
        Proof frSet = _d.Syl(_d.Jca(frFn, Exists(ph, iapp)), pr.Apply("fnex", S(("F", fr), ("A", iapp), ("B", "_V"))));
        Proof gSet = _d.Syl(frSet, pr.Apply("resexg", S(("A", fr), ("V", "_V"), ("B", $"Pred ( {rel} , {iapp} , {v} )"))));
        _known[(ph, fr)] = frSet;
        _known[(ph, g)] = gSet;
        Proof ov = _d.Syl(pr.Apply("3jca", S(("ph", ph), ("ps", $"{v} e. _V"), ("ch", $"{g} e. _V"), ("th", $"{atVg} e. _V")),
                Exists(ph, v), gSet, Exists(ph, atVg)),
            pr.Apply("ovmpog", S(("x", a), ("y", f), ("A", v), ("B", g), ("C", "_V"), ("D", "_V"), ("R", body), ("G", atV), ("S", atVg), ("F", mpo), ("H", "_V")),
                h1, h2, pr.Apply("eqid", S(("A", mpo)))));
        Proof cur = _d.Trans(_d.Trans(_d.Trans(eqR, once), toMpo), ov);
        string caseArg = Part(atVg, "A");
        cur = _d.Trans(cur, UnfoldRaw(ph, info.CaseTok, caseArg));
        if (Simp(ph, Rhs(cur)) is Proof simp0)
        {
            cur = _d.Trans(cur, simp0);
        }
        // The value v as the tagged tuple, outside g (which mentions v too).
        const string gHole = "ZZG";
        string ctxTag = Rhs(cur).Replace(g, gHole, StringComparison.Ordinal).Replace(v, "Z", StringComparison.Ordinal).Replace(gHole, g, StringComparison.Ordinal);
        if (ctxTag.Split(' ').Contains("Z"))
        {
            cur = _d.Trans(cur, _d.Congruence("class", ctxTag, "Z", eqV));
        }
        if (Simp(ph, Rhs(cur)) is Proof simp)
        {
            cur = _d.Trans(cur, simp);
        }

        // 4. The recursion at the recursive field is the recursor there.
        string minor = recArgs[np + rec.NumMotives + j];
        string want = fields.Aggregate(minor, (acc, x) => $"( {acc} ` {x} )");
        foreach (int ri in rf)
        {
            string r = fields[ri];
            string pred = $"Pred ( {rel} , {iapp} , {v} )";
            Proof rankLt = pr.Apply("eleqtrrd", S(("ph", ph), ("A", $"( rank ` {r} )"), ("B", $"( rank ` {tag} )"), ("C", $"( rank ` {v} )")),
                RankChain(ph, r, tag), pr.Apply("fveq2d", S(("ph", ph), ("A", v), ("B", tag), ("F", "rank")), eqV));
            Proof brBi = _d.Syl(_d.Jca(Exists(ph, r), Exists(ph, v)), Brabga(rx, ry, r, v, rel));
            Proof isR = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{r} {rel} {v}"), ("ch", $"( rank ` {r} ) e. ( rank ` {v} )")), rankLt, brBi);
            Proof predBi = _d.Syl(_d.Jca(Exists(ph, v), Pick(ph, $"{r} e. {iapp}")),
                pr.Apply("elpredg", S(("X", v), ("B", "_V"), ("Y", r), ("A", iapp), ("R", rel))));
            Proof inPred = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{r} e. {pred}"), ("ch", $"{r} {rel} {v}")), isR, predBi);
            Proof e1 = _d.Syl(inPred, pr.Apply("fvres", S(("A", r), ("B", pred), ("F", fr))));
            (Proof back, _, _) = Unfold(ph, rtok, recArgs.Append(r).ToList(), (i, dom) => Pick(ph, $"{(i < nrec ? recArgs[i] : r)} e. {dom}"));
            Proof e = _d.Trans(e1, _d.Symm(back));
            string here = $"( {g} ` {r} )";
            string ctxText = Rhs(cur).Replace(here, "Z", StringComparison.Ordinal);
            cur = _d.Trans(cur, _d.Congruence("class", ctxText, "Z", e));
            want = $"( {want} ` {Lhs(back)} )";
        }
        if (Rhs(cur) != want)
        {
            throw new InvalidOperationException($"the computation rule came out as {Rhs(cur)}, not {want}");
        }
        string[] dv = DistinctFor([itok, ctok, rtok, info.StepTok, info.CaseTok], recArgs.Concat(fields));
        return (cur.Proves, cur.Proof, [string.Join(' ', $"{dv[0]} {string.Join(' ', extraVars)}".Split(' ', StringSplitOptions.RemoveEmptyEntries).Distinct())]);
    }

    /// <summary>
    /// ( small -> c ps fields e. ⟦I ps⟧ ) for constructor j of a recursive type I: through the stages (eliun, the step's
    /// equation, rdgsuc, ssiun2s, and lean-stagess for several recursive fields). small holds the parameters' and fields'
    /// hypotheses; the parameters may be any terms, so a nested block's List (Rose α) uses it too. Also returns the
    /// constructor's equation, its tagged tuple, and ⟦I ps⟧ as applied.
    /// </summary>
    private (Proof EqV0, string Tag, string Iapp, Proof VIn) RecursiveMembership(string small, string ctok, string itok, RecursiveInfo info, int j, int numCtors,
        List<string> ps, List<string> fields, List<string> extraVars)
    {
        Proof Pick(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");
        List<int> rf = info.RecFields[j];
        List<string> ctorArgs = ps.Concat(fields).ToList();
        string v = ctorArgs.Aggregate($"( {ctok} ` U )", (acc, a) => $"( {acc} ` {a} )");
        (Proof eqV0, _, _) = Unfold(small, ctok, ctorArgs, (i, dom) => Pick(small, $"{ctorArgs[i]} e. {dom}"));
        string tag = Rhs(eqV0);
        (Proof eqT0, _, _) = Unfold(small, itok, ps, (i, dom) => Pick(small, $"{ps[i]} e. {dom}"));
        string iapp = Lhs(eqT0), set = Rhs(eqT0);
        string k = Part(set, "x"), stageBody = Part(set, "B");
        string Stage(string b) => Subst(stageBody, k, b);
        // rec ( stepf , (/) ) ` k: the stage function stepf = ( X e. _V |-> ( step ` <. P , X >. ) )
        string stepApp = Part(Part(Stage("(/)"), "F"), "F");
        string sx = Part(stepApp, "x"), sBody = Part(stepApp, "B");


        // ( ctx -> ( stepf ` sb ) = ( sb u. F ( sb ) ) ): rename stepf's variable away from sb (which contains it),
        // apply it, unfold the step at the packed argument, and read the packed parts back.
        Proof StepAt(string ctx, string sb)
        {
            string y = FirstVar(x => x != sx && !sb.Split(' ').Contains(x) && !sBody.Split(' ').Contains(x) && !ctx.Split(' ').Contains(x));
            extraVars.Add(y);
            string bodyY = Subst(sBody, sx, y), stepY = $"( {y} e. _V |-> {bodyY} )";
            Proof ren = pr.Apply("cbvmptv", S(("x", sx), ("y", y), ("A", "_V"), ("B", sBody), ("C", bodyY)),
                _d.Congruence("class", Subst(sBody, sx, "Z"), "Z", pr.Apply("id", S(("ph", $"{sx} = {y}")))));
            Proof e1 = pr.Apply("fveq1d", S(("ph", ctx), ("A", sb), ("F", stepApp), ("G", stepY)), _d.Lift(ctx, ren));
            Proof e2 = Beta(ctx, pr.Apply("eqid", S(("A", stepY))), y, "_V", bodyY, sb, Exists(ctx, sb), stepY);
            string arg = Subst(bodyY, y, sb);   // ( step ` <. P , sb >. )
            string packedArg = Part(arg, "A");
            Proof e3 = UnfoldRaw(ctx, info.StepTok, packedArg);
            Proof cur2 = _d.Trans(_d.Trans(e1, e2), e3);
            return Simp(ctx, Rhs(cur2)) is Proof sp ? _d.Trans(cur2, sp) : cur2;
        }

        Proof TagInStage(string ctx, string b, Proof bInOm, Func<int, Proof>? rIn)
        {
            string sb = Stage(b);
            Proof eqStep = StepAt(ctx, sb);
            string un = Rhs(eqStep);
            string fsb = Part(un, "B");
            Proof inF = MemberUnion(ctx, tag, fsb, numCtors, j, fields,
                (kk, h) => rf.Contains(kk) ? rIn!(kk) : Pick(ctx, h));
            Proof inUn = _d.Syl(inF, pr.Apply("elun2", S(("A", tag), ("B", fsb), ("C", sb))));
            Proof inStep = pr.Apply("eleqtrrd", S(("ph", ctx), ("A", tag), ("B", un), ("C", Lhs(eqStep))), inUn, eqStep);
            Proof rdg = _d.Syl(_d.Syl(bInOm, pr.Apply("nnon", S(("A", b)))), pr.Apply("rdgsuc", S(("B", b), ("F", stepApp), ("A", "(/)"))));
            string sucStage = Stage($"suc {b}");
            Proof inSuc = pr.Apply("eleqtrrd", S(("ph", ctx), ("A", tag), ("B", Lhs(eqStep)), ("C", sucStage)), inStep, rdg);
            Proof sub = _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = suc {b}"))));
            Proof incl = pr.Apply("ssiun2s", S(("x", k), ("A", "_om"), ("B", stageBody), ("C", $"suc {b}"), ("D", sucStage)), sub);
            Proof sub2 = _d.Syl(_d.Syl(bInOm, pr.Apply("peano2", S(("A", b)))), incl);
            Proof imp = pr.Apply("sseld", S(("ph", ctx), ("A", sucStage), ("B", set), ("C", tag)), sub2);
            Proof inSet = pr.Apply("mpd", S(("ph", ctx), ("ps", $"{tag} e. {sucStage}"), ("ch", $"{tag} e. {set}")), inSuc, imp);
            Proof eqT = _d.Syl(Restrict(ctx, small), eqT0);
            return pr.Apply("eleqtrrd", S(("ph", ctx), ("A", tag), ("B", set), ("C", iapp)), inSet, eqT);
        }

        Proof tagIn;
        if (rf.Count == 0)
        {
            tagIn = TagInStage(small, "(/)", _d.Lift(small, pr.Apply("peano1", S())), null);
        }
        else
        {
            // Each recursive field r_i is in some stage m_i (a variable of its own: ssiun2s needs the union's k disjoint
            // from suc m_i). Under ctx_i = ( ( ctx_i-1 /\ m_i e. _om ) /\ r_i e. stage m_i ), all of them are in the stage
            // b = ( ( m_1 u. m_2 ) u. … ), by lean-stagess; the tag is in the next one, and rexlimdva2 discharges the m_i.
            var stepVars = _values[info.StepTok].Split(' ').ToHashSet();
            var taken = new HashSet<string>(set.Split(' ').Concat(small.Split(' ')).Concat(stepApp.Split(' ')).Concat(stepVars)) { k };
            string Fresh() { string x = FirstVar(y => !taken.Contains(y)); taken.Add(x); extraVars.Add(x); return x; }
            Proof rInSet0(string r) => pr.Apply("eleqtrd", S(("ph", small), ("A", r), ("B", iapp), ("C", set)), Pick(small, $"{r} e. {iapp}"), eqT0);
            var ms = new List<string>();
            var somes = new List<Proof>();
            var ctxs = new List<string> { small };
            foreach (int ri in rf)
            {
                string r = fields[ri], m = Fresh();
                string setM = $"U_ {m} e. _om {Stage(m)}";
                Proof ren = pr.Apply("cbviunv", S(("x", k), ("y", m), ("A", "_om"), ("B", stageBody), ("C", Stage(m))),
                    _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = {m}")))));
                Proof rInSetM = pr.Apply("eleqtrd", S(("ph", small), ("A", r), ("B", set), ("C", setM)), rInSet0(r), _d.Lift(small, ren));
                Proof some = pr.Apply("sylib", S(("ph", small), ("ps", $"{r} e. {setM}"), ("ch", $"E. {m} e. _om {r} e. {Stage(m)}")),
                    rInSetM, pr.Apply("eliun", S(("A", r), ("x", m), ("B", "_om"), ("C", Stage(m)))));
                somes.Add(ctxs.Count == 1 ? some : _d.Syl(Restrict(ctxs[^1], small), some));
                ms.Add(m);
                ctxs.Add($"( ( {ctxs[^1]} /\\ {m} e. _om ) /\\ {r} e. {Stage(m)} )");
            }
            string ctx = ctxs[^1];

            // b, b e. _om, and m_i C_ b.
            var bs = new List<string> { ms[0] };
            Proof bOm = Pick(ctx, $"{ms[0]} e. _om");
            for (int i = 1; i < ms.Count; i++)
            {
                bs.Add($"( {bs[^1]} u. {ms[i]} )");
                bOm = _d.Syl(_d.Jca(bOm, Pick(ctx, $"{ms[i]} e. _om")), pr.Apply("omun", S(("A", bs[^2]), ("B", ms[i]))));
            }
            string b = bs[^1];
            Proof SsB(int i, int level) => i == level
                ? (level == 0 ? pr.Apply("ssid", S(("A", ms[0]))) : pr.Apply("ssun2", S(("A", ms[i]), ("B", bs[level - 1]))))
                : pr.Apply("sstri", S(("A", ms[i]), ("B", bs[level - 1]), ("C", bs[level])),
                    SsB(i, level - 1), pr.Apply("ssun1", S(("A", bs[level - 1]), ("B", ms[level]))));

            // The step's values contain their argument: ( small -> z C_ ( stepf ` z ) ), lean-stagess's hypothesis.
            Proof? grows = null;
            Proof RIn(int ri)
            {
                int i = rf.IndexOf(ri);
                string r = fields[ri];
                Proof here = Pick(ctx, $"{r} e. {Stage(ms[i])}");
                if (ms.Count == 1)
                {
                    return here;
                }
                if (grows is null)
                {
                    EnsureStageSs();
                    string z = Fresh();
                    Proof eqZ = StepAt(small, z);
                    grows = pr.Apply("sseqtrrd", S(("ph", small), ("A", z), ("B", Rhs(eqZ)), ("C", Lhs(eqZ))),
                        _d.Lift(small, pr.Apply("ssun1", S(("A", z), ("B", Part(Rhs(eqZ), "B"))))), eqZ);
                }
                string z0 = _d.Split(grows.Value.Proves).X.Split(' ')[0];
                Proof mono = pr.Apply(Recursion.StageSsLabel, S(("ph", small), ("z", z0), ("F", stepApp), ("A", "(/)"), ("M", b), ("N", ms[i])), grows.Value);
                Proof ante = _d.Jca(_d.Jca(bOm, Pick(ctx, $"{ms[i]} e. _om")), _d.Lift(ctx, SsB(i, ms.Count - 1)));
                Proof ss = pr.Apply("mpd", S(("ph", ctx), ("ps", small), ("ch", $"{Stage(ms[i])} C_ {Stage(b)}")),
                    Restrict(ctx, small), _d.Syl(ante, mono));
                Proof imp = pr.Apply("sseld", S(("ph", ctx), ("A", Stage(ms[i])), ("B", Stage(b)), ("C", r)), ss);
                return pr.Apply("mpd", S(("ph", ctx), ("ps", $"{r} e. {Stage(ms[i])}"), ("ch", $"{r} e. {Stage(b)}")), here, imp);
            }
            tagIn = TagInStage(ctx, b, bOm, RIn);
            for (int i = ms.Count - 1; i >= 0; i--)
            {
                string r = fields[rf[i]], m = ms[i];
                Proof lim = pr.Apply("rexlimdva2", S(("ph", ctxs[i]), ("x", m), ("A", "_om"), ("ps", $"{r} e. {Stage(m)}"), ("ch", $"{tag} e. {iapp}")), tagIn);
                tagIn = pr.Apply("mpd", S(("ph", ctxs[i]), ("ps", $"E. {m} e. _om {r} e. {Stage(m)}"), ("ch", $"{tag} e. {iapp}")), somes[i], lim);
            }
        }
        _ctorIn = (tagIn, extraVars.ToList());   // for the theorem translator's constructor typing (TheoremTranslator.cs)
        Proof vInSmall = pr.Apply("eqeltrd", S(("ph", small), ("A", v), ("B", tag), ("C", iapp)), eqV0, tagIn);
        return (eqV0, tag, iapp, vInSmall);
    }

    /// <summary>The part of a class term bound to the syntax variable <paramref name="var"/> of its top syntax axiom.</summary>
    private string Part(string term, string var)
    {
        SyntaxTree n = pr.Parse("class", term.Split(' ')) ?? throw new InvalidOperationException($"does not parse: {term}");
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
        int i = vars.IndexOf(var);
        return i >= 0 ? pr.Render(n.Children[i]) : throw new InvalidOperationException($"{n.Rule.Label} has no {var}");
    }

    /// <summary>( ph -> ( tok ` arg ) = body[w := arg] ) for a definition with no universe layer, tok = ( w e. _V |-> body ).</summary>
    private Proof UnfoldRaw(string ph, string tok, string arg)
    {
        Statement dfa = pr.Database["df-" + LabelPart(tok)];
        Proof df = pr.Apply(dfa.Label, dfa.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!));
        SyntaxTree m = pr.Parse("class", _values[tok].Split(' '))!;
        string w = pr.Render(m.Children[0]), body = pr.Render(m.Children[2]);
        return Beta(ph, df, w, "_V", body, arg, Exists(ph, arg), tok);
    }

    /// <summary>( ctx -> X e. _V ) where the map's domain is _V (an argument X of a map over _V).</summary>
    private Proof ExistsIn2(string ctx, string x, string dom) =>
        dom == "_V" ? Exists(ctx, x) : throw new InvalidOperationException($"expected the domain _V, got {dom}");

    /// <summary>( ph -> small ), for small a conjunction of some of ph's conjuncts.</summary>
    private Proof Restrict(string ph, string small)
    {
        var parts = Conjuncts(small).Reverse().ToList();
        return parts.Skip(1).Aggregate(Hyp(ph, parts[0]) ?? throw new Refused($"no {parts[0]}"), (acc, h) => _d.Jca(acc, Hyp(ph, h) ?? throw new Refused($"no {h}")));
    }

    /// <summary>|- ( ( A e. _V /\ B e. _V ) -> ( A rel B <-> ( rank ` A ) e. ( rank ` B ) ) ), by brabga.</summary>
    private Proof Brabga(string rx, string ry, string a, string b, string rel)
    {
        string h = $"( {rx} = {a} /\\ {ry} = {b} )";
        Proof e1 = _d.Congruence("wff", $"( rank ` Z ) e. ( rank ` {ry} )", "Z", pr.Apply("simpl", S(("ph", $"{rx} = {a}"), ("ps", $"{ry} = {b}"))));
        Proof e2 = _d.Congruence("wff", $"( rank ` {a} ) e. ( rank ` Z )", "Z", pr.Apply("simpr", S(("ph", $"{rx} = {a}"), ("ps", $"{ry} = {b}"))));
        Proof both = pr.Apply("bitrd", S(("ph", h), ("ps", $"( rank ` {rx} ) e. ( rank ` {ry} )"), ("ch", $"( rank ` {a} ) e. ( rank ` {ry} )"), ("th", $"( rank ` {a} ) e. ( rank ` {b} )")), e1, e2);
        return pr.Apply("brabga", S(("x", rx), ("y", ry), ("ph", $"( rank ` {rx} ) e. ( rank ` {ry} )"), ("ps", $"( rank ` {a} ) e. ( rank ` {b} )"),
                ("A", a), ("B", b), ("V", "_V"), ("W", "_V"), ("R", rel)),
            both, pr.Apply("eqid", S(("A", rel))));
    }

    /// <summary>( ph -> ( rank ` inner ) e. ( rank ` outer ) ), for inner a component, at any depth, of the nested pairs outer.</summary>
    private Proof RankChain(string ph, string inner, string outer)
    {
        SyntaxTree n = pr.Parse("class", outer.Split(' '))!;
        if (n.Rule.Label != "cop")
        {
            throw new InvalidOperationException($"{inner} is not inside the pairs {outer}");
        }
        string l = pr.Render(n.Children[0]), r = pr.Render(n.Children[1]);
        if (l == inner || r == inner)
        {
            return ComponentRank(ph, l, r, l == inner);
        }
        string via = $" {r} ".Contains($" {inner} ", StringComparison.Ordinal) ? r : l;
        Proof deeper = RankChain(ph, inner, via), top = ComponentRank(ph, l, r, via == l);
        Proof trans = pr.Apply("ax-mp", S(("ph", $"( rank ` {outer} ) e. On"), ("ps", $"( ( ( rank ` {inner} ) e. ( rank ` {via} ) /\\ ( rank ` {via} ) e. ( rank ` {outer} ) ) -> ( rank ` {inner} ) e. ( rank ` {outer} ) )")),
            pr.Apply("rankon", S(("A", outer))), pr.Apply("ontr1", S(("A", $"( rank ` {inner} )"), ("B", $"( rank ` {via} )"), ("C", $"( rank ` {outer} )"))));
        return _d.Syl(_d.Jca(deeper, top), trans);
    }

    /// <summary>( ph -> ( rank ` A ) e. ( rank ` <. A , B >. ) ) (or B's): A e. { A } e. <. A , B >. (B e. { A , B } e. …), by rankelb twice and ontr1.</summary>
    private Proof ComponentRank(string ph, string l, string r, bool first)
    {
        string c = first ? l : r, pair = $"<. {l} , {r} >.", mid = first ? $"{{ {l} }}" : $"{{ {l} , {r} }}";
        Proof hl = Exists(ph, l), hr = Exists(ph, r);
        Proof inMid = first
            ? _d.Syl(hl, pr.Apply("snidg", S(("A", l), ("V", "_V"))))
            : _d.Syl(hr, pr.Apply("prid2g", S(("A", l), ("B", r), ("V", "_V"))));
        Proof op = _d.Syl(_d.Jca(hl, hr), pr.Apply("dfopg", S(("A", l), ("B", r), ("V", "_V"), ("W", "_V"))));
        string kur = $"{{ {{ {l} }} , {{ {l} , {r} }} }}";
        Proof midSet = _d.Lift(ph, first ? pr.Apply("snex", S(("A", l))) : pr.Apply("prex", S(("A", l), ("B", r))));
        Proof midInKur = _d.Syl(midSet, first
            ? pr.Apply("prid1g", S(("A", mid), ("B", $"{{ {l} , {r} }}"), ("V", "_V")))
            : pr.Apply("prid2g", S(("A", $"{{ {l} }}"), ("B", mid), ("V", "_V"))));
        Proof midInPair = pr.Apply("eleqtrrd", S(("ph", ph), ("A", mid), ("B", kur), ("C", pair)), midInKur, op);
        Proof Rank(string x, string y, Proof xInY, Proof ySet)
        {
            Proof inR1 = pr.Apply("eleqtrrdi", S(("ph", ph), ("A", y), ("B", "_V"), ("C", "U. ( R1 \" On )")), ySet, pr.Apply("unir1", S()));
            Proof imp = _d.Syl(inR1, pr.Apply("rankelb", S(("A", x), ("B", y))));
            return pr.Apply("mpd", S(("ph", ph), ("ps", $"{x} e. {y}"), ("ch", $"( rank ` {x} ) e. ( rank ` {y} )")), xInY, imp);
        }
        Proof r1 = Rank(c, mid, inMid, midSet);
        Proof r2 = Rank(mid, pair, midInPair, _d.Lift(ph, pr.Apply("opex", S(("A", l), ("B", r)))));
        Proof trans = pr.Apply("ax-mp", S(("ph", $"( rank ` {pair} ) e. On"), ("ps", $"( ( ( rank ` {c} ) e. ( rank ` {mid} ) /\\ ( rank ` {mid} ) e. ( rank ` {pair} ) ) -> ( rank ` {c} ) e. ( rank ` {pair} ) )")),
            pr.Apply("rankon", S(("A", pair))), pr.Apply("ontr1", S(("A", $"( rank ` {c} )"), ("B", $"( rank ` {mid} )"), ("C", $"( rank ` {pair} )"))));
        return _d.Syl(_d.Jca(r1, r2), trans);
    }

    /// <summary>Write lean-rankfr (smaller rank is well-founded) into the output once, and teach it to the prover.</summary>
    private void EnsureRankFr()
    {
        if (pr.Database.Statements.ContainsKey("lean-rankfr"))
        {
            return;
        }
        var (stmt, proof, distinct) = new Recursion(pr).RankFr();
        string text = $"""
            $( Smaller rank is well-founded on any class: the recursors of recursive types rest on it (frr2). $)
            {"${"}
              {string.Join(" ", distinct.Select(d => $"$d {d} $."))}
              lean-rankfr $p {stmt} $=
                {string.Join(' ', pr.Database.Shared.Expand(proof))} $.
            {"$}"}

            """;
        _out.AppendLine(text);
        pr.Database.Extend(text);
    }

    /// <summary>Write lean-stagess (the stages of a recursive type only grow) into the output once, and teach it to the prover.</summary>
    private void EnsureStageSs()
    {
        if (pr.Database.Statements.ContainsKey(Recursion.StageSsLabel))
        {
            return;
        }
        var (stmt, proof, distinct) = new Recursion(pr).StageSs();
        string text = $"""
            $( The stages of a recursive type only grow: the recursors of constructors with several recursive fields
               rest on it, to put all the fields in one stage. $)
            {"${"}
              {string.Join(" ", distinct.Select(d => $"$d {d} $."))}
              {Recursion.StageSsHyp} $e {Recursion.StageSsHypText} $.
              {Recursion.StageSsLabel} $p {stmt} $=
                {string.Join(' ', pr.Database.Shared.Expand(proof))} $.
            {"$}"}

            """;
        _out.AppendLine(text);
        pr.Database.Extend(text);
    }

    private static bool IsProposition(ConstInfo ind)
    {
        Expr target = ind.Type;
        while (target is Binder { IsPi: true } pb)
        {
            target = pb.Body;
        }
        return target is Sort { Level: LZero };
    }

    /// <summary>
    /// The computation rule of a constructor of an inductive proposition whose recursor eliminates into any sort (one
    /// constructor, fields all proofs): I.rec params motive minor indices c = minor applied to (/) for each field, at
    /// the constructor's own indices. Every proof is (/), so the major premise is (/), and it is in the proposition
    /// because the constructor applies: the hypotheses say each field's proposition holds, ( (/) e. ⟦T⟧ ).
    /// When the recursor eliminates only into Prop, both sides of the rule are proofs, (/) = (/), and there is
    /// nothing to prove.
    /// </summary>
    private (MmExpr Statement, List<string> Proof, string[] Distinct) PropositionIota(ConstInfo ctor, ConstInfo ind, ConstInfo rec)
    {
        string itok = Token(ind.Name)!, rtok = Token(rec.Name)!;
        if (_intoPropOnly.Contains(rtok))
        {
            throw new Refused($"{rec.Name} eliminates only into Prop: both sides of its computation rule are proofs, (/)");
        }
        if (_leastRecursors.Contains(rtok))
        {
            throw new Refused($"{rec.Name} is well-founded recursion on a least fixed point; its computation rule is not in the model yet");
        }
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors;
        List<string> recArgs = ClassVarsFor(nrec, "more arguments than class variables");
        ProofsAsEmpty(ctor.Type, np, recArgs, []);

        // The constructor's indices, with the parameters as the class variables and every field (a proof) as (/).
        var vars = new Dictionary<ulong, string>();
        var types = new Dictionary<ulong, Expr>();
        Expr cty = ctor.Type;
        var fieldTypes = new List<Expr>();
        for (int i = 0; i < np + ctor.NumFields; i++)
        {
            var b = (Binder)cty;
            Expr fv = t.FVar(_fresh++);
            vars[((FVar)fv).Id] = i < np ? recArgs[i] : "(/)";
            types[((FVar)fv).Id] = b.Domain;
            if (i >= np)
            {
                fieldTypes.Add(b.Domain);
            }
            cty = _ops.Instantiate(b.Body, [fv]);
        }
        Ops.Spine(cty, out List<Expr> result);
        var sc = new Scope("U");
        foreach (var kv in vars)
        {
            sc.Vars[kv.Key] = kv.Value;
        }
        foreach (var kv in types)
        {
            sc.Types[kv.Key] = kv.Value;
        }
        List<string> indices = result.Skip(np).Select(e => Tr(e, sc)).ToList();
        List<string> fieldProps = fieldTypes.Select(ft => Tr(ft, sc)).ToList();   // ⟦T⟧ for each field, each in 2o

        var hyps = new List<string> { UHyp };
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        hyps.AddRange(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}"));
        hyps.AddRange(fieldProps.Select(p => $"(/) e. {p}"));
        string ph = Conj(hyps.Distinct());
        Proof Pick(string h) => Hyp(ph, h) ?? HypUpToRenaming(ph, h, hyps) ?? throw new Refused($"no hypothesis {h}");

        var allArgs = recArgs.Concat(indices).Append("(/)").ToList();
        Proof ArgIn(int i, string dom)
        {
            if (i < nrec + indices.Count)
            {
                return Pick($"{allArgs[i]} e. {dom}");
            }
            // The major premise: (/) is in the proposition at these indices, because the constructor applies.
            List<string> ps = recArgs.Take(np).Concat(indices).ToList();
            (Proof eqT, _, _) = Unfold(ph, itok, ps, (k, d) => Pick($"{ps[k]} e. {d}"));
            string iff = Rhs(eqT);
            SyntaxTree n = pr.Parse("class", iff.Split(' '))!;
            string cond = pr.Render(n.Children[0]);
            // Proved under the field hypotheses alone (or T.): rspcedvd needs its bound variable disjoint from the
            // context, and the full hypotheses may mention it inside an X_.
            var need = fieldProps.Select(p => $"(/) e. {p}").Distinct().ToList();
            string ph2 = need.Count == 0 ? "T." : Conj(need);
            Proof holds2 = ProveCase(ph2, cond, Array.IndexOf(ind.Ctors, ctor.Name), ind.Ctors.Length);
            Proof holds = need.Count == 0
                ? _d.Lift(ph, pr.Apply("mptru", S(("ph", cond)), holds2))
                : _d.Syl(need.Skip(1).Aggregate(Pick(need[0]), (acc, h) => _d.Jca(acc, Pick(h))), holds2);
            Proof isOne = pr.Apply("iftrued", S(("ph", ph), ("ch", cond), ("A", "1o"), ("B", "(/)")), holds);
            Proof toOne = _d.Trans(eqT, isOne);
            Proof inOne = _d.Lift(ph, pr.Apply("0lt1o", S()));
            Proof bi = pr.Apply("eleq2d", S(("ph", ph), ("A", Lhs(eqT)), ("B", "1o"), ("C", "(/)")), toOne);
            return pr.Apply("mpbird", S(("ph", ph), ("ps", $"(/) e. {Lhs(eqT)}"), ("ch", "(/) e. 1o")), inOne, bi);
        }
        (Proof eqR, _, _) = Unfold(ph, rtok, allArgs, ArgIn);
        string minor = recArgs[np + rec.NumMotives];
        string want = Enumerable.Range(0, ctor.NumFields).Aggregate(minor, (acc, _) => $"( {acc} ` (/) )");
        if (Rhs(eqR) != want)
        {
            throw new InvalidOperationException($"the computation rule came out as {Rhs(eqR)}, not {want}");
        }
        return (eqR.Proves, eqR.Proof, DistinctFor([itok, rtok], recArgs));
    }

    /// <summary>( ph -> φ ) for the case of constructor j in a proposition's disjunction of cases, its fields all (/).</summary>
    private Proof ProveCase(string ph, string cond, int j, int count)
    {
        if (count > 1)
        {
            SyntaxTree n = pr.Parse("wff", cond.Split(' '))!;
            if (n.Rule.Label != "wo")
            {
                throw new Refused($"a proposition's cases aren't a disjunction: {cond}");
            }
            string l = pr.Render(n.Children[0]), r = pr.Render(n.Children[1]);
            return j == count - 1
                ? pr.Apply("olcd", S(("ph", ph), ("ps", r), ("ch", l)), ProveWff(ph, r))
                : pr.Apply("orcd", S(("ph", ph), ("ps", l), ("ch", r)), ProveCase(ph, l, j, count - 1));
        }
        return ProveWff(ph, cond);
    }

    /// <summary>( ph -> w ) for T., A = A, conjunctions, and E. x e. T w' witnessed by (/) (a proof field).</summary>
    private Proof ProveWff(string ph, string w)
    {
        SyntaxTree n = pr.Parse("wff", w.Split(' ')) ?? throw new Refused($"not a formula: {w}");
        switch (n.Rule.Label)
        {
            case "wtru":
                return pr.Apply("trud", S(("ph", ph)));
            case "wceq" when pr.Render(n.Children[0]) == pr.Render(n.Children[1]):
                return _d.Refl(ph, pr.Render(n.Children[0]));
            case "wa":
                return _d.Jca(ProveWff(ph, pr.Render(n.Children[0])), ProveWff(ph, pr.Render(n.Children[1])));
            case "wrex":
                {
                    string body = pr.Render(n.Children[0]), x = pr.Render(n.Children[1]), dom = pr.Render(n.Children[2]);
                    if (ph.Split(' ').Contains(x))
                    {
                        // rspcedvd needs x disjoint from ph; a field's hypothesis (found up to renaming) may bind it
                        // (Std.TransCmp.mk, found by the Init-wide run: all three checkers rejected it).
                        throw new Refused($"the witness's variable {x} occurs in the hypotheses; not in the model yet");
                    }
                    string inst = Subst(body, x, "(/)");
                    Proof sub = body.Split(' ').Contains(x)
                        ? _d.Congruence("wff", Subst(body, x, "Z"), "Z", pr.Apply("simpr", S(("ph", ph), ("ps", $"{x} = (/)"))))
                        : _d.BiRefl($"( {ph} /\\ {x} = (/) )", body);
                    return pr.Apply("rspcedvd", S(("ph", ph), ("x", x), ("A", "(/)"), ("B", dom), ("ps", body), ("ch", inst)),
                        Hyp(ph, $"(/) e. {dom}") ?? HypUpToRenaming(ph, $"(/) e. {dom}", Conjuncts(ph)) ?? throw new Refused($"no hypothesis (/) e. {dom}"),
                        sub, ProveWff(ph, inst));
                }
        }
        throw new Refused($"can't prove {w} yet");
    }

    private (string L, string R) Eq(Proof p) => _d.Sides(_d.Split(p.Proves).X) is var (l, r, _) ? (l, r) : default;
    private string Lhs(Proof p) => Eq(p).L;
    private string Rhs(Proof p) => Eq(p).R;

    /// <summary>( ph -> tag e. set ), where set is the left-nested union of <paramref name="parts"/> constructor parts.</summary>
    private Proof MemberUnion(string ph, string tag, string set, int parts, int j, List<string> fields, Func<int, string, Proof> pick)
    {
        if (parts == 1)
        {
            return MemberPart(ph, tag, set, fields, 0, pick);
        }
        SyntaxTree u = pr.Parse("class", set.Split(' '))!;
        string left = pr.Render(u.Children[0]), right = pr.Render(u.Children[1]);
        if (j == parts - 1)
        {
            Proof p = MemberPart(ph, tag, right, fields, 0, pick);
            return _d.Syl(p, pr.Apply("elun2", S(("A", tag), ("B", right), ("C", left))));
        }
        Proof q = MemberUnion(ph, tag, left, parts - 1, j, fields, pick);
        return _d.Syl(q, pr.Apply("elun1", S(("A", tag), ("B", left), ("C", right))));
    }

    /// <summary>( ph -> tag e. part ), for a part U_ a1 e. T1 … { tag(a1, …) } and fields F1 …: by ssiun2s at each level, and snidg.</summary>
    private Proof MemberPart(string ph, string tag, string part, List<string> fields, int k, Func<int, string, Proof> pick)
    {
        SyntaxTree n = pr.Parse("class", part.Split(' '))!;
        if (n.Rule.Label == "csn")
        {
            return _d.Syl(Exists(ph, tag), pr.Apply("snidg", S(("A", tag), ("V", "_V"))));
        }
        // U_ x e. D B: the part with x := F_k, then the inclusion of that in the union.
        string x = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
        string inner = Subst(body, x, fields[k]);
        Proof pin = MemberPart(ph, tag, inner, fields, k + 1, pick);
        Proof sub = _d.Congruence("class", Subst(body, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {fields[k]}"))));
        Proof incl = pr.Apply("ssiun2s", S(("x", x), ("A", dom), ("B", body), ("C", fields[k]), ("D", inner)), sub);
        Proof sub2 = _d.Syl(pick(k, $"{fields[k]} e. {dom}"), incl);
        Proof imp = pr.Apply("sseld", S(("ph", ph), ("A", inner), ("B", part), ("C", tag)), sub2);
        return pr.Apply("mpd", S(("ph", ph), ("ps", $"{tag} e. {inner}"), ("ch", $"{tag} e. {part}")), pin, imp);
    }

    /// <summary>
    /// ( ph -> X = X' ), evaluating 1st and 2nd of explicit pairs (op1stg, op2ndg) and an if whose test is
    /// ( C = (/) ) with C evaluated to (/) or 1o (iftrued, iffalsed with 1n0). Null when nothing changes.
    /// </summary>
    private Proof? Simp(string ph, string x)
    {
        using var prof = Prof.Time("Simp");
        SyntaxTree n = pr.Parse("class", x.Split(' '))!;
        switch (n.Rule.Label)
        {
            case "cfv":
                {
                    string f = pr.Render(n.Children[1]), a = pr.Render(n.Children[0]);
                    Proof? pa = Simp(ph, a);
                    string a2 = pa is Proof qa ? Rhs(qa) : a;
                    if (f is "1st" or "2nd" && pr.Parse("class", a2.Split(' ')) is SyntaxTree { Rule.Label: "cop" } pair)
                    {
                        string l = pr.Render(pair.Children[0]), r = pr.Render(pair.Children[1]);
                        Proof sel = _d.Syl(_d.Jca(Exists(ph, l), Exists(ph, r)),
                            pr.Apply(f == "1st" ? "op1stg" : "op2ndg", S(("A", l), ("B", r), ("V", "_V"), ("W", "_V"))));
                        return pa is Proof p1 ? _d.Trans(pr.Apply("fveq2d", S(("ph", ph), ("A", a), ("B", a2), ("F", f)), p1), sel) : sel;
                    }
                    Proof? pf = Simp(ph, f);
                    if (pf is null && pa is null)
                    {
                        return null;
                    }
                    return pr.Apply("fveq12d", S(("ph", ph), ("A", a), ("B", a2), ("F", f), ("G", pf is Proof q ? Rhs(q) : f)),
                        pf ?? _d.Refl(ph, f), pa ?? _d.Refl(ph, a));
                }
            case "cif":
                {
                    SyntaxTree cond = n.Children[0];
                    string a = pr.Render(n.Children[1]), b = pr.Render(n.Children[2]), test = pr.Render(cond);
                    if (cond.Rule.Label != "wceq" || pr.Render(cond.Children[1]) != "(/)")
                    {
                        return null;
                    }
                    string c = pr.Render(cond.Children[0]);
                    Proof? pc = Simp(ph, c);
                    string c2 = pc is Proof q ? Rhs(q) : c;
                    Proof chosen;
                    string rest;
                    if (c2 == "(/)")
                    {
                        chosen = pr.Apply("iftrued", S(("ph", ph), ("ch", test), ("A", a), ("B", b)), pc ?? _d.Refl(ph, c));
                        rest = a;
                    }
                    else if (c2 == "1o")
                    {
                        Proof no = _d.Lift(ph, pr.Apply("neii", S(("A", "1o"), ("B", "(/)")), pr.Apply("1n0", S())));
                        Proof iff = pr.Apply("eqeq1d", S(("ph", ph), ("A", c), ("B", "1o"), ("C", "(/)")), pc!.Value);
                        Proof not = pr.Apply("mtbird", S(("ph", ph), ("ps", test), ("ch", "1o = (/)")), no, iff);
                        chosen = pr.Apply("iffalsed", S(("ph", ph), ("ch", test), ("A", a), ("B", b)), not);
                        rest = b;
                    }
                    else
                    {
                        return null;
                    }
                    return Simp(ph, rest) is Proof more ? _d.Trans(chosen, more) : chosen;
                }
        }
        // Anything else: simplify its class parts, but not under a binder (only a binder's domain), one at a time.
        string[] parts = n.Rule.Label switch
        {
            "ciun" => ["A", "B"],   // a body only where the binders avoid the context's variables (the step's do)
            "cmpt" or "cixp" => ["A"],
            "cun" or "cop" or "cres" or "co" or "cima" => ["A", "B"],
            "csn" => ["A"],
            _ => [],
        };
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
        Proof? acc = null;
        string curText = x;
        foreach (string part in parts)
        {
            SyntaxTree node = pr.Parse("class", curText.Split(' '))!;
            int idx = vars.IndexOf(part);
            if (idx < 0)
            {
                continue;
            }
            string child = pr.Render(node.Children[idx]);
            if (Simp(ph, child) is not Proof pc)
            {
                continue;
            }
            // The node with this child replaced by a hole Z, the others as they are.
            var kids = node.Children.Select(c => pr.Render(c)).ToList();
            kids[idx] = "Z";
            string ctx = string.Join(' ', node.Rule.Expr.Symbols.Select(sym => vars.IndexOf(sym) is int vi and >= 0 ? kids[vi] : sym));
            Proof step = _d.Congruence("class", ctx, "Z", pc);
            acc = acc is Proof a1 ? _d.Trans(a1, step) : step;
            curText = Rhs(step);
        }
        return acc;
    }

    /// <summary>
    /// ( ph -> ( F ` A ) = B[x := A] ), from |- F = ( x e. D |-> B ) and ( ph -> A e. D ), by fvmptd3. The substitution
    /// is proved outside ph, under x = A alone: ph may mention bound variables of B (a hypothesis A e. X_ w e. …), and
    /// a congruence under ph through B's binders would need them disjoint from ph.
    /// </summary>
    private Proof Beta(string ph, Proof fIsMap, string x, string dom, string body, string arg, Proof argIn, string f)
    {
        if (tower && (BoundIn(body).Contains(x) || BoundIn(body).Overlaps(ArgVars(arg))))
        {
            return BetaShadowed(ph, fIsMap, x, dom, body, arg, argIn, f);   // TheoremTranslator.cs
        }
        if (arg.Split(' ').Contains(x))
        {
            // fvmptd3 needs x distinct from the argument: rename the map's variable first (cbvmptv).
            var taken = arg.Split(' ').Concat(body.Split(' ')).Concat(dom.Split(' ')).Concat(ph.Split(' ')).ToHashSet();
            string y = FirstVar(v => !taken.Contains(v));
            string bodyY = Subst(body, x, y);
            Proof ren = pr.Apply("cbvmptv", S(("x", x), ("y", y), ("A", dom), ("B", body), ("C", bodyY)),
                body.Split(' ').Contains(x)
                    ? _d.Congruence("class", Subst(body, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {y}"))))
                    : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", $"{x} = {y}")), pr.Apply("eqid", S(("A", body)))));
            string mapX = $"( {x} e. {dom} |-> {body} )", mapY = $"( {y} e. {dom} |-> {bodyY} )";
            fIsMap = pr.Apply("eqtri", S(("A", f), ("B", mapX), ("C", mapY)), fIsMap, ren);
            (x, body) = (y, bodyY);
        }
        string result = Subst(body, x, arg);
        string h = $"{x} = {arg}";
        Proof sub = body.Split(' ').Contains(x)
            ? _d.Congruence("class", Subst(body, x, "Z"), "Z", pr.Apply("id", S(("ph", h))))
            : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", h)), pr.Apply("eqid", S(("A", body))));
        Proof exists = Exists(ph, result);
        return pr.Apply("fvmptd3", S(("ph", ph), ("x", x), ("A", arg), ("B", body), ("C", result), ("D", dom), ("F", f), ("V", "_V")),
            fIsMap, sub, argIn, exists);
    }

    /// <summary>
    /// ( ph -> X e. _V ) for a translated term X. Proved under only the hypotheses of the class variables X mentions (or
    /// T. when none), then carried back to ph: the proof may go through binders of X (ralrimivw needs them disjoint
    /// from its context), and ph may mention the same bound variables in hypotheses X doesn't need.
    /// </summary>
    private readonly Dictionary<(string, string), Proof> _known = new();   // sethood proved in context, e.g. of a recursion function

    private Proof Exists(string ph, string x)
    {
        if (_known.TryGetValue((ph, x), out Proof known))
        {
            return known;
        }
        var used = Conjuncts(ph).Where(h => x.Split(' ').Contains(h.Split(' ')[0]) && pr.Parse("class", [h.Split(' ')[0]]) is { Rule.Kind: 'f' }).Reverse().ToList();
        if (used.Count == 0)
        {
            Proof closed = ExistsIn("T.", x);
            return _d.Lift(ph, pr.Apply("mptru", S(("ph", $"{x} e. _V")), closed));
        }
        string sub = Conj(used);
        if (sub == ph)
        {
            return ExistsIn(ph, x);
        }
        Proof restrict = used.Skip(1).Aggregate(Hyp(ph, used[0])!.Value, (acc, h) => _d.Jca(acc, Hyp(ph, h)!.Value));
        return _d.Syl(restrict, ExistsIn(sub, x));
    }

    private readonly HashSet<string> _renamedTo = new();   // set variables RenameBound introduced, for the $d lists

    /// <summary>
    /// ( ph -> X e. _V ) for an indexed union or product X whose bound variable v also occurs in ph. ralrimivw needs v
    /// disjoint from ph, and sibling binders may share a variable, so a hypothesis can bind the same v (the equation of
    /// Nat.add.match_1, whose hypotheses D and E both bind w; found by the Init-wide run). So rename v first, to a
    /// variable in neither ph nor X (cbvixpv, cbviunv), and carry the sethood back (eqeltrid).
    /// </summary>
    private Proof? RenameBound(string ph, string x, string label, string v, string dom, string body)
    {
        var taken = new HashSet<string>(ph.Split(' ').Concat(x.Split(' ')));
        string? y = Enumerable.Reverse(SetVars).FirstOrDefault(s => !taken.Contains(s) && pr.Database.FloatOf(s) is not null);
        if (y is null)
        {
            return null;
        }
        _renamedTo.Add(y);
        string body2 = Subst(body, v, y);
        string x2 = label == "cixp" ? $"X_ {y} e. {dom} {body2}" : $"U_ {y} e. {dom} {body2}";
        Proof sub = body.Split(' ').Contains(v)
            ? _d.Congruence("class", Subst(body, v, "Z"), "Z", pr.Apply("id", S(("ph", $"{v} = {y}"))))
            : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", $"{v} = {y}")), pr.Apply("eqid", S(("A", body))));
        Proof eq = pr.Apply(label == "cixp" ? "cbvixpv" : "cbviunv", S(("x", v), ("y", y), ("A", dom), ("B", body), ("C", body2)), sub);
        return pr.Apply("eqeltrid", S(("ph", ph), ("A", x), ("B", x2), ("C", "_V")), eq, ExistsIn(ph, x2));
    }

    private Proof ExistsIn(string ph, string x)
    {
        SyntaxTree n = pr.Parse("class", x.Split(' ')) ?? throw new Refused($"does not parse: {x}");
        string C(int i) => pr.Render(n.Children[i]);
        switch (n.Rule.Label)
        {
            case "cfv":
                return pr.Apply("fvexd", S(("ph", ph), ("F", C(1)), ("A", C(0))));
            case "co":
                return pr.Apply("ovexd", S(("ph", ph), ("A", C(0)), ("B", C(1)), ("F", C(2))));
            case "cmpt":
                return pr.Apply("mptexd", S(("ph", ph), ("x", C(0)), ("A", C(1)), ("B", C(2)), ("V", "_V")), ExistsIn(ph, C(1)));
            case "c2o":
                return _d.Lift(ph, pr.Apply("2oex", S()));
            case "c1o":
                return _d.Lift(ph, pr.Apply("1oex", S()));
            case "c0":
                return _d.Lift(ph, pr.Apply("0ex", S()));
            case "com":
                return _d.Lift(ph, pr.Apply("omex", S()));
            case "cop":
                return _d.Lift(ph, pr.Apply("opex", S(("A", C(0)), ("B", C(1)))));
            case "csn":
                return _d.Lift(ph, pr.Apply("snex", S(("A", C(0)))));
            case "cuni":
                return pr.Apply("uniexd", S(("ph", ph), ("A", C(0)), ("V", "_V")), ExistsIn(ph, C(0)));
            case "crn":
                return pr.Apply("rnexd", S(("ph", ph), ("A", C(0)), ("V", "_V")), ExistsIn(ph, C(0)));
            case "csuc":
                return _d.Syl(ExistsIn(ph, C(0)), pr.Apply("sucexg", S(("A", C(0)), ("V", "_V"))));
            case "cima":
                return _d.Syl(ExistsIn(ph, C(0)), pr.Apply("imaexg", S(("A", C(0)), ("B", C(1)), ("V", "_V"))));
            case "cv":
                return _d.Lift(ph, pr.Apply("vex", S(("x", C(0)))));
            case "cun":
                return pr.Apply("unexd", S(("ph", ph), ("A", C(0)), ("B", C(1)), ("V", "_V"), ("W", "_V")), ExistsIn(ph, C(0)), ExistsIn(ph, C(1)));
            case "cif":
                return pr.Apply("ifexd", S(("ph", ph), ("ps", C(0)), ("A", C(1)), ("B", C(2)), ("V", "_V"), ("W", "_V")), ExistsIn(ph, C(1)), ExistsIn(ph, C(2)));
            case "ciun":
            case "cixp":
                {
                    // Pointwise sethood of the body, for every x in the domain (ralrimivw), then iunexg or ixpexg.
                    string v = C(0), dom = C(1), body = C(2);
                    if (ph.Split(' ').Contains(v))
                    {
                        // ph binds v in a hypothesis this term doesn't need (two minor premises over X_ w …): prove
                        // it under the hypotheses it does need, since ralrimivw needs v disjoint from its context.
                        var need = Conjuncts(ph).Where(h => x.Split(' ').Contains(h.Split(' ')[0]) && pr.Parse("class", [h.Split(' ')[0]]) is { Rule.Kind: 'f' }).Reverse().ToList();
                        string sub = need.Count == 0 ? "T." : Conj(need);
                        if (sub != ph && !sub.Split(' ').Contains(v))
                        {
                            return Exists(ph, x);
                        }
                        // Otherwise the hypotheses it needs bind v themselves: rename v (found by the Init-wide run).
                        if (RenameBound(ph, x, n.Rule.Label, v, dom, body) is Proof renamed)
                        {
                            return renamed;
                        }
                    }
                    Proof all = pr.Apply("ralrimivw", S(("ph", ph), ("ps", $"{body} e. _V"), ("x", v), ("A", dom)), ExistsIn(ph, body));
                    if (n.Rule.Label == "cixp")
                    {
                        return _d.Syl(all, pr.Apply("ixpexg", S(("x", v), ("A", dom), ("B", body), ("V", "_V"))));
                    }
                    return _d.Syl(_d.Jca(ExistsIn(ph, dom), all), pr.Apply("iunexg", S(("x", v), ("A", dom), ("B", body), ("V", "_V"), ("W", "_V"))));
                }
        }
        if (ExistsMore(ph, n) is Proof more)   // ModelBuiltins.cs: intersections, products, ranges, quotients, classes
        {
            return more;
        }
        // A class variable: from its hypothesis.
        if (n.Rule.Kind == 'f' && Conjuncts(ph).FirstOrDefault(h => h.StartsWith(x + " e. ", StringComparison.Ordinal)) is string hyp)
        {
            return pr.Apply("elexd", S(("ph", ph), ("A", x), ("V", hyp[(x.Length + 4)..])), Hyp(ph, hyp)!.Value);
        }
        throw new Refused($"no proof yet that {x} is a set");
    }

    /// <summary>The conjuncts of a left-nested conjunction ( ( h0 /\ h1 ) /\ h2 ), rightmost first.</summary>
    private IEnumerable<string> Conjuncts(string ph)
    {
        string cur = ph;
        while (pr.Parse("wff", cur.Split(' ')) is SyntaxTree { Rule.Label: "wa" } n)
        {
            yield return pr.Render(n.Children[1]);
            cur = pr.Render(n.Children[0]);
        }
        yield return cur;
    }

    /// <summary>( ph -> h ) for a conjunct h of the left-nested conjunction ph, by simpl and simpr.</summary>
    private Proof? Hyp(string ph, string h)
    {
        if (ph == h)
        {
            return pr.Apply("id", S(("ph", ph)));
        }
        if (pr.Parse("wff", ph.Split(' ')) is not SyntaxTree { Rule.Label: "wa" } n)
        {
            return null;
        }
        string left = pr.Render(n.Children[0]), right = pr.Render(n.Children[1]);
        if (right == h)
        {
            return pr.Apply("simpr", S(("ph", left), ("ps", right)));
        }
        return Hyp(left, h) is Proof p ? _d.Syl(pr.Apply("simpl", S(("ph", left), ("ps", right))), p) : null;
    }

    private static string Subst(string s, string var, string with) => string.Join(' ', s.Split(' ').Select(tok => tok == var ? with : tok));
}
