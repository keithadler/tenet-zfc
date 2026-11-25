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
public sealed class Model(Terms t, Environment env, Prover pr, bool dryRun = false)
{
    private const string UniverseVar = "u";
    private static readonly string[] SetVars = "x y z w v t s r q p o n m k j i h g f e d c b a".Split(' ');
    private static readonly string[] ClassVars = "A B C D E F G H I J K L M N O P Q R S T".Split(' ');   // U is the universe, Z a hole

    private readonly Ops _ops = new(t);
    private readonly Typing _typing = new(t, env);
    private readonly Deduction _d = new(pr);
    private readonly HashSet<Name> _defined = new(ReferenceEqualityComparer.Instance);
    private readonly StringBuilder _out = new();
    private ulong _fresh = 1UL << 58;

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>The set.mm token for a Lean constant, or null when its name has characters a token can't.</summary>
    public static string? Token(Name n)
    {
        string s = $"{n}";
        return s.Length > 0 && s.All(ch => char.IsAsciiLetterOrDigit(ch) || ch is '_' or '.' or '\'') && !s.Contains('\'') ? "lean." + s : null;
    }

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
                return IsZero(s.Level) ? "2o" : sc.Universe;
            case Const c:
                Define(c.Name);
                return $"( {Token(c.Name)} ` {sc.Universe} )";
            case App a:
                return $"( {Tr(a.Fn, sc)} ` {Tr(a.Arg, sc)} )";
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
                return x;
            }
        }
        throw new Refused("more nested binders than set.mm has set variables");
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
                return;
            case ConstKind.Recursor when $"{n}".EndsWith(".rec", StringComparison.Ordinal):
                Define(t.Of($"{n}"[..^4]));
                return;
        }
        throw new Refused($"{n} is not a definition but {(c.Kind == ConstKind.Inductive ? "an inductive type" : "a " + c.Kind.ToString().ToLowerInvariant())}; not in the model yet");
    }

    private Scope NewScope()
    {
        var sc = new Scope(UniverseVar);
        sc.Bound.Add(UniverseVar);
        sc.Active.Add(UniverseVar);
        return sc;
    }

    private void Emit(Name n, string tok, string body, Scope sc, string what)
    {
        string text = $"""
            $( The Lean {what} {n}, translated by the model of docs/milestone3.md. $)
            $c {tok} $.
            c{tok} $a class {tok} $.
            {"${"}
              {(sc.Bound.Count > 1 ? $"$d {string.Join(' ', sc.Bound)} $." : "")}
              df-{tok} $a |- {tok} = ( {UniverseVar} e. Univ |-> {body} ) $.
            {"$}"}

            """;
        _out.AppendLine(text);
        _values[tok] = body;
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
        if (ind.IsRec)
        {
            throw new Refused($"{n} is a recursive inductive type; only non-recursive ones are in the model so far");
        }
        if (ind.NumNested > 0 || ind.BlockMembers.Count(m => env.Find(m)?.Kind == ConstKind.Inductive) > 1)
        {
            throw new Refused($"{n} is a mutual or nested inductive type; not in the model yet");
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
        ConstInfo rec = env.Find(t.Of($"{n}.rec")) ?? throw new Refused($"{n}.rec is not in the export");
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
            if (ctors.Count == 0)
            {
                throw new Refused($"{n} has no constructors; the empty type isn't in the model yet");
            }
            _defined.Add(rec.Name);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, Case(0, major)), sc, "recursor");
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
        ConstInfo rec = env.Find(t.Of($"{n}.rec")) ?? throw new Refused($"{n}.rec is not in the export");
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
                // Subsingleton elimination: the one minor premise, at (/) for each field (all proofs).
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
        Statement dfa = pr.Database["df-" + tok];
        // The definition, its own variables substituted by themselves (a citation still pushes their syntax).
        Proof df = pr.Apply(dfa.Label, dfa.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!));
        Proof cur = Beta(ph, df, UniverseVar, "Univ", valueu, "U", Hyp(ph, "U e. Univ")!.Value, tok);
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
            val = Subst(body, x, args[i]);
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
            setvars.UnionWith(_values[tok].Split(' ').Where(s => SetVars.Contains(s)));
        }
        return [string.Join(' ', setvars.Concat(classVars).Append("U"))];
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
        if (arity > ClassVars.Length)
        {
            throw new Refused("more parameters than class variables");
        }
        var args = ClassVars.Take(arity).ToList();
        List<string> doms = Domains(tok, args, arity);
        var hyps = new List<string> { "U e. Univ" };
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
        ConstInfo rec = env.Find(t.Of($"{ind.Name}.rec"))!;
        if (IsProposition(ind))
        {
            return PropositionIota(ctor, ind, rec);
        }
        string itok = Token(ind.Name)!, ctok = Token(ctorName)!, rtok = Token(rec.Name)!;
        int j = Array.FindIndex(ind.Ctors, c => ReferenceEquals(c, ctorName));
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors, nf = ctor.NumFields;
        if (nrec + nf > ClassVars.Length)
        {
            throw new Refused("more arguments than class variables");
        }
        List<string> recArgs = ClassVars.Take(nrec).ToList();
        List<string> fields = ClassVars.Skip(nrec).Take(nf).ToList();
        List<string> ctorArgs = recArgs.Take(np).Concat(fields).ToList();
        string v = ctorArgs.Aggregate($"( {ctok} ` U )", (acc, a) => $"( {acc} ` {a} )");

        // Hypotheses: the recursor's arguments, then the fields, each in its domain.
        var hyps = new List<string> { "U e. Univ" };
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        hyps.AddRange(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}"));
        List<string> cdoms = Domains(ctok, ctorArgs, np + nf);
        RefuseBinders(cdoms.Skip(np).Select(d => ("", d)).ToList(), ctorName);
        hyps.AddRange(fields.Select((a, i) => $"{a} e. {cdoms[np + i]}"));
        string ph = Conj(hyps);
        Proof Pick(int _, string h) => Hyp(ph, h) ?? throw new Refused($"no hypothesis {h}");

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
        Proof toTag = _d.Congruence("class", Subst(lastBody, lastVar, "Z"), "Z", eqV);
        Proof cur = _d.Trans(eqR, toTag);
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
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors;
        List<string> recArgs = ClassVars.Take(nrec).ToList();

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

        var hyps = new List<string> { "U e. Univ" };
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        hyps.AddRange(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}"));
        hyps.AddRange(fieldProps.Select(p => $"(/) e. {p}"));
        string ph = Conj(hyps.Distinct());
        Proof Pick(string h) => Hyp(ph, h) ?? throw new Refused($"no hypothesis {h}");

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
        SyntaxTree n = pr.Parse("wff", w.Split(' '))!;
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
                    string inst = Subst(body, x, "(/)");
                    Proof sub = body.Split(' ').Contains(x)
                        ? _d.Congruence("wff", Subst(body, x, "Z"), "Z", pr.Apply("simpr", S(("ph", ph), ("ps", $"{x} = (/)"))))
                        : _d.BiRefl($"( {ph} /\\ {x} = (/) )", body);
                    return pr.Apply("rspcedvd", S(("ph", ph), ("x", x), ("A", "(/)"), ("B", dom), ("ps", body), ("ch", inst)),
                        Hyp(ph, $"(/) e. {dom}") ?? throw new Refused($"no hypothesis (/) e. {dom}"), sub, ProveWff(ph, inst));
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
        return null;
    }

    /// <summary>
    /// ( ph -> ( F ` A ) = B[x := A] ), from |- F = ( x e. D |-> B ) and ( ph -> A e. D ), by fvmptd3. The substitution
    /// is proved outside ph, under x = A alone: ph may mention bound variables of B (a hypothesis A e. X_ w e. …), and
    /// a congruence under ph through B's binders would need them disjoint from ph.
    /// </summary>
    private Proof Beta(string ph, Proof fIsMap, string x, string dom, string body, string arg, Proof argIn, string f)
    {
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
    private Proof Exists(string ph, string x)
    {
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
            case "cop":
                return _d.Lift(ph, pr.Apply("opex", S(("A", C(0)), ("B", C(1)))));
            case "csn":
                return _d.Lift(ph, pr.Apply("snex", S(("A", C(0)))));
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
                    Proof all = pr.Apply("ralrimivw", S(("ph", ph), ("ps", $"{body} e. _V"), ("x", v), ("A", dom)), ExistsIn(ph, body));
                    if (n.Rule.Label == "cixp")
                    {
                        return _d.Syl(all, pr.Apply("ixpexg", S(("x", v), ("A", dom), ("B", body), ("V", "_V"))));
                    }
                    return _d.Syl(_d.Jca(ExistsIn(ph, dom), all), pr.Apply("iunexg", S(("x", v), ("A", dom), ("B", body), ("V", "_V"), ("W", "_V"))));
                }
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
