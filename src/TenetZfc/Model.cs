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
public sealed class Model(Terms t, Environment env, Prover pr)
{
    private const string UniverseVar = "u";
    private static readonly string[] SetVars = "x y z w v t s r q p o n m k j i h g f e d c b a".Split(' ');
    private static readonly string[] ClassVars = "A B C D E F G H I J K L M N O P Q R S T".Split(' ');   // U is the universe, Z a hole

    private readonly Ops _ops = new(t);
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
        public List<string> Bound { get; } = new();   // setvars in use, outermost first
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
                    string x = Fresh(sc);
                    Expr fv = t.FVar(_fresh++);
                    sc.Vars[((FVar)fv).Id] = x;
                    sc.Bound.Add(x);
                    string body = Tr(_ops.Instantiate(b.Body, [fv]), sc);
                    return b.IsPi ? $"X_ {x} e. {dom} {body}" : $"( {x} e. {dom} |-> {body} )";
                }
            case Let l:
                return Tr(_ops.Instantiate(l.Body, [l.Value]), sc);
            default:
                throw new Refused($"not yet in the model: {e.GetType().Name} ({e})");
        }
    }

    private static bool IsZero(Level l) => l is LZero;

    private string Fresh(Scope sc)
    {
        // Each binder gets its own setvar, so that substituting for one never captures another.
        foreach (string x in SetVars)
        {
            if (!sc.Bound.Contains(x) && !sc.Vars.ContainsValue(x))
            {
                return x;
            }
        }
        throw new Refused("more nested binders than set.mm has set variables");
    }

    // ---- definitions --------------------------------------------------------------------------------------------

    /// <summary>
    /// Declare lean.c and define it, after the constants its value uses: $c, a syntax axiom, and
    /// df-lean.c $a |- lean.c = ( u e. Univ |-> ⟦value⟧ ) $. The definition's set variables are all bound, and distinct.
    /// </summary>
    public void Define(Name n)
    {
        if (_defined.Contains(n))
        {
            return;
        }
        ConstInfo c = env.Find(n) ?? throw new Refused($"{n} is not in the export");
        if (c.Kind != ConstKind.Definition || c.Value is null)
        {
            throw new Refused($"{n} is not a definition but {(c.Kind == ConstKind.Inductive ? "an inductive type" : "a " + c.Kind.ToString().ToLowerInvariant())}; only definitions are in the model so far");
        }
        string tok = Token(n) ?? throw new Refused($"{n}: the name has characters a set.mm token can't");
        var sc = new Scope(UniverseVar);
        sc.Bound.Add(UniverseVar);
        string body = Tr(c.Value, sc);   // defines what it uses first
        _defined.Add(n);
        string text = $"""
            $( The Lean definition {n}, translated by the model of docs/milestone3.md. $)
            $c {tok} $.
            c{tok} $a class {tok} $.
            {"${"}
              {(sc.Bound.Count > 1 ? $"$d {string.Join(' ', sc.Bound)} $." : "")}
              df-{tok} $a |- {tok} = ( {UniverseVar} e. Univ |-> {body} ) $.
            {"$}"}

            """;
        _out.AppendLine(text);
        pr.Database.Extend(text);
    }

    // ---- definitional equations ---------------------------------------------------------------------------------

    /// <summary>
    /// The definitional equation of a definition c := fun x1 … xn => b, as a set.mm theorem:
    /// |- ( ( ( U e. Univ /\ A e. ⟦T1⟧ ) /\ … ) -> ( ( ( lean.c ` U ) ` A ) … ) = ⟦b⟧[A, …] ),
    /// with its proof and the distinct-variable conditions it needs.
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) Equation(Name n)
    {
        Define(n);
        ConstInfo c = env.Find(n)!;
        string tok = Token(n)!;

        // The parameters: one class variable each, typed by a hypothesis.
        var vars = new Dictionary<ulong, string>();
        var hyps = new List<string> { "U e. Univ" };
        var args = new List<string>();
        Expr v = c.Value!;
        while (v is Binder { IsPi: false } lam)
        {
            if (args.Count >= ClassVars.Length)
            {
                throw new Refused("more parameters than class variables");
            }
            string a = ClassVars[args.Count];
            hyps.Add($"{a} e. {Class(lam.Domain, "U", vars)}");
            Expr fv = t.FVar(_fresh++);
            vars[((FVar)fv).Id] = a;
            args.Add(a);
            v = _ops.Instantiate(lam.Body, [fv]);
        }
        string ph = hyps.Skip(1).Aggregate(hyps[0], (acc, h) => $"( {acc} /\\ {h} )");
        Proof Pick(int i) => Hyp(ph, hyps[i]) ?? throw new InvalidOperationException($"no hypothesis {hyps[i]}");

        // ( lean.c ` U ) = ⟦value⟧[u := U], by the definition and fvmptd.
        string valueU = Class(c.Value!, "U", new Dictionary<ulong, string>());
        string valueu = Subst(valueU, "U", UniverseVar);
        // The definition, its own variables substituted by themselves (a citation still pushes their syntax).
        Statement dfa = pr.Database["df-" + tok];
        Proof df = _d.Lift(ph, pr.Apply(dfa.Label, dfa.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!)));
        Proof cur = Beta(ph, df, UniverseVar, "Univ", valueu, "U", Pick(0), tok);
        string app = $"( {tok} ` U )";
        string val = valueU;
        for (int i = 0; i < args.Count; i++)
        {
            // val is ( x e. D |-> B ); apply it to the next argument.
            SyntaxTree m = pr.Parse("class", val.Split(' ')) ?? throw new Refused($"does not parse: {val}");
            if (m.Rule.Label != "cmpt")
            {
                throw new Refused($"expected a map, got {val}");
            }
            string x = pr.Render(m.Children[0]), dom = pr.Render(m.Children[1]), body = pr.Render(m.Children[2]);
            Proof cong = pr.Apply("fveq1d", S(("ph", ph), ("A", args[i]), ("F", app), ("G", val)), cur);
            Proof beta = Beta(ph, _d.Refl(ph, val), x, dom, body, args[i], Pick(i + 1), val);
            cur = _d.Trans(cong, beta);
            app = $"( {app} ` {args[i]} )";
            val = Subst(body, x, args[i]);
        }
        var setvars = new HashSet<string>(valueu.Split(' ').Where(s => SetVars.Contains(s) || s == UniverseVar));   // every bound variable of the value
        string[] distinct = [string.Join(' ', setvars.Concat(args).Append("U"))];
        return (cur.Proves, cur.Proof, distinct);
    }

    /// <summary>( ph -> ( F ` A ) = B[x := A] ), from ( ph -> F = ( x e. D |-> B ) ) and ( ph -> A e. D ), by fvmptd.</summary>
    private Proof Beta(string ph, Proof fIsMap, string x, string dom, string body, string arg, Proof argIn, string f)
    {
        string result = Subst(body, x, arg);
        string h = $"( {ph} /\\ {x} = {arg} )";
        Proof eq = pr.Apply("simpr", S(("ph", ph), ("ps", $"{x} = {arg}")));
        Proof sub = body.Split(' ').Contains(x)
            ? _d.Congruence("class", Subst(body, x, "Z"), "Z", eq)
            : _d.Refl(h, body);
        Proof exists = Exists(ph, result);
        return pr.Apply("fvmptd", S(("ph", ph), ("x", x), ("A", arg), ("B", body), ("C", result), ("D", dom), ("F", f), ("V", "_V")),
            fIsMap, sub, argIn, exists);
    }

    /// <summary>( ph -> X e. _V ) for a translated term X.</summary>
    private Proof Exists(string ph, string x)
    {
        SyntaxTree n = pr.Parse("class", x.Split(' ')) ?? throw new Refused($"does not parse: {x}");
        switch (n.Rule.Label)
        {
            case "cfv":
                return pr.Apply("fvexd", S(("ph", ph), ("F", pr.Render(n.Children[1])), ("A", pr.Render(n.Children[0]))));
            case "co":
                return pr.Apply("ovexd", S(("ph", ph), ("A", pr.Render(n.Children[0])), ("B", pr.Render(n.Children[1])), ("F", pr.Render(n.Children[2]))));
            case "cmpt":
                {
                    string dom = pr.Render(n.Children[1]);
                    return pr.Apply("mptexd", S(("ph", ph), ("x", pr.Render(n.Children[0])), ("A", dom), ("B", pr.Render(n.Children[2])), ("V", "_V")), Exists(ph, dom));
                }
            case "c2o":
                return _d.Lift(ph, pr.Apply("2oex", S()));
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
