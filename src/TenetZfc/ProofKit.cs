using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// A small tactic layer over <see cref="Prover.Apply"/> for writing set.mm proofs by hand in C#. Apply needs every
/// variable of an assertion substituted; here the substitution is found by matching the assertion's hypotheses (and,
/// when given, its conclusion) against what is supplied, so a proof step names only the theorem and its premises.
/// Nothing here is trusted: every proof it builds is checked by both verifiers.
/// </summary>
public sealed class ProofKit(Prover pr)
{
    private Database Db => pr.Database;

    private static string[] Tok(string s) => s.Split(' ', StringSplitOptions.RemoveEmptyEntries);

    /// <summary>The formula a proof proves (without the leading |-).</summary>
    public static string Of(Proof p) => string.Join(' ', p.Proves.Symbols);

    public SyntaxTree Tree(string type, IReadOnlyList<string> syms) =>
        pr.Parse(type, syms) ?? throw new InvalidOperationException($"does not parse as {type}: {string.Join(' ', syms)}");

    public SyntaxTree Wff(string text) => Tree("wff", Tok(text));

    // ---------------------------------------------------------------- unification

    /// <summary>Apply an assertion to its essential hypotheses, finding its variables by matching.</summary>
    public Proof Use(string label, params Proof[] hyps) => Use(label, null, null, hyps, []);

    /// <summary>As <see cref="Use(string, Proof[])"/>, also matching the conclusion against <paramref name="goal"/>.</summary>
    public Proof UseG(string label, string goal, params Proof[] hyps) => Use(label, goal, null, hyps, []);

    /// <summary>As <see cref="Use(string, Proof[])"/>, with some variables given.</summary>
    public Proof UseS(string label, (string Var, string Value)[] subst, params Proof[] hyps) => Use(label, null, subst, hyps, []);

    public Proof Use(string label, string? goal, (string Var, string Value)[]? subst, Proof[] hyps, params (SyntaxTree Pattern, SyntaxTree Target)[] extra)
    {
        Statement a = Db[label];
        var binds = new Dictionary<string, SyntaxTree>();
        foreach ((string v, string val) in subst ?? [])
        {
            binds[v] = Tree(Db.FloatOf(v)?.Expr.Type ?? throw new InvalidOperationException($"{v} is not a variable"), Tok(val));
        }
        var es = a.Hyps.Where(h => h.Kind == 'e').ToList();
        if (es.Count != hyps.Length)
        {
            throw new InvalidOperationException($"{label} takes {es.Count} hypotheses, given {hyps.Length}");
        }
        for (int i = 0; i < es.Count; i++)
        {
            if (!Match(Tree("wff", es[i].Expr.Symbols), Tree("wff", hyps[i].Proves.Symbols), binds))
            {
                throw new InvalidOperationException($"{label}: hypothesis {es[i].Label} ({string.Join(' ', es[i].Expr.Symbols)}) does not match {Of(hyps[i])}");
            }
        }
        if (goal is not null && !Match(Tree("wff", a.Expr.Symbols), Wff(goal), binds))
        {
            throw new InvalidOperationException($"{label}: conclusion {string.Join(' ', a.Expr.Symbols)} does not match {goal}");
        }
        foreach ((SyntaxTree pat, SyntaxTree tgt) in extra)
        {
            if (!Match(pat, tgt, binds))
            {
                throw new InvalidOperationException($"{label}: {pr.Render(pat)} does not match {pr.Render(tgt)}");
            }
        }
        if (label.StartsWith("lean-", StringComparison.Ordinal))
        {
            // The translator's own lemmas: a variable nothing determines stands for itself (a bound variable, or the
            // universe U), as written in the lemma.
            foreach (Statement f in a.Hyps.Where(h => h.Kind == 'f' && !binds.ContainsKey(h.Var!)))
            {
                binds[f.Var!] = Tree(f.Expr.Type, [f.Var!]);
            }
        }
        var missing = a.Hyps.Where(h => h.Kind == 'f' && !binds.ContainsKey(h.Var!)).Select(h => h.Var).ToList();
        if (missing.Count > 0)
        {
            throw new InvalidOperationException($"{label}: nothing determines {string.Join(", ", missing)}");
        }
        return pr.Apply(label, binds.ToDictionary(kv => kv.Key, kv => pr.Render(kv.Value)), hyps);
    }

    private bool Match(SyntaxTree pattern, SyntaxTree target, Dictionary<string, SyntaxTree> binds)
    {
        if (pattern.Rule.Kind == 'f')
        {
            string v = pattern.Rule.Var!;
            if (pattern.Rule.Expr.Type == "setvar" && target.Rule.Kind != 'f')
            {
                return false;
            }
            if (binds.TryGetValue(v, out SyntaxTree? bound))
            {
                return pr.Render(bound) == pr.Render(target);
            }
            if (target.Rule.Expr.Type != pattern.Rule.Expr.Type)
            {
                return false;
            }
            binds[v] = target;
            return true;
        }
        if (pattern.Rule.Label != target.Rule.Label || pattern.Children.Count != target.Children.Count)
        {
            return false;
        }
        for (int i = 0; i < pattern.Children.Count; i++)
        {
            if (!Match(pattern.Children[i], target.Children[i], binds))
            {
                return false;
            }
        }
        return true;
    }

    // ---------------------------------------------------------------- forward reasoning

    /// <summary>The antecedent and consequent of an implication.</summary>
    public (string H, string X) Split(string wff)
    {
        SyntaxTree t = Wff(wff);
        if (t.Rule.Label != "wi")
        {
            throw new InvalidOperationException($"not an implication: {wff}");
        }
        return (pr.Render(Child(t, "ph")), pr.Render(Child(t, "ps")));
    }

    /// <summary>The child of a syntax node that fills the syntax axiom's variable <paramref name="v"/>.</summary>
    public static SyntaxTree Child(SyntaxTree n, string v)
    {
        var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
        int i = vars.IndexOf(v);
        return i >= 0 ? n.Children[i] : throw new InvalidOperationException($"{n.Rule.Label} has no {v}");
    }

    /// <summary>
    /// Modus ponens through a closed theorem ( X -> Q ): with <paramref name="h"/> null the premises are closed and
    /// give |- Q; otherwise each premise is |- ( h -> P_i ) and the result is |- ( h -> Q ). Two or three premises
    /// make X a conjunction. <paramref name="q"/> fixes variables that only Q mentions.
    /// </summary>
    public Proof Imp(string? h, string label, Proof[] premises, string? q = null, (string, string)[]? subst = null, Proof[]? closedHyps = null)
    {
        Proof c;
        if (h is null)
        {
            c = premises.Length switch
            {
                1 => premises[0],
                2 => Use("pm3.2i", premises[0], premises[1]),
                3 => Use("3pm3.2i", premises[0], premises[1], premises[2]),
                _ => throw new InvalidOperationException("Imp takes one to three premises"),
            };
        }
        else
        {
            c = premises.Length switch
            {
                1 => premises[0],
                2 => Use("jca", premises[0], premises[1]),
                3 => Use("3jca", premises[0], premises[1], premises[2]),
                _ => throw new InvalidOperationException("Imp takes one to three premises"),
            };
        }
        string x = h is null ? Of(c) : Split(Of(c)).X;
        SyntaxTree concl = Tree("wff", Db[label].Expr.Symbols);
        if (concl.Rule.Label != "wi")
        {
            throw new InvalidOperationException($"{label} is not an implication");
        }
        var extra = new List<(SyntaxTree, SyntaxTree)> { (Child(concl, "ph"), Wff(x)) };
        if (q is not null)
        {
            extra.Add((Child(concl, "ps"), Wff(q)));
        }
        Proof thm = Use(label, null, subst, closedHyps ?? [], extra.ToArray());
        return h is null ? Use("ax-mp", c, thm) : Use("syl", c, thm);
    }

    /// <summary>|- X, weakened to |- ( h -> X ).</summary>
    public Proof Lift(string h, Proof closed) => UseS("a1i", [("ps", h)], closed);

    /// <summary>|- ( h -> c ) for a conjunct c of h (nested /\ only).</summary>
    public Proof Hyp(string h, string c) => HypOf(h, c) ?? throw new InvalidOperationException($"no {c} in {h}");

    private Proof? HypOf(string h, string c)
    {
        if (h == c)
        {
            return UseS("id", [("ph", h)]);
        }
        SyntaxTree n = Wff(h);
        if (n.Rule.Label != "wa")
        {
            return null;
        }
        string left = pr.Render(Child(n, "ph")), right = pr.Render(Child(n, "ps"));
        if (right == c)
        {
            return UseS("simpr", [("ph", left), ("ps", right)]);
        }
        if (HypOf(left, c) is Proof p)
        {
            return Use("syl", UseS("simpl", [("ph", left), ("ps", right)]), p);
        }
        return HypOf(right, c) is Proof q ? Use("syl", UseS("simpr", [("ph", left), ("ps", right)]), q) : null;
    }

    /// <summary>From |- ( h -> P ) and |- ( h -> Q ): |- ( h -> ( P /\ Q ) ).</summary>
    public Proof Jca(Proof a, Proof b) => Use("jca", a, b);

    public Proof Refl(string h, string a) => UseS("eqidd", [("ph", h), ("A", a)]);

    public Proof Symm(Proof ab) => Use("eqcomd", ab);

    public Proof Trans(params Proof[] chain)
    {
        Proof acc = chain[0];
        foreach (Proof next in chain.Skip(1))
        {
            acc = Use("eqtrd", acc, next);
        }
        return acc;
    }

    /// <summary>Closed equations chained.</summary>
    public Proof TransI(params Proof[] chain)
    {
        Proof acc = chain[0];
        foreach (Proof next in chain.Skip(1))
        {
            acc = Use("eqtri", acc, next);
        }
        return acc;
    }

    // ---------------------------------------------------------------- rewriting

    private static readonly string[] Holes = ["Y", "X", "W", "V", "T", "R", "Q", "P", "O", "N", "M", "K", "E", "D", "C"];

    private static string HoleFor(string text) =>
        Holes.First(v => !Tok(text).Contains(v));

    /// <summary>The text with each occurrence of the token sequence <paramref name="what"/> replaced.</summary>
    public static string Replace(string text, string what, string with)
    {
        string[] t = Tok(text), w = Tok(what);
        var r = new List<string>();
        for (int i = 0; i < t.Length;)
        {
            if (i + w.Length <= t.Length && t.AsSpan(i, w.Length).SequenceEqual(w))
            {
                r.AddRange(Tok(with));
                i += w.Length;
            }
            else
            {
                r.Add(t[i++]);
            }
        }
        return string.Join(' ', r);
    }

    /// <summary>From |- ( h -> P ) and |- ( h -> A = B ): |- ( h -> P' ), P with every A replaced by B.</summary>
    public Proof Rw(Proof p, Proof eq)
    {
        (string h, string x) = Split(Of(p));
        (string a, _) = Sides(Split(Of(eq)).X);
        string hole = HoleFor(x + " " + Of(eq));
        string ctx = Replace(x, a, hole);
        if (ctx == x)
        {
            throw new InvalidOperationException($"{a} does not occur in {x}");
        }
        Proof bi = Cong("wff", ctx, hole, eq);
        return Use("mpbid", p, bi);
    }

    /// <summary>From |- ( h -> A = B ): |- ( h -> C[A] = C[B] ) for a class context written with <paramref name="hole"/>.</summary>
    public Proof CongEq(string ctx, string hole, Proof eq) => Cong("class", ctx, hole, eq);

    /// <summary>The two sides of an equation or biconditional.</summary>
    public (string L, string R) Sides(string x)
    {
        SyntaxTree t = Wff(x);
        return t.Rule.Label switch
        {
            "wceq" => (pr.Render(Child(t, "A")), pr.Render(Child(t, "B"))),
            "wb" => (pr.Render(Child(t, "ph")), pr.Render(Child(t, "ps"))),
            _ => throw new InvalidOperationException($"not an equation: {x}"),
        };
    }

    /// <summary>
    /// From |- ( H -> A = B ): |- ( H -> C[A] = C[B] ), or |- ( H -> ( C[A] <-> C[B] ) ) for a formula context.
    /// Like <see cref="Deduction.Congruence"/>, with more constructs.
    /// </summary>
    public Proof Cong(string type, string context, string hole, Proof ab)
    {
        SyntaxTree c = Tree(type, Tok(context));
        (string h, string x) = Split(Of(ab));
        (string a, string b) = Sides(x);
        return Go(c, hole, h, a, b, ab) ?? throw new InvalidOperationException($"the hole {hole} does not occur in {context}");
    }

    private string Render(SyntaxTree n, string hole, string with)
    {
        if (n.Rule.Kind == 'f')
        {
            return n.Rule.Var == hole ? with : n.Rule.Var!;
        }
        var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
        return string.Join(' ', n.Rule.Expr.Symbols.Select(s => vars.IndexOf(s) is int i and >= 0 ? Render(n.Children[i], hole, with) : s));
    }

    private static bool Has(SyntaxTree n, string hole) => n.Rule.Kind == 'f' ? n.Rule.Var == hole : n.Children.Any(k => Has(k, hole));

    private Proof? Go(SyntaxTree n, string hole, string h, string a, string b, Proof ab)
    {
        if (n.Rule.Kind == 'f')
        {
            return n.Rule.Var == hole ? ab : null;
        }
        if (!Has(n, hole))
        {
            return null;
        }
        string L(string v) => Render(Child(n, v), hole, a);
        string R(string v) => Render(Child(n, v), hole, b);
        Proof Sub(string v) => Go(Child(n, v), hole, h, a, b, ab) ?? Refl(h, L(v));
        Proof SubW(string v) => Go(Child(n, v), hole, h, a, b, ab) ?? UseS("biidd", [("ph", h), ("ps", L(v))]);
        bool In(string v) => Has(Child(n, v), hole);

        switch (n.Rule.Label)
        {
            case "co":
                if (In("F")) break;
                return UseS("oveq12d", [("F", L("F"))], Sub("A"), Sub("B"));
            case "cfv":
                return Use("fveq12d", Sub("F"), Sub("A"));
            case "cop":
                return Use("opeq12d", Sub("A"), Sub("B"));
            case "cun":
                return Use("uneq12d", Sub("A"), Sub("B"));
            case "csn":
                return Use("sneqd", Sub("A"));
            case "csuc":
                return Use("suceqd", Sub("A"));
            case "ccnv":
                return Use("cnveqd", Sub("A"));
            case "crn":
                return Use("rneqd", Sub("A"));
            case "cres":
                return Use("reseq12d", Sub("A"), Sub("B"));
            case "ccom":
                return Use("coeq12d", Sub("A"), Sub("B"));
            case "cmpt":
                return UseS("mpteq12dv", [("x", L("x"))], Sub("A"), Sub("B"));
            case "crdg":
                return Use("syl", Jca(Sub("F"), Sub("I")), UseS("rdgeq12", [("F", L("F")), ("G", R("F")), ("A", L("I")), ("B", R("I"))]));
            case "ciun":
                {
                    string x = L("x");
                    Proof? dom = In("A") ? UseS("iuneq1d", [("x", x), ("C", L("B"))], Sub("A")) : null;
                    Proof? body = In("B")
                        ? UseS("iuneq2dv", [("x", x), ("A", R("A"))], UseS("adantr", [("ch", $"{x} e. {R("A")}")], Sub("B")))
                        : null;
                    return dom is Proof d1 && body is Proof b1 ? Trans(d1, b1) : (dom ?? body!.Value);
                }
            case "cdm":
                return Use("dmeqd", Sub("A"));
            case "cixp":
                return UseS("ixpeq12dv", [("x", L("x"))], Sub("A"), Sub("B"));
            case "cmpo":
                return UseS("mpoeq123dv", [("x", L("x")), ("y", L("y"))], Sub("A"), Sub("B"), Sub("C"));
            case "cfrecs":
                return Use("syl", Use("3jca", Sub("R"), Sub("A"), Sub("F")),
                    UseS("frecseq123", [("R", L("R")), ("S", R("R")), ("A", L("A")), ("B", R("A")), ("F", L("F")), ("G", R("F"))]));
            case "wceq":
                return Use("eqeq12d", Sub("A"), Sub("B"));
            case "wbr":
                // A R B, the relation fixed (<_ and < in the order bridge's restatements).
                return UseS("breq12d", [("R", L("R"))], Sub("A"), Sub("B"));
            case "wf":
                return Use("feq123d", Sub("F"), Sub("A"), Sub("B"));
            case "wf1":
                return Use("f1eq123d", Sub("F"), Sub("A"), Sub("B"));
            case "wf1o":
                return Use("f1oeq123d", Sub("F"), Sub("A"), Sub("B"));
            case "wfun":
                return Use("funeqd", Sub("A"));
            case "cs1":
                return Use("s1eqd", Sub("A"));
            case "cif":
                return Use("ifbieq12d", SubW("ph"), Sub("A"), Sub("B"));
            case "wcel":
                return Use("eleq12d", Sub("A"), Sub("B"));
            case "wss":
                return Use("sseq12d", Sub("A"), Sub("B"));
            case "wi":
                return Use("imbi12d", SubW("ph"), SubW("ps"));
            case "wa":
                return Use("anbi12d", SubW("ph"), SubW("ps"));
            case "wo":
                return Use("orbi12d", SubW("ph"), SubW("ps"));
            case "wb":
                return Use("bibi12d", SubW("ph"), SubW("ps"));
            case "wn":
                return Use("notbid", SubW("ph"));
            case "w3a":
                return Use("3anbi123d", SubW("ph"), SubW("ps"), SubW("ch"));
            case "wral":
                if (In("A")) return UseS("raleqbidv", [("x", L("x"))], Sub("A"), SubW("ph"));
                return UseS("ralbidv", [("x", L("x")), ("A", L("A"))], SubW("ph"));
            case "wrex":
                if (In("A")) return UseS("rexeqbidv", [("x", L("x"))], Sub("A"), SubW("ph"));
                return UseS("rexbidv", [("x", L("x")), ("A", L("A"))], SubW("ph"));
        }
        throw new InvalidOperationException($"no congruence rule for {n.Rule.Label} (in {Render(n, hole, a)})");
    }

    // ---------------------------------------------------------------- induction on ω

    /// <summary>
    /// Induction on ω by finds. <paramref name="p"/> mentions the set variable <paramref name="x"/>; with a context
    /// <paramref name="ctx"/>, the base is |- ( ctx -> P(∅) ) and the step |- ( ( ( y e. _om /\ ctx ) /\ P(y) ) -> P(suc y) );
    /// without one, |- P(∅) and |- ( ( y e. _om /\ P(y) ) -> P(suc y) ). Gives |- ( A e. _om -> ( ctx -> P(A) ) ) (or
    /// without the context).
    /// </summary>
    public Proof Finds(string x, string y, string p, string? ctx, Proof baseP, Proof stepP, string target)
    {
        string ph = ctx is null ? p : $"( {ctx} -> {p} )";
        Proof Eqv(string t)
        {
            string hole = HoleFor(ph + " " + t);
            Proof id = UseS("id", [("ph", $"{x} = {t}")]);
            return Cong("wff", Replace(ph, x, hole), hole, id);
        }
        Proof step = Use("ex", stepP);
        if (ctx is not null)
        {
            step = Use("a2d", Use("ex", step));
        }
        return UseS("finds", [("x", x), ("y", y)], Eqv("(/)"), Eqv(y), Eqv($"suc {y}"), Eqv(target), baseP, step);
    }
}
