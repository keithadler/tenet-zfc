using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Proofs in set.mm's deduction form, |- ( H -> X ), where H gathers a theorem's hypotheses. Proof-term translation
/// builds on these: a Lean proof under its binders becomes a deduction under H. The congruence prover derives
/// |- ( H -> C[A] = C[B] ) (or <-> for a formula) from |- ( H -> A = B ) for any context C built from the
/// constructs below, which is what Lean's congrArg, congr, Eq.mpr and Eq.rec into Prop amount to.
/// </summary>
public sealed class Deduction(Prover pr)
{
    /// <summary>
    /// An alpha-variant h' of a hypothesis whose binders avoid the given letters (and every letter of the extra text),
    /// with |- ( h -> h' ) and |- ( h' -> h ); null when there is nothing to rename. The model supplies it (Alpha.cs):
    /// Congruence needs it when a hypothesis binds a letter that a binder of the rewritten text binds as well.
    /// </summary>
    public Func<string, ISet<string>, string, (string Renamed, Proof There, Proof Back)?>? RenameApart { get; set; }

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>The two sides of |- ( H -> X ).</summary>
    public (string H, string X) Split(MmExpr proves)
    {
        SyntaxTree t = pr.Parse("wff", proves.Symbols) ?? throw new InvalidOperationException($"not a formula: {proves}");
        if (t.Rule.Label != "wi")
        {
            throw new InvalidOperationException($"not an implication: {proves}");
        }
        return (pr.Render(t.Children[0]), pr.Render(t.Children[1]));
    }

    /// <summary>The two sides of an equation or a biconditional.</summary>
    public (string L, string R, bool IsBi) Sides(string x)
    {
        SyntaxTree t = pr.Parse("wff", x.Split(' ')) ?? throw new InvalidOperationException($"not a formula: {x}");
        return t.Rule.Label switch
        {
            "wceq" => (pr.Render(t.Children[0]), pr.Render(t.Children[1]), false),
            "wb" => (pr.Render(t.Children[0]), pr.Render(t.Children[1]), true),
            _ => throw new InvalidOperationException($"not an equation or biconditional: {x}"),
        };
    }

    /// <summary>|- X, weakened to |- ( H -> X ).</summary>
    public Proof Lift(string h, Proof closed) => pr.Apply("a1i", S(("ph", Strip(closed.Proves)), ("ps", h)), closed);

    /// <summary>From |- ( H -> P ) and a closed |- ( P -> Q ): |- ( H -> Q ).</summary>
    public Proof Syl(Proof hp, Proof pq)
    {
        (string h, string p) = Split(hp.Proves);
        (_, string q) = Split(pq.Proves);
        return pr.Apply("syl", S(("ph", h), ("ps", p), ("ch", q)), hp, pq);
    }

    /// <summary>From |- ( H -> P ) and |- ( H -> Q ): |- ( H -> ( P /\ Q ) ).</summary>
    public Proof Jca(Proof a, Proof b)
    {
        (string h, string p) = Split(a.Proves);
        (_, string q) = Split(b.Proves);
        return pr.Apply("jca", S(("ph", h), ("ps", p), ("ch", q)), a, b);
    }

    /// <summary>|- ( H -> A = A ).</summary>
    public Proof Refl(string h, string a) => pr.Apply("eqidd", S(("ph", h), ("A", a)));

    /// <summary>|- ( H -> ( P <-> P ) ).</summary>
    public Proof BiRefl(string h, string p) => pr.Apply("biidd", S(("ph", h), ("ps", p)));

    /// <summary>From |- ( H -> A = B ): |- ( H -> B = A ).</summary>
    public Proof Symm(Proof ab)
    {
        (string h, string x) = Split(ab.Proves);
        (string a, string b, _) = Sides(x);
        return pr.Apply("eqcomd", S(("ph", h), ("A", a), ("B", b)), ab);
    }

    /// <summary>From |- ( H -> A = B ) and |- ( H -> B = C ): |- ( H -> A = C ).</summary>
    public Proof Trans(Proof ab, Proof bc)
    {
        (string h, string x) = Split(ab.Proves);
        (string a, string b, _) = Sides(x);
        (_, string c, _) = Sides(Split(bc.Proves).X);
        return pr.Apply("eqtrd", S(("ph", h), ("A", a), ("B", b), ("C", c)), ab, bc);
    }

    /// <summary>From |- ( H -> P ) and |- ( H -> ( P <-> Q ) ): |- ( H -> Q ).</summary>
    public Proof Transport(Proof p, Proof pq)
    {
        (string h, string x) = Split(pq.Proves);
        (string a, string b, _) = Sides(x);
        return pr.Apply("mpbid", S(("ph", h), ("ps", a), ("ch", b)), p, pq);
    }

    private static string Strip(MmExpr e) => string.Join(' ', e.Symbols);

    /// <summary>
    /// From |- ( H -> A = B ): |- ( H -> C[A] = C[B] ) when the context is a class, or |- ( H -> ( C[A] <-> C[B] ) )
    /// when it is a formula. The context is written with the variable <paramref name="hole"/> where A and B go.
    /// </summary>
    public Proof Congruence(string type, string context, string hole, Proof ab)
    {
        SyntaxTree c = pr.Parse(type, context.Split(' ')) ?? throw new InvalidOperationException($"does not parse: {context}");
        (string h, string x) = Split(ab.Proves);
        (string a, string b, _) = Sides(x);
        // A binder of the context (A. w e. …, raleqbidv) must be distinct from the hypothesis, which may bind the same
        // letter itself. Then prove the congruence under the equation alone, ( a = b -> … ), and chain it (syl).
        var ctxTokens = context.Split(' ').ToHashSet();
        var clash = h.Split(' ').Where(ctxTokens.Contains).Where(tok => tok.Length > 0 && char.IsLower(tok[0]) && pr.Parse("setvar", [tok]) is not null).ToHashSet();
        if (clash.Count > 0 && !x.Split(' ').Any(clash.Contains))
        {
            Proof inner = Go(c, hole, x, a, b, pr.Apply("id", S(("ph", x)))) ?? throw new InvalidOperationException($"the hole {hole} does not occur in {context}");
            return Syl(ab, inner);
        }
        // The equation mentions the binder's letter too (the rewrite is under the binder), so it can't be split off. The
        // hypothesis only binds that letter, so an alpha-variant of it avoids it: prove the congruence under that
        // variant h', and go there and back by the alpha-equivalence ( h <-> h' ).
        if (clash.Count > 0 && RenameApart?.Invoke(h, clash, $"{context} {x}") is var (h2, there, back))
        {
            Proof inner = Go(c, hole, h2, a, b, Syl(back, ab)) ?? throw new InvalidOperationException($"the hole {hole} does not occur in {context}");
            return Syl(there, inner);
        }
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

    private bool Has(SyntaxTree n, string hole) => n.Rule.Kind == 'f' ? n.Rule.Var == hole : n.Children.Any(k => Has(k, hole));

    /// <summary>The congruence proof for one node, or null when the hole is not inside it.</summary>
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
        var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
        SyntaxTree Child(string v) => n.Children[vars.IndexOf(v)];
        string L(string v) => Render(Child(v), hole, a);
        string R(string v) => Render(Child(v), hole, b);
        Proof? Sub(string v) => Go(Child(v), hole, h, a, b, ab);

        switch (n.Rule.Label)
        {
            case "co":   // ( A F B )
                {
                    if (Has(Child("F"), hole))
                    {
                        break;
                    }
                    Proof? pa = Sub("A"), pb = Sub("B");
                    string f = L("F");
                    if (pa is Proof x && pb is Proof y)
                    {
                        return pr.Apply("oveq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B")), ("F", f)), x, y);
                    }
                    return pa is Proof only
                        ? pr.Apply("oveq1d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("F", f)), only)
                        : pr.Apply("oveq2d", S(("ph", h), ("A", L("B")), ("B", R("B")), ("C", L("A")), ("F", f)), pb!.Value);
                }
            case "cfv":  // ( F ` A )
                if (!Has(Child("F"), hole))
                {
                    return pr.Apply("fveq2d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("F", L("F"))), Sub("A")!.Value);
                }
                if (!Has(Child("A"), hole))
                {
                    return pr.Apply("fveq1d", S(("ph", h), ("A", L("A")), ("F", L("F")), ("G", R("F"))), Sub("F")!.Value);
                }
                return pr.Apply("fveq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("F", L("F")), ("G", R("F"))), Sub("F")!.Value, Sub("A")!.Value);
            case "cmpt": // ( x e. A |-> B ): the bound variable must not occur in the hypotheses ($d x ph)
                {
                    Proof pa = Sub("A") ?? Refl(h, L("A")), pb = Sub("B") ?? Refl(h, L("B"));
                    return pr.Apply("mpteq12dv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", L("B")), ("C", R("A")), ("D", R("B"))), pa, pb);
                }
            case "cop":  // <. A , B >.
                return pr.Apply("opeq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cun":  // ( A u. B )
                return pr.Apply("uneq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "csuc": // suc A
                return pr.Apply("suceqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "csn":  // { A }
                return pr.Apply("sneqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "cif":  // if ( ph , A , B )
                return pr.Apply("ifbieq12d", S(("ph", h), ("ps", L("ph")), ("ch", R("ph")), ("A", L("A")), ("B", L("B")), ("C", R("A")), ("D", R("B"))),
                    Sub("ph") ?? BiRefl(h, L("ph")), Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cixp": // X_ x e. A B ($d x ph)
                return pr.Apply("ixpeq12dv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "wf":   // F : A --> B
                return pr.Apply("feq123d", S(("ph", h), ("F", L("F")), ("G", R("F")), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("F") ?? Refl(h, L("F")), Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cuni": // U. A
                return pr.Apply("unieqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "wrex": // E. x e. A ph ($d x ph)
                return pr.Apply("rexeqbidv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", R("A")), ("ps", L("ph")), ("ch", R("ph"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("ph") ?? BiRefl(h, L("ph")));
            case "ciun": // U_ x e. A B: the domain by iuneq1d, the body by iuneq2dv
                {
                    string x = L("x");
                    Proof? pa = Sub("A"), pb = Sub("B");
                    Proof? dom = pa is Proof da ? pr.Apply("iuneq1d", S(("ph", h), ("x", x), ("A", L("A")), ("B", R("A")), ("C", L("B"))), da) : null;
                    Proof? body = pb is Proof db
                        ? pr.Apply("iuneq2dv", S(("ph", h), ("x", x), ("A", R("A")), ("B", L("B")), ("C", R("B"))),
                            pr.Apply("adantr", S(("ph", h), ("ps", Split(db.Proves).X), ("ch", $"{x} e. {R("A")}")), db))
                        : null;
                    return dom is Proof d1 && body is Proof b1 ? Trans(d1, b1) : (dom ?? body!.Value);
                }
            case "crdg": // rec ( F , I )
                return Syl(Jca(Sub("F") ?? Refl(h, L("F")), Sub("I") ?? Refl(h, L("I"))),
                    pr.Apply("rdgeq12", S(("F", L("F")), ("G", R("F")), ("A", L("I")), ("B", R("I")))));
            case "cfrecs": // frecs ( R , A , F )
                return Syl(pr.Apply("3jca", S(("ph", h), ("ps", $"{L("R")} = {R("R")}"), ("ch", $"{L("A")} = {R("A")}"), ("th", $"{L("F")} = {R("F")}")),
                        Sub("R") ?? Refl(h, L("R")), Sub("A") ?? Refl(h, L("A")), Sub("F") ?? Refl(h, L("F"))),
                    pr.Apply("frecseq123", S(("R", L("R")), ("S", R("R")), ("A", L("A")), ("B", R("A")), ("F", L("F")), ("G", R("F")))));
            case "cpred": // Pred ( R , A , X )
                return Syl(pr.Apply("3jca", S(("ph", h), ("ps", $"{L("R")} = {R("R")}"), ("ch", $"{L("A")} = {R("A")}"), ("th", $"{L("X")} = {R("X")}")),
                        Sub("R") ?? Refl(h, L("R")), Sub("A") ?? Refl(h, L("A")), Sub("X") ?? Refl(h, L("X"))),
                    pr.Apply("predeq123", S(("R", L("R")), ("S", R("R")), ("A", L("A")), ("B", R("A")), ("X", L("X")), ("Y", R("X")))));
            case "cima": // ( A " B )
                return pr.Apply("imaeq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cres": // ( A |` B )
                return pr.Apply("reseq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cmpo": // ( x e. A , y e. B |-> C ) ($d x y ph)
                return pr.Apply("mpoeq123dv", S(("ph", h), ("x", L("x")), ("y", L("y")), ("A", L("A")), ("D", R("A")), ("B", L("B")), ("E", R("B")), ("C", L("C")), ("F", R("C"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")), Sub("C") ?? Refl(h, L("C")));
            case "wbr":  // A R B
                return pr.Apply("breq123d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("R", L("R")), ("S", R("R")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("R") ?? Refl(h, L("R")), Sub("B") ?? Refl(h, L("B")));
            case "cs1":  // <" A ">
                return pr.Apply("s1eqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "cqs":  // ( A /. R )
                return Pair("qseq1d", "qseq2d", "qseq12d", "A", "R");
            case "cec":  // [ A ] R
                {
                    Proof? pa = Sub("A"), pr2 = Sub("R");
                    Proof? first = pa is Proof x ? pr.Apply("eceq1d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("R"))), x) : null;
                    Proof? second = pr2 is Proof y ? pr.Apply("eceq2d", S(("ph", h), ("A", L("R")), ("B", R("R")), ("C", R("A"))), y) : null;
                    return first is Proof f1 && second is Proof s1 ? Trans(f1, s1) : (first ?? second!.Value);
                }
            case "crn":  // ran A
                return pr.Apply("rneqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "cint": // |^| A
                return pr.Apply("inteqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "cpw":  // ~P A
                return pr.Apply("pweqd", S(("ph", h), ("A", L("A")), ("B", R("A"))), Sub("A")!.Value);
            case "cin":  // ( A i^i B )
                return pr.Apply("ineq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "cxp":  // ( A X. B )
                return pr.Apply("xpeq12d", S(("ph", h), ("A", L("A")), ("B", R("A")), ("C", L("B")), ("D", R("B"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("B") ?? Refl(h, L("B")));
            case "crab": // { x e. A | ph } ($d x ph)
                return pr.Apply("rabeqbidv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", R("A")), ("ps", L("ph")), ("ch", R("ph"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("ph") ?? BiRefl(h, L("ph")));
            case "copab": // { <. x , y >. | ph } ($d x y ph)
                return pr.Apply("opabbidv", S(("ph", h), ("x", L("x")), ("y", L("y")), ("ps", L("ph")), ("ch", R("ph"))), Sub("ph")!.Value);
            case "wer":  // R Er A, by the closed ereq1 and ereq2
                {
                    Proof? pRel = Sub("R"), pDom = Sub("A");
                    Proof? first = pRel is Proof x ? Syl(x, pr.Apply("ereq1", S(("R", L("R")), ("S", R("R")), ("A", L("A"))))) : null;
                    Proof? second = pDom is Proof y ? Syl(y, pr.Apply("ereq2", S(("A", L("A")), ("B", R("A")), ("R", R("R"))))) : null;
                    if (first is Proof f1 && second is Proof s1)
                    {
                        return pr.Apply("bitrd", S(("ph", h), ("ps", $"{L("R")} Er {L("A")}"), ("ch", $"{R("R")} Er {L("A")}"), ("th", $"{R("R")} Er {R("A")}")), f1, s1);
                    }
                    return first ?? second!.Value;
                }
            case "crio": // ( iota_ x e. A ph ) ($d x ph)
                return pr.Apply("riotaeqbidv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", R("A")), ("ps", L("ph")), ("ch", R("ph"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("ph") ?? BiRefl(h, L("ph")));
            case "wral": // A. x e. A ph ($d x ph)
                return pr.Apply("raleqbidv", S(("ph", h), ("x", L("x")), ("A", L("A")), ("B", R("A")), ("ps", L("ph")), ("ch", R("ph"))),
                    Sub("A") ?? Refl(h, L("A")), Sub("ph") ?? BiRefl(h, L("ph")));
            case "wal":  // A. x ph ($d x ph)
                return pr.Apply("albidv", S(("ph", h), ("x", L("x")), ("ps", L("ph")), ("ch", R("ph"))), Sub("ph")!.Value);
            case "wex":  // E. x ph ($d x ph)
                return pr.Apply("exbidv", S(("ph", h), ("x", L("x")), ("ps", L("ph")), ("ch", R("ph"))), Sub("ph")!.Value);
            case "wn":   // -. ph
                return pr.Apply("notbid", S(("ph", h), ("ps", L("ph")), ("ch", R("ph"))), Sub("ph")!.Value);
            case "wceq": // A = B
                return Pair("eqeq1d", "eqeq2d", "eqeq12d", "A", "B");
            case "wcel": // A e. B
                return Pair("eleq1d", "eleq2d", "eleq12d", "A", "B");
            case "wss":  // A C_ B
                return Pair("sseq1d", "sseq2d", "sseq12d", "A", "B");
            case "wi":   // ( ph -> ps )
                return PairWff("imbi1d", "imbi2d", "imbi12d", "ph", "ps");
            case "wa":   // ( ph /\ ps )
                return PairWff("anbi1d", "anbi2d", "anbi12d", "ph", "ps");
            case "wo":   // ( ph \/ ps )
                return PairWff("orbi1d", "orbi2d", "orbi12d", "ph", "ps");
        }
        throw new InvalidOperationException($"no congruence rule for {n.Rule.Label} (in {Render(n, hole, a)})");

        // A binary class relation: rewrite the left, the right, or both.
        Proof Pair(string left, string right, string both, string lv, string rv)
        {
            Proof? pl = Sub(lv), prr = Sub(rv);
            if (pl is Proof x && prr is Proof y)
            {
                return pr.Apply(both, S(("ph", h), ("A", L(lv)), ("B", R(lv)), ("C", L(rv)), ("D", R(rv))), x, y);
            }
            return pl is Proof only
                ? pr.Apply(left, S(("ph", h), ("A", L(lv)), ("B", R(lv)), ("C", L(rv))), only)
                : pr.Apply(right, S(("ph", h), ("A", L(rv)), ("B", R(rv)), ("C", L(lv))), prr!.Value);
        }

        // A binary connective: the children's proofs are biconditionals.
        Proof PairWff(string left, string right, string both, string lv, string rv)
        {
            Proof? pl = Sub(lv), prr = Sub(rv);
            if (pl is Proof x && prr is Proof y)
            {
                return pr.Apply(both, S(("ph", h), ("ps", L(lv)), ("ch", R(lv)), ("th", L(rv)), ("ta", R(rv))), x, y);
            }
            return pl is Proof only
                ? pr.Apply(left, S(("ph", h), ("ps", L(lv)), ("ch", R(lv)), ("th", L(rv))), only)
                : pr.Apply(right, S(("ph", h), ("ps", L(rv)), ("ch", R(rv)), ("th", L(lv))), prr!.Value);
        }
    }
}
