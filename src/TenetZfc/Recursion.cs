using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The bridge lemmas recursive inductive types rest on (docs/milestone3.md, step 3). A recursive type's recursor is
/// defined by set.mm's well-founded recursion, frecs, over the relation "has smaller rank":
///
///   RankLt := { &lt;. x , y &gt;. | ( rank ` x ) e. ( rank ` y ) }
///
/// frr2 then gives each computation rule, provided RankLt is well-founded on the type (Fr) and set-like there (Se,
/// which exse gives for any set). A recursive field sits inside nested ordered pairs of its value, so its rank is
/// smaller, which is what puts it among the value's predecessors.
///
/// These lemmas are proved once, for any class A, and written into each output that uses them as $p theorems.
/// </summary>
public sealed class Recursion(Prover pr)
{
    private readonly Deduction _d = new(pr);

    /// <summary>The relation, as set.mm text.</summary>
    public const string RankLt = "{ <. x , y >. | ( rank ` x ) e. ( rank ` y ) }";

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>
    /// |- RankLt Fr A: in a nonempty w, an element of least rank exists (the ranks form a nonempty set of ordinals,
    /// onint, and fvelimab finds an element with the least one), and nothing in w has smaller rank (onnmin).
    /// </summary>
    public (TenetZfc.Metamath.Expr Statement, List<string> Proof, string[] Distinct) RankFr()
    {
        const string r = RankLt, c = "( rank \" w )", min = "|^| ( rank \" w )";
        const string ph0 = "( w C_ A /\\ w =/= (/) )";
        const string goal = "E. v e. w A. s e. w -. s " + r + " v";

        // ( rank " w ) C_ On, and it is nonempty when w is.
        Proof onss = pr.Apply("sstri", S(("A", c), ("B", "ran rank"), ("C", "On")),
            pr.Apply("imassrn", S(("A", "rank"), ("B", "w"))),
            pr.Apply("ax-mp", S(("ph", "rank : U. ( R1 \" On ) --> On"), ("ps", "ran rank C_ On")),
                pr.Apply("rankf", S()), pr.Apply("frn", S(("F", "rank"), ("A", "U. ( R1 \" On )"), ("B", "On")))));
        Proof onssH = _d.Lift(ph0, onss);
        Proof fnAndSs(string bi) => pr.Apply("mp2an", S(("ph", "rank Fn _V"), ("ps", "w C_ _V"), ("ch", bi)),
            pr.Apply("rankfn", S()), pr.Apply("ssv", S(("A", "w"))),
            bi.StartsWith("( ( rank", StringComparison.Ordinal)
                ? pr.Apply("fnimaeq0", S(("F", "rank"), ("A", "_V"), ("B", "w")))
                : pr.Apply("fvelimab", S(("F", "rank"), ("A", "_V"), ("B", "w"), ("C", min), ("x", "v"))));
        Proof empty = fnAndSs($"( {c} = (/) <-> w = (/) )");
        Proof nonempty = pr.Apply("sylibr", S(("ph", ph0), ("ps", "w =/= (/)"), ("ch", $"{c} =/= (/)")),
            pr.Apply("simpr", S(("ph", "w C_ A"), ("ps", "w =/= (/)"))),
            pr.Apply("necon3bii", S(("A", c), ("B", "(/)"), ("C", "w"), ("D", "(/)")), empty));

        // The least rank is a rank of something in w.
        Proof inC = _d.Syl(_d.Jca(onssH, nonempty), pr.Apply("onint", S(("A", c))));
        Proof some = pr.Apply("sylib", S(("ph", ph0), ("ps", $"{min} e. {c}"), ("ch", $"E. v e. w ( rank ` v ) = {min}")),
            inC, fnAndSs($"( {min} e. {c} <-> E. v e. w ( rank ` v ) = {min} )"));

        // That element is minimal: for s in w, -. s RankLt v.
        const string ph1 = "( ( " + ph0 + " /\\ v e. w ) /\\ ( rank ` v ) = " + min + " )";
        const string ph2 = "( " + ph1 + " /\\ s e. w )";
        Proof Hyp(string ph, string h) => HypOf(ph, h) ?? throw new InvalidOperationException($"no {h} in {ph}");
        Proof sRank = pr.Apply("fnfvimad", S(("ph", ph2), ("F", "rank"), ("A", "_V"), ("B", "s"), ("C", "w")),
            _d.Lift(ph2, pr.Apply("rankfn", S())), _d.Lift(ph2, pr.Apply("vex", S(("x", "s")))), Hyp(ph2, "s e. w"));
        Proof notBelow = _d.Syl(_d.Jca(_d.Lift(ph2, onss), sRank), pr.Apply("onnmin", S(("A", c), ("B", "( rank ` s )"))));
        Proof bi = pr.Apply("eleq2d", S(("ph", ph2), ("A", "( rank ` v )"), ("B", min), ("C", "( rank ` s )")),
            Hyp(ph2, $"( rank ` v ) = {min}"));
        Proof notLt = pr.Apply("mtbird", S(("ph", ph2), ("ps", "( rank ` s ) e. ( rank ` v )"), ("ch", $"( rank ` s ) e. {min}")), notBelow, bi);
        Proof notR = pr.Apply("sylnibr", S(("ph", ph2), ("ps", "( rank ` s ) e. ( rank ` v )"), ("ch", $"s {r} v")), notLt, Brab("s", "v"));
        Proof all = pr.Apply("ralrimiva", S(("ph", ph1), ("ps", $"-. s {r} v"), ("x", "s"), ("A", "w")), notR);
        Proof step = pr.Apply("ex", S(("ph", $"( {ph0} /\\ v e. w )"), ("ps", $"( rank ` v ) = {min}"), ("ch", $"A. s e. w -. s {r} v")), all);
        Proof lift = pr.Apply("reximdva", S(("ph", ph0), ("ps", $"( rank ` v ) = {min}"), ("ch", $"A. s e. w -. s {r} v"), ("x", "v"), ("A", "w")), step);
        Proof found = pr.Apply("mpd", S(("ph", ph0), ("ps", $"E. v e. w ( rank ` v ) = {min}"), ("ch", goal)), some, lift);

        // Generalize over w, and read it as RankLt Fr A by df-fr.
        Proof gen = pr.Apply("ax-gen", S(("ph", $"( {ph0} -> {goal} )"), ("x", "w")), found);
        Proof fr = pr.Apply("mpbir", S(("ph", $"{r} Fr A"), ("ps", $"A. w ( {ph0} -> {goal} )")), gen,
            pr.Apply("df-fr", S(("R", r), ("A", "A"), ("x", "w"), ("y", "v"), ("z", "s"))));
        return (fr.Proves, fr.Proof, ["x y w v s A"]);
    }

    /// <summary>The label of <see cref="StageSs"/>'s theorem, and of its hypothesis.</summary>
    public const string StageSsLabel = "lean-stagess", StageSsHyp = "lean-stagess.1";

    /// <summary>Its hypothesis: in context ph, the step's values contain their argument.</summary>
    public const string StageSsHypText = "|- ( ph -> z C_ ( F ` z ) )";

    /// <summary>
    /// The stages of a recursive type only grow: for a step F whose values contain their argument (in context ph),
    ///   |- ( ( ( M e. _om /\ N e. _om ) /\ N C_ M ) -> ( ph -> ( rec ( F , A ) ` N ) C_ ( rec ( F , A ) ` M ) ) ).
    /// By induction from N (findsg) on ( ph -> stage N C_ stage x ): at N by ssid, and from y to suc y because stage
    /// suc y is F at stage y (rdgsuc), which contains stage y (the hypothesis at stage y, by vtocl).
    /// A constructor with several recursive fields, each in some stage, puts them all in the union of those stages.
    /// </summary>
    public (TenetZfc.Metamath.Expr Statement, List<string> Proof, string[] Distinct) StageSs()
    {
        static string G(string n) => $"( rec ( F , A ) ` {n} )";
        static string Phi(string n) => $"( ph -> {G("N")} C_ {G(n)} )";
        Proof hyp = ([StageSsHyp], TenetZfc.Metamath.Expr.Of(StageSsHypText));
        Proof Eq(string x, string to) => _d.Congruence("wff", Phi("Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {to}"))));

        // At N: stage N C_ stage N.
        Proof base_ = _d.Lift("N e. _om", _d.Lift("ph", pr.Apply("ssid", S(("A", G("N"))))));

        // From y to suc y: under H /\ ph, stage y C_ ( F ` stage y ) = stage suc y.
        const string h = "( ( y e. _om /\\ N e. _om ) /\\ N C_ y )";
        const string hp = "( " + h + " /\\ ph )";
        Proof Hyp(string ctx, string x) => HypOf(ctx, x) ?? throw new InvalidOperationException($"no {x} in {ctx}");
        Proof yOn = _d.Syl(Hyp(hp, "y e. _om"), pr.Apply("nnon", S(("A", "y"))));
        Proof suc = _d.Syl(yOn, pr.Apply("rdgsuc", S(("B", "y"), ("F", "F"), ("A", "A"))));
        string fy = $"( F ` {G("y")} )";
        Proof inst = pr.Apply("vtocl", S(("x", "z"), ("A", G("y")), ("ph", "( ph -> z C_ ( F ` z ) )"), ("ps", $"( ph -> {G("y")} C_ {fy} )")),
            pr.Apply("fvex", S(("F", "rec ( F , A )"), ("A", "y"))),
            _d.Congruence("wff", "( ph -> Z C_ ( F ` Z ) )", "Z", pr.Apply("id", S(("ph", $"z = {G("y")}")))),
            hyp);
        Proof grows = pr.Apply("sseqtrrd", S(("ph", hp), ("A", G("y")), ("B", fy), ("C", G("suc y"))),
            _d.Syl(Hyp(hp, "ph"), inst), suc);
        string k = $"( ( {h} /\\ {Phi("y")} ) /\\ ph )";
        Proof atY = pr.Apply("mpd", S(("ph", k), ("ps", "ph"), ("ch", $"{G("N")} C_ {G("y")}")), Hyp(k, "ph"), Hyp(k, Phi("y")));
        Proof atSuc = pr.Apply("sstrd", S(("ph", k), ("A", G("N")), ("B", G("y")), ("C", G("suc y"))),
            atY, _d.Syl(_d.Jca(Hyp(k, h), Hyp(k, "ph")), grows));
        Proof step = pr.Apply("ex", S(("ph", h), ("ps", Phi("y")), ("ch", Phi("suc y"))),
            pr.Apply("ex", S(("ph", $"( {h} /\\ {Phi("y")} )"), ("ps", "ph"), ("ch", $"{G("N")} C_ {G("suc y")}")), atSuc));

        Proof all = pr.Apply("findsg", S(("x", "x"), ("y", "y"), ("ph", Phi("x")), ("ps", Phi("N")), ("ch", Phi("y")), ("th", Phi("suc y")),
                ("ta", Phi("M")), ("A", "M"), ("B", "N")),
            Eq("x", "N"), Eq("x", "y"), Eq("x", "suc y"), Eq("x", "M"), base_, step);
        return (all.Proves, all.Proof, ["x y z", "x y z ph", "x y z F", "x y z A", "x y M", "x y N"]);
    }

    /// <summary>The label of <see cref="RankSe"/>'s theorem.</summary>
    public const string RankSeLabel = "lean-rankse";

    /// <summary>
    /// |- RankLt Se _V: the sets of smaller rank than z are a set, since they are all in ( R1 ` ( rank ` z ) )
    /// (rankr1ag). The recursors of mutual and nested blocks recurse over every set, so they need it on _V.
    /// </summary>
    public (TenetZfc.Metamath.Expr Statement, List<string> Proof, string[] Distinct) RankSe()
    {
        const string r = RankLt, r1 = "( R1 ` ( rank ` z ) )", below = "{ w e. _V | w " + r + " z }";
        Proof wf = pr.Apply("eleqtrri", S(("A", "w"), ("B", "_V"), ("C", "U. ( R1 \" On )")), pr.Apply("vex", S(("x", "w"))), pr.Apply("unir1", S()));
        Proof dom = pr.Apply("eleqtrri", S(("A", "( rank ` z )"), ("B", "On"), ("C", "dom R1")), pr.Apply("rankon", S(("A", "z"))),
            pr.Apply("ax-mp", S(("ph", "R1 Fn On"), ("ps", "dom R1 = On")), pr.Apply("r1fnon", S()), pr.Apply("fndm", S(("F", "R1"), ("A", "On")))));
        Proof inR1 = pr.Apply("mp2an", S(("ph", "w e. U. ( R1 \" On )"), ("ps", "( rank ` z ) e. dom R1"), ("ch", $"( w e. {r1} <-> ( rank ` w ) e. ( rank ` z ) )")),
            wf, dom, pr.Apply("rankr1ag", S(("A", "w"), ("B", "( rank ` z )"))));
        Proof imp = pr.Apply("sylbi", S(("ph", $"w {r} z"), ("ps", "( rank ` w ) e. ( rank ` z )"), ("ch", $"w e. {r1}")),
            Brab("w", "z"), pr.Apply("biimpri", S(("ph", $"w e. {r1}"), ("ps", "( rank ` w ) e. ( rank ` z )")), inR1));
        Proof all = pr.Apply("rgen", S(("x", "w"), ("A", "_V"), ("ph", $"( w {r} z -> w e. {r1} )")),
            pr.Apply("a1i", S(("ph", $"( w {r} z -> w e. {r1} )"), ("ps", "w e. _V")), imp));
        Proof ss = pr.Apply("mpbir", S(("ph", $"{below} C_ {r1}"), ("ps", $"A. w e. _V ( w {r} z -> w e. {r1} )")), all,
            pr.Apply("rabss", S(("x", "w"), ("A", "_V"), ("ph", $"w {r} z"), ("B", r1))));
        Proof set = pr.Apply("ssexi", S(("A", below), ("B", r1)), pr.Apply("fvex", S(("F", "R1"), ("A", "( rank ` z )"))), ss);
        Proof every = pr.Apply("rgen", S(("x", "z"), ("A", "_V"), ("ph", $"{below} e. _V")),
            pr.Apply("a1i", S(("ph", $"{below} e. _V"), ("ps", "z e. _V")), set));
        Proof se = pr.Apply("mpbir", S(("ph", $"{r} Se _V"), ("ps", $"A. z e. _V {below} e. _V")), every,
            pr.Apply("df-se", S(("R", r), ("A", "_V"), ("x", "z"), ("y", "w"))));
        return (se.Proves, se.Proof, ["x y z w"]);
    }

    /// <summary>|- ( a RankLt b <-> ( rank ` a ) e. ( rank ` b ) ), for set variables a and b, by brab.</summary>
    public Proof Brab(string a, string b)
    {
        string ps = $"( rank ` {a} ) e. ( rank ` y )", ch = $"( rank ` {a} ) e. ( rank ` {b} )";
        Proof h3 = _d.Congruence("wff", "( rank ` Z ) e. ( rank ` y )", "Z", pr.Apply("id", S(("ph", $"x = {a}"))));
        Proof h4 = _d.Congruence("wff", $"( rank ` {a} ) e. ( rank ` Z )", "Z", pr.Apply("id", S(("ph", $"y = {b}"))));
        return pr.Apply("brab", S(("x", "x"), ("y", "y"), ("ph", "( rank ` x ) e. ( rank ` y )"), ("ps", ps), ("ch", ch),
                ("A", a), ("B", b), ("R", RankLt)),
            pr.Apply("vex", S(("x", a))), pr.Apply("vex", S(("x", b))), h3, h4, pr.Apply("eqid", S(("A", RankLt))));
    }

    private Proof? HypOf(string ph, string h)
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
        return HypOf(left, h) is Proof p ? _d.Syl(pr.Apply("simpl", S(("ph", left), ("ps", right))), p) : null;
    }
}
