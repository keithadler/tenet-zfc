using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Types as members of universes (docs/milestone3.md, "Theorems through the model"): ( ph -> X e. ( U ` K ) ) for the
/// set X an inductive type, a function space or a proposition translates to, by the closure of the Grothendieck
/// universe ( U ` K ) under pairs, singletons, unions, indexed unions and function spaces (gruop, grusn, gruun,
/// gruiun, grumap). A recursive type's stages are members by induction over ω (finds2): the empty stage, and each
/// next stage, the last one with the constructors' tuples over it.
/// </summary>
public sealed partial class Model
{
    private static readonly string[] Ordinals = ["(/)", "1o", "2o", "3o", "4o"];

    private static int OrdinalIndex(string k) => Array.IndexOf(Ordinals, k);

    /// <summary>( ph -> K e. _om ) for a concrete ordinal.</summary>
    private Proof OrdOm(string ph, string k) => _d.Lift(ph, pr.Apply(k switch
    {
        "(/)" => "peano1",
        "1o" => "1onn",
        "2o" => "2onn",
        "3o" => "3onn",
        "4o" => "4onn",
        _ => throw new Refused($"not a concrete level: {k}"),
    }, S()));

    /// <summary>( ph -> ( U ` K ) e. Univ ).</summary>
    private Proof LevelUniv(string ph, string k)
    {
        EnsureTowerLemmas();
        return _d.Syl(_d.Jca(Hyp(ph, UHyp) ?? throw new Refused("no universe hypothesis"), OrdOm(ph, k)), ApplyId("lean-tw-u", S(("U", "U"), ("K", k))));
    }

    /// <summary>
    /// In the lowered tower (docs/milestone4.md), the weak universe a parameter-free recursive type's stages are built
    /// in: ( R1 ` ( ( rank ` (/) ) +o _om ) ), a member of every level (lean-wu-r).
    /// </summary>
    private const string SmallWuni = "( R1 ` ( ( rank ` (/) ) +o _om ) )";

    /// <summary>( ph -> G e. WUni ) for G a level of the lowered tower, or <see cref="SmallWuni"/> (wunex3).</summary>
    private Proof LevelWU(string ph, string g)
    {
        if (g == SmallWuni)
        {
            Proof w = pr.Apply("wunex3", S(("A", "(/)"), ("U", g), ("V", "_V")), pr.Apply("eqid", S(("A", g))));
            Proof both = pr.Apply("ax-mp", S(("ph", "(/) e. _V"), ("ps", $"( {g} e. WUni /\\ (/) C_ {g} )")), pr.Apply("0ex", S()), w);
            return _d.Lift(ph, pr.Apply("simpli", S(("ph", $"{g} e. WUni"), ("ps", $"(/) C_ {g}")), both));
        }
        string k = LevelOf(g) ?? throw new Refused($"not a weak universe of the lowered tower: {g}");
        EnsureTowerLemmas();
        return _d.Syl(LevelUniv(ph, k), ApplyId("lean-wu-w", S(("W", g))));
    }

    /// <summary>K for G = ( U ` K ) with K a concrete level, or null.</summary>
    private string? LevelOf(string g)
    {
        SyntaxTree? gn = pr.Parse("class", g.Split(' '));
        return gn is { Rule.Label: "cfv" } && pr.Render(gn.Children[1]) == "U" && OrdinalIndex(pr.Render(gn.Children[0])) >= 0
            ? pr.Render(gn.Children[0]) : null;
    }

    /// <summary>( ph -> Tr ( U ` K ) ) (grutr, or wuntr in the lowered tower).</summary>
    private Proof LevelTr(string ph, string k)
    {
        string g = $"( U ` {k} )";
        return lowered
            ? _d.Syl(LevelWU(ph, g), pr.Apply("wuntr", S(("U", g))))
            : _d.Syl(LevelUniv(ph, k), pr.Apply("grutr", S(("U", g))));
    }

    /// <summary>( ph -> B e. G ) from ( ph -> A e. G ) and ( ph -> B e. A ), G a weak universe (wunelss).</summary>
    private Proof WunEl(string ph, string g, string a, string b, Proof aIn, Proof bInA)
    {
        Proof ss = pr.Apply("wunelss", S(("ph", ph), ("U", g), ("A", a)), LevelWU(ph, g), aIn);
        return pr.Apply("sseldd", S(("ph", ph), ("A", a), ("B", g), ("C", b)), ss, bInA);
    }

    /// <summary>( ph -> ( U ` J ) e. ( U ` K ) ) for J below K.</summary>
    private Proof LevelIn(string ph, string j, string k)
    {
        int ji = OrdinalIndex(j), ki = OrdinalIndex(k);
        if (ji < 0 || ki <= ji)
        {
            throw new Refused($"( U ` {j} ) is not below ( U ` {k} )");
        }
        // ( U ` K' ) e. ( U ` suc K' ) for K' the level just below K, with suc K' written as K.
        string below = Ordinals[ki - 1];
        Proof s = _d.Syl(_d.Jca(Hyp(ph, UHyp)!.Value, OrdOm(ph, below)), ApplyId("lean-tw-s", S(("U", "U"), ("K", below))));
        Proof sucIs = _d.Lift(ph, pr.Apply("eqcomi", S(("A", k), ("B", $"suc {below}")), pr.Apply($"df-{k}", S())));
        Proof fv = pr.Apply("fveq2d", S(("ph", ph), ("A", $"suc {below}"), ("B", k), ("F", "U")), sucIs);
        Proof step = pr.Apply("eleqtrd", S(("ph", ph), ("A", $"( U ` {below} )"), ("B", $"( U ` suc {below} )"), ("C", $"( U ` {k} )")), s, fv);
        if (ki - 1 == ji)
        {
            return step;
        }
        Proof deeper = LevelIn(ph, j, below);
        return GruEl(ph, k, $"( U ` {below} )", $"( U ` {j} )", step, deeper);
    }

    /// <summary>( ph -> B e. G ) from ( ph -> A e. G ) and ( ph -> B e. A ), G = ( U ` K ) (gruel).</summary>
    private Proof GruEl(string ph, string k, string a, string b, Proof aIn, Proof bInA)
    {
        string g = $"( U ` {k} )";
        if (lowered)
        {
            return WunEl(ph, g, a, b, aIn, bInA);
        }
        return _d.Syl(pr.Apply("3jca", S(("ph", ph), ("ps", $"{g} e. Univ"), ("ch", $"{a} e. {g}"), ("th", $"{b} e. {a}")), LevelUniv(ph, k), aIn, bInA),
            pr.Apply("gruel", S(("U", g), ("A", a), ("B", b))));
    }

    /// <summary>( ph -> _om e. ( U ` K ) ).</summary>
    private Proof OmIn(string ph, string k)
    {
        EnsureTowerLemmas();
        Proof om0 = _d.Syl(Hyp(ph, UHyp)!.Value, ApplyId("lean-tw-om", S(("U", "U"))));
        return k == "(/)" ? om0 : GruEl(ph, k, "( U ` (/) )", "_om", LevelIn(ph, "(/)", k), om0);
    }

    /// <summary>( d.Ph -> X e. G ), G = ( U ` K ) or 2o.</summary>
    private Proof UnivMem(PCtx d, string x, string g)
    {
        using var prof = Prof.Time("UnivMem");
        if (g == "2o")
        {
            return PropIn2o(d, x);
        }
        if (lowered && g == SmallWuni)
        {
            return SmallMem(d, x);
        }
        SyntaxTree gn = pr.Parse("class", g.Split(' '))!;
        if (gn.Rule.Label != "cfv" || pr.Render(gn.Children[1]) != "U" || OrdinalIndex(pr.Render(gn.Children[0])) < 0)
        {
            throw new Refused($"not a level of the tower: {g} (for {x}; context {d.Ph})");
        }
        string k = pr.Render(gn.Children[0]);
        if (TryHyp(d, $"{x} e. {g}") is Proof direct)
        {
            return direct;
        }
        SyntaxTree n = pr.Parse("class", x.Split(' ')) ?? throw new Refused($"does not parse: {x}");
        string C(int i) => pr.Render(n.Children[i]);
        if (lowered && LoweredMem(d, x, g, n) is Proof lp)
        {
            return lp;
        }
        Proof Univ() => LevelUniv(d.Ph, k);
        Proof Three(string label, Dictionary<string, string> sub, string a, string b) =>
            _d.Syl(pr.Apply("3jca", S(("ph", d.Ph), ("ps", $"{g} e. Univ"), ("ch", $"{a} e. {g}"), ("th", $"{b} e. {g}")), Univ(), UnivMem(d, a, g), UnivMem(d, b, g)),
                pr.Apply(label, sub));
        switch (n.Rule.Label)
        {
            case "com":
                return OmIn(d.Ph, k);
            case "c0":
                return GruEl(d.Ph, k, "_om", "(/)", OmIn(d.Ph, k), _d.Lift(d.Ph, pr.Apply("peano1", S())));
            case "c1o":
                return GruEl(d.Ph, k, "_om", "1o", OmIn(d.Ph, k), _d.Lift(d.Ph, pr.Apply("1onn", S())));
            case "c2o":
                return GruEl(d.Ph, k, "_om", "2o", OmIn(d.Ph, k), _d.Lift(d.Ph, pr.Apply("2onn", S())));
            case "csn":
                return _d.Syl(_d.Jca(Univ(), UnivMem(d, C(0), g)), pr.Apply("grusn", S(("U", g), ("A", C(0)))));
            case "cop":
                return Three("gruop", S(("U", g), ("A", C(0)), ("B", C(1))), C(0), C(1));
            case "cun":
                return Three("gruun", S(("U", g), ("A", C(0)), ("B", C(1))), C(0), C(1));
            case "co" when C(2) == "^m":
                return Three("grumap", S(("U", g), ("A", C(0)), ("B", C(1))), C(0), C(1));
            case "cif":
                return pr.Apply("ifcld", S(("ph", d.Ph), ("ps", C(0)), ("A", C(1)), ("B", C(2)), ("C", g)), UnivMem(d, C(1), g), UnivMem(d, C(2), g));
            case "cfv" when C(1) == "U" && OrdinalIndex(C(0)) >= 0:
                return LevelIn(d.Ph, C(0), k);
            case "cfv" when pr.Parse("class", C(1).Split(' ')) is { Rule.Label: "crdg" } rdg:
                return StageIn(d, x, rdg, C(0), g);
            case "ciun" or "cixp" when !lowered:
                {
                    string v = C(0), dom = C(1), body = C(2);
                    if (d.Ph.Split(' ').Contains(v))
                    {
                        // The hypotheses bind the same letter: rename it apart (cbviunv, cbvixpv).
                        string v2 = FreshFor(d.Ph, x, g);
                        string x2 = $"{(n.Rule.Label == "ciun" ? "U_" : "X_")} {v2} e. {dom} {SubstFree(body, v, v2)}";
                        return pr.Apply("eqeltrd", S(("ph", d.Ph), ("A", x), ("B", x2), ("C", g)), AlphaIn(d.Ph, x, x2), UnivMem(d, x2, g));
                    }
                    Proof domIn = UnivMem(d, dom, g);
                    PCtx e = EnterText(d, v, dom);
                    Proof bodyIn = UnivMem(e, body, g);
                    Proof all = pr.Apply("ralrimiva", S(("ph", d.Ph), ("ps", $"{body} e. {g}"), ("x", v), ("A", dom)), bodyIn);
                    return _d.Syl(pr.Apply("3jca", S(("ph", d.Ph), ("ps", $"{g} e. Univ"), ("ch", $"{dom} e. {g}"), ("th", $"A. {v} e. {dom} {body} e. {g}")), Univ(), domIn, all),
                        pr.Apply(n.Rule.Label == "ciun" ? "gruiun" : "gruixp", S(("U", g), ("x", v), ("A", dom), ("B", body))));
                }
        }
        // A constant (a type former) applied: its typing lemma, then each argument.
        if (ConstApp(x) is (Name head, List<string> cargs))
        {
            (string label, string cty) = ConstTyLemma(head);
            Proof cur = _d.Syl(Hyp(d.Ph, UHyp) ?? throw new Refused("no universe hypothesis"), ApplyId(label, S(("U", "U"))));
            string f = $"( {Token(head)} ` U )", ty = cty;
            foreach (string a in cargs)
            {
                SyntaxTree tn = pr.Parse("class", ty.Split(' '))!;
                string dom = pr.Render(tn.Children[1]);
                Proof aIn = TryHyp(d, $"{a} e. {dom}") ?? HypAlpha(d, a, dom) ?? TextMem(d, a, dom);
                (cur, ty) = ApplyText(d.Ph, cur, f, ty, a, aIn);
                f = $"( {f} ` {a} )";
            }
            if (ty == g)
            {
                return cur;
            }
            Proof tyIn = ty == "2o" ? UnivMem(d, "2o", g) : LevelIn(d.Ph, pr.Render(pr.Parse("class", ty.Split(' '))!.Children[0]), k);
            return GruEl(d.Ph, k, ty, x, tyIn, cur);
        }
        // A value of a function variable, typed by its own hypothesis (a motive z e. X_ y e. D ( G ^m P ), applied):
        // down the application chain by ApplyText, and the last application into G at any argument, since a function's
        // value is in its range or (/) (fvrn0), both in G.
        if (n.Rule.Label == "cfv" && FnType(d, C(1)) is (Proof pf, string tyf)
            && pr.Parse("class", tyf.Split(' ')) is { Rule.Label: "co" } tyn && pr.Render(tyn.Children[2]) == "^m" && pr.Render(tyn.Children[0]) == g)
        {
            string fn = C(1), arg = C(0), fdom = pr.Render(tyn.Children[1]);
            Proof isF = _d.Syl(pf, pr.Apply("elmapi", S(("A", fn), ("B", g), ("C", fdom))));
            if ((TryHyp(d, $"{arg} e. {fdom}") ?? HypAlpha(d, arg, fdom)) is Proof ai)
            {
                return pr.Apply("ffvelcdmd", S(("ph", d.Ph), ("F", fn), ("A", fdom), ("B", g), ("C", arg)), isF, ai);
            }
            Proof ranIn = _d.Syl(isF, pr.Apply("frn", S(("F", fn), ("A", fdom), ("B", g))));
            Proof zeroIn = UnivMem(d, "(/)", g);
            Proof both = pr.Apply("unssd", S(("ph", d.Ph), ("A", $"ran {fn}"), ("B", "{ (/) }"), ("C", g)), ranIn,
                pr.Apply("snssd", S(("ph", d.Ph), ("A", "(/)"), ("B", g)), zeroIn));
            Proof inUn = _d.Lift(d.Ph, pr.Apply("fvrn0", S(("F", fn), ("X", arg))));
            return pr.Apply("sseldd", S(("ph", d.Ph), ("A", $"( ran {fn} u. {{ (/) }} )"), ("B", g), ("C", x)), both, inUn);
        }
        // A value of a function into G: F e. ( G ^m D ) and a e. D (elmapi, ffvelcdmd).
        if (n.Rule.Label == "cfv")
        {
            string fn = C(1), arg = C(0);
            foreach ((Proof p, string h) in Facts(d))
            {
                if (!h.StartsWith($"{fn} e. ( {g} ^m ", StringComparison.Ordinal))
                {
                    continue;
                }
                string map = h[(fn.Length + 4)..];
                string fdom = pr.Render(pr.Parse("class", map.Split(' '))!.Children[1]);
                Proof? aIn = TryHyp(d, $"{arg} e. {fdom}") ?? HypAlpha(d, arg, fdom);
                if (aIn is not Proof ai)
                {
                    continue;
                }
                Proof isF = _d.Syl(p, pr.Apply("elmapi", S(("A", fn), ("B", g), ("C", fdom))));
                return pr.Apply("ffvelcdmd", S(("ph", d.Ph), ("F", fn), ("A", fdom), ("B", g), ("C", arg)), isF, ai);
            }
        }
        // A member of something that is itself in G (G is transitive).
        foreach ((Proof p, string h) in Facts(d))
        {
            if (h.StartsWith(x + " e. ", StringComparison.Ordinal))
            {
                string outer = h[(x.Length + 4)..];
                if (outer == g)
                {
                    return p;
                }
                try
                {
                    return GruEl(d.Ph, k, outer, x, UnivMem(d, outer, g), p);
                }
                catch (Refused)
                {
                }
            }
        }
        throw new Refused($"no proof yet that {x} is in the universe {g}");
    }

    /// <summary>( d.Ph -> ( ( lean.c ` U ) ` a1 ) … e. dom ), by c's typing lemma and each argument's membership.</summary>
    private Proof ConstAppMem(PCtx d, Name head, List<string> cargs, string dom)
    {
        (string label, string cty) = ConstTyLemma(head);
        Proof cur = _d.Syl(Hyp(d.Ph, UHyp) ?? throw new Refused("no universe hypothesis"), ApplyId(label, S(("U", "U"))));
        string f = $"( {Token(head)} ` U )", ty = cty;
        foreach (string a in cargs)
        {
            SyntaxTree tn = pr.Parse("class", ty.Split(' '))!;
            if (tn.Rule.Label is not ("co" or "cixp"))
            {
                throw new Refused($"applying {head}, whose type {ty} isn't a function type");
            }
            string adom = pr.Render(tn.Children[1]);
            Proof aIn = TryHyp(d, $"{a} e. {adom}") ?? HypAlpha(d, a, adom) ?? TextMem(d, a, adom);
            (cur, ty) = ApplyText(d.Ph, cur, f, ty, a, aIn);
            f = $"( {f} ` {a} )";
        }
        return Retype(d, f, cur, ty, dom);
    }

    /// <summary>
    /// ( d.Ph -> a e. dom ) from ( d.Ph -> a e. ty ): the two equal as texts, up to bound names, or once a map applied
    /// to an argument at the head of ty is reduced (a recursor's value at a constant motive: ( ( v e. D |-> Nat ) ` q )
    /// is Nat).
    /// </summary>
    private Proof Retype(PCtx d, string a, Proof inTy, string ty, string dom)
    {
        if (ty == dom)
        {
            return inTy;
        }
        try
        {
            return pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", a), ("B", ty), ("C", dom)), inTy, AlphaIn(d.Ph, ty, dom));
        }
        catch (Refused) when (BetaHead(d, ty) is (Proof eq, string to))
        {
            return Retype(d, a, pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", a), ("B", ty), ("C", to)), inTy, eq), to, dom);
        }
    }

    /// <summary>
    /// The lowered tower's closure steps (docs/milestone4.md), or null to fall through to the shared cases (levels,
    /// constants, members of members). A weak universe is closed under pairs, singletons, unions, products and function
    /// spaces (wunop, wunsn, wunun, wunxp, wunmap), but not under indexed unions in general: those are bounded instead
    /// (<see cref="BoundedIun"/>).
    /// </summary>
    private Proof? LoweredMem(PCtx d, string x, string g, SyntaxTree n)
    {
        string C(int i) => pr.Render(n.Children[i]);
        Proof Wu() => LevelWU(d.Ph, g);
        Proof Two(string label, string a, string b) =>
            pr.Apply(label, S(("ph", d.Ph), ("U", g), ("A", a), ("B", b)), Wu(), UnivMem(d, a, g), UnivMem(d, b, g));
        switch (n.Rule.Label)
        {
            case "c0":
                return pr.Apply("wun0", S(("ph", d.Ph), ("U", g)), Wu());
            case "c1o" or "c2o":
                {
                    string o = pr.Render(n);
                    Proof om = pr.Apply("wunom", S(("ph", d.Ph), ("U", g)), Wu());
                    return pr.Apply("sseldd", S(("ph", d.Ph), ("A", "_om"), ("B", g), ("C", o)), om, _d.Lift(d.Ph, pr.Apply(o == "1o" ? "1onn" : "2onn", S())));
                }
            case "csn":
                return pr.Apply("wunsn", S(("ph", d.Ph), ("U", g), ("A", C(0))), Wu(), UnivMem(d, C(0), g));
            case "cop":
                return Two("wunop", C(0), C(1));
            case "cun":
                return Two("wunun", C(0), C(1));
            case "cxp":
                return Two("wunxp", C(0), C(1));
            case "co" when C(2) == "^m":
                return Two("wunmap", C(0), C(1));
            case "ciun":
                return BoundedIun(d, x, g, C(0), C(1), C(2));
        }
        return null;
    }

    /// <summary>( d.Ph -> X e. SmallWuni ): the closure steps alone (no levels, constants or omega inside it).</summary>
    private Proof SmallMem(PCtx d, string x)
    {
        if (TryHyp(d, $"{x} e. {SmallWuni}") is Proof direct)
        {
            return direct;
        }
        SyntaxTree n = pr.Parse("class", x.Split(' ')) ?? throw new Refused($"does not parse: {x}");
        if (n.Rule.Label == "cfv" && pr.Parse("class", pr.Render(n.Children[1]).Split(' ')) is { Rule.Label: "crdg" } rdg)
        {
            return StageIn(d, x, rdg, pr.Render(n.Children[0]), SmallWuni);
        }
        if (n.Rule.Label == "cif")
        {
            return pr.Apply("ifcld", S(("ph", d.Ph), ("ps", pr.Render(n.Children[0])), ("A", pr.Render(n.Children[1])), ("B", pr.Render(n.Children[2])), ("C", SmallWuni)),
                SmallMem(d, pr.Render(n.Children[1])), SmallMem(d, pr.Render(n.Children[2])));
        }
        return LoweredMem(d, x, SmallWuni, n) ?? throw new Refused($"no proof yet that {x} is in the weak universe {SmallWuni}");
    }

    /// <summary>
    /// ( d.Ph -> U_ v e. dom body e. G ) in a weak universe G, which isn't closed under indexed unions. Two shapes, the
    /// ones the model's types are built from:
    /// - a union of singletons of tuples, nested: U_ z e. A U_ w e. B { <. c , <. z , w >. >. }. It is a subset of the
    ///   product of the components' sets, ( { c } X. ( A X. B ) ), a member of G (wunxp, wunsn), so a member (wunss);
    /// - the union of a recursive type's stages, U_ k e. _om ( rec ( F , (/) ) ` k ). Each stage is in the small weak
    ///   universe ( R1 ` ( ( rank ` (/) ) +o _om ) ) (by induction over omega), so the union is a subset of it, and it is
    ///   a member of each level (lean-wu-r): the reflection step. A type with parameters needs a weak universe that
    ///   contains them, not built yet.
    /// </summary>
    private Proof BoundedIun(PCtx d, string x, string g, string v, string dom, string body)
    {
        if (d.Ph.Split(' ').Contains(v))
        {
            throw new Refused($"the union's variable {v} occurs in the hypotheses");
        }
        PCtx e = EnterText(d, v, dom);
        string bound;
        Proof sub;   // ( e.Ph -> body C_ bound )
        Proof boundIn;   // ( d.Ph -> bound e. G )
        SyntaxTree bn = pr.Parse("class", body.Split(' '))!;
        if (dom == "_om" && bn.Rule.Label == "cfv" && pr.Parse("class", pr.Render(bn.Children[1]).Split(' ')) is { Rule.Label: "crdg" } rdg
            && pr.Render(bn.Children[0]) == v)
        {
            bound = SmallWuni;
            Proof stage = StageIn(e, body, rdg, v, SmallWuni);
            sub = pr.Apply("wunelss", S(("ph", e.Ph), ("U", SmallWuni), ("A", body)), LevelWU(e.Ph, SmallWuni), stage);
            string k = LevelOf(g) ?? throw new Refused($"a recursive type's stages inside {g}");
            Proof zeroIn = pr.Apply("wun0", S(("ph", d.Ph), ("U", g)), LevelWU(d.Ph, g));
            boundIn = _d.Syl(_d.Jca(LevelUniv(d.Ph, k), zeroIn), ApplyId("lean-wu-r", S(("W", g), ("X", "(/)"))));
        }
        else
        {
            (bound, sub) = SubsetBound(e, body);
            if (bound.Split(' ').Contains(v))
            {
                throw new Refused($"no bound for the union {x} free of {v}");
            }
            boundIn = UnivMem(d, bound, g);
        }
        Proof iunSub = pr.Apply("iunssd", S(("ph", d.Ph), ("x", v), ("A", dom), ("B", body), ("C", bound)), sub);
        return pr.Apply("wunss", S(("ph", d.Ph), ("U", g), ("A", bound), ("B", x)), LevelWU(d.Ph, g), boundIn, iunSub);
    }

    /// <summary>A set S with ( d.Ph -> body C_ S ), for body a singleton of a tuple, or a union of such (nested).</summary>
    private (string, Proof) SubsetBound(PCtx d, string body)
    {
        SyntaxTree n = pr.Parse("class", body.Split(' '))!;
        if (n.Rule.Label == "csn")
        {
            string a = pr.Render(n.Children[0]);
            (string s, Proof aIn) = ElemBound(d, a);
            return (s, pr.Apply("snssd", S(("ph", d.Ph), ("A", a), ("B", s)), aIn));
        }
        if (n.Rule.Label == "ciun")
        {
            string v = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), inner = pr.Render(n.Children[2]);
            if (d.Ph.Split(' ').Contains(v))
            {
                throw new Refused($"the union's variable {v} occurs in the hypotheses");
            }
            PCtx e = EnterText(d, v, dom);
            (string s, Proof sub) = SubsetBound(e, inner);
            if (s.Split(' ').Contains(v))
            {
                throw new Refused($"no bound for {body} free of {v}");
            }
            return (s, pr.Apply("iunssd", S(("ph", d.Ph), ("x", v), ("A", dom), ("B", inner), ("C", s)), sub));
        }
        throw new Refused($"no bound yet for the union body {body} in a weak universe (milestone 4: an indexed union needs reflection)");
    }

    /// <summary>A set S with ( d.Ph -> a e. S ): a variable's domain, a product for a pair, a singleton for a closed term.</summary>
    private (string, Proof) ElemBound(PCtx d, string a)
    {
        foreach ((Proof p, string h) in Facts(d))
        {
            if (h.StartsWith(a + " e. ", StringComparison.Ordinal))
            {
                return (h[(a.Length + 4)..], p);
            }
        }
        SyntaxTree n = pr.Parse("class", a.Split(' '))!;
        if (n.Rule.Label == "cop")
        {
            string l = pr.Render(n.Children[0]), r = pr.Render(n.Children[1]);
            (string sl, Proof pl) = ElemBound(d, l);
            (string sr, Proof pr2) = ElemBound(d, r);
            return ($"( {sl} X. {sr} )", pr.Apply("opelxpd", S(("ph", d.Ph), ("A", l), ("B", r), ("C", sl), ("D", sr)), pl, pr2));
        }
        if (a.Split(' ').All(tok => pr.Database.FloatOf(tok) is null || pr.Database.FloatOf(tok)!.Expr.Type != "setvar"))
        {
            return ($"{{ {a} }}", pr.Apply("snidg", S(("A", a), ("V", "_V"))) is var sn
                ? _d.Syl(Exists(d.Ph, a), sn) : default);
        }
        throw new Refused($"no set yet known to contain {a}");
    }

    /// <summary>A constant applied to arguments, ( ( lean.c ` U ) ` a1 ) …, as the constant and the arguments.</summary>
    private (Name, List<string>)? ConstApp(string x)
    {
        var args = new List<string>();
        SyntaxTree? n = pr.Parse("class", x.Split(' '));
        while (n is { Rule.Label: "cfv" })
        {
            string fn = pr.Render(n.Children[1]), a = pr.Render(n.Children[0]);
            if (a == "U" && _tokenNames.TryGetValue(fn, out Name? name))
            {
                args.Reverse();
                return (name, args);
            }
            args.Add(a);
            n = n.Children[1];
        }
        return null;
    }

    /// <summary>( d.Ph -> X e. 2o ) for a proposition of the model, if ( φ , 1o , (/) ), or one assumed.</summary>
    private Proof PropIn2o(PCtx d, string x)
    {
        if (TryHyp(d, $"{x} e. 2o") is Proof direct)
        {
            return direct;
        }
        SyntaxTree n = pr.Parse("class", x.Split(' '))!;
        if (n.Rule.Label == "cif" && pr.Render(n.Children[1]) == "1o" && pr.Render(n.Children[2]) == "(/)")
        {
            Proof df = pr.Apply("df2o3", S());
            Proof one = pr.Apply("eleqtrri", S(("A", "1o"), ("B", "{ (/) , 1o }"), ("C", "2o")), pr.Apply("prid2", S(("A", "(/)"), ("B", "1o")), pr.Apply("1oex", S())), df);
            Proof zero = pr.Apply("eleqtrri", S(("A", "(/)"), ("B", "{ (/) , 1o }"), ("C", "2o")), pr.Apply("prid1", S(("A", "(/)"), ("B", "1o")), pr.Apply("0ex", S())), df);
            return _d.Lift(d.Ph, pr.Apply("ifcli", S(("ph", pr.Render(n.Children[0])), ("A", "1o"), ("B", "(/)"), ("C", "2o")), one, zero));
        }
        if (x == "(/)")
        {
            Proof df = pr.Apply("df2o3", S());
            return _d.Lift(d.Ph, pr.Apply("eleqtrri", S(("A", "(/)"), ("B", "{ (/) , 1o }"), ("C", "2o")), pr.Apply("prid1", S(("A", "(/)"), ("B", "1o")), pr.Apply("0ex", S())), df));
        }
        if (ConstApp(x) is (Name head, List<string> cargs))
        {
            // A proposition former applied (Bool.Reflects b p): through its typing lemma, argument by argument.
            return ConstAppMem(d, head, cargs, "2o");
        }
        throw new Refused($"no proof yet that {x} is a proposition");
    }

    /// <summary>The value of a Nat literal's text, ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` N ) ) with N a decimal, or null.</summary>
    private static System.Numerics.BigInteger? LitOfText(string x)
    {
        const string pre = "( lean.Nat.-lit ` ( lean.Nat.-ofnum ` ", post = " ) )";
        if (!x.StartsWith(pre, StringComparison.Ordinal) || !x.EndsWith(post, StringComparison.Ordinal))
        {
            return null;
        }
        // Decimal's inverse: a digit, or ; D d.
        var toks = x[pre.Length..^post.Length].Split(' ');
        int i = 0;
        System.Numerics.BigInteger? Num()
        {
            if (i >= toks.Length)
            {
                return null;
            }
            string tok = toks[i++];
            if (tok.Length == 1 && char.IsAsciiDigit(tok[0]))
            {
                return tok[0] - '0';
            }
            if (tok != ";" || Num() is not System.Numerics.BigInteger hi || i >= toks.Length || toks[i].Length != 1 || !char.IsAsciiDigit(toks[i][0]))
            {
                return null;
            }
            return hi * 10 + (toks[i++][0] - '0');
        }
        return Num() is System.Numerics.BigInteger v && i == toks.Length ? v : null;
    }

    /// <summary>( d.Ph -> x e. dom ) by the texts alone: a level of the tower, or a map into one (fmpt, mptelixpg).</summary>
    private Proof TextMem(PCtx d, string x, string dom)
    {
        SyntaxTree dn = pr.Parse("class", dom.Split(' '))!;
        SyntaxTree xn = pr.Parse("class", x.Split(' '))!;
        if (BetaHead(d, dom) is (Proof whole, string reduced))
        {
            // The expected type is a map applied to an argument (a constant motive at its index): reduce it first.
            return pr.Apply("eleqtrrd", S(("ph", d.Ph), ("A", x), ("B", reduced), ("C", dom)), TextMem(d, x, reduced), whole);
        }
        if (xn.Rule.Label != "cmpt" || dn.Rule.Label is not ("co" or "cixp"))
        {
            bool level = dom == "2o" || dn.Rule.Label == "cfv" && pr.Render(dn.Children[1]) == "U" && OrdinalIndex(pr.Render(dn.Children[0])) >= 0;
            if (!level && LitOfText(x) is System.Numerics.BigInteger lv)
            {
                // A Nat literal, ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` N ) ), as an argument (OfNat.ofNat Nat 2 _):
                // in Nat by its constructor form, as the literal itself is.
                Typed lm = LitMem(d, (NatLit)t.Nat(lv));
                return lm.Ty == dom ? lm.P : pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", x), ("B", lm.Ty), ("C", dom)), lm.P, AlphaIn(d.Ph, lm.Ty, dom));
            }
            if (!level && xn.Rule.Label == "cfv" && FnType(d, pr.Render(xn.Children[1])) is (Proof pf, string tyf))
            {
                // A function variable's value (z e. ( ( lean.Nat ` U ) ^m D ), applied), by its own hypothesis.
                string fv = pr.Render(xn.Children[1]), arg = pr.Render(xn.Children[0]);
                SyntaxTree tyn = pr.Parse("class", tyf.Split(' '))!;
                string fdom = pr.Render(tyn.Children[1]);
                Proof? aIn = TryHyp(d, $"{arg} e. {fdom}") ?? HypAlpha(d, arg, fdom);
                if (aIn is Proof ai)
                {
                    (Proof cur, string ty) = ApplyText(d.Ph, pf, fv, tyf, arg, ai);
                    if (ty == dom)
                    {
                        return cur;
                    }
                    try
                    {
                        return pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", x), ("B", ty), ("C", dom)), cur, AlphaIn(d.Ph, ty, dom));
                    }
                    catch (Refused)
                    {
                    }
                }
            }
            if (!level && ConstApp(x) is (Name head, List<string> cargs))
            {
                // Not a type in a universe but a term of an ordinary type (an instance, instLTNat : LT Nat): typed
                // through its constant's typing lemma, argument by argument.
                return ConstAppMem(d, head, cargs, dom);
            }
            // A variable of an ordinary type (o e. ( lean.Nat ` U )): by its own hypothesis, as it stands, up to bound
            // names, or once the hypothesis's type is reduced.
            if (!level && (TryHyp(d, $"{x} e. {dom}") ?? HypAlpha(d, x, dom) ?? HypBeta(d, x, dom)) is Proof hb)
            {
                return hb;
            }
            return UnivMem(d, x, dom);
        }
        string v = pr.Render(xn.Children[0]), vd = pr.Render(xn.Children[1]), body = pr.Render(xn.Children[2]);
        if (d.Ph.Split(' ').Contains(v) || dom.Split(' ').Contains(v))
        {
            string y = FreshFor(d.Ph, x, dom);
            string x2 = $"( {y} e. {vd} |-> {SubstFree(body, v, y)} )";
            return pr.Apply("eqeltrd", S(("ph", d.Ph), ("A", x), ("B", x2), ("C", dom)), AlphaIn(d.Ph, x, x2), TextMem(d, x2, dom));
        }
        bool dep = dn.Rule.Label == "cixp";
        string ddom = pr.Render(dn.Children[1]);
        string cod = dep ? SubstFree(pr.Render(dn.Children[2]), pr.Render(dn.Children[0]), v) : pr.Render(dn.Children[0]);
        if (ddom != vd && BetaHead(d, ddom) is (Proof deq, string dred))
        {
            // The expected domain is such an application, ( ( n e. Nat |-> Nat ) ` p ) for Nat: the same map is in the
            // type over the reduced domain, and the two types are equal (ixpeq1d, oveq2d).
            string dom2 = dep ? $"X_ {pr.Render(dn.Children[0])} e. {dred} {pr.Render(dn.Children[2])}" : $"( {pr.Render(dn.Children[0])} ^m {dred} )";
            Proof same = dep
                ? pr.Apply("ixpeq1d", S(("ph", d.Ph), ("x", pr.Render(dn.Children[0])), ("A", ddom), ("B", dred), ("C", pr.Render(dn.Children[2]))), deq)
                : pr.Apply("oveq2d", S(("ph", d.Ph), ("A", ddom), ("B", dred), ("C", pr.Render(dn.Children[0])), ("F", "^m")), deq);
            return pr.Apply("eleqtrrd", S(("ph", d.Ph), ("A", x), ("B", dom2), ("C", dom)), TextMem(d, x, dom2), same);
        }
        if (ddom != vd)
        {
            throw new Refused($"a map over {vd} where {ddom} is expected");
        }
        PCtx e = EnterText(d, v, vd);
        Proof q = TextMem(e, body, cod);
        Proof ral = pr.Apply("ralrimiva", S(("ph", d.Ph), ("ps", $"{body} e. {cod}"), ("x", v), ("A", vd)), q);
        if (dep)
        {
            string tyX = $"X_ {v} e. {vd} {cod}";
            Proof bi = _d.Syl(Exists(d.Ph, vd), pr.Apply("mptelixpg", S(("x", v), ("I", vd), ("J", body), ("K", cod), ("V", "_V"))));
            Proof inX = pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"{x} e. {tyX}"), ("ch", $"A. {v} e. {vd} {body} e. {cod}")), ral, bi);
            return tyX == dom ? inX : pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", x), ("B", tyX), ("C", dom)), inX, AlphaIn(d.Ph, tyX, dom));
        }
        Proof fmap = pr.Apply("fmpt", S(("x", v), ("A", vd), ("C", body), ("B", cod), ("F", x)), pr.Apply("eqid", S(("A", x))));
        Proof fn = pr.Apply("sylib", S(("ph", d.Ph), ("ps", $"A. {v} e. {vd} {body} e. {cod}"), ("ch", $"{x} : {vd} --> {cod}")), ral, fmap);
        Proof bi2 = pr.Apply("elmapd", S(("ph", d.Ph), ("A", cod), ("B", vd), ("C", x), ("V", "_V"), ("W", "_V")), Exists(d.Ph, cod), Exists(d.Ph, vd));
        return pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"{x} e. {dom}"), ("ch", $"{x} : {vd} --> {cod}")), fn, bi2);
    }

    /// <summary>
    /// ( d.Ph -> t = t' ) for t a map applied to an argument, ( ( w e. D |-> B ) ` a ), with a shown in D: t' is B at a.
    /// Lean's kernel reduces such a type silently (a recursor's motive at its index); the model's texts keep it until
    /// someone asks. Null when t isn't one, or the argument can't be shown in the map's domain.
    /// </summary>
    private (Proof Eq, string To)? BetaHead(PCtx d, string t)
    {
        SyntaxTree n = pr.Parse("class", t.Split(' '))!;
        if (n.Rule.Label != "cfv" || n.Children[1].Rule.Label != "cmpt")
        {
            return null;
        }
        SyntaxTree fn = n.Children[1];
        string w = pr.Render(fn.Children[0]), wd = pr.Render(fn.Children[1]), body = pr.Render(fn.Children[2]);
        string arg = pr.Render(n.Children[0]), f = pr.Render(fn);
        Proof? argIn = TryHyp(d, $"{arg} e. {wd}") ?? HypAlpha(d, arg, wd);
        if (argIn is null)
        {
            try
            {
                argIn = TextMem(d, arg, wd);
            }
            catch (Refused e)
            {
                if (System.Environment.GetEnvironmentVariable("TENET_DEBUG") is not null) Console.Error.WriteLine($"[debug] BetaHead: {arg} not in {wd}: {e.Message}");
                return null;
            }
        }
        Proof eq = BetaShadowed(d.Ph, pr.Apply("eqid", S(("A", f))), w, wd, body, arg, argIn.Value, f);
        return (eq, Rhs(eq));
    }

    /// <summary>( d.Ph -> a e. dom ) from a fact a e. T whose type is a map applied to an argument that reduces to dom.</summary>
    private Proof? HypBeta(PCtx d, string a, string dom)
    {
        foreach ((Proof p, string h) in Facts(d))
        {
            if (!h.StartsWith(a + " e. ( ( ", StringComparison.Ordinal))
            {
                continue;
            }
            string have = h[(a.Length + 4)..];
            if (BetaHead(d, have) is not (Proof eq, string to))
            {
                continue;
            }
            Proof red = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", a), ("B", have), ("C", to)), p, eq);
            if (to == dom)
            {
                return red;
            }
            try
            {
                return pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", a), ("B", to), ("C", dom)), red, AlphaIn(d.Ph, to, dom));
            }
            catch (Refused)
            {
            }
        }
        return null;
    }

    /// <summary>( d.Ph -> a e. dom ) from a fact a e. D' with D' equal to dom up to bound names.</summary>
    private Proof? HypAlpha(PCtx d, string a, string dom)
    {
        foreach ((Proof p, string h) in Facts(d))
        {
            if (!h.StartsWith(a + " e. ", StringComparison.Ordinal))
            {
                continue;
            }
            string have = h[(a.Length + 4)..];
            try
            {
                return pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", a), ("B", have), ("C", dom)), p, AlphaIn(d.Ph, have, dom));
            }
            catch (Refused)
            {
            }
        }
        return null;
    }

    private Proof? TryHyp(PCtx d, string h)
    {
        try
        {
            return HypIn(d, h);
        }
        catch (Refused)
        {
            return null;
        }
    }

    /// <summary>Every fact the context has: its conjuncts and its locals' memberships.</summary>
    /// <summary>
    /// ( d.Ph -> f e. T ) with T a map type (X_ or ^m), for a function variable with such a hypothesis or an application
    /// chain of one (each argument in its domain); null otherwise.
    /// </summary>
    private (Proof P, string Ty)? FnType(PCtx d, string f)
    {
        foreach ((Proof p, string h) in Facts(d))
        {
            if (h.StartsWith($"{f} e. ", StringComparison.Ordinal)
                && pr.Parse("class", h[(f.Length + 4)..].Split(' ')) is { } tn
                && (tn.Rule.Label == "cixp" || tn.Rule.Label == "co" && pr.Render(tn.Children[2]) == "^m"))
            {
                return (p, h[(f.Length + 4)..]);
            }
        }
        SyntaxTree? n = pr.Parse("class", f.Split(' '));
        if (n is not { Rule.Label: "cfv" })
        {
            return null;
        }
        string g = pr.Render(n.Children[1]), a = pr.Render(n.Children[0]);
        if (FnType(d, g) is not (Proof pg, string tyg))
        {
            return null;
        }
        SyntaxTree tg = pr.Parse("class", tyg.Split(' '))!;
        string dom = pr.Render(tg.Children[1]);
        Proof? aIn = TryHyp(d, $"{a} e. {dom}") ?? HypAlpha(d, a, dom);
        if (aIn is null)
        {
            try
            {
                aIn = TextMem(d, a, dom);
            }
            catch (Refused)
            {
                return null;
            }
        }
        (Proof cur, string ty) = ApplyText(d.Ph, pg, g, tyg, a, aIn.Value);
        SyntaxTree tn2 = pr.Parse("class", ty.Split(' '))!;
        return tn2.Rule.Label == "cixp" || tn2.Rule.Label == "co" && pr.Render(tn2.Children[2]) == "^m" ? (cur, ty) : null;
    }

    private IEnumerable<(Proof, string)> Facts(PCtx d)
    {
        foreach (string h in Conjuncts(d.Ph))
        {
            yield return (Hyp(d.Ph, h)!.Value, h);
        }
        foreach (var m in d.Mems.Values)
        {
            yield return (m.P, _d.Split(m.P.Proves).X);
        }
    }

    /// <summary>The context extended by a set variable bound by a class term (not a Lean local), with hypothesis x e. dom.</summary>
    private PCtx EnterText(PCtx c, string x, string dom)
    {
        var d = c.Clone();
        string hyp = $"{x} e. {dom}";
        d.Ph = $"( {c.Ph} /\\ {hyp} )";
        foreach (var kv in c.Mems)
        {
            d.Mems[kv.Key] = (Weaken(kv.Value.P, hyp), kv.Value.Ty);
        }
        d.Binders.Add(x);
        return d;
    }

    /// <summary>
    /// ( d.Ph -> ( rec ( F , (/) ) ` k ) e. G ), where d.Ph = ( ta /\ k e. _om ): finds2 over k. The empty stage is
    /// (/) (rdg0); the next stage is F at the last one (rdgsuc), which unfolds to the last stage with the
    /// constructors' tuples over it, a member of G by closure, given the last stage is.
    /// </summary>
    private Proof StageIn(PCtx d, string x, SyntaxTree rdg, string kv, string g)
    {
        string f = pr.Render(rdg.Children[0]), init = pr.Render(rdg.Children[1]);
        if (init != "(/)")
        {
            throw new Refused($"a recursion from {init}, not (/)");
        }
        SyntaxTree ph = pr.Parse("wff", d.Ph.Split(' '))!;
        if (ph.Rule.Label != "wa" || pr.Render(ph.Children[1]) != $"{kv} e. _om")
        {
            throw new Refused($"a stage at {kv} outside a union over _om");
        }
        string ta = pr.Render(ph.Children[0]);
        string y = FreshFor(d.Ph, x, g, f);
        string Phi(string at) => $"( rec ( {f} , (/) ) ` {at} ) e. {g}";
        Proof Sub(string to) => _d.Congruence("wff", Phi("Z"), "Z", pr.Apply("id", S(("ph", $"{kv} = {to}"))));
        // The base: ( rec ( F , (/) ) ` (/) ) = (/), a member of G.
        PCtx baseCtx = d.Clone();
        baseCtx.Ph = ta;
        foreach (var key in baseCtx.Mems.Keys.ToList())
        {
            baseCtx.Mems.Remove(key);
        }
        Proof r0 = _d.Lift(ta, pr.Apply("rdg0", S(("F", f), ("A", "(/)")), pr.Apply("0ex", S())));
        Proof baseP = pr.Apply("eqeltrd", S(("ph", ta), ("A", $"( rec ( {f} , (/) ) ` (/) )"), ("B", "(/)"), ("C", g)), r0, UnivMem(baseCtx, "(/)", g));
        // The step, under ( ( ta /\ y e. _om ) /\ stage y e. G ).
        string stageY = $"( rec ( {f} , (/) ) ` {y} )";
        var stepCtx = new PCtx { Ph = $"( ( {ta} /\\ {y} e. _om ) /\\ {stageY} e. {g} )" };
        Proof yOm = Hyp(stepCtx.Ph, $"{y} e. _om")!.Value;
        Proof suc = _d.Syl(_d.Syl(yOm, pr.Apply("nnon", S(("A", y)))), pr.Apply("rdgsuc", S(("B", y), ("F", f), ("A", "(/)"))));
        Proof app = ApplyStep(stepCtx.Ph, f, stageY);
        Proof eq = _d.Trans(suc, app);
        Proof stepIn = pr.Apply("eqeltrd", S(("ph", stepCtx.Ph), ("A", $"( rec ( {f} , (/) ) ` suc {y} )"), ("B", Rhs(eq)), ("C", g)), eq, UnivMem(stepCtx, Rhs(eq), g));
        Proof ex1 = pr.Apply("ex", S(("ph", $"( {ta} /\\ {y} e. _om )"), ("ps", Phi(y)), ("ch", Phi($"suc {y}"))), stepIn);
        Proof ex2 = pr.Apply("ex", S(("ph", ta), ("ps", $"{y} e. _om"), ("ch", $"( {Phi(y)} -> {Phi($"suc {y}")} )")), ex1);
        Proof stepP = pr.Apply("com12", S(("ph", ta), ("ps", $"{y} e. _om"), ("ch", $"( {Phi(y)} -> {Phi($"suc {y}")} )")), ex2);
        Proof all = pr.Apply("finds2", S(("x", kv), ("y", y), ("ph", Phi(kv)), ("ps", Phi("(/)")), ("ch", Phi(y)), ("th", Phi($"suc {y}")), ("ta", ta)),
            Sub("(/)"), Sub(y), Sub($"suc {y}"), baseP, stepP);
        return pr.Apply("impcom", S(("ph", $"{kv} e. _om"), ("ps", ta), ("ch", Phi(kv))), all);
    }

    /// <summary>( ph -> ( F ` S ) = S' ), F a stage function ( X e. _V |-> ( step ` <. P , X >. ) ), S' the unfolded step.</summary>
    private Proof ApplyStep(string ph, string f, string s)
    {
        SyntaxTree m = pr.Parse("class", f.Split(' '))!;
        if (m.Rule.Label != "cmpt")
        {
            throw new Refused($"a stage function that isn't a map: {f}");
        }
        string x = pr.Render(m.Children[0]), body = pr.Render(m.Children[2]);
        Proof e1 = Beta(ph, pr.Apply("eqid", S(("A", f))), x, "_V", body, s, Exists(ph, s), f);
        string arg = Rhs(e1);   // ( step ` <. P , S >. )
        SyntaxTree a = pr.Parse("class", arg.Split(' '))!;
        string tok = pr.Render(a.Children[1]), packed = pr.Render(a.Children[0]);
        Proof e2 = _d.Trans(e1, UnfoldRaw(ph, tok, packed));
        return Simp(ph, Rhs(e2)) is Proof sp ? _d.Trans(e2, sp) : e2;
    }
}
