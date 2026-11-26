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
        if (g == "2o")
        {
            return PropIn2o(d, x);
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
            case "ciun":
                {
                    string v = C(0), dom = C(1), body = C(2);
                    if (d.Ph.Split(' ').Contains(v))
                    {
                        throw new Refused($"the union's variable {v} occurs in the hypotheses");
                    }
                    Proof domIn = UnivMem(d, dom, g);
                    PCtx e = EnterText(d, v, dom);
                    Proof bodyIn = UnivMem(e, body, g);
                    Proof all = pr.Apply("ralrimiva", S(("ph", d.Ph), ("ps", $"{body} e. {g}"), ("x", v), ("A", dom)), bodyIn);
                    return _d.Syl(pr.Apply("3jca", S(("ph", d.Ph), ("ps", $"{g} e. Univ"), ("ch", $"{dom} e. {g}"), ("th", $"A. {v} e. {dom} {body} e. {g}")), Univ(), domIn, all),
                        pr.Apply("gruiun", S(("U", g), ("x", v), ("A", dom), ("B", body))));
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
        throw new Refused($"no proof yet that {x} is a proposition");
    }

    /// <summary>( d.Ph -> x e. dom ) by the texts alone: a level of the tower, or a map into one (fmpt, mptelixpg).</summary>
    private Proof TextMem(PCtx d, string x, string dom)
    {
        SyntaxTree dn = pr.Parse("class", dom.Split(' '))!;
        SyntaxTree xn = pr.Parse("class", x.Split(' '))!;
        if (xn.Rule.Label != "cmpt" || dn.Rule.Label is not ("co" or "cixp"))
        {
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
