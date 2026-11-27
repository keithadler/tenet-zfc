using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The typing of the quotient's constants for the theorem translator (docs/milestone3.md, "Quotients and choice in the
/// tower"): Quot, Quot.mk and Quot.lift by lemmas on their values (<see cref="QuotInLemma"/>), and Quot.ind, a proof,
/// by showing that its statement holds in the model.
/// </summary>
public sealed partial class Model
{
    /// <summary>
    /// ( d.Ph -> (/) e. ⟦body⟧ ) for a quotient constant that is a proof, under its binders (IntroPiProp):
    /// - Quot.ind: β q, from ∀ a, β (Quot.mk r a). q is a class [ z ] R of some z in α (elqsi), and Quot.mk r z
    ///   unfolds to [ z ] R, so the hypothesis at z gives β q. For a quotient of a proposition, q and Quot.mk r a are
    ///   proofs, (/), and the hypothesis at (/) gives it.
    /// - Quot.lift into a proposition β: f at a representative of q gives β.
    /// - Quot.mk of a proposition: Quot r is α, which holds since a proves it.
    /// </summary>
    private Proof QuotProofHolds(PCtx d, Expr body, string which)
    {
        string ph = d.Ph;
        if (which == "Quot.mk")
        {
            // body is Quot r (at α a proposition): ⟦Quot r⟧ unfolds to α, and (/) e. α is a's hypothesis.
            Expr qhead = Ops.Spine(body, out List<Expr> qa);
            string qty0 = TrIn(d, body);
            (Proof eq0, string x0, _) = QuotUnfold(d, qty0);
            Proof aIn = HypIn(d, $"(/) e. {x0}");
            _ = qhead;
            _ = qa;
            return pr.Apply("eleqtrrd", S(("ph", ph), ("A", "(/)"), ("B", x0), ("C", qty0)), aIn, eq0);
        }
        // The q the conclusion is about: the last binder, of type Quot r.
        FVar qf = d.Mems.Keys.Select(k => (Id: k, Ty: d.Types.TryGetValue(k, out Expr? t0) ? t0 : null))
            .Where(kv => kv.Ty is not null && Ops.Spine(kv.Ty, out _) is Const { } qc && BaseName(qc.Name) == "Quot")
            .Select(kv => (FVar)t.FVar(kv.Id)).LastOrDefault() ?? throw new Refused($"{which}: no q : Quot r in the context");
        var qm = d.Mems[qf.Id];
        string q = d.Vars[qf.Id], qty = qm.Ty;
        (Proof eqQ, string x, string qs) = QuotUnfold(d, qty);
        Proof qInQs = pr.Apply("eleqtrd", S(("ph", ph), ("A", q), ("B", qty), ("C", qs)), qm.P, eqQ);
        string goal = $"(/) e. {TrIn(d, body)}";
        string goalHead = which == "Quot.ind" ? Kid("class", goal[7..], "F") : "";

        // The hypothesis to use: for Quot.ind ∀ a, β (Quot.mk r a); for Quot.lift f : α → β.
        Proof hypP = d.Mems.Values.Select(m => m.P).LastOrDefault(p =>
        {
            string s0 = _d.Split(p.Proves).X;
            if (!s0.StartsWith("(/) e. if ( A. ", StringComparison.Ordinal))
            {
                return false;
            }
            string all = Kid("class", Kid("wff", s0, "B"), "ph");
            if (Kid("wff", all, "A") != x)
            {
                return false;
            }
            // Quot.lift: f : α → β, whose body is the conclusion; Quot.ind: ∀ a, β (Quot.mk r a), about β.
            string inner = Kid("wff", all, "ph");
            return which == "Quot.lift" ? inner == goal : inner.StartsWith($"(/) e. ( {goalHead} ` ", StringComparison.Ordinal);
        }) is { Proof: not null } found ? found : throw new Refused($"{which}'s hypothesis isn't in the context");
        string ite = Kid("wff", _d.Split(hypP.Proves).X, "B");

        if (qs == x)
        {
            // A quotient of a proposition: q is (/), and so is Quot.mk r a.
            Proof r0 = PropAt(ph, ite, "(/)", hypP, "(/)", qInQs, []);
            return Close(d, r0, goal);
        }
        string rel = Kid("class", qs, "R");
        string z = FreshFor(ph, qty, qs, ite, goal, q);
        string zx = $"{z} e. {x}", eqz = $"{q} = [ {z} ] {rel}";
        Proof ex = _d.Syl(qInQs, pr.Apply("elqsi", S(("x", z), ("A", x), ("B", q), ("R", rel))));
        string ctx1 = $"( {ph} /\\ {zx} )", ctx2 = $"( {ctx1} /\\ {eqz} )";
        Proof Up(Proof p) => _d.Syl(pr.Apply("simpll", S(("ph", ph), ("ps", zx), ("ch", eqz))), p);
        Proof zIn = pr.Apply("simplr", S(("ph", ph), ("ps", zx), ("ch", eqz)));
        Proof atZ = PropAt(ctx2, ite, "(/)", Up(hypP), z, zIn, [z]);
        Proof atQ;
        if (which == "Quot.lift")
        {
            atQ = atZ;   // β doesn't depend on q
        }
        else
        {
            // β at Quot.mk r z, which unfolds to [ z ] R, that is q.
            string bmk = Kid("wff", _d.Split(atZ.Proves).X, "B"), mkz = Kid("class", bmk, "A"), b = Kid("class", bmk, "F");
            string mktok = Kid("class", Kid("class", Kid("class", Kid("class", mkz, "F"), "F"), "F"), "F");
            string y = Kid("class", Kid("class", mkz, "F"), "A");
            (Proof eqMk, _, _) = Unfold(ctx2, mktok, [x, y, z], (i, dom) => i == 2 ? zIn : Up(HypIn(d, $"{(i == 0 ? x : y)} e. {dom}")));
            if (Rhs(eqMk) != $"[ {z} ] {rel}")
            {
                throw new Refused($"Quot.mk unfolds to {Rhs(eqMk)}, not [ {z} ] {rel}");
            }
            Proof mkIsQ = pr.Apply("eqtr4d", S(("ph", ctx2), ("A", mkz), ("B", $"[ {z} ] {rel}"), ("C", q)), eqMk,
                pr.Apply("simpr", S(("ph", ctx1), ("ps", eqz))));
            Proof fv = pr.Apply("fveq2d", S(("ph", ctx2), ("A", mkz), ("B", q), ("F", b)), mkIsQ);
            atQ = pr.Apply("eleqtrd", S(("ph", ctx2), ("A", "(/)"), ("B", bmk), ("C", $"( {b} ` {q} )")), atZ, fv);
        }
        string got = _d.Split(atQ.Proves).X;
        Proof imp = pr.Apply("ex", S(("ph", ctx1), ("ps", eqz), ("ch", got)), atQ);
        Proof rex = pr.Apply("rexlimdva", S(("ph", ph), ("x", z), ("A", x), ("ps", eqz), ("ch", got)), imp);
        return Close(d, pr.Apply("mpd", S(("ph", ph), ("ps", $"E. {z} e. {x} {eqz}"), ("ch", got)), ex, rex), goal);
    }

    /// <summary>
    /// ( d.Ph -> (/) e. ⟦Eq (Quot r) (Quot.mk r a) (Quot.mk r b)⟧ ) under Quot.sound's binders (IntroPiProp), from its
    /// hypothesis r a b: Eq unfolds to if ( Y = X , 1o , (/) ), and the two classes are equal (lean-sound-k). At level
    /// 0, where α is a proposition, both sides are proofs, (/), and equal outright.
    /// </summary>
    private Proof QuotSoundHolds(PCtx d, Expr body)
    {
        string goalTy = TrIn(d, body);
        if (Ops.Spine(_typing.Whnf(body), out List<Expr> ea) is not Const eqc || ea.Count != 3)
        {
            throw new Refused($"Quot.sound's statement isn't an equation: {goalTy}");
        }
        var texts = ea.Select(e => TrIn(d, e)).ToList();
        (Proof eqEq, _, _) = Unfold(d.Ph, Token(eqc.Name)!, texts, (i, dom) => Check(d, ea[i], InferIn(d, ea[i]), dom));
        string ite = Rhs(eqEq);
        SyntaxTree n = pr.Parse("class", ite.Split(' '))!;
        if (n.Rule.Label != "cif")
        {
            throw new Refused($"{eqc.Name} doesn't unfold to a proposition: {ite}");
        }
        string phi = pr.Render(n.Children[0]);
        string x = texts[1], y = texts[2];
        Proof xy = x == y ? _d.Refl(d.Ph, x) : QuotMkEq(d, ea[1], ea[2]);
        Proof phiP = phi == $"{x} = {y}" ? xy : phi == $"{y} = {x}" ? _d.Symm(xy) : throw new Refused($"{eqc.Name}'s condition is {phi}");
        EnsureTowerLemmas();
        Proof inIf = _d.Syl(phiP, Bi2(ApplyId("lean-prop", S(("ph", phi)))));
        Proof r = pr.Apply("eleqtrrd", S(("ph", d.Ph), ("A", "(/)"), ("B", ite), ("C", Lhs(eqEq))), inIf, eqEq);
        return Lhs(eqEq) == goalTy ? r : pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", Lhs(eqEq)), ("C", goalTy)), r, AlphaIn(d.Ph, Lhs(eqEq), goalTy));
    }

    /// <summary>( d.Ph -> Quot.mk r a = Quot.mk r b ), by lean-sound-k at a, b and the hypothesis r a b.</summary>
    private Proof QuotMkEq(PCtx d, Expr ma, Expr mb)
    {
        if (Ops.Spine(ma, out List<Expr> aa) is not Const mk || BaseName(mk.Name) != "Quot.mk" || aa.Count != 3
            || Ops.Spine(mb, out List<Expr> ba) is not Const mk2 || mk2.Name != mk.Name || ba.Count != 3)
        {
            throw new Refused("Quot.sound's sides aren't Quot.mk");
        }
        string label = QuotSoundLemma(mk.Name);
        List<Expr> doms = PiDomains(env.Find(mk.Name)!.Type, aa);
        var args = new List<(string, Expr, Expr)> { ("A", aa[0], doms[0]), ("B", aa[1], doms[1]), ("C", aa[2], doms[2]), ("D", ba[2], doms[2]) };
        return InstLemma(d, label, args);
    }

    /// <summary>
    /// lean-sound-k: |- ( ( ( ( ( ( U e. lean.-tower /\ A e. D0 ) /\ B e. D1 ) /\ C e. A ) /\ D e. A ) /\ (/) e. ( ( B ` C ) ` D ) )
    /// -> ( ( ( ( lean.Quot.mk.{k} ` U ) ` A ) ` B ) ` C ) = ( … ` D ) ). The pairs r relates are in the quotient's
    /// relation R, which contains them by definition (opabssxp, ssintrab), so C R D, and R being an equivalence
    /// relation (riiner, as for the computation rule) their classes are equal (erth).
    /// </summary>
    private string QuotSoundLemma(Name mkN)
    {
        string label = $"lean-sound-{LabelPart($"{mkN}")}";
        if (Has(label))
        {
            return label;
        }
        Define(mkN);
        string mk = Token(mkN)!;
        List<string> md = Domains(mk, ["A", "B", "C"], 3);
        if (md[2] != "A")
        {
            throw new Refused($"{mkN}'s third argument ranges over {md[2]}, not A");
        }
        string ph = Conj([UHyp, $"A e. {md[0]}", $"B e. {md[1]}", "C e. A", "D e. A", "(/) e. ( ( B ` C ) ` D )"]);
        Proof H(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");
        (Proof eqC, _, _) = Unfold(ph, mk, ["A", "B", "C"], (i, dom) => H(ph, $"{"ABC"[i]} e. {dom}"));
        (Proof eqD, _, _) = Unfold(ph, mk, ["A", "B", "D"], (i, dom) => H(ph, $"{"ABD"[i]} e. {dom}"));
        string rel = $"( ( ( {QuotEqv} ` U ) ` A ) ` B )";
        if (Rhs(eqC) != $"[ C ] {rel}")
        {
            throw new Refused($"{mkN} unfolds to {Rhs(eqC)}, not [ C ] {rel}");
        }
        var (eqE, ebody, sq, sx, pw, Phi, _, r0, _, erR) = Eqv(ph, md[0], "C D", H);
        // r0 C_ R: r0 C_ ( A X. A ) (opabssxp), and r0 is inside every relation intersected (ssintrab).
        string sv = Kid("class", sx, "x"), phi = Kid("class", sx, "ph");
        Proof inSq = pr.Apply("opabssxp", S(("x", Kid("class", r0, "x")), ("y", Kid("class", r0, "y")), ("A", "A"), ("B", "A"),
            ("ph", Kid("wff", Kid("class", r0, "ph"), "ps"))));
        Proof each = pr.Apply("rgen", S(("x", sv), ("A", pw), ("ph", $"( {phi} -> {r0} C_ {sv} )")),
            pr.Apply("simpl", S(("ph", $"{r0} C_ {sv}"), ("ps", $"{sv} Er A"))));
        Proof inInt = pr.Apply("mpbir", S(("ph", $"{r0} C_ |^| {sx}"), ("ps", $"A. {sv} e. {pw} ( {phi} -> {r0} C_ {sv} )")), each,
            pr.Apply("ssintrab", S(("A", r0), ("x", sv), ("B", pw), ("ph", phi))));
        Proof inE = pr.Apply("mpbi", S(("ph", $"( {r0} C_ {sq} /\\ {r0} C_ |^| {sx} )"), ("ps", $"{r0} C_ {ebody}")),
            pr.Apply("pm3.2i", S(("ph", $"{r0} C_ {sq}"), ("ps", $"{r0} C_ |^| {sx}")), inSq, inInt),
            pr.Apply("ssin", S(("A", r0), ("B", sq), ("C", $"|^| {sx}"))));
        Proof inR = pr.Apply("sseqtrrd", S(("ph", ph), ("A", r0), ("B", ebody), ("C", rel)), _d.Lift(ph, inE), eqE);
        // C r0 D, from C e. A, D e. A and the hypothesis (opelopabg, df-br).
        string b = Kid("class", r0, "x"), c = Kid("class", r0, "y"), body = Kid("class", r0, "ph");
        string mid = Subst(body, b, "C");
        Proof s1 = _d.Congruence("wff", Subst(body, b, "Z"), "Z", pr.Apply("id", S(("ph", $"{b} = C"))));
        Proof s2 = _d.Congruence("wff", Subst(mid, c, "Z"), "Z", pr.Apply("id", S(("ph", $"{c} = D"))));
        string fin = Subst(mid, c, "D");
        Proof ope = pr.Apply("opelopabg", S(("x", b), ("y", c), ("A", "C"), ("B", "D"), ("V", "A"), ("W", "A"), ("ph", body), ("ps", mid), ("ch", fin)),
            s1, s2);
        Proof cd = _d.Jca(H(ph, "C e. A"), H(ph, "D e. A"));
        Proof inR0 = pr.Apply("mpbird", S(("ph", ph), ("ps", $"<. C , D >. e. {r0}"), ("ch", fin)),
            _d.Jca(cd, H(ph, "(/) e. ( ( B ` C ) ` D )")), _d.Syl(cd, ope));
        Proof br0 = pr.Apply("sylibr", S(("ph", ph), ("ps", $"<. C , D >. e. {r0}"), ("ch", $"C {r0} D")), inR0, pr.Apply("df-br", S(("A", "C"), ("R", r0), ("B", "D"))));
        Proof brR = pr.Apply("mpd", S(("ph", ph), ("ps", $"C {r0} D"), ("ch", $"C {rel} D")), br0,
            pr.Apply("ssbrd", S(("ph", ph), ("A", r0), ("B", rel), ("C", "C"), ("D", "D")), inR));
        Proof cls = pr.Apply("mpbid", S(("ph", ph), ("ps", $"C {rel} D"), ("ch", $"[ C ] {rel} = [ D ] {rel}")), brR,
            pr.Apply("erth", S(("ph", ph), ("R", rel), ("X", "A"), ("A", "C"), ("B", "D")), erR, H(ph, "C e. A")));
        Proof r = _d.Trans(_d.Trans(eqC, cls), _d.Symm(eqD));
        EmitLemma(label, $"Quot.sound in the model: {mkN} r a = {mkN} r b when r a b.", r);
        return label;
    }

    /// <summary>The proof, if it proves the goal; else refused.</summary>
    private Proof Close(PCtx d, Proof p, string goal) =>
        _d.Split(p.Proves).X == goal ? p : throw new Refused($"the quotient's typing came out as {_d.Split(p.Proves).X}, not {goal}");

    /// <summary>
    /// For Q = ( ( ( lean.Quot.{k} ` U ) ` x ) ` y ): ( d.Ph -> Q = qs ), with x, and qs = ( x /. R ) (or x itself, at
    /// a proposition α).
    /// </summary>
    private (Proof Eq, string X, string Qs) QuotUnfold(PCtx d, string qty)
    {
        string qf1 = Kid("class", qty, "F");
        string x = Kid("class", qf1, "A"), y = Kid("class", qty, "A");
        string qtok = Kid("class", Kid("class", qf1, "F"), "F");
        (Proof eqQ, _, _) = Unfold(d.Ph, qtok, [x, y], (i, dom) => HypIn(d, $"{(i == 0 ? x : y)} e. {dom}"));
        return (eqQ, x, Rhs(eqQ));
    }
    /// <summary>
    /// The quotient's computation rule as a conversion step: Quot.lift f h (Quot.mk r a) ⟶ f a, by the rule proved as
    /// a lemma (lean-iota-Quot.lift.{k,l}, <see cref="QuotLiftIota(Name, Name)"/>), as a recursor at a constructor is.
    /// Null when the quotient argument isn't Quot.mk, or at level 0 (where Quot.mk or Quot.lift is a proof).
    /// </summary>
    private (Expr, Proof)? QuotIotaStep(PCtx c, Const head, List<Expr> args)
    {
        (Expr maj, Proof pm) = WhnfFull(c, args[5]);
        if (Ops.Spine(maj, out List<Expr> margs) is not Const mk || BaseName(mk.Name) != "Quot.mk" || margs.Count != 3)
        {
            return null;
        }
        string label = $"lean-iota-{LabelPart($"{head.Name}")}";
        if (!Has(label))
        {
            try
            {
                var (stmt, proof, _) = QuotLiftIota(head.Name, mk.Name);
                EmitLemma(label, $"The computation rule of the quotient: {head.Name} f h ({mk.Name} r a) = f a.", (proof, stmt));
            }
            catch (Refused) when (_values.TryGetValue(Token(head.Name)!, out string? lv) && lv == "(/)" || _values.TryGetValue(Token(mk.Name)!, out string? mv) && mv == "(/)")
            {
                return null;
            }
        }
        Proof e1 = ArgCong(c, head, args, 5, pm);
        ConstInfo lci = env.Find(head.Name)!, mci = env.Find(mk.Name)!;
        List<Expr> ldoms = PiDomains(lci.Type, args.Take(5).ToList());
        List<Expr> mdoms = PiDomains(mci.Type, margs);
        var largs = new List<(string, Expr, Expr)>();
        for (int i = 0; i < 5; i++)
        {
            largs.Add((ClassVars[i], args[i], ldoms[i]));
        }
        largs.Add((ClassVars[5], margs[2], mdoms[2]));
        Proof iota = InstLemma(c, label, largs);
        Proof e2 = AppCong(c, iota, args.Skip(6));
        Proof joined = _d.Trans(_d.Trans(e1, AlphaIn(c.Ph, Rhs(e1), Lhs(e2))), e2);
        Expr reduct = t.MkApp(t.App(args[3], margs[2]), args.Skip(6));
        return (reduct, Reconcile(c, joined, reduct));
    }
}
