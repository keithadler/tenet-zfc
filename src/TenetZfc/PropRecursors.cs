using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The type of a proposition's recursor that eliminates only into Prop (Exists.rec, And.rec and Or.rec at a
/// proposition-valued motive). Its value is a proof, (/), so its typing is a statement: under its binders, the motive
/// holds at the major premise. The major premise says the proposition holds, which unfolds to the disjunction of its
/// constructors' cases, each "there are fields"; in each case the constructor's minor premise, applied to those
/// fields, is the motive.
/// </summary>
public sealed partial class Model
{
    /// <summary>
    /// ( d.Ph -> (/) e. ⟦motive t⟧ ), in the context d of the recursor's binders (entered from c0): parameters,
    /// motive, minor premises, major premise.
    /// </summary>
    private Proof PropRecHolds(PCtx c0, PCtx d, Expr body, ConstInfo ind, ConstInfo rec) =>
        PropRecIn(c0, d, ind, rec, "(/)", TrIn(d, body));

    /// <summary>
    /// ( d.Ph -> elem e. target ) for a proposition that isn't recursive: elem is what its recursor is at the binders
    /// of d, (/) when it eliminates into Prop, and the minor premise at (/) for each field when it eliminates into
    /// any sort (And.rec, Iff.rec: all their fields are proofs).
    /// </summary>
    private Proof PropRecIn(PCtx c0, PCtx d, ConstInfo ind, ConstInfo rec, string elem, string target)
    {
        if (ind.IsRec)
        {
            throw new Refused($"no typing lemma yet for {rec.Name}: a recursive proposition's recursor into any sort");
        }
        if (ind.NumIndices > 0 || rec.NumMotives != 1)
        {
            throw new Refused($"no typing lemma yet for {rec.Name}: the recursor into Prop of an indexed proposition that isn't recursive");
        }
        // The binders IntroPiProp entered, in order: the free variables d has and c0 doesn't.
        var fvs = d.Types.Keys.Where(k => !c0.Types.ContainsKey(k)).OrderBy(k => k).ToList();
        int np = ind.NumParams, nm = rec.NumMinors;
        if (ind.Ctors.Length == 0 && fvs.Count == np + 2)
        {
            // No constructors (False): the major premise says (/) is in the empty set.
            ulong mj = fvs[^1];
            Ops.Spine(d.Types[mj], out List<Expr> fargs);
            List<Expr> fdoms = PiDomains(ind.Type, fargs);
            var ftexts = fargs.Select(a => TrIn(d, a)).ToList();
            (Proof eqF, _, _) = Unfold(d.Ph, Token(ind.Name)!, ftexts, (i, dom) => Check(d, fargs[i], fdoms[i], dom));
            if (Rhs(eqF) != "(/)")
            {
                throw new Refused($"{ind.Name} has no constructors, but its set is {Rhs(eqF)}");
            }
            Proof inEmpty = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", Lhs(eqF)), ("C", "(/)")), FixMem(d.Ph, d.Mems[mj].P, "(/)", Lhs(eqF)), eqF);
            return pr.Apply("pm2.21dd", S(("ph", d.Ph), ("ps", "(/) e. (/)"), ("ch", $"{elem} e. {target}")), inEmpty,
                _d.Lift(d.Ph, pr.Apply("noel", S(("A", "(/)")))));
        }
        if (fvs.Count != np + 1 + nm + 1 || nm != ind.Ctors.Length || nm == 0)
        {
            throw new Refused($"{rec.Name}: {fvs.Count} binders entered, {np} parameters and {nm} minor premises expected");
        }
        string goal = $"{elem} e. {target}";
        ulong major = fvs[^1];

        // The major premise: the proposition at the parameters holds, so the disjunction of its cases does.
        Ops.Spine(d.Types[major], out List<Expr> args);
        string tok = Token(ind.Name)!;
        List<Expr> doms = PiDomains(ind.Type, args);
        var texts = args.Select(a => TrIn(d, a)).ToList();
        (Proof eqT, _, _) = Unfold(d.Ph, tok, texts, (i, dom) => Check(d, args[i], doms[i], dom));
        SyntaxTree n = pr.Parse("class", Rhs(eqT).Split(' '))!;
        if (n.Rule.Label != "cif")
        {
            throw new Refused($"{ind.Name} doesn't unfold to a proposition: {Rhs(eqT)}");
        }
        string cond = pr.Render(n.Children[0]);
        Proof inProp = FixMem(d.Ph, d.Mems[major].P, "(/)", Lhs(eqT));
        Proof inIf = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", Lhs(eqT)), ("C", Rhs(eqT))), inProp, eqT);
        EnsureTowerLemmas();
        Proof holds = _d.Syl(inIf, Bi1(ApplyId("lean-prop", S(("ph", cond)))));

        // The cases' bound variables become hypotheses below, and rexlimdva needs each out of the context and the
        // goal: rename them all apart first.
        string cond2 = RenameApart(cond, BoundIn(cond), d.Ph, goal, string.Join(' ', d.Binders));
        if (cond2 != cond)
        {
            Proof al = Alpha("wff", cond, cond2) ?? throw new Refused($"not alpha-equivalent: {cond}  vs  {cond2}");
            Proof bi = _d.Lift(d.Ph, pr.Apply("mptru", S(("ph", $"( {cond} <-> {cond2} )")), al));
            holds = pr.Apply("mpbid", S(("ph", d.Ph), ("ps", cond), ("ch", cond2)), holds, bi);
        }

        // The cases: a disjunction nested to the left, one per constructor.
        var cases = new List<string>();
        SyntaxTree cn = pr.Parse("wff", cond2.Split(' '))!;
        for (int k = nm - 1; k >= 1; k--)
        {
            if (cn.Rule.Label != "wo")
            {
                throw new Refused($"{ind.Name}'s cases aren't a disjunction of {nm}: {cond2}");
            }
            cases.Insert(0, pr.Render(cn.Children[1]));
            cn = cn.Children[0];
        }
        cases.Insert(0, pr.Render(cn));

        // ( d.Ph -> ( case j -> goal ) ): enter the constructor's fields, apply minor premise j to them, and close
        // the fields again.
        Proof CaseImp(int j)
        {
            ConstInfo ctor = env.Find(ind.Ctors[j]) ?? throw new Refused($"{ind.Ctors[j]} is not in the export");
            Expr cty = ctor.Type;
            for (int i = 0; i < np; i++)
            {
                cty = _ops.Instantiate(((Binder)_typing.Whnf(cty)).Body, [args[i]]);
            }
            PCtx e = d;
            string rest = cases[j];
            var fields = new List<Expr>();
            var opened = new List<(string Ph, string Var, string Dom, string Body)>();
            for (int k = 0; k < ctor.NumFields; k++)
            {
                SyntaxTree rn = pr.Parse("wff", rest.Split(' '))!;
                if (rn.Rule.Label != "wrex")
                {
                    throw new Refused($"{ctor.Name}'s case has no field {k}: {rest}");
                }
                string g = pr.Render(rn.Children[1]), dom = pr.Render(rn.Children[2]), psi = pr.Render(rn.Children[0]);
                var b = (Binder)_typing.Whnf(cty);
                opened.Add((e.Ph, g, dom, psi));
                (e, Expr fv) = Enter(e, b.Domain, g, dom);
                fields.Add(fv);
                cty = _ops.Instantiate(b.Body, [fv]);
                rest = psi;
            }
            if (rest != "T.")
            {
                throw new Refused($"{ctor.Name}'s case ends in {rest}, not T.");
            }
            Typed m = MemOf(e, t.MkApp(t.FVar(fvs[np + 1 + j]), fields));
            string got = KidOf("wff", _d.Split(m.P.Proves).X, "A");
            if (got != elem)
            {
                throw new Refused($"{rec.Name} at {ctor.Name} is {got} by its minor premise, but {elem} in the model");
            }
            Proof q = FixMem(e.Ph, m.P, elem, target);
            q = pr.Apply("a1d", S(("ph", e.Ph), ("ps", goal), ("ch", rest)), q);
            for (int k = opened.Count - 1; k >= 0; k--)
            {
                var (ph, g, dom, psi) = opened[k];
                q = pr.Apply("rexlimdva", S(("ph", ph), ("x", g), ("A", dom), ("ps", psi), ("ch", goal)), q);
            }
            return q;
        }

        Proof all = CaseImp(0);
        string acc = cases[0];
        for (int j = 1; j < nm; j++)
        {
            all = pr.Apply("jaod", S(("ph", d.Ph), ("ps", acc), ("ch", goal), ("th", cases[j])), all, CaseImp(j));
            acc = $"( {acc} \\/ {cases[j]} )";
        }
        return pr.Apply("mpd", S(("ph", d.Ph), ("ps", cond2), ("ch", goal)), holds, all);
    }

    /// <summary>
    /// ( d.Ph -> cond ), cond the disjunction of a proposition's cases, by constructor j: each field's existential is
    /// witnessed by the constructor's own argument, the last binders of d (a variable for data, (/) for a proof).
    /// </summary>
    private Proof HoldsCase(PCtx d, string cond, ConstInfo ind, int j)
    {
        ConstInfo ctor = env.Find(ind.Ctors[j]) ?? throw new Refused($"{ind.Ctors[j]} is not in the export");
        var ids = d.Types.Keys.OrderBy(k => k).ToList();
        if (ids.Count < ctor.NumFields)
        {
            throw new Refused($"{ctor.Name}: its fields aren't in the context");
        }
        ids = ids.Skip(ids.Count - ctor.NumFields).ToList();
        // rspcedvd needs each bound variable out of the hypotheses and the witness: rename them all apart.
        string cond2 = RenameApart(cond, BoundIn(cond), d.Ph, string.Join(' ', d.Binders));

        Proof Fields(string w, int k)
        {
            SyntaxTree n = pr.Parse("wff", w.Split(' ')) ?? throw new Refused($"not a formula: {w}");
            if (n.Rule.Label != "wrex")
            {
                return ProveWff(d.Ph, w);
            }
            if (k >= ids.Count)
            {
                throw new Refused($"{ctor.Name}'s case has more fields than the constructor: {w}");
            }
            string body = pr.Render(n.Children[0]), x = pr.Render(n.Children[1]), dom = pr.Render(n.Children[2]);
            string a = d.Vars[ids[k]];
            string inst = Subst(body, x, a);
            Proof mem = FixMem(d.Ph, d.Mems[ids[k]].P, a, dom);
            Proof sub = body.Split(' ').Contains(x)
                ? _d.Congruence("wff", Subst(body, x, "Z"), "Z", pr.Apply("simpr", S(("ph", d.Ph), ("ps", $"{x} = {a}"))))
                : _d.BiRefl($"( {d.Ph} /\\ {x} = {a} )", body);
            return pr.Apply("rspcedvd", S(("ph", d.Ph), ("x", x), ("A", a), ("B", dom), ("ps", body), ("ch", inst)), mem, sub, Fields(inst, k + 1));
        }

        Proof Case(SyntaxTree n, int jj, int count)
        {
            if (count > 1)
            {
                if (n.Rule.Label != "wo")
                {
                    throw new Refused($"a proposition's cases aren't a disjunction: {pr.Render(n)}");
                }
                string l = pr.Render(n.Children[0]), r = pr.Render(n.Children[1]);
                return jj == count - 1
                    ? pr.Apply("olcd", S(("ph", d.Ph), ("ps", r), ("ch", l)), Fields(r, 0))
                    : pr.Apply("orcd", S(("ph", d.Ph), ("ps", l), ("ch", r)), Case(n.Children[0], jj, count - 1));
            }
            return Fields(pr.Render(n), 0);
        }

        Proof holds2 = Case(pr.Parse("wff", cond2.Split(' '))!, j, ind.Ctors.Length);
        if (cond2 == cond)
        {
            return holds2;
        }
        Proof al = Alpha("wff", cond, cond2) ?? throw new Refused($"not alpha-equivalent: {cond}  vs  {cond2}");
        Proof bi = _d.Lift(d.Ph, pr.Apply("mptru", S(("ph", $"( {cond} <-> {cond2} )")), al));
        return pr.Apply("mpbird", S(("ph", d.Ph), ("ps", cond), ("ch", cond2)), holds2, bi);
    }

    /// <summary>
    /// A field of a proposition that is a structure (And.left, Iff.mp), out of a proof of it: the proposition holds,
    /// so its fields exist, and a proof field's own proposition holds.
    /// </summary>
    private Typed PropProjMem(PCtx c, Proj p, ConstInfo ind, List<Expr> ps)
    {
        if (ind.IsRec || ind.NumIndices > 0 || ind.Ctors.Length != 1)
        {
            throw new Refused($"a projection out of {ind.Name}, a proposition that isn't a plain structure");
        }
        Expr lty = InferIn(c, p);
        string target = TrIn(c, lty), goal = $"(/) e. {target}";
        Typed sm = MemOf(c, p.Struct);
        List<Expr> doms = PiDomains(ind.Type, ps);
        var texts = ps.Select(a => TrIn(c, a)).ToList();
        (Proof eqT, _, _) = Unfold(c.Ph, Token(ind.Name)!, texts, (i, dom) => Check(c, ps[i], doms[i], dom));
        if (LabelOfText("class", Rhs(eqT)) != "cif")
        {
            throw new Refused($"{ind.Name} doesn't unfold to a proposition: {Rhs(eqT)}");
        }
        string cond = KidOf("class", Rhs(eqT), "ph");
        string elem = KidOf("wff", _d.Split(sm.P.Proves).X, "A");
        Proof inIf = pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", elem), ("B", Lhs(eqT)), ("C", Rhs(eqT))), FixMem(c.Ph, sm.P, elem, Lhs(eqT)), eqT);
        Proof holds = CondOfMember(c.Ph, inIf, elem, cond);
        string cond2 = RenameApart(cond, BoundIn(cond), c.Ph, goal, string.Join(' ', c.Binders));
        if (cond2 != cond)
        {
            Proof al = Alpha("wff", cond, cond2) ?? throw new Refused($"not alpha-equivalent: {cond}  vs  {cond2}");
            holds = pr.Apply("mpbid", S(("ph", c.Ph), ("ps", cond), ("ch", cond2)), holds,
                _d.Lift(c.Ph, pr.Apply("mptru", S(("ph", $"( {cond} <-> {cond2} )")), al)));
        }
        ConstInfo ctor = env.Find(ind.Ctors[0]) ?? throw new Refused($"{ind.Ctors[0]} is not in the export");
        Expr cty = ctor.Type;
        for (int i = 0; i < ind.NumParams; i++)
        {
            cty = _ops.Instantiate(((Binder)_typing.Whnf(cty)).Body, [ps[i]]);
        }
        PCtx e = c;
        string rest = cond2;
        var ids = new List<ulong>();
        var opened = new List<(string Ph, string Var, string Dom, string Body)>();
        for (int k = 0; k < ctor.NumFields; k++)
        {
            if (LabelOfText("wff", rest) != "wrex")
            {
                throw new Refused($"{ctor.Name}'s case has no field {k}: {rest}");
            }
            string g = KidOf("wff", rest, "x"), dom = KidOf("wff", rest, "A"), psi = KidOf("wff", rest, "ph");
            var b = (Binder)_typing.Whnf(cty);
            opened.Add((e.Ph, g, dom, psi));
            (e, Expr fv) = Enter(e, b.Domain, g, dom);
            ids.Add(((FVar)fv).Id);
            cty = _ops.Instantiate(b.Body, [fv]);
            rest = psi;
        }
        if (p.Idx >= ids.Count || e.Vars[ids[p.Idx]] != "(/)")
        {
            throw new Refused($"field {p.Idx} of {ind.Name} is data; a projection of data out of a proof isn't in the model");
        }
        Proof q = FixMem(e.Ph, e.Mems[ids[p.Idx]].P, "(/)", target);
        q = pr.Apply("a1d", S(("ph", e.Ph), ("ps", goal), ("ch", rest)), q);
        for (int k = opened.Count - 1; k >= 0; k--)
        {
            var (ph, g, dom, psi) = opened[k];
            q = pr.Apply("rexlimdva", S(("ph", ph), ("x", g), ("A", dom), ("ps", psi), ("ch", goal)), q);
        }
        Proof r = pr.Apply("mpd", S(("ph", c.Ph), ("ps", cond2), ("ch", goal)), holds, q);
        return new Typed(r, target, lty);
    }

    /// <summary>
    /// Classical.em, p ∨ ¬p, proved in the model directly: a proposition of the model is a member of 2o, so it is
    /// (/) or 1o. Lean's own proof (Diaconescu's) goes through Classical.choice as data, which the theorem translator
    /// doesn't follow; the statement is the same, and here it needs no choice at all.
    /// </summary>
    private Proof EmTyping(PCtx c, Expr type) => IntroPiProp(c, type, (d, body) =>
    {
        if (Ops.Spine(body, out List<Expr> args) is not Const orc || $"{orc.Name}" != "Or" || args.Count != 2
            || args[0] is not FVar pv || Ops.Spine(args[1], out List<Expr> nargs) is not Const notc || nargs.Count != 1)
        {
            throw new Refused("Classical.em's statement isn't p ∨ ¬p");
        }
        Expr p = args[0], notP = args[1];
        string x = d.Vars[pv.Id], ty = TrIn(d, body), goal = $"(/) e. {ty}";
        Proof x2 = FixMem(d.Ph, d.Mems[pv.Id].P, x, "2o");
        Proof inPr = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", x), ("B", "2o"), ("C", "{ (/) , 1o }")), x2, _d.Lift(d.Ph, pr.Apply("df2o3", S())));
        Proof either = _d.Syl(inPr, pr.Apply("elpri", S(("A", x), ("B", "(/)"), ("C", "1o"))));
        Expr Ctor(string name) => t.Const((env.Find(t.Of(name)) ?? throw new Refused($"{name} is not in the export")).Name, []);

        // p is 1o: it holds, by Or.inl.
        PCtx e1 = Extend(d, $"{x} = 1o");
        Expr h = t.FVar(_fresh++);
        ulong hid = ((FVar)h).Id;
        e1.Types[hid] = p;
        e1.Vars[hid] = "(/)";
        e1.Mems[hid] = (pr.Apply("eleqtrrd", S(("ph", e1.Ph), ("A", "(/)"), ("B", "1o"), ("C", x)), _d.Lift(e1.Ph, pr.Apply("0lt1o", S())),
            pr.Apply("simpr", S(("ph", d.Ph), ("ps", $"{x} = 1o")))), x);
        Proof r1 = FixMem(e1.Ph, MemOf(e1, t.MkApp(Ctor("Or.inl"), [p, notP, h])).P, "(/)", ty);

        // p is (/): nothing is in it, so p → False holds, and Or.inr.
        PCtx e0 = Extend(d, $"{x} = (/)");
        (Proof eqN, _, _) = Unfold(e0.Ph, Token(notc.Name)!, [x], (i, dom) => FixMem(e0.Ph, e0.Mems[pv.Id].P, x, dom));
        if (LabelOfText("class", Rhs(eqN)) != "cif" || LabelOfText("wff", KidOf("class", Rhs(eqN), "ph")) != "wral")
        {
            throw new Refused($"¬p doesn't unfold to a Π-proposition: {Rhs(eqN)}");
        }
        string cond = KidOf("class", Rhs(eqN), "ph");
        if (KidOf("wff", cond, "A") != x)
        {
            throw new Refused($"¬p doesn't quantify over p: {cond}");
        }
        Proof all = _d.Syl(pr.Apply("simpr", S(("ph", d.Ph), ("ps", $"{x} = (/)"))),
            pr.Apply("rzal", S(("A", x), ("x", KidOf("wff", cond, "x")), ("ph", KidOf("wff", cond, "ph")))));
        Proof inNot = pr.Apply("eleqtrrd", S(("ph", e0.Ph), ("A", "(/)"), ("B", Rhs(eqN)), ("C", Lhs(eqN))), MemberOfCond(e0.Ph, all, cond), eqN);
        Expr hn = t.FVar(_fresh++);
        ulong nid = ((FVar)hn).Id;
        e0.Types[nid] = notP;
        e0.Vars[nid] = "(/)";
        e0.Mems[nid] = (inNot, Lhs(eqN));
        Proof r0 = FixMem(e0.Ph, MemOf(e0, t.MkApp(Ctor("Or.inr"), [p, notP, hn])).P, "(/)", ty);

        return pr.Apply("mpjaodan", S(("ph", d.Ph), ("ps", $"{x} = (/)"), ("ch", goal), ("th", $"{x} = 1o")), r0, r1, either);
    });
}
