using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Induction on a recursive proposition (Nat.le): its recursor at a motive into Prop, typed for the theorem translator
/// (docs/milestone3.md, "Theorems across Init"). The proposition is the least set of index tuples, built in stages
/// (DefineRecursiveProposition): I ps i⃗ holds when <. i⃗ >. e. U_ k e. _om stage k. So the motive holds wherever the
/// proposition does, by induction on k (finds2) of
///   Phi(k) := A. q⃗ ( <. q⃗ >. e. stage k -> ψ(q⃗) ),   ψ(q⃗) the goal (/) e. ( M ` q⃗ … ` (/) ) at the indices q⃗.
/// Stage (/) is empty. Stage suc y is stage y, where Phi(y) holds, and the constructors' parts over it: a tuple in
/// constructor j's part is that constructor's result over some fields (eliun, elsni, opthg), where minor premise j
/// applies: data fields as themselves, proofs as (/), a recursive premise's proof as (/) (its tuple is in stage y, so
/// in the least set), and its induction hypothesis from Phi(y). The major premise puts <. i⃗ >. in some stage.
/// </summary>
public sealed partial class Model
{
    private (string, string) RecPropRecLemma(Const k0, ConstInfo rec, ConstInfo ind, Name iname)
    {
        EnsureTowerLemmas();
        EnsurePf();
        var c = new PCtx { Ph = UHyp };
        Expr ty0 = _ops.InstantiateLevels(rec.Type, rec.LevelParams, k0.Levels);
        string tyText = TrIn(c, ty0);
        int np = ind.NumParams, ni = ind.NumIndices, nb = np + rec.NumMotives + rec.NumMinors;
        string itok = Token(iname)!, steptok = itok + ".-step";
        Proof p = IntroPiProp(c, ty0, (d, body) =>
        {
            var vs = d.Binders.TakeLast(nb + ni + 1).ToList();
            string Ty(string v) => Conjuncts(d.Ph).First(x => x.StartsWith($"{v} e. ", StringComparison.Ordinal))[(v.Length + 4)..];
            string ta = d.Ph;
            string goal = $"(/) e. {TrIn(d, body)}";
            var texts = d.Vars.Values.ToHashSet();
            string Txt(string v) => texts.Contains(v) ? v : "(/)";
            var idxVars = vs.Skip(nb).Take(ni).Select(Txt).ToList();
            // Indices that are proofs (Nat.le.below's t) are (/) in every tuple: only the others are quantified.
            var dataPos = Enumerable.Range(0, ni).Where(i => idxVars[i] != "(/)").ToList();
            List<string> Full(IReadOnlyList<string> at)
            {
                var r = Enumerable.Repeat("(/)", ni).ToList();
                for (int i = 0; i < dataPos.Count; i++)
                {
                    r[dataPos[i]] = at[i];
                }
                return r;
            }
            var iargs = vs.Take(np).Select(Txt).Concat(idxVars).ToList();
            string pMajor = Ty(vs[^1]);
            Proof major = HypIn(d, $"(/) e. {pMajor}");
            (Proof eqI, _, _) = Unfold(ta, itok, iargs, (i, dom) => HypIn(d, $"{iargs[i]} e. {dom}"));
            Proof inIf = pr.Apply("eleqtrd", S(("ph", ta), ("A", "(/)"), ("B", pMajor), ("C", Rhs(eqI))), major,
                AlphaIn(ta, pMajor, Lhs(eqI)) is var a1 ? _d.Trans(a1, eqI) : eqI);
            string cond = pr.Render(pr.Parse("class", Rhs(eqI).Split(' '))!.Children[0]);
            var (member, least) = LeastCond(cond) ?? throw new Refused($"{iname} doesn't unfold to a least set of index tuples: {cond}");
            if (member != Tuple(idxVars))
            {
                throw new Refused($"{iname}'s index tuple came out as {member}, not {Tuple(idxVars)}");
            }
            Proof inLeast = _d.Syl(inIf, Bi1(ApplyId("lean-prop", S(("ph", cond)))));
            string k = Part(least, "x"), stageBody = Part(least, "B");
            if ((ta + " " + goal).Split(' ').Contains(k))
            {
                // The union's letter is the induction variable: rename it away from the context and the goal.
                string k2 = FirstVar(x => !(ta + " " + goal + " " + least).Split(' ').Contains(x));
                string least2 = $"U_ {k2} e. _om {Subst(stageBody, k, k2)}";
                inLeast = pr.Apply("eleqtrd", S(("ph", ta), ("A", member), ("B", least), ("C", least2)), inLeast, AlphaIn(ta, least, least2));
                (least, k, stageBody) = (least2, k2, Subst(stageBody, k, k2));
            }
            string Stage(string b) => Subst(stageBody, k, b);
            string stepApp = Part(Part(Stage("(/)"), "F"), "F");
            string sx = Part(stepApp, "x"), sBody = Part(stepApp, "B");

            // Fresh letters: the quantified indices q⃗ and the step's y.
            var taken = new HashSet<string>((ta + " " + goal + " " + least + " " + sBody).Split(' ')) { k, sx };
            string Fresh() { string v = FirstVar(x => !taken.Contains(x)); taken.Add(v); return v; }
            var qs = dataPos.Select(_ => Fresh()).ToList();
            string yv = Fresh();
            string Psi(IReadOnlyList<string> at)
            {
                string g = goal;
                for (int i = 0; i < dataPos.Count; i++)
                {
                    g = string.Join(' ', g.Split(' ').Select(tok => tok == idxVars[dataPos[i]] ? $"ZZQ{i}" : tok));
                }
                for (int i = 0; i < dataPos.Count; i++)
                {
                    g = g.Replace($"ZZQ{i}", at[i], StringComparison.Ordinal);
                }
                return g;
            }
            var rs = dataPos.Select(_ => Fresh()).ToList();   // Phi's letters inside the step, apart from q⃗ (alrimiv)
            string Inner(string b) => $"( {Tuple(Full(qs))} e. {Stage(b)} -> {Psi(qs)} )";
            string PhiL(string b, List<string> ls) => ls.AsEnumerable().Reverse().Aggregate($"( {Tuple(Full(ls))} e. {Stage(b)} -> {Psi(ls)} )", (acc, q) => $"A. {q} {acc}");
            string Phi(string b) => PhiL(b, qs);
            Proof Sub(string to) => _d.Congruence("wff", Phi("ZZK").Replace("ZZK", "Z", StringComparison.Ordinal), "Z", pr.Apply("id", S(("ph", $"{k} = {to}"))));

            // From ( ctx -> Phi(b) ): ( ctx -> ( <. t⃗ >. e. stage b -> ψ(t⃗) ) ), instantiating each q (spcgv).
            Proof Instantiate(string ctx, Proof phi, string b, IReadOnlyList<string> ts, List<string>? letters = null)
            {
                var ls = letters ?? qs;
                Proof cur = phi;
                var at = ls.ToList();
                for (int i = 0; i < dataPos.Count; i++)
                {
                    string before = ls.Skip(i).Reverse().Aggregate(InnerAt(b, at), (acc, q) => $"A. {q} {acc}");
                    string bodyBefore = ls.Skip(i + 1).Reverse().Aggregate(InnerAt(b, at), (acc, q) => $"A. {q} {acc}");
                    var at2 = at.ToList();
                    at2[i] = ts[i];
                    string bodyAfter = ls.Skip(i + 1).Reverse().Aggregate(InnerAt(b, at2), (acc, q) => $"A. {q} {acc}");
                    Proof sub = ls[i] == ts[i] ? pr.Apply("a1i", S(("ph", $"( {bodyBefore} <-> {bodyBefore} )"), ("ps", $"{ls[i]} = {ts[i]}")), pr.Apply("biid", S(("ph", bodyBefore))))
                        : _d.Congruence("wff", Subst(bodyBefore, ls[i], "Z"), "Z", pr.Apply("id", S(("ph", $"{ls[i]} = {ts[i]}"))));
                    Proof spc = _d.Syl(Exists(ctx, ts[i]), pr.Apply("spcgv", S(("x", ls[i]), ("A", ts[i]), ("V", "_V"), ("ph", bodyBefore), ("ps", bodyAfter)), sub));
                    cur = pr.Apply("mpd", S(("ph", ctx), ("ps", before), ("ch", bodyAfter)), cur, spc);
                    at = at2;
                }
                return cur;
            }
            string InnerAt(string b, IReadOnlyList<string> at) => $"( {Tuple(Full(at))} e. {Stage(b)} -> {Psi(at)} )";

            // The base: stage (/) is empty.
            Proof r0 = pr.Apply("rdg0", S(("F", stepApp), ("A", "(/)")), pr.Apply("0ex", S()));
            string tq = Tuple(Full(qs));
            Proof notIn = pr.Apply("mtbir", S(("ph", $"{tq} e. {Stage("(/)")}"), ("ps", $"{tq} e. (/)")), pr.Apply("noel", S(("A", tq))),
                pr.Apply("eleq2i", S(("A", Stage("(/)")), ("B", "(/)"), ("C", tq)), r0));
            Proof baseP;
            baseP = BaseAll(ta, qs, Inner("(/)"), _d.Lift(ta, pr.Apply("pm2.21i", S(("ph", $"{tq} e. {Stage("(/)")}"), ("ps", Psi(qs))), notIn)));

            // The step: ( ( ta /\ y e. _om ) /\ Phi(y) ) gives Phi(suc y).
            string ctx = $"( ( {ta} /\\ {yv} e. _om ) /\\ {PhiL(yv, rs)} )";
            string memS = $"{tq} e. {Stage($"suc {yv}")}";
            string ctx2 = $"( {ctx} /\\ {memS} )";
            Proof yOm = Hyp(ctx2, $"{yv} e. _om")!.Value;
            Proof rdg = _d.Syl(_d.Syl(yOm, pr.Apply("nnon", S(("A", yv)))), pr.Apply("rdgsuc", S(("B", yv), ("F", stepApp), ("A", "(/)"))));
            var avoid = new HashSet<string>(qs.Concat(rs)) { yv };
            foreach (string cj in Conjuncts(ta))
            {
                if (SetVarSet.Contains(cj.Split(' ')[0]))
                {
                    avoid.Add(cj.Split(' ')[0]);
                }
            }
            (Proof stepEq, string parts) = StageStep(ctx2, steptok, stepApp, Stage(yv), avoid);
            Proof toUn = _d.Trans(rdg, stepEq);
            string sy = Stage(yv);
            Proof inUn = pr.Apply("eleqtrd", S(("ph", ctx2), ("A", tq), ("B", Stage($"suc {yv}")), ("C", $"( {sy} u. {parts} )")), Hyp(ctx2, memS)!.Value, toUn);
            Proof either = pr.Apply("sylib", S(("ph", ctx2), ("ps", $"{tq} e. ( {sy} u. {parts} )"), ("ch", $"( {tq} e. {sy} \\/ {tq} e. {parts} )")),
                inUn, pr.Apply("elun", S(("A", tq), ("B", sy), ("C", parts))));
            // In stage y: Phi(y).
            Proof phiY = Hyp(ctx2, PhiL(yv, rs))!.Value;
            Proof oldCase = Instantiate(ctx2, phiY, yv, qs, rs);
            // In the parts: one constructor at a time.
            int nc = ind.Ctors.Length;
            Proof PartsCase(string cx, string ps2, int count)
            {
                if (count == 1)
                {
                    return PartCase(cx, ps2, 0);
                }
                SyntaxTree un = pr.Parse("class", ps2.Split(' '))!;
                string l = pr.Render(un.Children[0]), r = pr.Render(un.Children[1]);
                Proof left = count == 2 ? PartCase(cx, l, 0) : PartsCase(cx, l, count - 1);
                Proof right = PartCase(cx, r, count - 1);
                Proof split = pr.Apply("elun", S(("A", tq), ("B", l), ("C", r)));
                Proof both = pr.Apply("jaod", S(("ph", cx), ("ps", $"{tq} e. {l}"), ("ch", Psi(qs)), ("th", $"{tq} e. {r}")), left, right);
                return pr.Apply("biimtrid", S(("ph", $"{tq} e. ( {l} u. {r} )"), ("ps", $"( {tq} e. {l} \\/ {tq} e. {r} )"), ("ch", cx), ("th", Psi(qs))), split, both);
            }
            // ( cx -> ( tq e. part_j -> ψ(q⃗) ) ).
            Proof PartCase(string cx, string part, int j) => FieldsCase(cx, part, j, []);
            Proof FieldsCase(string cx, string part, int j, List<(string Var, string Dom)> fields)
            {
                SyntaxTree n = pr.Parse("class", part.Split(' '))!;
                if (n.Rule.Label == "ciun")
                {
                    string f = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), inner = pr.Render(n.Children[2]);
                    Proof? toRenamed = null;
                    string partHere = part;
                    if (cx.Split(' ').Contains(f) || Psi(qs).Split(' ').Contains(f) || taken.Contains(f))
                    {
                        // Rename the field's binder to a letter free everywhere here.
                        string f2 = FirstVar(x => !taken.Contains(x) && !part.Split(' ').Contains(x) && !cx.Split(' ').Contains(x));
                        inner = SubstFree(inner, f, f2);
                        partHere = $"U_ {f2} e. {dom} {inner}";
                        toRenamed = pr.Apply("eleq2d", S(("ph", cx), ("A", part), ("B", partHere), ("C", tq)), AlphaIn(cx, part, partHere));
                        f = f2;
                    }
                    taken.Add(f);
                    string cx2 = $"( {cx} /\\ {f} e. {dom} )";
                    Proof innerP = FieldsCase(cx2, inner, j, [.. fields, (f, dom)]);
                    Proof lim = pr.Apply("rexlimdva", S(("ph", cx), ("x", f), ("A", dom), ("ps", $"{tq} e. {inner}"), ("ch", Psi(qs))), innerP);
                    Proof el = pr.Apply("eliun", S(("A", tq), ("x", f), ("B", dom), ("C", inner)));
                    Proof here = pr.Apply("biimtrid", S(("ph", $"{tq} e. {partHere}"), ("ps", $"E. {f} e. {dom} {tq} e. {inner}"), ("ch", cx), ("th", Psi(qs))), el, lim);
                    return toRenamed is Proof tr
                        ? pr.Apply("sylbid", S(("ph", cx), ("ps", $"{tq} e. {part}"), ("ch", $"{tq} e. {partHere}"), ("th", Psi(qs))), tr, here)
                        : here;
                }
                if (n.Rule.Label != "csn")
                {
                    throw new Refused($"{iname}'s constructor part isn't a union of singletons: {part}");
                }
                string t = pr.Render(n.Children[0]);
                string cx3 = $"( {cx} /\\ {tq} e. {part} )";
                Proof teq = _d.Syl(Hyp(cx3, $"{tq} e. {part}")!.Value, pr.Apply("elsni", S(("A", tq), ("B", t))));
                // The index equalities q_i = t_i, from <. q⃗ >. = <. t⃗ >. (opthg).
                var ts = new List<string>();
                var eqs = new List<Proof>();
                string lhs = tq, rhs = t;
                Proof cur = teq;
                for (int i = 0; i < ni; i++)
                {
                    SyntaxTree ln = pr.Parse("class", lhs.Split(' '))!, rn = pr.Parse("class", rhs.Split(' '))!;
                    if (ln.Rule.Label != "cop" || rn.Rule.Label != "cop")
                    {
                        throw new Refused($"{iname}'s tuple {rhs} isn't a pair");
                    }
                    string la = pr.Render(ln.Children[0]), lb = pr.Render(ln.Children[1]), ra = pr.Render(rn.Children[0]), rb = pr.Render(rn.Children[1]);
                    Proof bi = _d.Syl(_d.Jca(Exists(cx3, la), Exists(cx3, lb)), pr.Apply("opthg", S(("A", la), ("B", lb), ("C", ra), ("D", rb), ("V", "_V"), ("W", "_V"))));
                    Proof both = pr.Apply("mpbid", S(("ph", cx3), ("ps", $"{lhs} = {rhs}"), ("ch", $"( {la} = {ra} /\\ {lb} = {rb} )")), cur, bi);
                    if (dataPos.Contains(i))
                    {
                        eqs.Add(pr.Apply("simpld", S(("ph", cx3), ("ps", $"{la} = {ra}"), ("ch", $"{lb} = {rb}")), both));
                        ts.Add(ra);
                    }
                    cur = pr.Apply("simprd", S(("ph", cx3), ("ps", $"{la} = {ra}"), ("ch", $"{lb} = {rb}")), both);
                    (lhs, rhs) = (lb, rb);
                }
                // ψ(t⃗) by minor premise j.
                Proof holds = MinorAt(cx3, j, fields, ts);
                // Back to ψ(q⃗): q_i = t_i.
                Proof back = holds;
                var at = ts.ToList();
                for (int i = dataPos.Count - 1; i >= 0; i--)
                {
                    var at2 = at.ToList();
                    at2[i] = qs[i];
                    string from = Psi(at), to = Psi(at2);
                    if (from != to)
                    {
                        Proof cong = _d.Congruence("wff", Subst(to, qs[i], "Z"), "Z", eqs[i]);   // ( cx3 -> ( ψ(q_i) <-> ψ(t_i) ) )
                        back = pr.Apply("mpbird", S(("ph", cx3), ("ps", to), ("ch", from)), back, cong);
                    }
                    at = at2;
                }
                return pr.Apply("ex", S(("ph", cx), ("ps", $"{tq} e. {part}"), ("ch", Psi(qs))), back);
            }
            // A recursive premise's field f e. if ( idx e. B , 1o , (/) ), B the stage y (read through the packed argument):
            // ( cx -> idx e. stage y ), or null for another field.
            (string Idx, Proof InSy)? Premise(string cx, string f, string fdom)
            {
                SyntaxTree fn = pr.Parse("class", fdom.Split(' '))!;
                if (fn.Rule.Label != "cif" || pr.Render(fn.Children[1]) != "1o" || pr.Render(fn.Children[2]) != "(/)")
                {
                    return null;
                }
                string chi = pr.Render(fn.Children[0]);
                SyntaxTree cn = pr.Parse("wff", chi.Split(' '))!;
                if (cn.Rule.Label != "wcel")
                {
                    return null;
                }
                string idx = pr.Render(cn.Children[0]), bcls = pr.Render(cn.Children[1]);
                Proof? toSy = bcls == sy ? null : Simp(cx, bcls);
                if (bcls != sy && (toSy is null || Rhs(toSy.Value) != sy))
                {
                    return null;
                }
                Proof fIn = Hyp(cx, $"{f} e. {fdom}") ?? throw new Refused($"no hypothesis {f} e. {fdom}");
                Proof c2 = _d.Syl(fIn, Bi1(pr.Apply("elif0", S(("A", f), ("ph", chi), ("B", "1o")))));
                Proof inB = pr.Apply("simpld", S(("ph", cx), ("ps", chi), ("ch", $"{f} e. 1o")), c2);
                return (idx, toSy is Proof q ? pr.Apply("eleqtrd", S(("ph", cx), ("A", idx), ("B", bcls), ("C", sy)), inB, q) : inB);
            }

            // ( cx -> ψ(t⃗) ): minor j applied to the fields, then to each recursive premise's induction hypothesis.
            Proof MinorAt(string cx, int j, List<(string Var, string Dom)> fields, List<string> ts)
            {
                string minor = vs[np + rec.NumMotives + j];
                string ty = Ty(minor);
                Proof m = WeakenTo(cx, HypIn(d, $"(/) e. {ty}"));
                var ihs = new List<(string Idx, List<string> Comps)>();
                foreach (var (f, fdom0) in fields)
                {
                    Proof fIn = Hyp(cx, $"{f} e. {fdom0}")!.Value;
                    string fdom = fdom0;
                    string arg;
                    Func<string, Proof> argIn;
                    if (Premise(cx, f, fdom0) is (string idx, Proof inSy))
                    {
                        // A recursive premise: its tuple idx is in stage y, so in the least set; the premise holds.
                        Proof subK = _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = {yv}"))));
                        Proof incl = _d.Syl(Hyp(cx, $"{yv} e. _om")!.Value, pr.Apply("ssiun2s", S(("x", k), ("A", "_om"), ("B", stageBody), ("C", yv), ("D", sy)), subK));
                        Proof inL = pr.Apply("mpd", S(("ph", cx), ("ps", $"{idx} e. {sy}"), ("ch", $"{idx} e. {least}")), inSy,
                            pr.Apply("sseld", S(("ph", cx), ("A", sy), ("B", least), ("C", idx)), incl));
                        Proof holdsIf = _d.Syl(inL, Bi2(ApplyId("lean-prop", S(("ph", $"{idx} e. {least}")))));
                        string ifL = $"if ( {idx} e. {least} , 1o , (/) )";
                        arg = "(/)";
                        argIn = dom =>
                        {
                            if (dom == ifL)
                            {
                                return holdsIf;
                            }
                            if (ConstApp(dom) is (Name h, List<string> cargs) && ReferenceEquals(h, iname))
                            {
                                (Proof eqD, _, _) = Unfold(cx, itok, cargs, (i, dd) => TryHyp(new PCtx { Ph = cx }, $"{cargs[i]} e. {dd}") ?? HoldsByMember(cx, cargs[i], dd) ?? TextMem(new PCtx { Ph = cx }, cargs[i], dd));
                                Proof eqD2 = Rhs(eqD) == ifL ? eqD : _d.Trans(eqD, AlphaIn(cx, Rhs(eqD), ifL));
                                return pr.Apply("eleqtrrd", S(("ph", cx), ("A", "(/)"), ("B", ifL), ("C", dom)), holdsIf, eqD2);
                            }
                            throw new Refused($"{iname}'s premise has the domain {dom}");
                        };
                        // Its components, for the induction hypothesis.
                        var comps = new List<string>();
                        string rest = idx;
                        for (int i = 0; i < ni; i++)
                        {
                            SyntaxTree rn = pr.Parse("class", rest.Split(' '))!;
                            comps.Add(pr.Render(rn.Children[0]));
                            rest = pr.Render(rn.Children[1]);
                        }
                        ihs.Add((idx, comps));
                    }
                    else
                    {
                        if (Simp(cx, fdom0) is Proof sp)
                        {
                            fdom = Rhs(sp);
                            fIn = pr.Apply("eleqtrd", S(("ph", cx), ("A", f), ("B", fdom0), ("C", fdom)), fIn, sp);
                        }
                        Proof? inh;
                        try
                        {
                            inh = Inhabited(cx, f, fdom);
                        }
                        catch (Refused)
                        {
                            inh = null;
                        }
                        arg = inh is null ? f : "(/)";
                        Proof have = inh ?? fIn;
                        argIn = dom => dom == fdom ? have : pr.Apply("eleqtrd", S(("ph", cx), ("A", arg), ("B", fdom), ("C", dom)), have, AlphaIn(cx, fdom, dom));
                    }
                    (m, string inst) = TextApplyProp(cx, m, ty, arg, argIn);
                    ty = inst[7..];
                }
                foreach (var (idx, comps) in ihs)
                {
                    // ψ(comps), from Phi(y) at the premise's tuple, which is in stage y.
                    Proof phi = WeakenTo(cx, phiY);
                    var dcomps = dataPos.Select(i => comps[i]).ToList();
                    if (Tuple(Full(dcomps)) != idx)
                    {
                        throw new Refused($"{iname}'s premise tuple {idx} has a proof index that isn't (/)");
                    }
                    Proof imp = Instantiate(cx, phi, yv, dcomps, rs);
                    Proof inSy = TupleInStage(cx, idx);
                    Proof ih = pr.Apply("mpd", S(("ph", cx), ("ps", $"{Tuple(Full(dcomps))} e. {sy}"), ("ch", Psi(dcomps))), inSy, imp);
                    string ihProp = Psi(dcomps)[7..];
                    (m, string inst) = TextApplyProp(cx, m, ty, "(/)", dom => dom == ihProp ? ih
                        : pr.Apply("eleqtrd", S(("ph", cx), ("A", "(/)"), ("B", ihProp), ("C", dom)), ih, AlphaIn(cx, ihProp, dom)));
                    ty = inst[7..];
                }
                string want = Psi(ts)[7..];
                return ty == want ? m : pr.Apply("eleqtrd", S(("ph", cx), ("A", "(/)"), ("B", ty), ("C", want)), m, AlphaIn(cx, ty, want));
            }
            // ( cx -> idx e. stage y ), from the premise field's hypothesis.
            Proof TupleInStage(string cx, string idx)
            {
                foreach (string cj in Conjuncts(cx))
                {
                    SyntaxTree jn = pr.Parse("wff", cj.Split(' '))!;
                    if (jn.Rule.Label == "wcel" && Premise(cx, pr.Render(jn.Children[0]), pr.Render(jn.Children[1])) is (string i2, Proof inSy) && i2 == idx)
                    {
                        return inSy;
                    }
                }
                throw new Refused($"no premise puts {idx} in stage {yv}");
            }

            Proof newCase = PartsCase(ctx2, parts, nc);
            Proof sucInner = pr.Apply("jaod", S(("ph", ctx2), ("ps", $"{tq} e. {sy}"), ("ch", Psi(qs)), ("th", $"{tq} e. {parts}")),
                InnerOld(ctx2, oldCase), newCase);
            Proof psiQ = pr.Apply("mpd", S(("ph", ctx2), ("ps", $"( {tq} e. {sy} \\/ {tq} e. {parts} )"), ("ch", Psi(qs))), either, sucInner);
            Proof innerSuc = pr.Apply("ex", S(("ph", ctx), ("ps", memS), ("ch", Psi(qs))), psiQ);
            Proof phiSuc = BaseAll(ctx, qs, Inner($"suc {yv}"), innerSuc);
            Proof ex0 = pr.Apply("ex", S(("ph", $"( {ta} /\\ {yv} e. _om )"), ("ps", PhiL(yv, rs)), ("ch", Phi($"suc {yv}"))), phiSuc);
            Proof alphaY = pr.Apply("mptru", S(("ph", $"( {Phi(yv)} <-> {PhiL(yv, rs)} )")), Alpha("wff", Phi(yv), PhiL(yv, rs)) ?? throw new Refused("Phi's letters didn't rename"));
            Proof ex1 = pr.Apply("biimtrid", S(("ph", Phi(yv)), ("ps", PhiL(yv, rs)), ("ch", $"( {ta} /\\ {yv} e. _om )"), ("th", Phi($"suc {yv}"))), alphaY, ex0);
            Proof ex2 = pr.Apply("ex", S(("ph", ta), ("ps", $"{yv} e. _om"), ("ch", $"( {Phi(yv)} -> {Phi($"suc {yv}")} )")), ex1);
            Proof stepP = pr.Apply("com12", S(("ph", ta), ("ps", $"{yv} e. _om"), ("ch", $"( {Phi(yv)} -> {Phi($"suc {yv}")} )")), ex2);
            Proof every = pr.Apply("finds2", S(("x", k), ("y", yv), ("ph", Phi(k)), ("ps", Phi("(/)")), ("ch", Phi(yv)), ("th", Phi($"suc {yv}")), ("ta", ta)),
                Sub("(/)"), Sub(yv), Sub($"suc {yv}"), baseP, stepP);

            // The major premise: <. i⃗ >. is in some stage k.
            string ctxK = $"( {ta} /\\ {k} e. _om )";
            Proof phiK = pr.Apply("impcom", S(("ph", $"{k} e. _om"), ("ps", ta), ("ch", Phi(k))), every);
            Proof atIdx = Instantiate(ctxK, phiK, k, dataPos.Select(i => idxVars[i]).ToList());                        // ( ctxK -> ( member e. stage k -> goal ) )
            Proof lim = pr.Apply("rexlimdva", S(("ph", ta), ("x", k), ("A", "_om"), ("ps", $"{member} e. {Stage(k)}"), ("ch", goal)), atIdx);
            Proof some = pr.Apply("sylib", S(("ph", ta), ("ps", $"{member} e. {least}"), ("ch", $"E. {k} e. _om {member} e. {Stage(k)}")),
                inLeast, pr.Apply("eliun", S(("A", member), ("x", k), ("B", "_om"), ("C", Stage(k)))));
            return pr.Apply("mpd", S(("ph", ta), ("ps", $"E. {k} e. _om {member} e. {Stage(k)}"), ("ch", goal)), some, lim);
        });
        string label = $"lean-ind-{LabelOf(iname)}";
        EmitLemma(label, $"Induction on {iname}, a recursive proposition: its recursor at a motive into Prop, by induction over its stages.", p);
        _propRec[k0.Name] = (label, tyText);
        return (label, tyText);
    }

    /// <summary>( ctx -> (/) e. P ) for a proof argument, when the context has a member v e. P (lean-pf); else null.</summary>
    private Proof? HoldsByMember(string ctx, string arg, string prop)
    {
        if (arg != "(/)")
        {
            return null;
        }
        foreach (string cj in Conjuncts(ctx))
        {
            if (cj.EndsWith($" e. {prop}", StringComparison.Ordinal) && cj != $"(/) e. {prop}")
            {
                try
                {
                    return Inhabited(ctx, cj[..^(prop.Length + 4)], prop);
                }
                catch (Refused)
                {
                }
            }
        }
        return null;
    }

    /// <summary>( ctx -> ( tq e. stage y -> ψ ) ) as given: the old stage's case, already in that form.</summary>
    private static Proof InnerOld(string ctx, Proof p) => p;

    /// <summary>From ( ctx -> body ): ( ctx -> A. q1 … body ), the q not in ctx (alrimiv).</summary>
    private Proof BaseAll(string ctx, List<string> qs, string body, Proof p)
    {
        Proof cur = p;
        string b = body;
        foreach (string q in qs.AsEnumerable().Reverse())
        {
            cur = pr.Apply("alrimiv", S(("ph", ctx), ("x", q), ("ps", b)), cur);
            b = $"A. {q} {b}";
        }
        return cur;
    }

    /// <summary>
    /// ( ctx -> ( stepf ` sb ) = ( sb u. parts ) ) for a recursive proposition's stage sb: rename stepf's variable away
    /// from sb, apply it, unfold the step at the packed argument, rename the parts' binders apart from the letters to
    /// avoid, and read the packed parts back (Simp). Also returns the parts.
    /// </summary>
    private (Proof Eq, string Parts) StageStep(string ctx, string steptok, string stepApp, string sb, ISet<string> avoid)
    {
        string sx = Part(stepApp, "x"), sBody = Part(stepApp, "B");
        string y = FirstVar(x => x != sx && !sb.Split(' ').Contains(x) && !sBody.Split(' ').Contains(x) && !ctx.Split(' ').Contains(x));
        string bodyY = Subst(sBody, sx, y), stepY = $"( {y} e. _V |-> {bodyY} )";
        Proof ren = pr.Apply("cbvmptv", S(("x", sx), ("y", y), ("A", "_V"), ("B", sBody), ("C", bodyY)),
            _d.Congruence("class", Subst(sBody, sx, "Z"), "Z", pr.Apply("id", S(("ph", $"{sx} = {y}")))));
        Proof e1 = pr.Apply("fveq1d", S(("ph", ctx), ("A", sb), ("F", stepApp), ("G", stepY)), _d.Lift(ctx, ren));
        Proof e2 = Beta(ctx, pr.Apply("eqid", S(("A", stepY))), y, "_V", bodyY, sb, Exists(ctx, sb), stepY);
        string arg = Subst(bodyY, y, sb);
        Proof e3 = UnfoldRaw(ctx, steptok, Part(arg, "A"));
        Proof eq = _d.Trans(_d.Trans(e1, e2), e3);
        string r0 = Rhs(eq), r1 = RenameApart(r0, avoid, ctx);
        if (r1 != r0)
        {
            eq = _d.Trans(eq, AlphaIn(ctx, r0, r1));
        }
        if (Simp(ctx, Rhs(eq)) is Proof sp)
        {
            eq = _d.Trans(eq, sp);
        }
        SyntaxTree un = pr.Parse("class", Rhs(eq).Split(' '))!;
        if (un.Rule.Label != "cun" || pr.Render(un.Children[0]) != sb)
        {
            throw new Refused($"the step came out as {Rhs(eq)}");
        }
        return (eq, pr.Render(un.Children[1]));
    }
}
