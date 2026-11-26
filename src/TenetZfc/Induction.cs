using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Induction (docs/milestone3.md, "Theorems through the model"): a recursor used at a motive into Prop. Its type is
/// then a proposition, and every proof of it is (/), so it is typed by a lemma of its own, lean-ind-I:
/// (/) e. ⟦(motive : I → Prop) → minors → (t : I) → motive t⟧. It follows from the recursor's typing (lean-recty-I)
/// with each minor premise, a proof, replaced by a witness of the minor premise's data type: the map that is (/)
/// everywhere, which is in that type because each motive value it lands in holds, by the minor premise.
/// </summary>
public sealed partial class Model
{
    private readonly Dictionary<Name, (string, string)> _propRec = new(ReferenceEqualityComparer.Instance);

    private (string Label, string Ty) PropRecLemma(Const k)
    {
        if (_propRec.TryGetValue(k.Name, out var done))
        {
            return done;
        }
        ConstInfo rec = env.Find(k.Name)!;
        Name iname = k.Name is StrName { Value: "rec" } rn ? rn.Prefix : throw new Refused($"{k.Name} isn't a type's recursor");
        ConstInfo ind = env.Find(iname)!;
        Define(iname);
        Define(k.Name);
        if (IsProposition(ind) && !ind.IsRec && ind.Ctors.Length == 1)
        {
            return _propRec[k.Name] = SubstRecLemma(k, rec, ind, iname);
        }
        string rl = RecTyLemma(ind);
        EnsureTowerLemmas();
        EnsurePf();
        var c = new PCtx { Ph = UHyp };
        Expr ty0 = _ops.InstantiateLevels(rec.Type, rec.LevelParams, k.Levels);
        string tyText = TrIn(c, ty0);
        int np = ind.NumParams, nm = rec.NumMinors, nb = np + rec.NumMotives + nm;
        Proof p = IntroPiProp(c, ty0, (d, body) =>
        {
            var vs = d.Binders.TakeLast(nb + 1).ToList();
            string motive = vs[np], tv = vs[^1];
            Statement st = pr.Database[rl];
            (string lante, _) = _d.Split(st.Expr);
            var lhyps = Conjuncts(lante).Reverse().ToList();   // U, params, motive, minors
            var sub = new Dictionary<string, string> { ["U"] = "U" };
            for (int i = 0; i < np; i++)
            {
                sub[ClassVars[i]] = vs[i];
            }
            sub[ClassVars[np]] = motive;
            string Inst(string text) => string.Join(' ', text.Split(' ').Select(tok => sub.TryGetValue(tok, out string? v) && pr.Parse("class", [tok]) is { Rule.Kind: 'f' } ? v : tok));
            var proofs = new List<Proof>();
            for (int h = 0; h < lhyps.Count; h++)
            {
                string hv = lhyps[h].Split(' ')[0];
                int ai = Array.IndexOf(ClassVars, hv);
                if (lhyps[h] == UHyp || ai < 0 || ai <= np - 1)
                {
                    proofs.Add(HypIn(d, Inst(lhyps[h])));
                    continue;
                }
                string dom = Inst(lhyps[h][(hv.Length + 4)..]);
                if (ai == np)
                {
                    // The motive, into 2o, is a motive into the whole tower.
                    string have = Conjuncts(d.Ph).First(x => x.StartsWith($"{motive} e. ", StringComparison.Ordinal))[(motive.Length + 4)..];
                    proofs.Add(Cumulate(d.Ph, motive, have, dom, HypIn(d, $"{motive} e. {have}")));
                    continue;
                }
                // Minor premise j: its witness, the map that is (/) everywhere.
                int j = ai - np - 1;
                string minorVar = vs[np + 1 + j];
                string holdsTy = Conjuncts(d.Ph).First(x => x.StartsWith($"{minorVar} e. ", StringComparison.Ordinal))[(minorVar.Length + 4)..];
                Proof holds = HypIn(d, $"(/) e. {holdsTy}");
                string w = Witness(dom, d.Ph);
                sub[hv] = w;
                proofs.Add(WitnessMem(d, w, dom, holds, holdsTy, motive, []));
            }
            Proof all = proofs.Skip(1).Aggregate(proofs[0], (acc, q) => _d.Jca(acc, q));
            foreach (Statement h in st.Hyps.Where(h => h.Kind == 'f'))
            {
                sub.TryAdd(h.Var!, h.Var!);
            }
            Proof li = pr.Apply(rl, sub);
            Proof sub1 = _d.Syl(all, li);
            SyntaxTree sn = pr.Parse("wff", _d.Split(sub1.Proves).X.Split(' '))!;
            string iapp = pr.Render(sn.Children[0]), q = pr.Render(sn.Children[1]);
            Proof tIn = pr.Apply("sseld", S(("ph", d.Ph), ("A", iapp), ("B", q), ("C", tv)), sub1);
            Proof tQ = pr.Apply("mpd", S(("ph", d.Ph), ("ps", $"{tv} e. {iapp}"), ("ch", $"{tv} e. {q}")), HypIn(d, $"{tv} e. {iapp}"), tIn);
            SyntaxTree qn = pr.Parse("class", q.Split(' '))!;
            string qv = pr.Render(qn.Children[1]), qb = pr.Render(qn.Children[0]);
            string pt = SubstFree(qb, qv, tv);
            Proof bi = _d.Syl(Exists(d.Ph, tv), pr.Apply("elabg", S(("x", qv), ("ph", qb), ("ps", pt), ("A", tv), ("V", "_V")), SubstEq("wff", qb, qv, $"{qv} = {tv}")));
            Proof inMt = pr.Apply("mpbid", S(("ph", d.Ph), ("ps", $"{tv} e. {q}"), ("ch", pt)), tQ, bi);
            SyntaxTree pn = pr.Parse("wff", pt.Split(' '))!;
            string elem = pr.Render(pn.Children[0]), mt = pr.Render(pn.Children[1]);
            Proof r = _d.Syl(_d.Jca(MotiveProp(d, motive, tv), inMt), pr.Apply("lean-pf", S(("A", mt), ("B", elem))));
            if (d.Vars[d.LastFv] == "(/)")
            {
                // Induction on a proposition: the major premise is a proof, written (/), and the member tv of the
                // proposition is (/) too (lean-pf0), so the motive holds there.
                EnsurePf0();
                Expr majTy = d.Types[d.LastFv];
                Proof isProp = FixMem(d.Ph, Check(d, majTy, InferIn(d, majTy), "2o"), iapp, "2o");
                Proof is0 = _d.Syl(_d.Jca(isProp, HypIn(d, $"{tv} e. {iapp}")), pr.Apply("lean-pf0", S(("A", iapp), ("B", tv))));
                Proof eq = _d.Congruence("class", Subst(mt, tv, "Z"), "Z", is0);
                r = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", mt), ("C", Rhs(eq))), r, eq);
            }
            return r;
        });
        string label = $"lean-ind-{LabelPart($"{iname}")}";
        EmitLemma(label, $"Induction on {iname}: its recursor at a motive into Prop.", p);
        _propRec[k.Name] = (label, tyText);
        return (label, tyText);
    }

    /// <summary>
    /// The recursor of a one-constructor proposition (Eq) at a motive into Prop: substitution. The major premise holds,
    /// so its condition does, equalities between the indices and the constructor's (b = a for Eq); the motive at the
    /// indices is then the motive at the constructor's, where the minor premise holds. (lean-subst-I)
    /// </summary>
    private (string, string) SubstRecLemma(Const k, ConstInfo rec, ConstInfo ind, Name iname)
    {
        EnsureTowerLemmas();
        var c = new PCtx { Ph = UHyp };
        Expr ty0 = _ops.InstantiateLevels(rec.Type, rec.LevelParams, k.Levels);
        string tyText = TrIn(c, ty0);
        int np = ind.NumParams, ni = ind.NumIndices, nb = np + rec.NumMotives + rec.NumMinors;
        string itok = Token(iname)!;
        Proof p = IntroPiProp(c, ty0, (d, body) =>
        {
            var vs = d.Binders.TakeLast(nb + ni + 1).ToList();
            string minorVar = vs[np + 1], majorVar = vs[^1];
            string Ty(string v) => Conjuncts(d.Ph).First(x => x.StartsWith($"{v} e. ", StringComparison.Ordinal))[(v.Length + 4)..];
            string pMinor = Ty(minorVar), pMajor = Ty(majorVar);
            Proof minor = HypIn(d, $"(/) e. {pMinor}"), major = HypIn(d, $"(/) e. {pMajor}");
            // The major premise's proposition, unfolded: if ( φ , 1o , (/) ), so φ.
            var iargs = vs.Take(np).Concat(vs.Skip(nb).Take(ni)).ToList();
            (Proof eqI, _, _) = Unfold(d.Ph, itok, iargs, (i, dom) => HypIn(d, $"{iargs[i]} e. {dom}"));
            Proof inIf = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", pMajor), ("C", Rhs(eqI))), major,
                AlphaIn(d.Ph, pMajor, Lhs(eqI)) is var a1 ? _d.Trans(a1, eqI) : eqI);
            SyntaxTree ifn = pr.Parse("class", Rhs(eqI).Split(' '))!;
            string phi = pr.Render(ifn.Children[0]);
            Proof holds = _d.Syl(inIf, Bi1(ApplyId("lean-prop", S(("ph", phi)))));
            // The equalities, index = term, rewrite the goal to the minor premise's proposition.
            var eqs = new List<Proof>();
            void Split(string w, Proof pw)
            {
                SyntaxTree wn = pr.Parse("wff", w.Split(' '))!;
                if (wn.Rule.Label == "wa")
                {
                    string l = pr.Render(wn.Children[0]), r = pr.Render(wn.Children[1]);
                    Split(l, pr.Apply("simpld", S(("ph", d.Ph), ("ps", l), ("ch", r)), pw));
                    Split(r, pr.Apply("simprd", S(("ph", d.Ph), ("ps", l), ("ch", r)), pw));
                }
                else if (wn.Rule.Label == "wceq")
                {
                    eqs.Add(pw);
                }
                else if (wn.Rule.Label != "wtru")
                {
                    throw new Refused($"{iname}'s condition isn't equalities: {w}");
                }
            }
            Split(phi, holds);
            string goal = TrIn(d, body);
            Proof cur = _d.Refl(d.Ph, goal);
            foreach (Proof e in eqs)
            {
                (string ix, string term, _) = _d.Sides(_d.Split(e.Proves).X);
                string ctx = SubstFree(Rhs(cur), ix, "Z");
                if (ctx.Split(' ').Contains("Z"))
                {
                    cur = _d.Trans(cur, _d.Congruence("class", ctx, "Z", e));
                }
            }
            Proof toMinor = _d.Trans(cur, AlphaIn(d.Ph, Rhs(cur), pMinor));
            return pr.Apply("eleqtrrd", S(("ph", d.Ph), ("A", "(/)"), ("B", pMinor), ("C", goal)), minor, toMinor);
        });
        string label = $"lean-subst-{LabelPart($"{iname}")}";
        EmitLemma(label, $"Substitution along {iname}: its recursor at a motive into Prop.", p);
        return (label, tyText);
    }

    /// <summary>( d.Ph -> ( M ` t ) e. 2o ), from M e. ( 2o ^m D ) and t e. D.</summary>
    private Proof MotiveProp(PCtx d, string motive, string tv)
    {
        string have = Conjuncts(d.Ph).First(x => x.StartsWith($"{motive} e. ", StringComparison.Ordinal))[(motive.Length + 4)..];
        SyntaxTree n = pr.Parse("class", have.Split(' '))!;
        string dom = pr.Render(n.Children[1]);
        return ApplyText(d.Ph, HypIn(d, $"{motive} e. {have}"), motive, have, tv, HypIn(d, $"{tv} e. {dom}")).Item1;
    }

    /// <summary>The map that is (/) everywhere, shaped like a minor premise's type (X_ and ^m over motive values).</summary>
    private string Witness(string ty, string ph)
    {
        SyntaxTree n = pr.Parse("class", ty.Split(' '))!;
        if (n.Rule.Label == "cixp")
        {
            string z = pr.Render(n.Children[0]), x = FreshFor(ty, ph);
            return $"( {x} e. {pr.Render(n.Children[1])} |-> {Witness(SubstFree(pr.Render(n.Children[2]), z, x), ph + " " + x)} )";
        }
        if (n.Rule.Label == "co" && pr.Render(n.Children[2]) == "^m")
        {
            string inner = Witness(pr.Render(n.Children[0]), ph);
            string v = FreshFor(ty, inner, ph);
            return $"( {v} e. {pr.Render(n.Children[1])} |-> {inner} )";
        }
        return "(/)";
    }

    /// <summary>
    /// ( d.Ph -> w e. ty ) for a witness w of a minor premise's type ty, given the minor premise holds,
    /// ( d.Ph -> (/) e. P ): under each binder, the minor premise is applied to the field, or, at an induction
    /// hypothesis p e. ( M ` r ), to (/), which is in ( M ` r ) since p is (lean-pf).
    /// </summary>
    private Proof WitnessMem(PCtx d, string w, string ty, Proof holds, string holdsTy, string motive, List<string> applied)
    {
        SyntaxTree n = pr.Parse("class", ty.Split(' '))!;
        SyntaxTree wn = pr.Parse("class", w.Split(' '))!;
        if (wn.Rule.Label != "cmpt")
        {
            // At a motive value: the minor premise, applied all the way, holds there.
            if (!holdsTy.StartsWith("if ( A. ", StringComparison.Ordinal))
            {
                Proof h0 = holds;
                return FixMem(d.Ph, h0, w, ty);
            }
            throw new Refused($"a minor premise with more binders than its type: {holdsTy}");
        }
        string x = pr.Render(wn.Children[0]), dom = pr.Render(wn.Children[1]), body = pr.Render(wn.Children[2]);
        bool dep = n.Rule.Label == "cixp";
        string cod = dep ? SubstFree(pr.Render(n.Children[2]), pr.Render(n.Children[0]), x) : pr.Render(n.Children[0]);
        if (d.Ph.Split(' ').Contains(x))
        {
            throw new Refused($"a witness variable {x} occurs in the hypotheses");
        }
        PCtx e = EnterText(d, x, dom);
        Proof hw = Weaken(holds, $"{x} e. {dom}");
        // Apply the minor premise to this binder: the field itself, or (/) for an induction hypothesis.
        string arg = dep ? x : "(/)";
        (Proof h2, string inst) = TextApplyProp(e.Ph, hw, holdsTy, arg, dm =>
        {
            if (dep)
            {
                return dm == dom ? Hyp(e.Ph, $"{x} e. {dom}")!.Value
                    : pr.Apply("eleqtrd", S(("ph", e.Ph), ("A", x), ("B", dom), ("C", dm)), Hyp(e.Ph, $"{x} e. {dom}")!.Value, AlphaIn(e.Ph, dom, dm));
            }
            // (/) e. ( M ` r ), since x e. ( M ` r ) and ( M ` r ) is a proposition.
            SyntaxTree mr = pr.Parse("class", dom.Split(' '))!;
            string r = pr.Render(mr.Children[0]);
            Proof isProp = MotiveProp(e, motive, r);
            Proof pf = _d.Syl(_d.Jca(isProp, Hyp(e.Ph, $"{x} e. {dom}")!.Value), pr.Apply("lean-pf", S(("A", dom), ("B", x))));
            return dm == dom ? pf : pr.Apply("eleqtrd", S(("ph", e.Ph), ("A", "(/)"), ("B", dom), ("C", dm)), pf, AlphaIn(e.Ph, dom, dm));
        });
        string holds2 = inst.StartsWith("(/) e. ", StringComparison.Ordinal) ? inst[7..] : throw new Refused($"expected (/) e. …, got {inst}");
        Proof q = FixMem(e.Ph, WitnessMem(e, body, cod, h2, holds2, motive, [.. applied, arg]), body, cod);
        Proof ral = pr.Apply("ralrimiva", S(("ph", d.Ph), ("ps", $"{body} e. {cod}"), ("x", x), ("A", dom)), q);
        if (dep)
        {
            string tyX = $"X_ {x} e. {dom} {cod}";
            Proof bi = _d.Syl(Exists(d.Ph, dom), pr.Apply("mptelixpg", S(("x", x), ("I", dom), ("J", body), ("K", cod), ("V", "_V"))));
            Proof inX = pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"{w} e. {tyX}"), ("ch", $"A. {x} e. {dom} {body} e. {cod}")), ral, bi);
            return FixMem(d.Ph, inX, w, ty);
        }
        Proof fmap = pr.Apply("fmpt", S(("x", x), ("A", dom), ("C", body), ("B", cod), ("F", w)), pr.Apply("eqid", S(("A", w))));
        Proof fn = pr.Apply("sylib", S(("ph", d.Ph), ("ps", $"A. {x} e. {dom} {body} e. {cod}"), ("ch", $"{w} : {dom} --> {cod}")), ral, fmap);
        Proof bi2 = pr.Apply("elmapd", S(("ph", d.Ph), ("A", cod), ("B", dom), ("C", w), ("V", "_V"), ("W", "_V")), Exists(d.Ph, cod), Exists(d.Ph, dom));
        return pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"{w} e. {ty}"), ("ch", $"{w} : {dom} --> {cod}")), fn, bi2);
    }
}
