using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Induction on a proposition with several constructors and no indices, not recursive (Or): its recursor at a motive
/// into Prop, typed for the theorem translator (docs/milestone3.md, "Theorems across Init").
/// </summary>
public sealed partial class Model
{
    /// <summary>
    /// lean-ind-I for such a proposition I. Under the recursor's binders (params, motive M, minors, major t), the goal
    /// is (/) e. ( M ` (/) ): every proof is (/). The major premise makes I's condition hold, a disjunction of the
    /// constructors' cases, E. z1 e. D1 … ψ over their fields (ProveCase builds the same disjunction). In case j each
    /// field's proposition D_i holds, since z_i is in it (lean-pf), so minor premise j, a Π-proposition over the fields,
    /// applies at (/) for each, and gives ( M ` (/) ) (jaod over the cases, rexlimdva over the fields).
    /// </summary>
    private (string, string) PropCasesRecLemma(Const k, ConstInfo rec, ConstInfo ind, Name iname)
    {
        EnsureTowerLemmas();
        EnsurePf();
        var c = new PCtx { Ph = UHyp };
        Expr ty0 = _ops.InstantiateLevels(rec.Type, rec.LevelParams, k.Levels);
        string tyText = TrIn(c, ty0);
        int np = ind.NumParams, nm = rec.NumMinors, nb = np + rec.NumMotives + nm;
        string itok = Token(iname)!;
        Proof p = IntroPiProp(c, ty0, (d, body) =>
        {
            var vs = d.Binders.TakeLast(nb + 1).ToList();
            string Ty(string v) => Conjuncts(d.Ph).First(x => x.StartsWith($"{v} e. ", StringComparison.Ordinal))[(v.Length + 4)..];
            string goal = $"(/) e. {TrIn(d, body)}";
            string pMajor = Ty(vs[^1]);
            Proof major = HypIn(d, $"(/) e. {pMajor}");
            var texts = d.Vars.Values.ToHashSet();
            var iargs = vs.Take(np).Select(v => texts.Contains(v) ? v : "(/)").ToList();
            (Proof eqI, _, _) = Unfold(d.Ph, itok, iargs, (i, dom) => HypIn(d, $"{iargs[i]} e. {dom}"));
            Proof inIf = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", pMajor), ("C", Rhs(eqI))), major,
                AlphaIn(d.Ph, pMajor, Lhs(eqI)) is var a1 ? _d.Trans(a1, eqI) : eqI);
            SyntaxTree ifn = pr.Parse("class", Rhs(eqI).Split(' '))!;
            if (ifn.Rule.Label != "cif")
            {
                throw new Refused($"{iname} doesn't unfold to a proposition: {Rhs(eqI)}");
            }
            string cond = pr.Render(ifn.Children[0]);
            Proof holds = _d.Syl(inIf, Bi1(ApplyId("lean-prop", S(("ph", cond)))));

            // ( ctx -> ( w -> goal ) ) for case j, w = E. z1 e. D1 … ψ: down the fields, then minor j at (/) for each.
            Proof Case(string ctx, string w, int j, List<string> fields)
            {
                SyntaxTree n = pr.Parse("wff", w.Split(' '))!;
                if (n.Rule.Label == "wrex")
                {
                    string wbody = pr.Render(n.Children[0]), a = pr.Render(n.Children[1]), dom = pr.Render(n.Children[2]);
                    if (ctx.Split(' ').Contains(a) || goal.Split(' ').Contains(a))
                    {
                        string a2 = FreshFor(ctx, w, goal);
                        string w2 = $"E. {a2} e. {dom} {SubstFree(wbody, a, a2)}";
                        Proof eqv = _d.Lift(ctx, pr.Apply("mptru", S(("ph", $"( {w} <-> {w2} )")), Alpha("wff", w, w2)!.Value));
                        return pr.Apply("sylbid", S(("ph", ctx), ("ps", w), ("ch", w2), ("th", goal)), eqv, Case(ctx, w2, j, fields));
                    }
                    string ctx2 = $"( {ctx} /\\ {a} e. {dom} )";
                    Proof inner = Case(ctx2, wbody, j, [.. fields, a]);
                    return pr.Apply("rexlimdva", S(("ph", ctx), ("x", a), ("A", dom), ("ps", wbody), ("ch", goal)), inner);
                }
                // The fields are entered: apply minor j to (/) once per field.
                string minor = vs[np + 1 + j];
                string ty = Ty(minor);
                Proof m = WeakenTo(ctx, HypIn(d, $"(/) e. {ty}"));
                foreach (string f in fields)
                {
                    string fdom = Conjuncts(ctx).First(x => x.StartsWith($"{f} e. ", StringComparison.Ordinal))[(f.Length + 4)..];
                    if (fields.Any(g => fdom.Split(' ').Contains(g)))
                    {
                        throw new Refused($"{iname}'s case {j} has a field whose proposition mentions another field: {fdom}");
                    }
                    (m, string inst) = TextApplyProp(ctx, m, ty, "(/)", dom => dom == fdom
                        ? Inhabited(ctx, f, fdom)
                        : pr.Apply("eleqtrd", S(("ph", ctx), ("A", "(/)"), ("B", fdom), ("C", dom)), Inhabited(ctx, f, fdom), AlphaIn(ctx, fdom, dom)));
                    ty = inst[7..];
                }
                string got = $"(/) e. {ty}";
                Proof g = got == goal ? m : pr.Apply("eleqtrd", S(("ph", ctx), ("A", "(/)"), ("B", ty), ("C", goal[7..])), m, AlphaIn(ctx, ty, goal[7..]));
                return pr.Apply("a1d", S(("ph", ctx), ("ps", goal), ("ch", w)), g);
            }
            // ( d.Ph -> ( cond -> goal ) ) over the left-nested disjunction of the cases.
            Proof Cases(string w, int count)
            {
                if (count == 1)
                {
                    return Case(d.Ph, w, 0, []);
                }
                SyntaxTree n = pr.Parse("wff", w.Split(' '))!;
                if (n.Rule.Label != "wo")
                {
                    throw new Refused($"a proposition's cases aren't a disjunction: {w}");
                }
                string l = pr.Render(n.Children[0]), r = pr.Render(n.Children[1]);
                Proof left = count == 2 ? Case(d.Ph, l, 0, []) : Cases(l, count - 1);
                return pr.Apply("jaod", S(("ph", d.Ph), ("ps", l), ("ch", goal), ("th", r)), left, Case(d.Ph, r, count - 1, []));
            }
            return pr.Apply("mpd", S(("ph", d.Ph), ("ps", cond), ("ch", goal)), holds, Cases(cond, ind.Ctors.Length));
        });
        string label = $"lean-ind-{LabelPart($"{iname}")}";
        EmitLemma(label, $"Induction on {iname}: its recursor at a motive into Prop, by cases.", p);
        _propRec[k.Name] = (label, tyText);
        return (label, tyText);
    }

    /// <summary>( ctx -> X ) from ( d.Ph -> X ), ctx being d.Ph with more conjuncts on the right.</summary>
    private Proof WeakenTo(string ctx, Proof p)
    {
        (string h, string x) = _d.Split(p.Proves);
        while (ctx != h)
        {
            SyntaxTree n = pr.Parse("wff", ctx.Split(' '))!;
            if (n.Rule.Label != "wa")
            {
                throw new Refused($"{h} isn't a part of {ctx}");
            }
            string l = pr.Render(n.Children[0]);
            p = WeakenTo(l, p);
            return pr.Apply("adantr", S(("ph", l), ("ps", x), ("ch", pr.Render(n.Children[1]))), p);
        }
        return p;
    }

    /// <summary>
    /// ( ctx -> (/) e. dom ) from ctx's a e. dom, dom a proposition: a hypothesis dom e. 2o (lean-pf), or dom itself
    /// if ( χ , 1o , (/) ) (elif0, lean-prop).
    /// </summary>
    private Proof Inhabited(string ctx, string a, string dom)
    {
        Proof aIn = Hyp(ctx, $"{a} e. {dom}") ?? throw new Refused($"no hypothesis {a} e. {dom}");
        if (Hyp(ctx, $"{dom} e. 2o") is Proof isProp)
        {
            EnsurePf();
            return _d.Syl(_d.Jca(isProp, aIn), pr.Apply("lean-pf", S(("A", dom), ("B", a))));
        }
        SyntaxTree dn = pr.Parse("class", dom.Split(' '))!;
        if (dn.Rule.Label == "cif" && pr.Render(dn.Children[1]) == "1o" && pr.Render(dn.Children[2]) == "(/)")
        {
            string chi = pr.Render(dn.Children[0]);
            Proof c2 = _d.Syl(aIn, Bi1(pr.Apply("elif0", S(("A", a), ("ph", chi), ("B", "1o")))));
            Proof chiP = pr.Apply("simpld", S(("ph", ctx), ("ps", chi), ("ch", $"{a} e. 1o")), c2);
            EnsureTowerLemmas();
            return _d.Syl(chiP, Bi2(ApplyId("lean-prop", S(("ph", chi)))));
        }
        throw new Refused($"a proof field whose proposition the translator can't show is one: {dom}");
    }
}
