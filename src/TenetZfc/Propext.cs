using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// propext holds in the model (docs/milestone3.md, "Theorems through the model"): a proposition is (/) or 1o, so two
/// that hold together are equal. Its typing lemma, (/) e. ⟦∀ a b : Prop, (a ↔ b) → a = b⟧, is proved from
/// lean-2oif, |- ( A e. 2o -> A = if ( (/) e. A , 1o , (/) ) ): a proposition is determined by whether it holds.
/// </summary>
public sealed partial class Model
{
    /// <summary>lean-2oif and lean-ifn0, once.</summary>
    private void EnsurePropLemmas()
    {
        if (Has("lean-2oif"))
        {
            return;
        }
        // lean-ifn0: |- ( if ( ph , 1o , (/) ) =/= (/) -> ph ).
        {
            Proof f = pr.Apply("iffalse", S(("ph", "ph"), ("A", "1o"), ("B", "(/)")));
            EmitLemma("lean-ifn0", "A proposition of the model that isn't empty holds.",
                pr.Apply("necon1ai", S(("ph", "ph"), ("A", "if ( ph , 1o , (/) )"), ("B", "(/)")), f));
        }
        // lean-2oif: |- ( A e. 2o -> A = if ( (/) e. A , 1o , (/) ) ), by cases A = (/) and A = 1o.
        {
            const string ifA = "if ( (/) e. A , 1o , (/) )";
            // A = (/): (/) isn't in it, so the if is (/).
            Proof notIn = pr.Apply("mtbird", S(("ph", "A = (/)"), ("ps", "(/) e. A"), ("ch", "(/) e. (/)")),
                _d.Lift("A = (/)", pr.Apply("noel", S(("A", "(/)")))), pr.Apply("eleq2", S(("A", "A"), ("B", "(/)"), ("C", "(/)"))));
            Proof c0 = pr.Apply("eqtr4d", S(("ph", "A = (/)"), ("A", "A"), ("B", "(/)"), ("C", ifA)),
                pr.Apply("id", S(("ph", "A = (/)"))), pr.Apply("iffalsed", S(("ph", "A = (/)"), ("ch", "(/) e. A"), ("A", "1o"), ("B", "(/)")), notIn));
            // A = 1o: (/) is in it, so the if is 1o.
            Proof isIn = pr.Apply("mpbiri", S(("ph", "A = 1o"), ("ps", "(/) e. A"), ("ch", "(/) e. 1o")), pr.Apply("0lt1o", S()),
                pr.Apply("eleq2", S(("A", "A"), ("B", "1o"), ("C", "(/)"))));
            Proof c1 = pr.Apply("eqtr4d", S(("ph", "A = 1o"), ("A", "A"), ("B", "1o"), ("C", ifA)),
                pr.Apply("id", S(("ph", "A = 1o"))), pr.Apply("iftrued", S(("ph", "A = 1o"), ("ch", "(/) e. A"), ("A", "1o"), ("B", "(/)")), isIn));
            Proof both = pr.Apply("jaoi", S(("ph", "A = (/)"), ("ps", $"A = {ifA}"), ("ch", "A = 1o")), c0, c1);
            Proof inPr = pr.Apply("eleqtrd", S(("ph", "A e. 2o"), ("A", "A"), ("B", "2o"), ("C", "{ (/) , 1o }")),
                pr.Apply("id", S(("ph", "A e. 2o"))), _d.Lift("A e. 2o", pr.Apply("df2o3", S())));
            Proof cases = _d.Syl(inPr, pr.Apply("elpri", S(("A", "A"), ("B", "(/)"), ("C", "1o"))));
            EmitLemma("lean-2oif", "A proposition of the model is determined by whether it holds.", _d.Syl(cases, both));
        }
    }

    /// <summary>lean-ty-propext: (/) e. ⟦propext's type⟧.</summary>
    private Proof PropextTyping(PCtx c, Expr ty)
    {
        EnsureTowerLemmas();
        EnsurePropLemmas();
        Define(t.Of("Iff"));
        return IntroPiProp(c, ty, (d, body) =>
        {
            var vs = d.Binders.TakeLast(3).ToList();
            string a = vs[0], b = vs[1], h = vs[2];
            string Ty(string v) => Conjuncts(d.Ph).First(x => x.StartsWith($"{v} e. ", StringComparison.Ordinal))[(v.Length + 4)..];
            string iffApp = Ty(h);
            Proof hIff = HypIn(d, $"(/) e. {iffApp}");
            // Iff a b unfolds to if ( E. z e. ( a -> b ) E. w e. ( b -> a ) T. , 1o , (/) ).
            (Proof eqIff, _, _) = Unfold(d.Ph, Token(t.Of("Iff"))!, [a, b], (i, dom) => HypIn(d, $"{(i == 0 ? a : b)} e. {dom}"));
            Proof inIf = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", iffApp), ("C", Rhs(eqIff))), hIff, _d.Trans(AlphaIn(d.Ph, iffApp, Lhs(eqIff)), eqIff));
            SyntaxTree ifn = pr.Parse("class", Rhs(eqIff).Split(' '))!;
            string phi = pr.Render(ifn.Children[0]);
            Proof phiP = _d.Syl(inIf, Bi1(ApplyId("lean-prop", S(("ph", phi)))));
            // phi = E. z e. P1 E. w e. P2 T.: each Pi is nonempty, so holds.
            SyntaxTree pn = pr.Parse("wff", phi.Split(' '))!;
            string inner = pr.Render(pn.Children[0]), z = pr.Render(pn.Children[1]), p1 = pr.Render(pn.Children[2]);
            SyntaxTree inn = pr.Parse("wff", inner.Split(' '))!;
            string w = pr.Render(inn.Children[1]), p2 = pr.Render(inn.Children[2]);
            Proof Holds(Proof ex, string rexBody, string v, string dom)
            {
                Proof ne = _d.Syl(ex, pr.Apply("rexn0", S(("x", v), ("A", dom), ("ph", rexBody))));
                SyntaxTree dn = pr.Parse("class", dom.Split(' '))!;
                return _d.Syl(ne, ApplyId("lean-ifn0", S(("ph", pr.Render(dn.Children[0])))));
            }
            Proof psi1 = Holds(phiP, inner, z, p1);
            Proof innerP = _d.Syl(phiP, pr.Apply("rexlimiv", S(("x", z), ("A", p1), ("ph", inner), ("ps", inner)),
                pr.Apply("a1i", S(("ph", $"( {inner} -> {inner} )"), ("ps", $"{z} e. {p1}")), pr.Apply("id", S(("ph", inner))))));
            Proof psi2 = Holds(innerP, pr.Render(inn.Children[0]), w, p2);
            // ψ1 = A. v e. a (/) e. b and ψ2 = A. v e. b (/) e. a give ( (/) e. a <-> (/) e. b ).
            Proof Imp(Proof psi, string from, string to)
            {
                SyntaxTree qn = pr.Parse("wff", _d.Split(psi.Proves).X.Split(' '))!;
                string v = pr.Render(qn.Children[1]), qb = pr.Render(qn.Children[0]);
                Proof inst = pr.Apply("rspcv", S(("x", v), ("A", "(/)"), ("B", from), ("ph", qb), ("ps", $"(/) e. {to}")), SubstEq("wff", qb, v, $"{v} = (/)"));
                return pr.Apply("com12", S(("ph", $"(/) e. {from}"), ("ps", $"A. {v} e. {from} {qb}"), ("ch", $"(/) e. {to}")), inst) is var sw
                    ? _d.Syl(psi, sw) : default;
            }
            Proof ab = Imp(psi1, a, b), ba = Imp(psi2, b, a);
            Proof iff = pr.Apply("impbid", S(("ph", d.Ph), ("ps", $"(/) e. {a}"), ("ch", $"(/) e. {b}")), ab, ba);
            Proof ia = _d.Syl(HypIn(d, $"{a} e. 2o"), ApplyId("lean-2oif", S(("A", a))));
            Proof ib = _d.Syl(HypIn(d, $"{b} e. 2o"), ApplyId("lean-2oif", S(("A", b))));
            Proof ifs = pr.Apply("ifbid", S(("ph", d.Ph), ("ps", $"(/) e. {a}"), ("ch", $"(/) e. {b}"), ("A", "1o"), ("B", "(/)")), iff);
            Proof aEqB = _d.Trans(_d.Trans(ia, ifs), _d.Symm(ib));
            // The goal, Eq Prop a b, unfolds to if ( b = a , 1o , (/) ).
            Expr prop = t.Sort(t.Zero);
            string goal = TrIn(d, body);
            Expr head = Ops.Spine(body, out List<Expr> eargs);
            var etexts = eargs.Select(x => TrIn(d, x)).ToList();
            (Proof eqEq, _, _) = Unfold(d.Ph, Token(((Const)head).Name)!, etexts, (i, dom) => i == 0 ? UnivMem(d, etexts[0], dom) : HypIn(d, $"{etexts[i]} e. {dom}"));
            SyntaxTree en = pr.Parse("class", Rhs(eqEq).Split(' '))!;
            string cond = pr.Render(en.Children[0]);
            Proof condP = cond == $"{b} = {a}" ? _d.Symm(aEqB) : cond == $"{a} = {b}" ? aEqB : throw new Refused($"Eq unfolds to {Rhs(eqEq)}");
            Proof one = _d.Trans(eqEq, pr.Apply("iftrued", S(("ph", d.Ph), ("ch", cond), ("A", "1o"), ("B", "(/)")), condP));
            Proof r = pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"(/) e. {Lhs(eqEq)}"), ("ch", "(/) e. 1o")),
                _d.Lift(d.Ph, pr.Apply("0lt1o", S())), pr.Apply("eleq2d", S(("ph", d.Ph), ("A", Lhs(eqEq)), ("B", "1o"), ("C", "(/)")), one));
            _ = prop;
            return FixMem(d.Ph, r, "(/)", goal);
        });
    }
}
