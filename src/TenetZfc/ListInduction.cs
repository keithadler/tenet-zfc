using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Translates a proof by List.rec into Prop: Lean's induction adds at the front of a list, set.mm's wrdind adds at the
/// end of a word, so wrdind is applied to the motive composed with word reversal, ψ(x) := φ(reverse x). Then
/// ψ((/)) is the nil case (rev0), the step ψ(y) → ψ(y ++ ⟨z⟩) is the cons case for tail reverse y and head z
/// (revccat, revs1), wrdind gives ψ(reverse B), and revrev turns that into φ(B). Both cases are translated from
/// Lean's own proof term by <see cref="ProofTranslator"/>; the substitution hypotheses come from the congruence prover.
///
/// Handled shape: fun α xs ys => List.rec α motive nil cons xs, a theorem about two lists over one type with
/// induction on the first (List.length_append's). Others are refused with the reason.
/// </summary>
public sealed class ListInduction(Terms t, Environment env, Prover pr)
{
    private readonly Ops _ops = new(t);
    private readonly Deduction _d = new(pr);

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>The distinct-variable conditions the emitted theorem needs: the dummy set variables x, y, z apart from everything.</summary>
    public static readonly string[] Distinct = ["x y z A", "x y z B", "x y z C"];

    public (Proof? Proof, string? Why) Prove(ConstInfo thm)
    {
        // fun α xs ys => List.rec α motive nil cons xs
        Expr v = thm.Value!;
        ulong id = 1UL << 59;
        Expr Fresh() => t.FVar(id++);
        if (v is not Binder { IsPi: false } b1 || b1.Domain is not Sort)
        {
            return (null, "not a proof over a type variable");
        }
        Expr alpha = Fresh();
        if (_ops.Instantiate(b1.Body, [alpha]) is not Binder { IsPi: false } b2)
        {
            return (null, "not a proof over two lists");
        }
        Expr xs = Fresh();
        if (_ops.Instantiate(b2.Body, [xs]) is not Binder { IsPi: false } b3)
        {
            return (null, "not a proof over two lists");
        }
        Expr ys = Fresh();
        Expr body = _ops.Instantiate(b3.Body, [ys]);
        Expr listTy = _ops.Instantiate(b2.Domain, []);
        Expr ysTy = _ops.Instantiate(b3.Domain, [xs]);
        if (Ops.Spine(body, out List<Expr> args) is not Const rec || rec.Name.ToString() != "List.rec" || args.Count != 5 || !ReferenceEquals(args[4], xs))
        {
            return (null, "not an induction on the first list");
        }
        Expr motive = args[1], nilCase = args[2], consCase = args[3];
        Level[] lv = ((Const)Ops.Head(listTy)).Levels;

        // φ(X): the motive at a class term X, other variables as in the statement (α = A, xs = B, ys = C).
        var st = new StatementTranslator(t);
        string Phi(string x)
        {
            st.Reset();
            st.Bind(alpha, "A");
            st.Bind(ys, "C");
            st.Bind(xs, x);
            return st.Wff(Beta(t.App(motive, xs))) ?? throw new InvalidOperationException($"the motive is outside the table: {st.Why}");
        }
        const string oh = "C e. Word A";
        string Psi(string x) => $"( {oh} -> {Phi($"( reverse ` {x} )")} )";

        var tr = new ProofTranslator(t, env, pr);

        // Base: ψ((/)), from the nil case and rev0.
        tr.Begin([(alpha, "A")], "A", [(ys, "C", ysTy, false)]);
        Proof nil = tr.ProveAs(nilCase, t.App(motive, t.App(t.Const(t.Of("List.nil"), lv), alpha)));
        Proof rev0 = _d.Lift(oh, (["rev0"], MmExpr.Of("|- ( reverse ` (/) ) = (/)")));
        Proof baseCase = Rewrite(oh, nil, Phi("Z"), "Z", rev0);

        // Step: ( ( y e. Word A /\ z e. A ) -> ( ψ(y) -> ψ(( y ++ <" z "> )) ) ), from the cons case at tail reverse y.
        var c1 = (Binder)consCase;
        Expr hd = Fresh();
        var c2 = (Binder)_ops.Instantiate(c1.Body, [hd]);
        Expr tl = Fresh();
        var c3 = (Binder)_ops.Instantiate(c2.Body, [tl]);
        Expr ih = Fresh();
        tr.Begin([(alpha, "A")], "A", [(ys, "C", ysTy, false), (hd, "z", c1.Domain, false), (tl, "( reverse ` y )", _ops.Instantiate(c2.Domain, [hd]), false), (ih, "", c3.Domain, true)]);
        Proof cons = tr.ProveAs(_ops.Instantiate(c3.Body, [ih]), t.App(motive, t.MkApp(t.Const(t.Of("List.cons"), lv), [alpha, hd, tl])));
        Proof step = Step(cons, Phi);

        // Substitution hypotheses: ( x = T -> ( ψ(x) <-> ψ(T) ) ).
        Proof Subst(string target) => _d.Congruence("wff", Psi("Z"), "Z", pr.Apply("id", S(("ph", $"x = {target}"))));
        Proof h1 = Subst("(/)"), h2 = Subst("y"), h3 = Subst("( y ++ <\" z \"> )"), h4 = Subst("( reverse ` B )");

        // wrdind at A := reverse B: |- ( ( reverse ` B ) e. Word A -> ψ(reverse B) ).
        Proof ind = pr.Apply("wrdind", S(("ph", Psi("x")), ("ps", Psi("(/)")), ("ch", Psi("y")), ("th", Psi("( y ++ <\" z \"> )")),
                ("ta", Psi("( reverse ` B )")), ("x", "x"), ("y", "y"), ("z", "z"), ("A", "( reverse ` B )"), ("B", "A")),
            h1, h2, h3, h4, baseCase, step);

        // Under ( B e. Word A /\ C e. Word A ): ψ(reverse B), then C, then revrev.
        const string h = "( B e. Word A /\\ C e. Word A )";
        Proof pB = pr.Apply("simpl", S(("ph", "B e. Word A"), ("ps", oh)));
        Proof pC = pr.Apply("simpr", S(("ph", "B e. Word A"), ("ps", oh)));
        Proof psiRev = _d.Syl(_d.Syl(pB, pr.Apply("revcl", S(("W", "B"), ("A", "A")))), ind);
        Proof bodyRevRev = pr.Apply("mpd", S(("ph", h), ("ps", oh), ("ch", Phi("( reverse ` ( reverse ` B ) )"))), pC, psiRev);
        Proof revrev = _d.Syl(pB, pr.Apply("revrev", S(("W", "B"), ("A", "A"))));
        Proof final = Rewrite(h, bodyRevRev, Phi("Z"), "Z", revrev, forward: true);
        // The proof's conclusion comes from its motive; it must be the theorem's own statement, translated.
        string? stated = new StatementTranslator(t).Statement(thm.Type);
        if (stated != final.Proves.ToString())
        {
            return (null, $"the proof concludes {final.Proves}, but the theorem states {stated ?? "something outside the table"}");
        }
        return (final, null);
    }

    /// <summary>
    /// From |- ( H -> P[b] ) and |- ( H -> a = b ), with P written over the hole: |- ( H -> P[a] ) (or, forward,
    /// from |- ( H -> P[a] ): |- ( H -> P[b] )).
    /// </summary>
    private Proof Rewrite(string h, Proof have, string context, string hole, Proof eq, bool forward = false)
    {
        Proof bi = _d.Congruence("wff", context, hole, eq);   // ( H -> ( P[a] <-> P[b] ) )
        (string pa, string pb, _) = _d.Sides(_d.Split(bi.Proves).X);
        return forward
            ? pr.Apply("mpbid", S(("ph", h), ("ps", pa), ("ch", pb)), have, bi)
            : pr.Apply("mpbird", S(("ph", h), ("ps", pa), ("ch", pb)), have, bi);
    }

    /// <summary>The induction step, from the translated cons case under ( ( ( C /\ z ) /\ rev y ) /\ ih ).</summary>
    private Proof Step(Proof cons, Func<string, string> phi)
    {
        const string oh = "C e. Word A", y = "( y e. Word A /\\ z e. A )";
        string ihW = phi("( reverse ` y )");
        string cih = $"( {oh} -> {ihW} )";
        string h3 = $"( ( {y} /\\ {cih} ) /\\ {oh} )";
        Proof pA = pr.Apply("simpl", S(("ph", $"( {y} /\\ {cih} )"), ("ps", oh)));
        Proof pY = _d.Syl(pA, pr.Apply("simpl", S(("ph", y), ("ps", cih))));
        Proof pyW = _d.Syl(pY, pr.Apply("simpl", S(("ph", "y e. Word A"), ("ps", "z e. A"))));
        Proof pz = _d.Syl(pY, pr.Apply("simpr", S(("ph", "y e. Word A"), ("ps", "z e. A"))));
        Proof pCih = _d.Syl(pA, pr.Apply("simpr", S(("ph", y), ("ps", cih))));
        Proof pOh = pr.Apply("simpr", S(("ph", $"( {y} /\\ {cih} )"), ("ps", oh)));
        Proof pIh = pr.Apply("mpd", S(("ph", h3), ("ps", oh), ("ch", ihW)), pOh, pCih);
        Proof pRev = _d.Syl(pyW, pr.Apply("revcl", S(("W", "y"), ("A", "A"))));
        // The cons case's hypotheses, all under h3.
        Proof h2 = _d.Jca(_d.Jca(_d.Jca(pOh, pz), pRev), pIh);
        Proof goal = _d.Syl(h2, cons);   // ( h3 -> φ(<" z "> ++ reverse y) )
        // reverse ( y ++ <" z "> ) = ( <" z "> ++ reverse y )
        Proof s1 = pr.Apply("s1cld", S(("ph", h3), ("A", "z"), ("B", "A")), pz);
        Proof e1 = pr.Apply("syl2anc", S(("ph", h3), ("ps", "y e. Word A"), ("ch", "<\" z \"> e. Word A"),
                ("th", "( reverse ` ( y ++ <\" z \"> ) ) = ( ( reverse ` <\" z \"> ) ++ ( reverse ` y ) )")),
            pyW, s1, pr.Apply("revccat", S(("S", "y"), ("T", "<\" z \">"), ("A", "A"))));
        Proof e2 = pr.Apply("oveq1d", S(("ph", h3), ("A", "( reverse ` <\" z \"> )"), ("B", "<\" z \">"), ("C", "( reverse ` y )"), ("F", "++")),
            _d.Lift(h3, pr.Apply("revs1", S(("S", "z")))));
        Proof g2 = Rewrite(h3, goal, phi("Z"), "Z", _d.Trans(e1, e2));   // ( h3 -> φ(reverse ( y ++ <" z "> )) )
        Proof ex1 = pr.Apply("ex", S(("ph", $"( {y} /\\ {cih} )"), ("ps", oh), ("ch", phi("( reverse ` ( y ++ <\" z \"> ) )"))), g2);
        return pr.Apply("ex", S(("ph", y), ("ps", cih), ("ch", $"( {oh} -> {phi("( reverse ` ( y ++ <\" z \"> ) )")} )")), ex1);
    }

    private Expr Beta(Expr e)
    {
        Expr head = Ops.Spine(e, out List<Expr> args);
        if (head is Binder { IsPi: false } lam && args.Count > 0)
        {
            return Beta(t.MkApp(_ops.Instantiate(lam.Body, [args[0]]), args.Skip(1)));
        }
        return e;
    }
}
