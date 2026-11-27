using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Universe elimination (docs/milestone4.md): ZFC proves that a lowered tower exists, so a theorem proved under
/// U e. lean.-wtower whose statement doesn't mention U holds with no hypothesis.
///
/// The witness is lean.-wit = ( n e. _om |-> ( R1 ` ( _om .o ( _om .o suc n ) ) ) ): R1 at the limit ordinals
/// omega^2 (n + 1). Each level is a weak universe (r1limwun); it contains omega; each is a member of the next (r1ord);
/// and each is reflecting: for x in R1 ( lambda ), rank x + omega is still below lambda, because lambda is omega times a
/// limit ordinal (lean-wit-add), so R1 ( rank x + omega ) is in R1 ( lambda ). No Grothendieck universe and no ax-groth:
/// only set.mm's ordinal arithmetic and the cumulative hierarchy, which ZF proves.
/// </summary>
public sealed class TowerWitness(Prover pr, ProofKit k, Action<string, string, Proof> thm)
{
    public const string Wit = "lean.-wit";
    public const string Definiens = "( n e. _om |-> ( R1 ` ( _om .o ( _om .o suc n ) ) ) )";

    private Database Db => pr.Database;

    private Proof Use(string label, params Proof[] h) => k.Use(label, h);
    private Proof UseS(string label, (string, string)[] s, params Proof[] h) => k.UseS(label, s, h);
    private Proof Imp(string? h, string label, Proof[] premises, (string, string)[]? s = null, Proof[]? closed = null) =>
        k.Imp(h, label, premises, null, s, closed);
    private Proof Hyp(string h, string c) => k.Hyp(h, c);
    private Proof Lift(string h, Proof p) => k.Lift(h, p);
    private Proof Jca(Proof a, Proof b) => k.Jca(a, b);
    private Proof Ax(string label) => k.UseG(label, string.Join(' ', Db[label].Expr.Symbols));
    private Proof SubBi(string x, string to, string body) => k.Cong("wff", ProofKit.Replace(body, x, "Y"), "Y", UseS("id", [("ph", $"{x} = {to}")]));
    private Proof SubEq(string x, string to, string body) => k.CongEq(ProofKit.Replace(body, x, "Y"), "Y", UseS("id", [("ph", $"{x} = {to}")]));

    private static string Lam(string n) => $"( _om .o ( _om .o suc {n} ) )";

    /// <summary>
    /// Prove lean-wit-tw, |- lean.-wit e. lean.-wtower, with the lemmas before it, once. The definitions df-lean.-wit,
    /// df-lean.-wuni and df-lean.-wtower must be in the database; <paramref name="condF"/> is what f e. lean.-wtower says.
    /// </summary>
    public void Ensure(string condF)
    {
        if (Db.Statements.ContainsKey("lean-wit-tw"))
        {
            return;
        }
        Proof omOnC = Use("omelon");

        // lean-wit-lim1: ( N e. _om -> Lim ( _om .o suc N ) ).
        {
            const string h = "N e. _om";
            Proof nOn = Imp(h, "nnon", [Hyp(h, h)]);
            Proof omOn = Lift(h, omOnC);
            Proof eq = Imp(h, "omsuc", [omOn, nOn]);
            Proof wn = Imp(h, "omcl", [omOn, nOn]);
            Proof lim = Imp(h, "oalimcl", [wn, Jca(Lift(h, Use("omex")), Lift(h, Use("limom")))]);
            Proof iff = Imp(h, "limeq", [eq]);
            thm("lean-wit-lim1", "omega times a successor is a limit ordinal.", Use("mpbird", lim, iff));
        }
        // lean-wit-lim: ( N e. _om -> Lim ( _om .o ( _om .o suc N ) ) ).
        {
            const string h = "N e. _om";
            Proof omOn = Lift(h, omOnC);
            Proof cV = Lift(h, UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "suc N")]));
            Proof lim1 = Imp(h, "lean-wit-lim1", [Hyp(h, h)]);
            thm("lean-wit-lim", "The levels of the witness are at limit ordinals.",
                Imp(h, "omlimcl", [Jca(omOn, Jca(cV, lim1)), Lift(h, Use("peano1"))]));
        }
        // lean-wit-add: ( ( ( C e. V /\ Lim C ) /\ B e. ( _om .o C ) ) -> ( B +o _om ) e. ( _om .o C ) ).
        {
            const string ph = "( ( C e. V /\\ Lim C ) /\\ B e. ( _om .o C ) )";
            Proof cV = Hyp(ph, "C e. V"), limC = Hyp(ph, "Lim C");
            Proof omOn = Lift(ph, omOnC);
            Proof cOn = Imp(ph, "limelon", [cV, limC]);
            Proof eqU = Imp(ph, "omlim", [omOn, Jca(cV, limC)], [("x", "x")]);
            Proof bU = Use("eleqtrd", Hyp(ph, "B e. ( _om .o C )"), eqU);
            Proof rex = Use("sylib", bU, UseS("eliun", [("A", "B"), ("x", "x"), ("B", "C"), ("C", "( _om .o x )")]));
            const string ph3 = "( ( " + ph + " /\\ x e. C ) /\\ B e. ( _om .o x ) )";
            Proof omOn3 = Lift(ph3, omOnC);
            Proof cOn3 = Imp(ph3, "limelon", [Hyp(ph3, "C e. V"), Hyp(ph3, "Lim C")]);
            Proof xC = Hyp(ph3, "x e. C");
            Proof xOn = Imp(ph3, "onelon", [cOn3, xC]);
            Proof oxOn = Imp(ph3, "omcl", [omOn3, xOn]);
            Proof bIn = Hyp(ph3, "B e. ( _om .o x )");
            Proof bOn = Imp(ph3, "onelon", [oxOn, bIn]);
            Proof bSs = Use("mpd", bIn, Imp(ph3, "onelss", [oxOn], [("B", "B")]));
            Proof addSs = Use("mpd", bSs, Imp(ph3, "oawordri", [bOn, oxOn, omOn3]));
            Proof suc = Imp(ph3, "omsuc", [omOn3, xOn]);
            Proof addSs2 = Use("sseqtrrd", addSs, suc);
            Proof sucIn = Use("mpbid", xC, Imp(ph3, "limsuc", [Hyp(ph3, "Lim C")], [("B", "x")]));
            Proof ordIn = Use("mpd", sucIn, Imp(ph3, "omordi", [Jca(cOn3, omOn3), Lift(ph3, Use("peano1"))], [("A", "suc x")]));
            Proof aOn = Imp(ph3, "oacl", [bOn, omOn3]);
            Proof wcOn = Imp(ph3, "omcl", [omOn3, cOn3]);
            Proof fin = Use("mpd", Jca(addSs2, ordIn), Imp(ph3, "ontr2", [aOn, wcOn], [("B", "( _om .o suc x )")]));
            Proof lim = Use("rexlimdva", Use("ex", fin));
            thm("lean-wit-add", "Below omega times a limit ordinal, adding omega stays below it.", Use("mpd", rex, lim));
        }
        // lean-wit-fv: ( N e. _om -> ( lean.-wit ` N ) = ( R1 ` ( _om .o ( _om .o suc N ) ) ) ).
        {
            Proof sub = SubEq("n", "N", $"( R1 ` {Lam("n")} )");
            Proof fv = UseS("fvmpt", [("D", "_om")], sub, Ax($"df-{Wit}"), UseS("fvex", [("F", "R1"), ("A", Lam("N"))]));
            thm("lean-wit-fv", "The levels of the witness.", fv);
        }
        // lean-wit-wu: ( N e. _om -> ( R1 ` ( _om .o ( _om .o suc N ) ) ) e. lean.-wuni ).
        string r1 = $"( R1 ` {Lam("N")} )";
        {
            const string h = "N e. _om";
            Proof lamV = Lift(h, UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "( _om .o suc N )")]));
            Proof limL = Imp(h, "lean-wit-lim", [Hyp(h, h)]);
            Proof wun = Imp(h, "r1limwun", [lamV, limL]);
            string h2 = $"( {h} /\\ x e. {r1} )";
            Proof rk = Imp(h2, "rankr1ai", [Hyp(h2, $"x e. {r1}")]);
            Proof cV = Lift(h2, UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "suc N")]));
            Proof lim1 = Imp(h2, "lean-wit-lim1", [Hyp(h2, h)]);
            Proof add = Imp(h2, "lean-wit-add", [Jca(cV, lim1), rk]);
            Proof lamOn = Imp(h2, "limelon", [Lift(h2, UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "( _om .o suc N )")])), Imp(h2, "lean-wit-lim", [Hyp(h2, h)])]);
            Proof r1In = Use("mpd", add, Imp(h2, "r1ord", [lamOn], [("A", "( ( rank ` x ) +o _om )")]));
            Proof ral = Use("ralrimiva", r1In);
            const string inner = "A. x e. w ( R1 ` ( ( rank ` x ) +o _om ) ) e. w";
            Proof sub = SubBi("w", r1, inner);
            Proof el = UseS("elrab", [("x", "w"), ("A", r1), ("B", "WUni"), ("ph", inner)], sub);
            Proof inRab = Use("mpbir2and", wun, ral, Lift(h, el));
            thm("lean-wit-wu", "Each level of the witness is a reflecting weak universe.", Use("eleqtrrd", inRab, Lift(h, Ax($"df-{Model.WuniToken}"))));
        }
        // lean-wit-f: lean.-wit : _om --> lean.-wuni.
        {
            Proof all = Use("rgen", UseS("lean-wit-wu", [("N", "n")]));
            Proof f = UseS("fmpt", [("x", "n"), ("A", "_om"), ("C", $"( R1 ` {Lam("n")} )"), ("B", Model.WuniToken), ("F", Wit)], Ax($"df-{Wit}"));
            thm("lean-wit-f", "The witness is an omega-sequence of reflecting weak universes.", Use("mpbi", all, f));
        }
        // lean-wit-om: _om e. ( lean.-wit ` (/) ).
        {
            string l0 = Lam("(/)");
            Proof p1 = Use("peano1");
            Proof lim0 = Use("ax-mp", p1, UseS("lean-wit-lim", [("N", "(/)")]));
            Proof lim1 = Use("ax-mp", p1, UseS("lean-wit-lim1", [("N", "(/)")]));
            Proof cV = UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "suc (/)")]);
            Proof zero = Use("ax-mp", lim0, UseS("0ellim", [("A", l0)]));
            Proof add = Use("ax-mp", Use("pm3.2i", Use("pm3.2i", cV, lim1), zero), UseS("lean-wit-add", [("C", "( _om .o suc (/) )"), ("B", "(/)"), ("V", "_V")]));
            Proof oa0 = Use("ax-mp", Use("omelon"), UseS("oa0r", [("A", "_om")]));
            Proof omIn = Use("eqeltrri", oa0, add);
            Proof lamV = UseS("ovex", [("A", "_om"), ("F", ".o"), ("B", "( _om .o suc (/) )")]);
            Proof lamOn = Use("ax-mp", Use("pm3.2i", lamV, lim0), UseS("limelon", [("A", l0), ("B", "_V")]));
            Proof dom = Use("ax-mp", Use("r1fnon"), UseS("fndm", [("F", "R1"), ("A", "On")]));
            Proof lamDom = Use("eleqtrri", lamOn, dom);
            Proof ss = Use("ax-mp", lamDom, UseS("onssr1", [("A", l0)]));
            Proof inR1 = Use("ax-mp", omIn, UseS("sseli", [("C", "_om")], ss));
            Proof fv = Use("ax-mp", p1, UseS("lean-wit-fv", [("N", "(/)")]));
            thm("lean-wit-om", "The first level of the witness contains omega.", Use("eleqtrri", inR1, fv));
        }
        // lean-wit-s: A. n e. _om ( lean.-wit ` n ) e. ( lean.-wit ` suc n ).
        {
            const string h = "n e. _om";
            Proof hn = Hyp(h, h);
            Proof omOn = Lift(h, omOnC);
            Proof sn = Imp(h, "peano2", [hn]);
            Proof ssn = Imp(h, "peano2", [sn]);
            Proof ssnOn = Imp(h, "nnon", [ssn]);
            Proof snIn = Imp(h, "sucidg", [Imp(h, "elex", [sn])], [("V", "_V")]);
            Proof c1 = Use("mpd", snIn, Imp(h, "omordi", [Jca(ssnOn, omOn), Lift(h, Use("peano1"))], [("A", "suc n")]));
            Proof cOn = Imp(h, "omcl", [omOn, ssnOn]);
            Proof c2 = Use("mpd", c1, Imp(h, "omordi", [Jca(cOn, omOn), Lift(h, Use("peano1"))], [("A", "( _om .o suc n )")]));
            Proof lamOn = Imp(h, "omcl", [omOn, cOn]);
            Proof r1In = Use("mpd", c2, Imp(h, "r1ord", [lamOn], [("A", Lam("n"))]));
            Proof fvn = UseS("lean-wit-fv", [("N", "n")]);
            Proof fvs = Imp(h, "lean-wit-fv", [sn]);
            Proof a = Use("eqeltrd", Use("syl", hn, fvn), Use("eleqtrrd", r1In, fvs));
            thm("lean-wit-s", "Each level of the witness is a member of the next.", Use("rgen", a));
        }
        // lean-wit-tw: lean.-wit e. lean.-wtower.
        {
            Proof cond = Use("pm3.2i", Use("pm3.2i", Use("lean-wit-f"), Use("lean-wit-om")), Use("lean-wit-s"));
            Proof sub = SubBi("f", Wit, condF);
            Proof isSet = Use("eqeltri", Ax($"df-{Wit}"), UseS("mptex", [("x", "n"), ("A", "_om"), ("B", $"( R1 ` {Lam("n")} )")], Use("omex")));
            Proof el = Use("ax-mp", isSet, UseS("elabg", [("x", "f"), ("ph", condF), ("A", Wit), ("V", "_V")], sub));
            Proof inAb = Use("mpbir", cond, el);
            thm("lean-wit-tw", "ZFC proves that a lowered tower exists: the witness is one.", Use("eleqtrri", inAb, Ax($"df-{Model.LoweredTowerToken}")));
        }
    }

    /// <summary>
    /// From |- ( ( U e. lean.-wtower /\ ph ) -> ps ) with U in neither ph nor ps: |- ( ph -> ps ), with U the witness;
    /// from |- ( U e. lean.-wtower -> ps ): |- ps.
    /// </summary>
    public Proof Discharge(string label)
    {
        Proof inst = UseS(label, [("U", Wit)]);
        string h = k.Split(ProofKit.Of(inst)).H;
        return h == $"{Wit} e. {Model.LoweredTowerToken}" ? Use("ax-mp", Use("lean-wit-tw"), inst) : Use("mpan", Use("lean-wit-tw"), inst);
    }
}
