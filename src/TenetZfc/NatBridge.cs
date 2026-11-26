using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Bridge theorems between the generic model's Nat (docs/milestone3.md, step 3) and set.mm's NN0.
///
/// The model's Nat is the union of an ω-chain of stages of tagged tuples, zero is &lt;. (/) , (/) &gt;. and succ x is
/// &lt;. 1o , &lt;. (/) , &lt;. x , (/) &gt;. &gt;. &gt;.. The literal map lean.Nat.-lit sends the ordinal k to succ applied k times to
/// zero. These theorems prove it is a bijection from ω onto the model's Nat, and so that
///
///   F = ( `' lean.Nat.-ofnum o. `' lean.Nat.-lit )
///
/// (the inverse of the literal map, followed by set.mm's isomorphism from ω onto NN0) is a bijection from the
/// model's Nat onto NN0 taking zero to 0, succ to + 1 and every literal to its numeral. Through F, any function
/// satisfying Nat.add's computation rules is +, and a model statement such as 2 + 2 = 4 is equivalent to set.mm's.
///
/// Every theorem is proved here from the model's definitions and set.mm, and checked by both verifiers: none is
/// assumed. Milestone 2's hand table (Nat as NN0, Nat.add as +, literals as numerals) becomes these theorems.
/// </summary>
public sealed class NatBridge
{
    private readonly Prover _pr;
    private readonly ProofKit _k;
    private Database Db => _pr.Database;

    /// <summary>The theorems proved, in order: label, comment, statement, proof, $d lines.</summary>
    public List<(string Label, string Comment, MmExpr Statement, List<string> Proof, string[] Distinct)> Theorems { get; } = [];

    // The model's encoding, checked against its definitions when the bridge starts.
    public const string Nat = "( lean.Nat ` U )";
    public const string Z = "<. (/) , (/) >.";
    public static string S(string t) => $"<. 1o , <. (/) , <. {t} , (/) >. >. >.";
    public const string Lit = "lean.Nat.-lit";
    public static string Lt(string t) => $"( {Lit} ` {t} )";
    public const string Rf = "rec ( ( z e. _V |-> ( lean.Nat.-step ` <. <. U , (/) >. , z >. ) ) , (/) )";
    public static string St(string t) => $"( {Rf} ` {t} )";
    public static string Step(string x) => $"( {x} u. ( {{ {Z} }} u. U_ x e. {x} {{ {S("x")} }} ) )";
    /// <summary>set.mm's isomorphism from ω onto NN0 (om2uzf1oi with C = 0), as lean.Nat.-ofnum inverts it.</summary>
    public const string Gm = "( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om )";
    public static string Gv(string t) => $"( {Gm} ` {t} )";
    /// <summary>The bridge: the model's Nat onto NN0.</summary>
    public const string F = "( `' lean.Nat.-ofnum o. `' lean.Nat.-lit )";
    public static string Fv(string t) => $"( {F} ` {t} )";
    public static string Ofn(string t) => $"( lean.Nat.-ofnum ` {t} )";
    public const string Zero = "( lean.Nat.zero ` U )";
    public static string Succ(string t) => $"( ( lean.Nat.succ ` U ) ` {t} )";

    /// <summary>The class the universe argument ranges over: lean.-tower (the default), or Univ in the one-universe model.</summary>
    private readonly string D;

    public NatBridge(Prover pr, bool tower = true)
    {
        _pr = pr;
        _k = new ProofKit(pr);
        D = tower ? Model.TowerToken : "Univ";
    }

    /// <summary>
    /// The whole bridge as a set.mm file: the model's definitions of Nat, its constructors, Nat.add and the literal
    /// maps, then every bridge theorem and a theorem F ( n ) = n for each numeral given. The export must contain Nat.add.
    ///
    /// In tower mode (the default) Nat.add's computation rules are proved from its definition, so ⟦Nat.add⟧ = + holds
    /// with no hypotheses but the tower's; each theorem named in <paramref name="restate"/> (Nat.add_zero, Nat.zero_add)
    /// is then proved through the model and restated in set.mm's arithmetic. In the one-universe model the rules are
    /// hypotheses, and the output proves instead that Nat.below, and so Nat.add, collapses there.
    /// </summary>
    public static (string Text, List<(string Label, string Comment, MmExpr Statement, List<string> Proof, string[] Distinct)> Theorems) Emit(
        string export, string setmm, IEnumerable<System.Numerics.BigInteger> numerals, bool compress = true, bool tower = true,
        IReadOnlyList<string>? restate = null)
    {
        var t = new Terms();
        Environment env = Reader.ReadExport(t, export);
        var pr = new Prover(Database.Read(setmm));
        var bridge = new NatBridge(pr, tower);
        Model model;
        TheoremTranslator? tt = null;
        if (tower)
        {
            tt = new TheoremTranslator(t, env, pr);
            model = tt.Model;
        }
        else
        {
            model = new Model(t, env, pr, tower: false);
        }
        foreach (string c in new[] { "Nat", "Nat.zero", "Nat.succ", "Nat.add" })
        {
            model.Define(tt is null ? t.Of(c) : ((Const)tt.Const0(c)).Name);
        }
        model.Class(t.Nat(2), "U", new Dictionary<ulong, string>());   // declares the literal maps
        bridge.ProveAll(numerals);
        if (tt is not null)
        {
            bridge.NatAddRules(tt);
            foreach (string name in restate ?? [])
            {
                bridge.Restate(tt, name);
            }
        }
        else
        {
            var (bstmt, bproof, bdistinct) = model.Equation(t.Of("Nat.below"));
            bridge.Add("lean-Nat.below-eq", "The definitional equation of Nat.below.", bstmt, bproof, bdistinct);
            bridge.BelowCollapses(bdistinct);
        }
        var w = new Writer(Path.GetFileName(setmm), "tenet-zfc bridge theorems: the model's Nat is NN0 (docs/bridges.md)", compress ? pr.Database : null);
        w.Assumptions(model.Assumptions());
        w.Raw(model.Declarations);
        foreach (var th in bridge.Theorems)
        {
            w.Theorem(th.Label, th.Comment, th.Statement, th.Proof, th.Distinct);
        }
        return (w.ToString(), bridge.Theorems);
    }

    private static string U(string s) => ProofKit.Replace(s, "U", "u");

    /// <summary>Fail loudly if the model's definitions are not the encoding these proofs are written for.</summary>
    public void CheckEncoding()
    {
        void Expect(string label, string text)
        {
            string have = Db.Statements.TryGetValue(label, out Statement? s) ? string.Join(' ', s.Expr.Symbols) : "(missing)";
            if (have != text)
            {
                throw new InvalidOperationException($"the model's {label} is not the encoding the Nat bridge proves things about:\n  have {have}\n  want {text}");
            }
        }
        Expect("df-lean.Nat", $"lean.Nat = ( u e. {D} |-> U_ x e. _om ( {U(Rf)} ` x ) )");
        Expect("df-lean.Nat.-step", "lean.Nat.-step = ( y e. _V |-> " + Step("( 2nd ` y )") + " )");
        Expect("df-lean.Nat.-lit", $"{Lit} = ( rec ( ( x e. _V |-> {S("x")} ) , {Z} ) |` _om )");
        Expect("df-lean.Nat.-ofnum", $"lean.Nat.-ofnum = `' {Gm}");
    }

    private Proof Ax(string label) => _k.UseG(label, string.Join(' ', Db[label].Expr.Symbols));

    private Proof Use(string label, params Proof[] h) => _k.Use(label, h);
    private Proof UseS(string label, (string, string)[] s, params Proof[] h) => _k.UseS(label, s, h);
    private Proof UseG(string label, string goal, params Proof[] h) => _k.UseG(label, goal, h);
    private Proof Imp(string? h, string label, Proof[] premises, string? q = null, (string, string)[]? s = null, Proof[]? closed = null) =>
        _k.Imp(h, label, premises, q, s, closed);
    private Proof Hyp(string h, string c) => _k.Hyp(h, c);
    private Proof Lift(string h, Proof p) => _k.Lift(h, p);
    private Proof Trans(params Proof[] c) => _k.Trans(c);
    private Proof Symm(Proof p) => _k.Symm(p);
    private Proof Rw(Proof p, Proof eq) => _k.Rw(p, eq);
    private Proof Ce(string ctx, Proof eq) => _k.CongEq(ctx, "Y", eq);
    /// <summary>
    /// From ( x = C -> ( P(x) <-> P(C) ) ), |- ( h -> A. x e. A P(x) ) and |- ( h -> C e. A ): |- ( h -> P(C) ), by rspcv
    /// (rspcdva would need x absent from h, which binds it).
    /// </summary>
    private Proof Spec(Proof sub, Proof all, Proof mem)
    {
        string h = _k.Split(ProofKit.Of(mem)).H;
        return Use("mpd", all, Imp(h, "rspcv", [mem], closed: [sub]));
    }

    private Proof Id(string eq) => UseS("id", [("ph", eq)]);
    private Proof Opex(string a, string b) => UseS("opex", [("A", a), ("B", b)]);
    private Proof Fvex(string f, string a) => UseS("fvex", [("F", f), ("A", a)]);

    /// <summary>( x = t -> B(x) = B(t) ) for a class B written with x.</summary>
    private Proof SubEq(string x, string t, string body) => _k.CongEq(ProofKit.Replace(body, x, "Y"), "Y", Id($"{x} = {t}"));

    /// <summary>( x = t -> ( P(x) <-> P(t) ) ) for a formula P written with x.</summary>
    private Proof SubBi(string x, string t, string body) => _k.Cong("wff", ProofKit.Replace(body, x, "Y"), "Y", Id($"{x} = {t}"));

    /// <summary>Record a theorem, teach it to the prover, and return it by label.</summary>
    public void Thm(string label, string comment, Proof p, string[]? extraDistinct = null)
    {
        string[] distinct = [.. Distinct(p), .. extraDistinct ?? []];
        Theorems.Add((label, comment, p.Proves, p.Proof, distinct));
        string text = "${ " + string.Join(' ', distinct.Select(d => $"$d {d} $.")) + $" {label} $p {p.Proves} $= {string.Join(' ', p.Proof)} $. $}}";
        Db.Extend(text);
    }

    /// <summary>Add a theorem proved elsewhere (the model's definitional equations).</summary>
    public void Add(string label, string comment, MmExpr statement, List<string> proof, string[] distinct)
    {
        Theorems.Add((label, comment, statement, proof, distinct));
        Db.Extend("${ " + string.Join(' ', distinct.Select(d => $"$d {d} $.")) + $" {label} $p {statement} $= {string.Join(' ', proof)} $. $}}");
    }

    /// <summary>
    /// $d conditions: every set variable (bound in the statement or used in the proof) is distinct from every other
    /// variable. Class and wff variables of the statement are left free of each other, so the theorem can be used
    /// with substitutions that share variables.
    /// </summary>
    private string[] Distinct(Proof p)
    {
        var setvars = new List<string>();
        var others = new List<string>();
        foreach (string s in p.Proves.Symbols)
        {
            if (Db.FloatOf(s) is Statement f)
            {
                (f.Expr.Type == "setvar" ? setvars : others).Add(s);
            }
        }
        foreach (string l in p.Proof)
        {
            if (Db.Statements.TryGetValue(l, out Statement? st) && st.Kind == 'f' && st.Expr.Type == "setvar")
            {
                setvars.Add(st.Var!);
            }
        }
        setvars = setvars.Distinct().ToList();
        others = others.Distinct().ToList();
        var lines = new List<string>();
        if (setvars.Count > 1)
        {
            lines.Add(string.Join(' ', setvars));
        }
        if (setvars.Count > 0)
        {
            lines.AddRange(others.Select(o => o + " " + string.Join(' ', setvars)));
        }
        return lines.ToArray();
    }

    // ================================================================ the stages and the literal map

    public void ProveAll(IEnumerable<System.Numerics.BigInteger> numerals)
    {
        CheckEncoding();
        Constructors();
        Stages();
        LiteralMap();
        Bijection();
        Arithmetic();
        foreach (var n in numerals)
        {
            Numeral(n);
        }
    }

    private void Constructors()
    {
        // Nat.zero and Nat.succ at the universe U, by fvmpt. (The model's own definitional equations declare every
        // variable distinct, U from A included, which would stop A from being a term that mentions U.)
        Proof z = UseS("fvmpt", [("D", D)], Lift("u = U", UseS("eqid", [("A", Z)])), Ax("df-lean.Nat.zero"), Opex("(/)", "(/)"));
        Thm("lean-nat-zeroeq", "The model's zero at the universe U.", z);

        string h = $"( U e. {D} /\\ A e. ( lean.Nat ` U ) )";
        string mpt = $"( x e. {Nat} |-> {S("x")} )";
        Proof f1 = Use("fvmpt", SubEq("u", "U", $"( x e. ( lean.Nat ` u ) |-> {S("x")} )"), Ax("df-lean.Nat.succ"),
            UseS("mptex", [("x", "x"), ("B", S("x"))], Fvex("lean.Nat", "U")));
        Proof f2 = Use("fvmpt", SubEq("x", "A", S("x")), UseS("eqid", [("A", mpt)]), Opex("1o", "<. (/) , <. A , (/) >. >."));
        Proof e1 = Ce("( Y ` A )", Use("syl", Hyp(h, $"U e. {D}"), f1));
        Thm("lean-nat-succeq", "The model's successor at the universe U.", Trans(e1, Use("syl", Hyp(h, "A e. ( lean.Nat ` U )"), f2)));
    }

    private void Stages()
    {
        // The first stage is empty.
        Thm("lean-nat-stage0", "The first stage of the model's Nat is empty.", UseG("rdg0", $"{St("(/)")} = (/)", Use("0ex")));

        // Each stage adds zero and the successors of the last.
        {
            const string h = "A e. _om";
            string x = St("A");
            string gz = $"( z e. _V |-> ( lean.Nat.-step ` <. <. U , (/) >. , z >. ) )";
            string gw = $"( w e. _V |-> ( lean.Nat.-step ` <. <. U , (/) >. , w >. ) )";
            string p = $"<. <. U , (/) >. , {x} >.";
            Proof e1 = Imp(h, "rdgsuc", [Imp(h, "nnon", [Hyp(h, h)])], q: $"{St("suc A")} = ( {gz} ` {x} )");
            Proof cbv = UseS("cbvmptv", [("A", "_V")], SubEq("z", "w", "( lean.Nat.-step ` <. <. U , (/) >. , z >. )"));
            Proof e2 = UseS("fveq1i", [("A", x)], cbv);
            Proof fv3 = UseS("fvmpt", [("D", "_V")],
                SubEq("w", x, "( lean.Nat.-step ` <. <. U , (/) >. , w >. )"), UseS("eqid", [("A", gw)]), Fvex("lean.Nat.-step", p));
            Proof e3 = Use("ax-mp", UseG("fvex", $"{x} e. _V"), fv3);
            string body(string y) => Step($"( 2nd ` {y} )");
            Proof iun = UseS("iunex", [("x", "x")], Fvex("2nd", p), UseS("snex", [("A", S("x"))]));
            Proof cex = Use("unex", Fvex("2nd", p), Use("unex", UseS("snex", [("A", Z)]), iun));
            Proof fv4 = Use("fvmpt", SubEq("y", p, body("y")), Ax("df-lean.Nat.-step"), cex);
            Proof e4 = Use("ax-mp", Opex("<. U , (/) >.", x), fv4);
            Proof snd = Use("op2nd", Opex("U", "(/)"), UseG("fvex", $"{x} e. _V"));
            Proof e5 = _k.CongEq(ProofKit.Replace(body(p), $"( 2nd ` {p} )", "Y"), "Y", Lift(h, snd));
            Thm("lean-nat-stagesuc", "Each stage of the model's Nat adds zero and the successors of the last stage.",
                Trans(e1, Lift(h, e2), Lift(h, e3), Lift(h, e4), e5));
        }

        // The model's Nat is the union of its stages.
        {
            string body = $"U_ x e. _om {St("x")}";
            Proof cex = UseS("iunex", [("x", "x")], Use("omex"), UseG("fvex", $"{St("x")} e. _V"));
            Thm("lean-nat-iun", "The model's Nat is the union of its stages.",
                Use("fvmpt", SubEq("u", "U", U(body)), Ax("df-lean.Nat"), cex));
        }
    }

    private void LiteralMap()
    {
        string recL = $"( rec ( ( x e. _V |-> {S("x")} ) , {Z} ) |` _om )";
        Proof dfLit = Ax("df-lean.Nat.-lit");

        Proof lit0 = Use("eqtri", UseS("fveq1i", [("A", "(/)")], dfLit),
            Imp(null, "fr0g", [Opex("(/)", "(/)")], s: [("F", $"( x e. _V |-> {S("x")} )")]));
        Thm("lean-nat-lit0", "The literal map takes 0 to the model's zero.", lit0);

        {
            Proof fs = UseS("frsucmpt2", [("y", "v"), ("V", "_V")], dfLit, SubEq("v", "x", S("v")), SubEq("v", Lt("A"), S("v")));
            Thm("lean-nat-litsuc", "The literal map takes a successor to the model's successor.",
                Use("mpan2", Opex("1o", $"<. (/) , <. {Lt("A")} , (/) >. >."), fs));
        }

        Proof litfn = Use("mpbir", UseG("frfnom", $"{recL} Fn _om"), UseS("fneq1i", [("A", "_om")], dfLit));
        Thm("lean-nat-litfn", "The literal map is a function on omega.", litfn);

        // Each literal is in a stage.
        {
            string p = $"{Lt("n")} e. {St("suc n")}";
            string iu(string t) => $"U_ x e. {St(t)} {{ {S("x")} }}";
            Proof sn = Use("snid", Opex("(/)", "(/)"));
            Proof a1 = Imp(null, "elun1", [sn], q: $"{Z} e. ( {{ {Z} }} u. {iu("(/)")} )");
            Proof a2 = Imp(null, "elun2", [a1], q: $"{Z} e. {Step(St("(/)"))}");
            Proof a3 = Use("eleqtrri", a2, Imp(null, "lean-nat-stagesuc", [Use("peano1")]));
            Proof b = Use("eqeltri", Ax("lean-nat-lit0"), a3);

            string h = $"( j e. _om /\\ {ProofKit.Replace(p, "n", "j")} )";
            string lj = Lt("j");
            Proof hj = Hyp(h, "j e. _om");
            Proof e1 = Imp(h, "lean-nat-litsuc", [hj]);
            Proof ss = Imp(h, "ssiun2s", [Hyp(h, $"{lj} e. {St("suc j")}")], closed: [SubEq("x", lj, $"{{ {S("x")} }}")]);
            Proof mem = Use("mpd", Lift(h, Use("snid", Opex("1o", $"<. (/) , <. {lj} , (/) >. >."))), UseS("sseld", [("C", S(lj))], ss));
            Proof m2 = Imp(h, "elun2", [mem], q: $"{S(lj)} e. ( {{ {Z} }} u. {iu("suc j")} )");
            Proof m3 = Imp(h, "elun2", [m2], q: $"{S(lj)} e. {Step(St("suc j"))}");
            Proof eqs = Imp(h, "lean-nat-stagesuc", [Imp(h, "peano2", [hj])]);
            Proof st = Use("eqeltrd", e1, Use("eleqtrrd", m3, eqs));
            Thm("lean-nat-litstage", "The literal k is in stage k + 1.", _k.Finds("n", "j", p, null, b, st, "A"));
        }

        // Its range is inside the model's Nat.
        {
            string h = $"( U e. {D} /\\ n e. _om )";
            Proof hn = Hyp(h, "n e. _om");
            Proof ls = Imp(h, "lean-nat-litstage", [hn]);
            Proof ssi = Imp(h, "ssiun2s", [Imp(h, "peano2", [hn])], closed: [SubEq("x", "suc n", St("x"))], s: [("A", "_om")]);
            Proof m = Use("mpd", ls, UseS("sseld", [("C", Lt("n"))], ssi));
            Proof m2 = Use("eleqtrrd", m, Imp(h, "lean-nat-iun", [Hyp(h, $"U e. {D}")]));
            Proof all = Use("ralrimiva", m2);
            Thm("lean-nat-litrnss", "Every literal is in the model's Nat.",
                Imp($"U e. {D}", "fnfvrnss", [Lift($"U e. {D}", litfn), all]));
        }

        // The model's successor of a literal is a literal.
        {
            const string h = "( n e. _om /\\ ( lean.Nat.-lit ` n ) = A )";
            Proof hn = Hyp(h, "n e. _om");
            Proof e1 = Imp(h, "lean-nat-litsuc", [hn]);
            Proof e2 = Ce(S("Y"), Hyp(h, $"{Lt("n")} = A"));
            Proof r = Imp(h, "fnfvelrn", [Lift(h, litfn), Imp(h, "peano2", [hn])]);
            Proof m = Rw(r, Trans(e1, e2));
            Proof rl = Use("rexlimiva", m);
            Proof fv = Imp(null, "fvelrnb", [litfn], s: [("B", "A"), ("x", "n")]);
            Thm("lean-nat-litsucrn", "The range of the literal map is closed under the model's successor.", Use("sylbi", fv, rl));
        }

        // Each stage is inside the range of the literal map.
        {
            string p = $"{St("n")} C_ ran {Lit}";
            Proof b = Use("eqsstri", Ax("lean-nat-stage0"), UseS("0ss", [("A", $"ran {Lit}")]));
            string pj = ProofKit.Replace(p, "n", "j");
            string h = $"( j e. _om /\\ {pj} )";
            Proof zr = Use("eqeltrri", Ax("lean-nat-lit0"), Imp(null, "fnfvelrn", [litfn, Use("peano1")]));
            Proof sn = Imp(null, "snssi", [zr]);
            string h2 = $"( {h} /\\ x e. {St("j")} )";
            Proof xr = Use("mpd", Hyp(h2, $"x e. {St("j")}"), UseS("sseld", [("C", "x")], Hyp(h2, pj)));
            Proof sn2 = Imp(h2, "snssi", [Imp(h2, "lean-nat-litsucrn", [xr])]);
            string iu = $"U_ x e. {St("j")} {{ {S("x")} }}";
            Proof iun = Use("sylibr", Use("ralrimiva", sn2),
                UseG("iunss", $"( {iu} C_ ran {Lit} <-> A. x e. {St("j")} {{ {S("x")} }} C_ ran {Lit} )"));
            Proof u = Use("unssd", Hyp(h, pj), Use("unssd", Lift(h, sn), iun));
            Proof st = Use("eqsstrd", Imp(h, "lean-nat-stagesuc", [Hyp(h, "j e. _om")]), u);
            Thm("lean-nat-stagern", "Every stage of the model's Nat is made of literals.", _k.Finds("n", "j", p, null, b, st, "A"));
        }

        // So the literals are exactly the model's Nat.
        {
            string h = $"U e. {D}";
            Proof all = Use("rgen", UseS("lean-nat-stagern", [("A", "x"), ("U", "U")]));
            Proof iss = Use("mpbir", all, UseG("iunss", $"( U_ x e. _om {St("x")} C_ ran {Lit} <-> A. x e. _om {St("x")} C_ ran {Lit} )"));
            Proof natss = Use("eqsstrd", Imp(h, "lean-nat-iun", [Hyp(h, h)]), Lift(h, iss));
            Thm("lean-nat-rnlit", "The literals are exactly the model's Nat.", Use("eqssd", Imp(h, "lean-nat-litrnss", [Hyp(h, h)]), natss));
        }

        // Zero is not a successor, and the successor is injective (on literals).
        {
            Proof o = UseS("opth1", [("C", "1o"), ("D", "<. (/) , <. A , (/) >. >.")], Use("0ex"), Use("0ex"));
            Proof ne = Use("neii", Use("necomi", Use("1n0")));
            Thm("lean-nat-zns", "The model's zero is not a successor.", Use("mto", ne, o));
        }
        {
            string la = Lt("A"), lb = Lt("B");
            Proof b1 = UseS("opth", [("C", "1o"), ("D", $"<. (/) , <. {lb} , (/) >. >.")], Use("1oex"), Opex("(/)", $"<. {la} , (/) >."));
            Proof b2 = UseS("opth", [("C", "(/)"), ("D", $"<. {lb} , (/) >.")], Use("0ex"), Opex(la, "(/)"));
            Proof b3 = UseS("opth1", [("C", lb), ("D", "(/)")], Fvex(Lit, "A"), Use("0ex"));
            Proof s1 = Use("simprd", Use("biimpi", b1));
            Proof s2 = Use("simprd", Use("biimpi", b2));
            Thm("lean-nat-sinj", "The model's successor is injective on literals.", Use("syl", Use("syl", s1, s2), b3));
        }

        // The literal map is injective, by induction.
        {
            string q(string n, string m) => $"( {Lt(n)} = {Lt(m)} -> {n} = {m} )";
            string p = $"A. m e. _om {q("n", "m")}";

            // Base: 0 is only the literal of 0.
            const string h = "m e. _om";
            Proof c1 = Lift(h, UseS("a1d", [("ch", $"{Lt("(/)")} = {Lt("m")}")], Use("biimpi", UseS("eqcom", [("A", "m"), ("B", "(/)")]))));
            string h2 = $"( ( {h} /\\ i e. _om ) /\\ m = suc i )";
            Proof lm2 = Trans(Ce(Lt("Y"), Hyp(h2, "m = suc i")), Imp(h2, "lean-nat-litsuc", [Hyp(h2, "i e. _om")]));
            Proof n1 = Rw(Lift(h2, UseS("lean-nat-zns", [("A", Lt("i"))])), Symm(lm2));
            Proof n2 = Rw(n1, Lift(h2, Use("eqcomi", Ax("lean-nat-lit0"))));
            Proof c2 = Use("rexlimdva", Use("ex", UseS("pm2.21d", [("ch", "(/) = m")], n2)));
            Proof cases0 = Imp(h, "nn0suc", [Hyp(h, h)], s: [("x", "i")]);
            Proof b = Use("rgen", Use("mpd", cases0, Use("jaod", c1, c2)));

            // Step.
            string pj = ProofKit.Replace(p, "n", "j");
            string hs = $"( j e. _om /\\ {pj} )";
            string h3 = $"( {hs} /\\ l e. _om )";
            
            // m = 0: the successor of a literal is not zero.
            string h4 = $"( {h3} /\\ l = (/) )";
            Proof ls4 = Imp(h4, "lean-nat-litsuc", [Hyp(h4, "j e. _om")]);
            Proof lm4 = Trans(Ce(Lt("Y"), Hyp(h4, "l = (/)")), Lift(h4, Ax("lean-nat-lit0")));
            Proof nzc = Use("mtbi", UseS("lean-nat-zns", [("A", Lt("j"))]), UseS("eqcom", [("A", Z), ("B", S(Lt("j")))]));
            Proof m1 = Rw(Lift(h4, nzc), Symm(ls4));
            Proof m2 = Rw(m1, Symm(lm4));
            Proof d1 = Use("ex", UseS("pm2.21d", [("ch", "suc j = l")], m2));
            // l = suc i: peel the successor and use the induction hypothesis at i.
            string h5 = $"( ( {h3} /\\ i e. _om ) /\\ l = suc i )";
            string h6 = $"( {h5} /\\ {Lt("suc j")} = {Lt("l")} )";
            Proof ls6 = Imp(h6, "lean-nat-litsuc", [Hyp(h6, "j e. _om")]);
            Proof lm6 = Trans(Ce(Lt("Y"), Hyp(h6, "l = suc i")), Imp(h6, "lean-nat-litsuc", [Hyp(h6, "i e. _om")]));
            Proof e = Trans(Symm(ls6), Hyp(h6, $"{Lt("suc j")} = {Lt("l")}"), lm6);
            Proof li = Imp(h6, "lean-nat-sinj", [e]);
            Proof ih = Spec(SubBi("m", "i", q("j", "m")), Hyp(h6, pj), Hyp(h6, "i e. _om"));
            Proof ji = Use("mpd", li, ih);
            Proof res = Trans(Use("suceqd", ji), Symm(Hyp(h6, "l = suc i")));
            Proof d2 = Use("rexlimdva", Use("ex", Use("ex", res)));
            Proof cases = Imp(h3, "nn0suc", [Hyp(h3, "l e. _om")], s: [("x", "i")]);
            Proof all = Use("ralrimiva", Use("mpd", cases, Use("jaod", d1, d2)));
            // The step generalizes over l; the induction hypothesis binds m. Rename to match.
            Proof st = Use("sylib", all, UseS("cbvralvw", [("A", "_om")], SubBi("l", "m", q("suc j", "l"))));

            Proof ind = _k.Finds("n", "j", p, null, b, st, "A");
            const string h7 = "( A e. _om /\\ B e. _om )";
            Proof pa = Use("syl", Hyp(h7, "A e. _om"), ind);
            Proof rs = Imp(h7, "rspcv", [Hyp(h7, "B e. _om")], closed: [SubBi("m", "B", q("A", "m"))]);
            Thm("lean-nat-litinj", "The literal map is injective.", Use("mpd", pa, rs));
        }

        // So it is a bijection from ω onto the model's Nat.
        {
            Proof f = Use("mpbir", Use("pm3.2i", litfn, UseS("ssid", [("A", $"ran {Lit}")])),
                UseG("df-f", $"( {Lit} : _om --> ran {Lit} <-> ( {Lit} Fn _om /\\ ran {Lit} C_ ran {Lit} ) )"));
            Proof inj = Use("rgen2", UseS("lean-nat-litinj", [("A", "x"), ("B", "y")]));
            Proof f1 = Use("mpbir", Use("pm3.2i", f, inj),
                UseG("dff13", $"( {Lit} : _om -1-1-> ran {Lit} <-> ( {Lit} : _om --> ran {Lit} /\\ A. x e. _om A. y e. _om ( ( {Lit} ` x ) = ( {Lit} ` y ) -> x = y ) ) )"));
            Thm("lean-nat-litf1o", "The literal map is a bijection from omega onto its range.", Imp(null, "f1f1orn", [f1]));
            string h = $"U e. {D}";
            Proof bi = Imp(h, "f1oeq3", [Imp(h, "lean-nat-rnlit", [Hyp(h, h)])], s: [("F", Lit), ("C", "_om")]);
            Thm("lean-nat-litf1onat", "The literal map is a bijection from omega onto the model's Nat.",
                Use("mpbid", Lift(h, Ax("lean-nat-litf1o")), bi));
        }
    }

    private void Bijection()
    {
        Proof litf1o = Ax("lean-nat-litf1o");
        Proof litfn = Ax("lean-nat-litfn");
        Proof eqG = UseS("eqid", [("A", Gm)]);

        Proof cnv = Use("eqtri", Use("cnveqi", Ax("df-lean.Nat.-ofnum")),
            Use("mpbi", UseG("relres", $"Rel {Gm}"), UseS("dfrel2", [("R", Gm)])));
        Thm("lean-nat-ofnumcnv", "The inverse of lean.Nat.-ofnum is set.mm's map from omega onto NN0.", cnv);

        Proof g = Use("om2uzf1oi", Use("0z"), eqG);
        Proof gbi = Imp(null, "f1oeq3", [Use("eqcomi", Use("nn0uz"))], s: [("F", Gm), ("C", "_om")]);
        Thm("lean-nat-omf1o", "set.mm's map from omega onto NN0.", Use("mpbi", g, gbi));
        Proof gom = Ax("lean-nat-omf1o");

        // F on a literal.
        {
            const string h = "A e. ran lean.Nat.-lit";
            Proof cf = Imp(null, "f1of", [Imp(null, "f1ocnv", [litf1o])]);
            Proof e1 = Imp(h, "fvco3", [Lift(h, cf), Hyp(h, h)], s: [("F", "`' lean.Nat.-ofnum")]);
            Proof e2 = Lift(h, UseS("fveq1i", [("A", $"( `' {Lit} ` A )")], Ax("lean-nat-ofnumcnv")));
            Thm("lean-nat-fval", "The bridge F reads a literal's ordinal and maps it into NN0.", Trans(e1, e2));
        }
        {
            const string h = "A e. _om";
            Proof r = Imp(h, "fnfvelrn", [Lift(h, litfn), Hyp(h, h)]);
            Proof e2 = Imp(h, "f1ocnvfv1", [Lift(h, litf1o), Hyp(h, h)]);
            Thm("lean-nat-flit", "The bridge F on the literal of k is set.mm's image of k in NN0.",
                Trans(Imp(h, "lean-nat-fval", [r]), Ce(Gv("Y"), e2)));
        }

        // Headline: F is a bijection from the model's Nat onto NN0.
        {
            string h = $"U e. {D}";
            Proof c = Imp(h, "f1ocnv", [Imp(h, "lean-nat-litf1onat", [Hyp(h, h)])]);
            Proof obi = Imp(null, "f1oeq1", [Use("eqcomi", Ax("lean-nat-ofnumcnv"))], s: [("A", "_om"), ("B", "NN0")]);
            Proof o = Use("mpbi", gom, obi);
            Thm("lean-nat-f1o", "Bridge: F is a bijection from the model's Nat onto NN0.", Imp(h, "f1oco", [Lift(h, o), c]));
        }
        {
            string h = $"( U e. {D} /\\ A e. ( lean.Nat ` U ) )";
            Proof f = Imp(h, "f1of", [Imp(h, "lean-nat-f1o", [Hyp(h, $"U e. {D}")])]);
            Thm("lean-nat-fcn", "The bridge F takes the model's Nat into CC.", Imp(h, "nn0cn", [Imp(h, "ffvelcdm", [f, Hyp(h, "A e. ( lean.Nat ` U )")])]));
        }
        {
            const string h = "A e. _om";
            Proof f = Lift(h, Imp(null, "f1of", [gom]));
            Thm("lean-nat-gcn", "set.mm's map from omega onto NN0 takes values in CC.", Imp(h, "nn0cn", [Imp(h, "ffvelcdm", [f, Hyp(h, h)])]));
        }
        {
            string h = $"( U e. {D} /\\ A e. _om )";
            Proof f = Imp(h, "f1of", [Imp(h, "lean-nat-litf1onat", [Hyp(h, $"U e. {D}")])]);
            Thm("lean-nat-litnat", "Every literal is in the model's Nat.", Imp(h, "ffvelcdm", [f, Hyp(h, "A e. _om")]));
        }

        // Headline: F takes zero to 0.
        {
            string h = $"U e. {D}";
            Proof z = Imp(h, "lean-nat-zeroeq", [Hyp(h, h)]);
            Proof e = Trans(z, Lift(h, Use("eqcomi", Ax("lean-nat-lit0"))));
            Proof f2 = Lift(h, Imp(null, "lean-nat-flit", [Use("peano1")]));
            Proof f3 = Lift(h, Use("om2uz0i", Use("0z"), eqG));
            Thm("lean-nat-fzero", "Bridge: F takes the model's zero to 0.", Trans(Ce(Fv("Y"), e), f2, f3));
        }

        // Headline: F takes succ to + 1.
        {
            string h = $"( U e. {D} /\\ A e. ( lean.Nat ` U ) )";
            string k = $"( `' {Lit} ` A )";
            Proof hu = Hyp(h, $"U e. {D}");
            Proof se = Imp(h, "lean-nat-succeq", [Hyp(h, h)]);
            Proof ar = Rw(Hyp(h, "A e. ( lean.Nat ` U )"), Symm(Imp(h, "lean-nat-rnlit", [hu])));
            Proof kom = Imp(h, "f1ocnvdm", [Lift(h, litf1o), ar]);
            Proof lk = Imp(h, "f1ocnvfv2", [Lift(h, litf1o), ar]);
            Proof ls = Imp(h, "lean-nat-litsuc", [kom]);
            Proof succLit = Trans(se, Symm(Trans(ls, Ce(S("Y"), lk))));
            Thm("lean-nat-succlit", "The model's successor of n is the literal of n's ordinal plus one.", succLit);

            Proof r = Imp(h, "fnfvelrn", [Lift(h, litfn), Imp(h, "peano2", [kom])]);
            Proof inRn = Rw(r, Symm(succLit));
            Thm("lean-nat-succel", "The model's successor stays in the model's Nat.", Rw(inRn, Imp(h, "lean-nat-rnlit", [hu])));

            Proof f1 = Ce(Fv("Y"), succLit);
            Proof f2 = Imp(h, "lean-nat-flit", [Imp(h, "peano2", [kom])]);
            Proof f3 = Imp(h, "om2uzsuci", [kom], closed: [Use("0z"), eqG]);
            Proof f4 = Symm(Imp(h, "lean-nat-fval", [ar]));
            Thm("lean-nat-fsucc", "Bridge: F takes the model's successor to + 1.", Trans(f1, f2, f3, Ce("( Y + 1 )", f4)));
        }

        // Headline: F takes the literal of a numeral to the numeral.
        {
            const string h = "A e. NN0";
            Proof o = Lift(h, UseS("fveq1i", [("A", "A")], Ax("df-lean.Nat.-ofnum")));
            Proof dm = Imp(h, "f1ocnvdm", [Lift(h, gom), Hyp(h, h)]);
            Proof om = Rw(dm, Symm(o));
            Thm("lean-nat-ofnumom", "lean.Nat.-ofnum takes NN0 into omega.", om);
            Proof f1 = Imp(h, "lean-nat-flit", [om]);
            Proof f3 = Imp(h, "f1ocnvfv2", [Lift(h, gom), Hyp(h, h)]);
            Thm("lean-nat-flitnum", "Bridge: F takes the model's literal of a numeral to the numeral.", Trans(f1, Ce(Gv("Y"), o), f3));
            string h2 = $"( U e. {D} /\\ A e. NN0 )";
            Thm("lean-nat-litnumel", "The literal of a numeral is in the model's Nat.",
                Imp(h2, "lean-nat-litnat", [Hyp(h2, $"U e. {D}"), Imp(h2, "lean-nat-ofnumom", [Hyp(h2, "A e. NN0")])]));
        }

        // Equality in the model's Nat is equality of F's values.
        {
            string h = $"( U e. {D} /\\ ( A e. ( lean.Nat ` U ) /\\ B e. ( lean.Nat ` U ) ) )";
            Proof f1 = Imp(h, "f1of1", [Imp(h, "lean-nat-f1o", [Hyp(h, $"U e. {D}")])]);
            Proof bi = Imp(h, "f1fveq", [f1, Hyp(h, "( A e. ( lean.Nat ` U ) /\\ B e. ( lean.Nat ` U ) )")]);
            Thm("lean-nat-eq", "Bridge: two elements of the model's Nat are equal when their values under F are.", Use("bicomd", bi));
        }
    }

    // ================================================================ addition

    /// <summary>Nat.add's computation rules for a function G: a + 0 = a and a + succ b = succ (a + b).</summary>
    public string Rules(string g) =>
        $"( ( U e. {D} /\\ A. a e. {Nat} ( ( {g} ` a ) ` {Zero} ) = a ) /\\ " +
        $"A. a e. {Nat} A. b e. {Nat} ( ( {g} ` a ) ` {Succ("b")} ) = {Succ($"( ( {g} ` a ) ` b )")} )";

    private static string Ga(string g, string a, string b) => $"( ( {g} ` {a} ) ` {b} )";

    private void Arithmetic()
    {
        const string g = "G";
        string h0 = Rules(g);
        string c0 = $"( {h0} /\\ A e. {Nat} )";
        Proof eqG = UseS("eqid", [("A", Gm)]);

        // Induction on the second argument's ordinal.
        {
            string p = $"( {Ga(g, "A", Lt("n"))} e. {Nat} /\\ {Fv(Ga(g, "A", Lt("n")))} = ( {Fv("A")} + {Gv("n")} ) )";
            string r0 = $"A. a e. {Nat} ( ( {g} ` a ) ` {Zero} ) = a";
            string r1 = $"A. a e. {Nat} A. b e. {Nat} ( ( {g} ` a ) ` {Succ("b")} ) = {Succ($"( ( {g} ` a ) ` b )")}";

            // Base: A + 0 = A.
            Proof hu = Hyp(c0, $"U e. {D}"), ha = Hyp(c0, $"A e. {Nat}");
            Proof l0 = Trans(Lift(c0, Ax("lean-nat-lit0")), Symm(Imp(c0, "lean-nat-zeroeq", [hu])));
            Proof rz = Spec(SubBi("a", "A", $"( ( {g} ` a ) ` {Zero} ) = a"), Hyp(c0, r0), ha);
            Proof g0 = Trans(Ce(Ga(g, "A", "Y"), l0), rz);
            Proof mem0 = Use("eqeltrd", g0, ha);
            Proof fa = Imp(c0, "lean-nat-fcn", [hu, ha]);
            Proof add0 = Symm(Imp(c0, "addrid", [fa]));
            Proof z0 = Symm(Ce($"( {Fv("A")} + Y )", Lift(c0, Use("om2uz0i", Use("0z"), eqG))));
            Proof b = Use("jca", mem0, Trans(Ce(Fv("Y"), g0), add0, z0));

            // Step: A + succ j = succ (A + j).
            string pj = ProofKit.Replace(p, "n", "j");
            string h = $"( ( j e. _om /\\ {c0} ) /\\ {pj} )";
            Proof hj = Hyp(h, "j e. _om"), hu2 = Hyp(h, $"U e. {D}"), ha2 = Hyp(h, $"A e. {Nat}");
            string x = Ga(g, "A", Lt("j"));
            Proof xm = Use("simpld", Hyp(h, pj));
            Proof xf = Use("simprd", Hyp(h, pj));
            Proof ljn = Imp(h, "lean-nat-litnat", [hu2, hj]);
            Proof ls = Trans(Imp(h, "lean-nat-litsuc", [hj]), Symm(Imp(h, "lean-nat-succeq", [hu2, ljn])));
            string body1(string a) => $"A. b e. {Nat} ( ( {g} ` {a} ) ` {Succ("b")} ) = {Succ($"( ( {g} ` {a} ) ` b )")}";
            Proof ra = Spec(SubBi("a", "A", body1("a")), Hyp(h, r1), ha2);
            Proof rb = Spec(SubBi("b", Lt("j"), $"( ( {g} ` A ) ` {Succ("b")} ) = {Succ($"( ( {g} ` A ) ` b )")}"), ra, ljn);
            Proof g1 = Trans(Ce(Ga(g, "A", "Y"), ls), rb);
            Proof mem = Use("eqeltrd", g1, Imp(h, "lean-nat-succel", [hu2, xm]));
            Proof f2 = Imp(h, "lean-nat-fsucc", [hu2, xm]);
            Proof f3 = Ce("( Y + 1 )", xf);
            Proof f4 = Imp(h, "addass", [Imp(h, "lean-nat-fcn", [hu2, ha2]), Imp(h, "lean-nat-gcn", [hj]), Lift(h, Use("ax-1cn"))]);
            Proof f5 = Ce($"( {Fv("A")} + Y )", Symm(Imp(h, "om2uzsuci", [hj], closed: [Use("0z"), eqG])));
            Proof st = Use("jca", mem, Trans(Ce(Fv("Y"), g1), f2, f3, f4, f5));
            Thm("lean-nat-addind", "Addition by induction: any G with Nat.add's computation rules adds literals as + does.",
                _k.Finds("n", "j", p, c0, b, st, "C"));
        }

        // Headline: F ( G A B ) = F A + F B.
        {
            string h = $"( {h0} /\\ ( A e. {Nat} /\\ B e. {Nat} ) )";
            Proof hu = Hyp(h, $"U e. {D}");
            Proof ar = Rw(Hyp(h, $"B e. {Nat}"), Symm(Imp(h, "lean-nat-rnlit", [hu])));
            Proof litf1o = Ax("lean-nat-litf1o");
            Proof kom = Imp(h, "f1ocnvdm", [Lift(h, litf1o), ar]);
            Proof ctx = Use("jca", Hyp(h, h0), Hyp(h, $"A e. {Nat}"));
            Proof pk = Use("mpd", ctx, Imp(h, "lean-nat-addind", [kom]));
            Proof lk = Imp(h, "f1ocnvfv2", [Lift(h, litf1o), ar]);
            Proof gk = Symm(Imp(h, "lean-nat-fval", [ar]));
            Proof both = Rw(Rw(pk, lk), gk);
            Thm("lean-nat-addel", "A function with Nat.add's computation rules stays in the model's Nat.", Use("simpld", both));
            Thm("lean-nat-add", "Bridge: any function with Nat.add's computation rules is + through F.", Use("simprd", both));
        }

        // 2 + 2 = 4 through the bridge, and set.mm's 2p2e4 back in the model.
        {
            string l2 = Lt(Ofn("2")), l4 = Lt(Ofn("4"));
            string h = h0;
            Proof hu = Hyp(h, $"U e. {D}");
            Proof l2n = Imp(h, "lean-nat-litnumel", [hu, Lift(h, Use("2nn0"))]);
            Proof l4n = Imp(h, "lean-nat-litnumel", [hu, Lift(h, Use("4nn0"))]);
            string x = Ga(g, l2, l2);
            Proof xm = Imp(h, "lean-nat-addel", [Hyp(h, h), Use("jca", l2n, l2n)]);
            Proof eqb = Imp(h, "lean-nat-eq", [hu, Use("jca", xm, l4n)]);
            Proof fx = Imp(h, "lean-nat-add", [Hyp(h, h), Use("jca", l2n, l2n)]);
            Proof f2 = Lift(h, Imp(null, "lean-nat-flitnum", [Use("2nn0")]));
            Proof f4 = Lift(h, Imp(null, "lean-nat-flitnum", [Use("4nn0")]));
            Proof iff = Rw(Rw(eqb, Trans(fx, Ce("( Y + Y )", f2))), f4);
            Thm("lean-nat-2p2e4-iff", "Cross-check: 2 + 2 = 4 in the model is set.mm's ( 2 + 2 ) = 4, through the bridge.", iff);
            Thm("lean-nat-2p2e4", "Cross-check: set.mm's 2p2e4 proves 2 + 2 = 4 in the model, for any function with Nat.add's computation rules.",
                Use("mpbird", Lift(h, Use("2p2e4")), iff));
        }

        // The same, for the model's own Nat.add, given its rules (in tower mode they are proved: NatAddRules).
        if (D == "Univ")
        {
            (string, string)[] s = [("G", "( lean.Nat.add ` U )"), ("U", "U"), ("A", "A"), ("B", "B")];
            Thm("lean-nat-natadd", "Bridge: the model's Nat.add is + through F, given its computation rules.", UseS("lean-nat-add", s));
            Thm("lean-nat-natadd-2p2e4", "Cross-check: 2 + 2 = 4 for the model's Nat.add, from set.mm's 2p2e4, given its computation rules.",
                UseS("lean-nat-2p2e4", [("G", "( lean.Nat.add ` U )"), ("U", "U")]));
        }
    }

    // ================================================================ Nat.add's computation rules, proved (tower mode)

    /// <summary>
    /// In tower mode Nat.add satisfies its computation rules, so they are theorems: n + 0 = n and n + succ m = succ (n + m),
    /// each proved from Nat.add's definition by the theorem translator's conversion steps (through Nat.brecOn, Nat.below and
    /// Nat.rec). Then lean-nat-add applies with no hypotheses but the tower's: ⟦Nat.add⟧ is + through F.
    /// </summary>
    public void NatAddRules(TheoremTranslator tt)
    {
        Expr natT = tt.Const0("Nat"), zeroT = tt.Const0("Nat.zero"), succT = tt.Const0("Nat.succ"), addT = tt.Const0("Nat.add");
        Terms t = tt.Terms;
        Expr Plus(Expr a, Expr b) => t.App(t.App(addT, a), b);
        Expr Succ1(Expr a) => t.App(succT, a);
        var (zs, zp) = tt.ProveDefEq([natT], v => (Plus(v[0], zeroT), v[0]));
        Add("lean-nat-natadd-zero", "Nat.add's first computation rule, n + 0 = n, proved from its definition: it holds in tower mode.",
            zs, zp, Required(zp));
        var (ss, sp) = tt.ProveDefEq([natT, natT], v => (Plus(v[0], Succ1(v[1])), Succ1(Plus(v[0], v[1]))));
        Add("lean-nat-natadd-succ", "Nat.add's second computation rule, n + succ m = succ (n + m), proved from its definition: it holds in tower mode.",
            ss, sp, Required(sp));

        const string g = "( lean.Nat.add ` U )";
        string h = $"U e. {D}";
        {
            Proof l0 = Imp(h, "lean-nat-litnat", [Hyp(h, h), Lift(h, Use("peano1"))]);
            Proof e = Trans(Lift(h, Ax("lean-nat-lit0")), Symm(Imp(h, "lean-nat-zeroeq", [Hyp(h, h)])));
            Thm("lean-nat-zeroel", "The model's zero is in the model's Nat.", Rw(l0, e));
        }
        // A. a e. N ( G a 0 ) = a
        Proof z = UseS("lean-nat-natadd-zero", [("U", "U"), ("A", "a")]);
        Proof r0 = Use("ralrimiva", z);
        // A. a e. N A. b e. N ( G a ( succ b ) ) = succ ( G a b )
        Proof sb = UseS("lean-nat-natadd-succ", [("U", "U"), ("A", "a"), ("B", "b")]);
        Proof r1 = Use("ralrimiva", Use("ralrimiva", sb));
        Proof rules = Use("jca", Use("jca", UseS("id", [("ph", h)]), r0), r1);
        if (_k.Split(ProofKit.Of(rules)).X != Rules(g))
        {
            throw new InvalidOperationException($"Nat.add's rules came out as {ProofKit.Of(rules)}, not {Rules(g)}");
        }
        Thm("lean-nat-natadd-rules", "In tower mode the model's Nat.add satisfies its computation rules.", rules);

        string hab = $"( {h} /\\ ( A e. {Nat} /\\ B e. {Nat} ) )";
        Proof rr = Imp(hab, "lean-nat-natadd-rules", [Hyp(hab, h)]);
        Proof ab = Hyp(hab, $"( A e. {Nat} /\\ B e. {Nat} )");
        Thm("lean-nat-natadd", "Bridge: the model's Nat.add is + through F (no hypotheses but the tower's).",
            Imp(hab, "lean-nat-add", [rr, ab]));
        Thm("lean-nat-natadd-el", "The model's Nat.add stays in the model's Nat.", Imp(hab, "lean-nat-addel", [rr, ab]));
        Thm("lean-nat-natadd-2p2e4", "Cross-check: 2 + 2 = 4 for the model's Nat.add, from set.mm's 2p2e4.",
            Imp(h, "lean-nat-2p2e4", [Imp(h, "lean-nat-natadd-rules", [Hyp(h, h)])]));
    }

    /// <summary>
    /// A Lean theorem about Nat, proved through the model and restated in set.mm's arithmetic. The theorem must be
    /// ∀ (a b … : Nat), l = r with l and r built from +, 0, literals, Nat.succ and the variables (Nat.add_zero,
    /// Nat.zero_add). Three theorems are written:
    /// - lean-thm-T: (/) e. ⟦l = r⟧ in the model, from its proof term (TheoremTranslator);
    /// - lean-nat-T: ( F ` ⟦l⟧ ) = ( F ` ⟦r⟧ ) computed in NN0, for a b … in the model's Nat: Eq is =, l and r unfold to
    ///   Nat.add, Nat.zero and Nat.succ (conversion), and F takes those to +, 0 and + 1 (lean-nat-natadd, …);
    /// - lean-nn0-T: the statement in NN0, for A B … e. NN0, by substituting ( `' F ` A ) and F's inverse.
    /// So ( A + 0 ) = A, for instance, is derived from Lean's proof of Nat.add_zero, not from set.mm's addrid.
    /// </summary>
    public void Restate(TheoremTranslator tt, string name)
    {
        Terms t = tt.Terms;
        var ops = new Ops(t);
        string lp = Model.LabelPart(name);
        var (tstmt, tproof) = tt.Prove(t.Of(name));
        Add($"lean-thm-{lp}", $"The Lean theorem {name}, proved through the model from its proof term.", tstmt, tproof, Required(tproof));

        // The statement: binders over Nat, then @Eq Nat l r.
        Expr natT = tt.Const0("Nat");
        Expr ty = tt.Type0(name);
        var binderTypes = new List<Expr>();
        for (Expr b = ty; b is Binder { IsPi: true } pb; b = pb.Body)
        {
            binderTypes.Add(natT);
        }
        (Expr L, Expr R, Expr T) Sides(IReadOnlyList<Expr> fvs)
        {
            Expr e = ty;
            int i = 0;
            while (e is Binder { IsPi: true } pb)
            {
                if (!ReferenceEquals(Ops.Spine(pb.Domain, out _), Ops.Spine(natT, out _)) && $"{pb.Domain}" != $"{natT}")
                {
                    throw new Model.Refused($"{name}: restating needs every binder in Nat, not {pb.Domain}");
                }
                e = ops.Instantiate(pb.Body, [fvs[i++]]);
            }
            if (Ops.Spine(e, out List<Expr> a) is not Const { } eq || !$"{eq.Name}".StartsWith("Eq.{", StringComparison.Ordinal) || a.Count != 3)
            {
                throw new Model.Refused($"{name}: restating needs an equation, not {e}");
            }
            return (a[1], a[2], a[0]);
        }
        var (nfls, nflp) = tt.ProveDefEq(binderTypes, v => { var (l, _, _) = Sides(v); return (l, Nf(tt, l)); });
        var (nfrs, nfrp) = tt.ProveDefEq(binderTypes, v => { var (_, r, _) = Sides(v); return (r, Nf(tt, r)); });
        Add($"lean-nat-{lp}-lhs", $"The left side of {name}, unfolded to Nat.add, Nat.zero and Nat.succ.", nfls, nflp, Required(nflp));
        Add($"lean-nat-{lp}-rhs", $"The right side of {name}, unfolded to Nat.add, Nat.zero and Nat.succ.", nfrs, nfrp, Required(nfrp));
        Proof thm = Use($"lean-thm-{lp}");
        Proof dl = Use($"lean-nat-{lp}-lhs"), dr = Use($"lean-nat-{lp}-rhs");
        string ph = _k.Split(ProofKit.Of(thm)).H;
        Proof hu = Hyp(ph, $"U e. {D}");
        string nfl = _k.Sides(_k.Split(ProofKit.Of(dl)).X).R, nfr = _k.Sides(_k.Split(ProofKit.Of(dr)).X).R;

        // Eq is =: lean.Eq.{1} at ( N , L , R ) is if ( R = L , 1o , (/) ).
        Name eqInst = t.Of("Eq.{1}");
        var (es, ep, ed) = tt.Model.Equation(eqInst);
        if (!Db.Statements.ContainsKey("lean-Eq.u1-eq"))
        {
            Add("lean-Eq.u1-eq", "The definitional equation of Eq.{1}.", es, ep, ed);
        }
        Proof lm = Use("eqeltrd", dl, Mem(ph, nfl, hu));
        Proof rm = Use("eqeltrd", dr, Mem(ph, nfr, hu));
        Proof tyNat = Imp(ph, "lean-ty-Nat", [hu]);
        Proof eqv = Imp(ph, "lean-Eq.u1-eq", [Use("jca", Use("jca", Use("jca", hu, tyNat), lm), rm)]);
        Proof holds = Rw(thm, eqv);
        string cond = _k.Split(ProofKit.Of(holds)).X;   // (/) e. if ( R = L , 1o , (/) )
        string rEqL = _pr.Render(ProofKit.Child(ProofKit.Child(_k.Wff(cond), "B"), "ph"));
        Proof rl = Use("sylib", holds, UseS("lean-prop", [("ph", rEqL)]));
        Proof nfEq = Trans(Symm(dl), Symm(rl), dr);   // ( ph -> NfL = NfR )
        Proof fEq = Ce(Fv("Y"), nfEq);
        Proof model = Trans(Symm(FVal(ph, nfl, hu)), fEq, FVal(ph, nfr, hu));
        Thm($"lean-nat-{lp}", $"The Lean theorem {name} in NN0, for elements of the model's Nat: through the bridge F, from its proof through the model.", model);

        // For A B … in NN0: substitute ( `' F ` A ), which is in the model's Nat, and F ( `' F ` A ) = A.
        var vars = Enumerable.Range(0, binderTypes.Count).Select(i => ((char)('A' + i)).ToString()).ToList();
        string Inv(string v) => $"( `' {F} ` {v} )";
        Proof inst = UseS($"lean-nat-{lp}", [("U", "U"), .. vars.Select(v => (v, Inv(v)))]);
        string ph2 = vars.Aggregate($"U e. {D}", (acc, v) => $"( {acc} /\\ {v} e. NN0 )");
        Proof hu2 = Hyp(ph2, $"U e. {D}");
        Proof f1o = Imp(ph2, "lean-nat-f1o", [hu2]);
        Proof cnv = Imp(ph2, "f1ocnv", [f1o]);
        Proof cnvf = Imp(ph2, "f1of", [cnv]);
        Proof ctx = hu2;
        foreach (string v in vars)
        {
            ctx = Use("jca", ctx, Imp(ph2, "ffvelcdm", [cnvf, Hyp(ph2, $"{v} e. NN0")]));
        }
        Proof r = Use("syl", ctx, inst);
        foreach (string v in vars)
        {
            r = Rw(r, Imp(ph2, "f1ocnvfv2", [f1o, Hyp(ph2, $"{v} e. NN0")]));
        }
        Thm($"lean-nn0-{lp}", $"The Lean theorem {name}, restated in set.mm's arithmetic: derived from Lean's proof through the model and the bridge F.", r);
    }

    /// <summary>A side of an equation about Nat, as Nat.add, Nat.zero and Nat.succ over the free variables.</summary>
    private static Expr Nf(TheoremTranslator tt, Expr e)
    {
        Terms t = tt.Terms;
        Expr zero = tt.Const0("Nat.zero"), succ = tt.Const0("Nat.succ"), add = tt.Const0("Nat.add");
        Expr Lit(System.Numerics.BigInteger n) => n == 0 ? zero : t.App(succ, Lit(n - 1));
        Expr h = Ops.Spine(e, out List<Expr> a);
        string hn = h is Const c ? $"{c.Name}" : "";
        return (h, hn, a.Count) switch
        {
            (FVar, _, 0) => e,
            (NatLit l, _, 0) when l.Value <= 10 => Lit(l.Value),
            (_, "Nat.zero", 0) => zero,
            (_, "Nat.succ", 1) => t.App(succ, Nf(tt, a[0])),
            (_, "Nat.add", 2) => t.App(t.App(add, Nf(tt, a[0])), Nf(tt, a[1])),
            (_, "HAdd.hAdd.{0,0,0}", 6) => t.App(t.App(add, Nf(tt, a[4])), Nf(tt, a[5])),
            (_, "OfNat.ofNat.{0}", 3) when a[1] is NatLit l && l.Value <= 10 => Lit(l.Value),
            _ => throw new Model.Refused($"restating: {e} is not built from +, literals, Nat.succ and variables"),
        };
    }

    /// <summary>( ph -> nf e. ( lean.Nat ` U ) ) for a text built from Nat.add, Nat.zero, Nat.succ and class variables in Nat.</summary>
    private Proof Mem(string ph, string nf, Proof hu)
    {
        SyntaxTree n = _k.Tree("class", nf.Split(' '));
        if (nf == Zero)
        {
            return Imp(ph, "lean-nat-zeroel", [hu]);
        }
        if (n.Rule.Label == "cfv" && _pr.Render(n.Children[1]) is string f)
        {
            string arg = _pr.Render(n.Children[0]);
            if (f == "( lean.Nat.succ ` U )")
            {
                return Imp(ph, "lean-nat-succel", [hu, Mem(ph, arg, hu)]);
            }
            SyntaxTree inner = n.Children[1];
            if (inner.Rule.Label == "cfv" && _pr.Render(inner.Children[1]) == "( lean.Nat.add ` U )")
            {
                string x = _pr.Render(inner.Children[0]);
                return Imp(ph, "lean-nat-natadd-el", [hu, Use("jca", Mem(ph, x, hu), Mem(ph, arg, hu))]);
            }
        }
        return Hyp(ph, $"{nf} e. {Nat}");
    }

    /// <summary>( ph -> ( F ` nf ) = arithmetic ) for a text as in <see cref="Mem"/>: + for Nat.add, 0 for zero, + 1 for succ.</summary>
    private Proof FVal(string ph, string nf, Proof hu)
    {
        SyntaxTree n = _k.Tree("class", nf.Split(' '));
        if (nf == Zero)
        {
            return Imp(ph, "lean-nat-fzero", [hu]);
        }
        if (n.Rule.Label == "cfv")
        {
            string f = _pr.Render(n.Children[1]), arg = _pr.Render(n.Children[0]);
            if (f == "( lean.Nat.succ ` U )")
            {
                Proof inner = FVal(ph, arg, hu);
                return Trans(Imp(ph, "lean-nat-fsucc", [hu, Mem(ph, arg, hu)]), Ce("( Y + 1 )", inner));
            }
            SyntaxTree g = n.Children[1];
            if (g.Rule.Label == "cfv" && _pr.Render(g.Children[1]) == "( lean.Nat.add ` U )")
            {
                string x = _pr.Render(g.Children[0]);
                Proof add = Imp(ph, "lean-nat-natadd", [hu, Use("jca", Mem(ph, x, hu), Mem(ph, arg, hu))]);
                Proof fx = FVal(ph, x, hu), fy = FVal(ph, arg, hu);
                string ry = _k.Sides(_k.Split(ProofKit.Of(fy)).X).L;
                Proof c1 = Ce($"( Y + {ry} )", fx);
                string lx = _k.Sides(_k.Split(ProofKit.Of(fx)).X).R;
                Proof c2 = Ce($"( {lx} + Y )", fy);
                return Trans(add, c1, c2);
            }
        }
        return _k.Refl(ph, Fv(nf));
    }

    private string[] Required(List<string> proof) =>
        DistinctVars.Required(Db, proof).Select(p => $"{p.Item1} {p.Item2}").ToArray();

    // ================================================================ a limit of the current model

    /// <summary>
    /// Why Nat.add's computation rules are hypotheses: in the one-universe model, Nat.below's motive returns the
    /// universe U itself, and U is not in U, so the motive is outside Nat.rec's domain and Nat.below is (/) at every
    /// argument. Lean's Nat.below motive 0 is PUnit, which is not empty. Nat.add, compiled through Nat.brecOn and
    /// Nat.below, inherits this. Needs Nat.below's definitional equation (label lean-Nat.below-eq) in the database.
    /// </summary>
    public void BelowCollapses(string[] belowEqDistinct)
    {
        string h = $"U e. {D}";
        string m = "( z e. ( lean.Nat ` U ) |-> U )";
        SyntaxTree df = _k.Tree("wff", Db["df-lean.Nat.rec"].Expr.Symbols);
        string inner = _pr.Render(ProofKit.Child(ProofKit.Child(df, "B"), "B"));
        string innerU = ProofKit.Replace(inner, "u", "U");
        string dom = $"( U ^m {Nat} )";
        Proof rec = Use("fvmpt", SubEq("u", "U", inner), Ax("df-lean.Nat.rec"),
            UseG("mptex", $"{innerU} e. _V", UseS("ovex", [("A", "U"), ("F", "^m"), ("B", Nat)])));

        // The motive ( z e. Nat |-> U ) is not a function into U: its value U would be in U.
        string h2 = $"( U e. {D} /\\ ( z e. ( lean.Nat ` U ) |-> U ) e. ( U ^m ( lean.Nat ` U ) ) )";
        Proof f = Imp(h2, "elmapi", [Hyp(h2, $"{m} e. {dom}")]);
        Proof zn = Imp(h2, "lean-nat-litnat", [Hyp(h2, $"U e. {D}"), Lift(h2, Use("peano1"))]);
        Proof fv = Imp(h2, "ffvelcdm", [f, zn]);
        Proof mv = UseS("fvmptd3", [("V", D)], UseS("eqid", [("A", m)]), Lift($"z = {Lt("(/)")}", UseS("eqid", [("A", "U")])), zn, Hyp(h2, $"U e. {D}"));
        Proof uu = Rw(fv, mv);
        Proof notIn = Use("mtod", Lift(h, UseS("elirr", [("A", "U")])), Use("ex", uu));
        Proof domSs = Rw(Lift(h, Use("dmmptss", UseS("eqid", [("A", innerU)]))), Symm(Use("syl", Hyp(h, h), rec)));
        Proof notDom = Use("mpd", notIn, UseS("ssneld", [("C", m)], domSs));
        Thm("lean-nat-belowmotive", "The motive Nat.below gives Nat.rec is outside Nat.rec's domain in the one-universe model.",
            Imp(h, "ndmfv", [notDom]));

        // So Nat.below is (/) everywhere.
        Proof eq = Use("lean-Nat.below-eq");
        string ant = _k.Split(ProofKit.Of(eq)).H;
        Proof r = Rw(eq, Imp(ant, "lean-nat-belowmotive", [Hyp(ant, $"U e. {D}")]));
        while (ZeroApp(_k.Split(ProofKit.Of(r)).X) is string arg)
        {
            r = Rw(r, Lift(ant, UseS("0fv", [("A", arg)])));
        }
        Thm("lean-nat-belowempty", "In the one-universe model, Nat.below is empty at every argument (Lean's Nat.below motive 0 is PUnit).",
            r, belowEqDistinct);
    }

    /// <summary>The argument A of the first ( (/) ` A ) in a formula, or null.</summary>
    private static string? ZeroApp(string x)
    {
        string[] t = x.Split(' ');
        for (int i = 0; i + 3 < t.Length; i++)
        {
            if (t[i] == "(" && t[i + 1] == "(/)" && t[i + 2] == "`")
            {
                int depth = 0, j = i + 3;
                var arg = new List<string>();
                for (; j < t.Length; j++)
                {
                    if (depth == 0 && t[j] == ")")
                    {
                        return string.Join(' ', arg);
                    }
                    depth += t[j] is "(" or "<." or "{" ? 1 : t[j] is ")" or ">." or "}" ? -1 : 0;
                    arg.Add(t[j]);
                }
            }
        }
        return null;
    }

    // ================================================================ literals

    /// <summary>|- n e. NN0 for a decimal numeral: a digit's own theorem, or deccl.</summary>
    private Proof Nn0(System.Numerics.BigInteger n) =>
        n < 10 ? Use($"{n}nn0") : Use("deccl", Nn0(n / 10), Nn0(n % 10));

    /// <summary>|- ( F ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` n ) ) ) = n for a decimal numeral n.</summary>
    public void Numeral(System.Numerics.BigInteger n)
    {
        Thm($"lean-nat-lit-{n}", $"Bridge: F takes the model's literal {n} to the numeral {n}.", Imp(null, "lean-nat-flitnum", [Nn0(n)]));
    }
}
