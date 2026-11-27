using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Bridge theorems between the generic model's List (docs/milestone3.md) and set.mm's Word (docs/bridges.md).
///
/// The model's List A, at a universe U and a type A in ( U ` (/) ), is the union of an ω-chain of stages of tagged
/// tuples: nil is &lt;. (/) , (/) &gt;. and cons a l is &lt;. 1o , &lt;. (/) , &lt;. a , &lt;. l , (/) &gt;. &gt;. &gt;. &gt;.. The bridge W is
/// built by recursion on ω alongside those stages: stage k of W is a function on stage k of List A, taking nil to
/// (/) and cons a l to ( &lt;" a "&gt; ++ ( W ` l ) ). Each stage is one-to-one into Word A, the stages form a chain, and
/// their union (f1iun) is a bijection from List A onto Word A. Through W, the model's List.length is # (with the Nat
/// bridge F), List.append and HAppend.hAppend are ++, and List.nil is (/). Lean's List.length_append, proved through
/// the model from its proof term, then restates as set.mm's ccatlen.
///
/// Every theorem is proved from the model's definitions and set.mm and checked by the verifiers; each carries exactly
/// the $d conditions its proof needs (the terms here bind variables that later substitutions must not meet).
/// </summary>
public sealed class ListBridge
{
    private readonly Prover _pr;
    private readonly ProofKit _k;
    private readonly NatBridge _nat;
    private readonly Model _model;
    private Database Db => _pr.Database;

    // ---------------------------------------------------------------- the texts

    public const string Tw = "lean.-tower";
    /// <summary>The hypotheses of every List theorem: U is a tower, and A a type of its first universe.</summary>
    public const string H0 = "( U e. lean.-tower /\\ A e. ( U ` (/) ) )";
    /// <summary>The model's List A.</summary>
    public const string L = "( ( lean.List.{0} ` U ) ` A )";
    public const string Nil = "<. (/) , (/) >.";
    public static string Cons(string a, string l) => $"<. 1o , <. (/) , <. {a} , <. {l} , (/) >. >. >. >.";
    /// <summary>The recursion whose values are the stages of the model's List A.</summary>
    public const string Rf = "rec ( ( v e. _V |-> ( lean.List.{0}.-step ` <. <. U , <. A , (/) >. >. , v >. ) ) , (/) )";
    public static string St(string k) => $"( {Rf} ` {k} )";
    /// <summary>nil, and cons of every element of A and of S.</summary>
    public static string Xs(string s) => $"( {{ {Nil} }} u. U_ y e. A U_ z e. {s} {{ {Cons("y", "z")} }} )";
    public static string Hd(string x) => $"( 1st ` ( 2nd ` ( 2nd ` {x} ) ) )";
    public static string Tl(string x) => $"( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` {x} ) ) ) )";

    /// <summary>W's step on a graph R: nil to (/), cons a l (l in R's domain) to ( &lt;" a "&gt; ++ ( R ` l ) ).</summary>
    public static string Dm(string r) => Xs($"dom {r}");
    public static string Val(string r, string x) => $"if ( {x} = {Nil} , (/) , ( <\" {Hd(x)} \"> ++ ( {r} ` {Tl(x)} ) ) )";
    public static string Mp(string r) => $"( x e. {Dm(r)} |-> {Val(r, "x")} )";

    /// <summary>
    /// The step as written inside the recursion. Its binders (r s b t) differ from the lemmas' (x y z), so that a lemma
    /// about Mp ( R ) can be used at a stage of W, which contains this text.
    /// </summary>
    public const string Gf = "( r e. _V |-> ( s e. ( { <. (/) , (/) >. } u. U_ b e. A U_ t e. dom r { <. 1o , <. (/) , <. b , <. t , (/) >. >. >. >. } )"
        + " |-> if ( s = <. (/) , (/) >. , (/) , ( <\" ( 1st ` ( 2nd ` ( 2nd ` s ) ) ) \"> ++ ( r ` ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` s ) ) ) ) ) ) ) ) )";
    public static string Gf2 => $"( q e. _V |-> {Mp("q")} )";
    public static string Rk(string k) => $"( rec ( {Gf} , (/) ) ` {k} )";
    /// <summary>The bridge: the model's List A onto Word A.</summary>
    public static string W => $"U_ n e. _om {Rk("n")}";
    public static string Wv(string t) => $"( {W} ` {t} )";

    public ListBridge(Prover pr, NatBridge nat, Model model)
    {
        _pr = pr;
        _k = new ProofKit(pr);
        _nat = nat;
        _model = model;
    }

    /// <summary>
    /// The whole List bridge as a set.mm file: the model's definitions, the Nat bridge (with Nat.add's rules), the
    /// bijection W and its computation through List.length, List.append and HAppend.hAppend, then each theorem named
    /// (List.length_append) proved through the model and restated in set.mm's words. With <paramref name="bridgeOnly"/>
    /// only the bijection is proved (no Nat bridge, no restatement).
    /// </summary>
    public static (string Text, List<(string Label, string Comment, MmExpr Statement, List<string> Proof, string[] Distinct)> Theorems) Emit(
        string export, string setmm, IReadOnlyList<string> restate, bool compress = true, bool bridgeOnly = false, Action<string>? log = null)
    {
        var sw = System.Diagnostics.Stopwatch.StartNew();
        void Log(string m) => log?.Invoke($"[{sw.Elapsed.TotalSeconds,6:F1}s] {m}");
        var t = new Terms();
        Environment env = Reader.ReadExport(t, export);
        var pr = new Prover(Database.Read(setmm));
        Log("read the export and set.mm");
        var tt = new TheoremTranslator(t, env, pr);
        var nat = new NatBridge(pr, tower: true);
        Model model = tt.Model;
        foreach (string c in new[] { "List", "List.nil", "List.cons" })
        {
            model.Define(((Const)tt.Const0(c)).Name);
        }
        var bridge = new ListBridge(pr, nat, model);
        bridge.ProveAll(tt);
        Log("the bijection W from the model's List onto Word");
        if (!bridgeOnly)
        {
            foreach (string c in new[] { "Nat", "Nat.zero", "Nat.succ", "Nat.add" })
            {
                model.Define(((Const)tt.Const0(c)).Name);
            }
            model.Class(t.Nat(2), "U", new Dictionary<ulong, string>());   // declares the literal maps
            nat.ProveAll([]);
            Log("the Nat bridge F");
            nat.NatAddRules(tt);
            Log("Nat.add's computation rules, so F takes Nat.add to +");
            bridge.Computation(tt);
            Log("List.length, List.append and HAppend.hAppend through W");
            foreach (string name in restate)
            {
                bridge.Restate(tt, name);
                Log($"{name} through the model, restated in set.mm's words");
            }
        }
        var w = new Writer(Path.GetFileName(setmm), "tenet-zfc bridge theorems: the model's List is Word (docs/bridges.md)", compress ? pr.Database : null);
        w.Assumptions(model.Assumptions());
        w.Raw(model.Declarations);
        foreach (var th in nat.Theorems)
        {
            w.Theorem(th.Label, th.Comment, th.Statement, compress ? th.Proof : pr.Database.Shared.Expand(th.Proof), th.Distinct);
        }
        Log("written");
        return (w.ToString(), nat.Theorems);
    }

    public void ProveAll(TheoremTranslator tt)
    {
        CheckEncoding();
        Constructors(tt);
        Stages();
        Step();
        Graph();
        OnList();
    }

    // ---------------------------------------------------------------- the proof kit, as in NatBridge

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
    private Proof Cw(string ctx, Proof eq) => _k.Cong("wff", ctx, "Y", eq);
    private Proof Id(string eq) => UseS("id", [("ph", eq)]);
    private Proof SubEq(string x, string t, string body) => _k.CongEq(ProofKit.Replace(body, x, "Y"), "Y", Id($"{x} = {t}"));
    private Proof SubBi(string x, string t, string body) => _k.Cong("wff", ProofKit.Replace(body, x, "Y"), "Y", Id($"{x} = {t}"));
    private Proof Vex(string x) => UseS("vex", [("x", x)]);
    private Proof Opex(string a, string b) => UseS("opex", [("A", a), ("B", b)]);
    private Proof Fvex(string f, string a) => UseS("fvex", [("F", f), ("A", a)]);
    private static string Of(Proof p) => ProofKit.Of(p);
    private string Ante(Proof p) => _k.Split(Of(p)).H;
    private string Cons_(Proof p) => _k.Split(Of(p)).X;
    private string Lhs(Proof p) => _k.Sides(Cons_(p)).L;
    private string Rhs(Proof p) => _k.Sides(Cons_(p)).R;

    /// <summary>( h -> P(C) ) from ( h -> A. x e. A P(x) ) and ( h -> C e. A ), by rspcv.</summary>
    private Proof Spec(string x, string body, Proof all, Proof mem)
    {
        string h = Ante(mem);
        string c = _k.Split(Of(mem)).X;
        string t = c[..c.IndexOf(" e. ", StringComparison.Ordinal)];
        return Use("mpd", all, Imp(h, "rspcv", [mem], closed: [SubBi(x, t, body)]));
    }

    /// <summary>Record a theorem with exactly the $d conditions its proof needs, and teach it to the prover.</summary>
    public void Thm(string label, string comment, Proof p) => _nat.Add(label, comment, p.Proves, p.Proof, Required(p.Proof));

    private string[] Required(List<string> proof) =>
        DistinctVars.Required(Db, proof).Select(p => $"{p.Item1} {p.Item2}").ToArray();

    /// <summary>A recorded theorem, instantiated.</summary>
    private Proof T(string label, params (string, string)[] s) => UseS(label, s);

    // ================================================================ the stages of the model's List

    public void CheckEncoding()
    {
        void Expect(string label, string text)
        {
            string have = Db.Statements.TryGetValue(label, out Statement? s) ? string.Join(' ', s.Expr.Symbols) : "(missing)";
            if (have != text)
            {
                throw new InvalidOperationException($"the model's {label} is not the encoding the List bridge proves things about:\n  have {have}\n  want {text}");
            }
        }
        Expect("df-lean.List.u0", "lean.List.{0} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> U_ y e. _om ( rec ( ( v e. _V |-> ( lean.List.{0}.-step ` <. <. u , <. x , (/) >. >. , v >. ) ) , (/) ) ` y ) ) )");
        Expect("df-lean.List.u0.-step", "lean.List.{0}.-step = ( w e. _V |-> ( ( 2nd ` w ) u. ( { <. (/) , (/) >. } u. U_ y e. ( 1st ` ( 2nd ` ( 1st ` w ) ) ) U_ z e. ( 2nd ` w ) { <. 1o , <. (/) , <. y , <. z , (/) >. >. >. >. } ) ) )");
        Expect("df-lean.List.nil.u0", "lean.List.nil.{0} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> <. (/) , (/) >. ) )");
        Expect("df-lean.List.cons.u0", "lean.List.cons.{0} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> ( y e. x |-> ( z e. ( ( lean.List.{0} ` u ) ` x ) |-> <. 1o , <. (/) , <. y , <. z , (/) >. >. >. >. ) ) ) )");
    }

    /// <summary>The model's definitional equations of List, List.nil and List.cons, with the $d conditions their proofs need.</summary>
    private void Constructors(TheoremTranslator tt)
    {
        foreach (var (name, label) in new[] { ("List", "lean-list-eq"), ("List.nil", "lean-list-nileq"), ("List.cons", "lean-list-conseq") })
        {
            var (s, p, _) = _model.Equation(((Const)tt.Const0(name)).Name);
            _nat.Add(label, $"The definitional equation of {name}.{{0}}.", s, p, Required(p));
        }
        // The model's List as the union of its stages, indexed by k (its own binder y is the stages' cons variable).
        {
            Proof eq = Use("lean-list-eq");
            string iu = Rhs(eq);
            string iuk = $"U_ k e. _om {St("k")}";
            Thm("lean-list-iun", "The model's List A is the union of its stages.", Trans(eq, Lift(H0, _model.AlphaEq(iu, iuk))));
        }
    }

    /// <summary>U and A are sets: the stages and W's step are about sets.</summary>
    public const string Hv = "( U e. _V /\\ A e. _V )";

    private void Stages()
    {
        Thm("lean-list-stage0", "The first stage of the model's List is empty.", UseG("rdg0", $"{St("(/)")} = (/)", Use("0ex")));

        // Each stage adds nil and cons of every element of A and of the last stage.
        {
            const string h = "( ( U e. _V /\\ A e. _V ) /\\ K e. _om )";
            string x = St("K");
            const string stepF = "lean.List.{0}.-step";
            string gv = $"( v e. _V |-> ( {stepF} ` <. <. U , <. A , (/) >. >. , v >. ) )";
            string gw = $"( w e. _V |-> ( {stepF} ` <. <. U , <. A , (/) >. >. , w >. ) )";
            string p = $"<. <. U , <. A , (/) >. >. , {x} >.";
            Proof hk = Hyp(h, "K e. _om");
            Proof e1 = Imp(h, "rdgsuc", [Imp(h, "nnon", [hk])], q: $"{St("suc K")} = ( {gv} ` {x} )");
            Proof cbv = UseS("cbvmptv", [("A", "_V")], SubEq("v", "w", $"( {stepF} ` <. <. U , <. A , (/) >. >. , v >. )"));
            Proof e2 = UseS("fveq1i", [("A", x)], cbv);
            Proof fv3 = UseS("fvmpt", [("D", "_V")],
                SubEq("w", x, $"( {stepF} ` <. <. U , <. A , (/) >. >. , w >. )"), UseS("eqid", [("A", gw)]), Fvex(stepF, p));
            Proof e3 = Use("ax-mp", UseG("fvex", $"{x} e. _V"), fv3);
            string body(string y) => $"( ( 2nd ` {y} ) u. ( {{ {Nil} }} u. U_ y e. ( 1st ` ( 2nd ` ( 1st ` {y} ) ) ) U_ z e. ( 2nd ` {y} ) {{ {Cons("y", "z")} }} ) )";
            Proof iunIn = UseS("iunex", [("x", "z")], Fvex("2nd", "w"), UseS("snex", [("A", Cons("y", "z"))]));
            Proof iunOut = UseS("iunex", [("x", "y")], Fvex("1st", "( 2nd ` ( 1st ` w ) )"), iunIn);
            Proof cexw = Use("unex", Fvex("2nd", "w"), Use("unex", UseS("snex", [("A", Nil)]), iunOut));
            // The step's value at p, a set (by the same union, written at p).
            Proof iunInP = UseS("iunex", [("x", "z")], Fvex("2nd", p), UseS("snex", [("A", Cons("y", "z"))]));
            Proof iunOutP = UseS("iunex", [("x", "y")], Fvex("1st", $"( 2nd ` ( 1st ` {p} ) )"), iunInP);
            Proof cex = Use("unex", Fvex("2nd", p), Use("unex", UseS("snex", [("A", Nil)]), iunOutP));
            _ = cexw;
            Proof fv4 = Use("fvmpt", SubEq("w", p, body("w")), Ax("df-lean.List.u0.-step"), cex);
            Proof e4 = Use("ax-mp", Opex("<. U , <. A , (/) >. >.", x), fv4);
            Proof e = Trans(e1, Lift(h, e2), Lift(h, e3), Lift(h, e4));
            Proof snd = Use("op2nd", Opex("U", "<. A , (/) >."), UseG("fvex", $"{x} e. _V"));
            Proof fst = Use("op1st", Opex("U", "<. A , (/) >."), UseG("fvex", $"{x} e. _V"));
            Proof snd2 = Imp(h, "op2ndg", [Hyp(h, "U e. _V"), Lift(h, Opex("A", "(/)"))]);
            Proof fst2 = Imp(h, "op1stg", [Hyp(h, "A e. _V"), Lift(h, Use("0ex"))]);
            e = Rw(e, Lift(h, snd));
            e = Rw(e, Lift(h, fst));
            e = Rw(e, snd2);
            e = Rw(e, fst2);
            Thm("lean-list-stagesuc", "Each stage of the model's List adds nil and cons of every element of A and of the last stage.", e);
        }
    }

    // ================================================================ W's step on graphs

    private void Step()
    {
        {
            // Rename Gf's binders r s b t to q x y z: cbvmptv, cbviunv.
            string inner(string r, string sv) =>
                $"( {sv} e. ( {{ {Nil} }} u. U_ b e. A U_ t e. dom {r} {{ {Cons("b", "t")} }} ) |-> {Val(r, sv)} )";
            Proof e1 = UseS("cbvmptv", [("A", "_V")], SubEq("r", "q", inner("r", "s")));
            string dq = $"( {{ {Nil} }} u. U_ b e. A U_ t e. dom q {{ {Cons("b", "t")} }} )";
            Proof e2 = UseS("cbvmptv", [("A", dq)], SubEq("s", "x", Val("q", "s")));
            Proof i1 = UseS("cbviunv", [("A", "dom q")], SubEq("t", "z", $"{{ {Cons("b", "t")} }}"));
            Proof i2 = UseS("iuneq2i", [("x", "b"), ("A", "A")], Lift("b e. A", i1));
            Proof i3 = UseS("cbviunv", [("A", "A")], SubEq("b", "y", $"U_ z e. dom q {{ {Cons("b", "z")} }}"));
            Proof e3 = UseS("uneq2i", [("C", $"{{ {Nil} }}")], Use("eqtri", i2, i3));
            Proof e4 = UseS("mpteq1i", [("x", "x"), ("C", Val("q", "x"))], e3);
            Proof e5 = UseS("mpteq2i", [("x", "q"), ("A", "_V")], Use("eqtri", e2, e4));
            Thm("lean-list-gf2", "W's step, with its binders renamed apart from the lemmas'.", Use("eqtri", e1, e5));
        }
        Thm("lean-list-g0", "W's first stage is empty.", UseG("rdg0", $"{Rk("(/)")} = (/)", Use("0ex")));

        // The step's domain is a set.
        {
            const string h = "( A e. _V /\\ S e. _V )";
            string inner = $"U_ z e. S {{ {Cons("y", "z")} }}";
            Proof pin = Imp(h, "iunexg", [Hyp(h, "S e. _V"), Lift(h, UseS("rgen", [("x", "z"), ("A", "S")], Lift("z e. S", UseS("snex", [("A", Cons("y", "z"))]))))], s: [("V", "_V"), ("W", "_V")]);
            Proof all = UseS("ralrimivw", [("x", "y"), ("A", "A")], pin);
            Proof pout = Imp(h, "iunexg", [Hyp(h, "A e. _V"), all], s: [("V", "_V"), ("W", "_V")]);
            Proof u = Imp(h, "unexg", [Lift(h, UseS("snex", [("A", Nil)])), pout], s: [("V", "_V"), ("W", "_V")]);
            _ = inner;
            Thm("lean-list-xsex", "nil and the conses over a set form a set.", u);
        }
        // nil, and conses over a bigger set, are a bigger set.
        {
            const string h = "S C_ T";
            Proof inner = Imp(h, "iunss1", [Hyp(h, h)], s: [("x", "z"), ("C", $"{{ {Cons("y", "z")} }}")]);
            Proof all = UseS("ralrimivw", [("x", "y"), ("A", "A")], inner);
            Proof outer = Imp(h, "ss2iun", [all]);
            Thm("lean-list-xss", "nil and the conses over a set grow with the set.", Imp(h, "unss2", [outer], s: [("C", $"{{ {Nil} }}")]));
        }
        // The projections of a cons.
        {
            const string h = "( B e. _V /\\ C e. _V )";
            Proof c1 = Use("op2nd", Use("1oex"), Opex("(/)", "<. B , <. C , (/) >. >."));
            Proof c2 = Use("op2nd", Use("0ex"), Opex("B", "<. C , (/) >."));
            Proof hdb = Imp(h, "op1stg", [Hyp(h, "B e. _V"), Lift(h, Opex("C", "(/)"))]);
            string cbc = Cons("B", "C");
            Proof hd = Trans(Ce("( 1st ` ( 2nd ` Y ) )", Lift(h, c1)), Ce("( 1st ` Y )", Lift(h, c2)), hdb);
            Thm("lean-list-hd", "The head of a cons.", hd);
            Proof c3 = Imp(h, "op2ndg", [Hyp(h, "B e. _V"), Lift(h, Opex("C", "(/)"))]);
            Proof c4 = Imp(h, "op1stg", [Hyp(h, "C e. _V"), Lift(h, Use("0ex"))]);
            Proof tl = Trans(Ce("( 1st ` ( 2nd ` ( 2nd ` Y ) ) )", Lift(h, c1)), Ce("( 1st ` ( 2nd ` Y ) )", Lift(h, c2)), Ce("( 1st ` Y )", c3), c4);
            _ = cbc;
            Thm("lean-list-tl", "The tail of a cons.", tl);
            Proof o = UseS("opth1", [("C", "(/)"), ("D", "(/)")], Use("1oex"), Opex("(/)", "<. B , <. C , (/) >. >."));
            Thm("lean-list-consnnil", "A cons is not nil.", Use("mto", Use("neii", Use("1n0")), o));
        }
        // An element of the step's domain other than nil is a cons of its head and tail.
        {
            string dm = Dm("R");
            string iu = $"U_ y e. A U_ z e. dom R {{ {Cons("y", "z")} }}";
            string iuz = $"U_ z e. dom R {{ {Cons("y", "z")} }}";
            string c = $"( x e. {dm} /\\ -. x = {Nil} )";
            string g = $"( ( {Hd("x")} e. A /\\ {Tl("x")} e. dom R ) /\\ x = {Cons(Hd("x"), Tl("x"))} )";
            Proof orr = Use("sylib", Hyp(c, $"x e. {dm}"), UseS("elun", [("A", "x"), ("B", $"{{ {Nil} }}"), ("C", iu)]));
            Proof nsn = Use("sylnibr", Hyp(c, $"-. x = {Nil}"), UseS("elsn", [("A", "x"), ("B", Nil)], Vex("x")));
            Proof inIu = Use("mpd", nsn, Use("ord", orr));
            Proof ex0 = Use("sylib", inIu, UseS("eliun", [("A", "x"), ("x", "y"), ("B", "A"), ("C", iuz)]));
            // Rename the witnesses to g and h: the context binds y and z (in Dm), so they can't be the rexlim variables.
            Proof ex1 = Use("sylib", ex0, UseS("cbvrexvw", [("A", "A")], SubBi("y", "g", $"x e. {iuz}")));
            string iug = $"U_ z e. dom R {{ {Cons("g", "z")} }}";
            Proof inner = Use("bitri", UseS("eliun", [("A", "x"), ("x", "z"), ("B", "dom R"), ("C", $"{{ {Cons("g", "z")} }}")]),
                UseS("cbvrexvw", [("A", "dom R")], SubBi("z", "h", $"x e. {{ {Cons("g", "z")} }}")));
            string d = $"( ( ( {c} /\\ g e. A ) /\\ h e. dom R ) /\\ x e. {{ {Cons("g", "h")} }} )";
            Proof xe = Imp(d, "elsni", [Hyp(d, $"x e. {{ {Cons("g", "h")} }}")]);
            Proof hdc = Imp(null, "lean-list-hd", [Vex("g"), Vex("h")]);
            Proof tlc = Imp(null, "lean-list-tl", [Vex("g"), Vex("h")]);
            Proof hd = Trans(Ce(Hd("Y"), xe), Lift(d, hdc));
            Proof tl = Trans(Ce(Tl("Y"), xe), Lift(d, tlc));
            Proof e1 = Ce(Cons("Y", "h"), hd);
            Proof e2 = Ce(Cons(Hd("x"), "Y"), tl);
            Proof xeq = Trans(xe, Symm(e1), Symm(e2));
            Proof goal = Use("jca", Use("jca", Use("eqeltrd", hd, Hyp(d, "g e. A")), Use("eqeltrd", tl, Hyp(d, "h e. dom R"))), xeq);
            Proof i2 = Use("rexlimdva", Use("ex", goal));
            Proof i3 = Use("sylbid", Lift($"( {c} /\\ g e. A )", inner), i2);
            Proof i4 = Use("rexlimdva", i3);
            _ = iug;
            Proof r = Use("mpd", ex1, i4);
            if (Cons_(r) != g)
            {
                throw new InvalidOperationException($"dmcase came out as {Of(r)}");
            }
            Thm("lean-list-dmcase", "An element of W's step's domain other than nil is a cons of its head and tail.", r);
        }
        // The step's values are sets, so its domain is Dm.
        {
            Proof vex = UseS("ifex", [("ph", $"x = {Nil}")], Use("0ex"), UseS("ovex", [("A", $"<\" {Hd("x")} \">"), ("F", "++"), ("B", $"( R ` {Tl("x")} )")]));
            Proof all = UseS("rgen", [("x", "x"), ("A", Dm("R"))], Lift($"x e. {Dm("R")}", vex));
            Thm("lean-list-dmmp", "The domain of W's step at R.", Imp(null, "dmmptg", [all], s: [("V", "_V")]));
        }
        StepF1();
        // The step is monotone, on functions.
        {
            const string h = "( Fun S /\\ R C_ S )";
            Proof dss = Imp(h, "dmss", [Hyp(h, "R C_ S")]);
            Proof xss = Imp(h, "lean-list-xss", [dss]);
            string c = $"( {h} /\\ x e. {Dm("R")} )";
            string cN = $"( {c} /\\ -. x = {Nil} )";
            var (_, tl, _) = DmFacts(cN, "x", "R");
            Proof fs = Imp(cN, "funssfv", [Hyp(cN, "Fun S"), Hyp(cN, "R C_ S"), tl]);
            Proof eq = Ce($"( <\" {Hd("x")} \"> ++ Y )", Symm(fs));
            Proof ifeq = UseS("ifeq2da", [("C", "(/)")], eq);
            Proof mpeq = Use("mpteq2dva", ifeq);
            Proof mss = Imp(h, "mptss", [xss], s: [("x", "x"), ("C", Val("S", "x"))]);
            Thm("lean-list-mpss", "W's step is monotone on functions.", Use("eqsstrd", mpeq, mss));
        }
    }

    /// <summary>From the context: ( ctx -> Hd v e. A ), ( ctx -> Tl v e. dom R ), ( ctx -> v = cons (Hd v) (Tl v) ).</summary>
    private (Proof Hd, Proof Tl, Proof Dec) DmFacts(string ctx, string v, string r)
    {
        Proof f = Imp(ctx, "lean-list-dmcase", [Hyp(ctx, $"{v} e. {Dm(r)}"), Hyp(ctx, $"-. {v} = {Nil}")]);
        Proof a = Use("simpld", f);
        return (Use("simpld", a), Use("simprd", a), Use("simprd", f));
    }

    /// <summary>W's step takes a one-to-one map into Word A to a one-to-one map into Word A.</summary>
    private void StepF1()
    {
        const string f1 = "R : dom R -1-1-> Word A";
        string dm = Dm("R");
        string E(string v) => $"( <\" {Hd(v)} \"> ++ ( R ` {Tl(v)} ) )";
        Proof S1(string ctx, string v) => Imp(ctx, "s1cl", [DmFacts(ctx, v, "R").Hd]);
        Proof Rv(string ctx, string v) => Imp(ctx, "ffvelcdm", [Imp(ctx, "f1f", [Hyp(ctx, f1)]), DmFacts(ctx, v, "R").Tl]);
        Proof ValN(string ctx, string v) => Imp(ctx, "iftrue", [Hyp(ctx, $"{v} = {Nil}")], q: $"{Val("R", v)} = (/)");
        Proof ValC(string ctx, string v) => Imp(ctx, "iffalse", [Hyp(ctx, $"-. {v} = {Nil}")], q: $"{Val("R", v)} = {E(v)}");
        Proof NE(string ctx, string v)
        {
            Proof bi = Imp(ctx, "ccat0", [S1(ctx, v), Rv(ctx, v)]);
            Proof ns1 = Lift(ctx, Use("neii", UseS("s1nz", [("A", Hd(v))])));
            Proof intn = UseS("intnanrd", [("ch", $"( R ` {Tl(v)} ) = (/)")], ns1);
            return Use("mtbird", intn, bi);
        }

        // Its values are in Word A.
        string c = $"( {f1} /\\ x e. {dm} )";
        Proof m0 = Lift($"( {c} /\\ x = {Nil} )", UseS("wrd0", [("S", "A")]));
        string cN = $"( {c} /\\ -. x = {Nil} )";
        Proof m1 = Imp(cN, "ccatcl", [S1(cN, "x"), Rv(cN, "x")]);
        Proof memAll = Use("ralrimiva", Use("ifclda", m0, m1));

        // It is one-to-one: nil goes to (/), a cons to a nonempty word, and a cons's word determines its head and tail.
        string c2 = $"( ( {f1} /\\ x e. {dm} ) /\\ w e. {dm} )";
        string goalT = $"( {Val("R", "x")} = {Val("R", "w")} -> x = w )";
        string xN = $"( {c2} /\\ x = {Nil} )", xC = $"( {c2} /\\ -. x = {Nil} )";
        Proof nn;
        {
            string k = $"( {xN} /\\ w = {Nil} )";
            nn = UseS("a1d", [("ch", $"{Val("R", "x")} = {Val("R", "w")}")], Trans(Hyp(k, $"x = {Nil}"), Symm(Hyp(k, $"w = {Nil}"))));
        }
        Proof nc;
        {
            string k = $"( {xN} /\\ -. w = {Nil} )";
            Proof bi1 = Use("eqeq12d", ValN(k, "x"), ValC(k, "w"));
            Proof ne = Use("sylnibr", NE(k, "w"), UseS("eqcom", [("A", "(/)"), ("B", E("w"))]));
            nc = UseS("pm2.21d", [("ch", "x = w")], Use("mtbird", ne, bi1));
        }
        Proof cn;
        {
            string k = $"( {xC} /\\ w = {Nil} )";
            Proof bi1 = Use("eqeq12d", ValC(k, "x"), ValN(k, "w"));
            cn = UseS("pm2.21d", [("ch", "x = w")], Use("mtbird", NE(k, "x"), bi1));
        }
        Proof cc;
        {
            string k = $"( {xC} /\\ -. w = {Nil} )";
            var (hx, tx, dx) = DmFacts(k, "x", "R");
            var (hw, tw, dw) = DmFacts(k, "w", "R");
            Proof bi1 = Use("eqeq12d", ValC(k, "x"), ValC(k, "w"));
            Proof len = Use("eqtr4i", UseS("s1len", [("A", Hd("x"))]), UseS("s1len", [("A", Hd("w"))]));
            Proof bi2 = Imp(k, "ccatopth", [Use("jca", S1(k, "x"), Rv(k, "x")), Use("jca", S1(k, "w"), Rv(k, "w")), Lift(k, len)]);
            Proof bi3 = Imp(k, "s111", [hx, hw]);
            Proof bi4 = Imp(k, "f1fveq", [Hyp(k, f1), Use("jca", tx, tw)]);
            Proof biv = Use("bitrd", Use("bitrd", bi1, bi2), Use("anbi12d", bi3, bi4));
            string k2 = $"( {k} /\\ ( {Hd("x")} = {Hd("w")} /\\ {Tl("x")} = {Tl("w")} ) )";
            var (_, _, dx2) = DmFacts(k2, "x", "R");
            var (_, _, dw2) = DmFacts(k2, "w", "R");
            Proof e1 = Ce(Cons("Y", Tl("x")), Hyp(k2, $"{Hd("x")} = {Hd("w")}"));
            Proof e2 = Ce(Cons(Hd("w"), "Y"), Hyp(k2, $"{Tl("x")} = {Tl("w")}"));
            Proof xw = Trans(dx2, e1, e2, Symm(dw2));
            _ = (dx, dw);
            cc = Use("sylbid", biv, Use("ex", xw));
        }
        Proof inj = Use("pm2.61dan", Use("pm2.61dan", nn, nc), Use("pm2.61dan", cn, cc));
        Proof injAll = Use("ralrimiva", Use("ralrimiva", inj));
        _ = goalT;
        Proof bi = UseS("f1mpt", [("B", "Word A")], UseS("eqid", [("A", Mp("R"))]), SubEq("x", "w", Val("R", "x")));
        Thm("lean-list-mpf1", "W's step takes a one-to-one map into Word A to a one-to-one map into Word A.",
            Use("mpbird", Use("jca", memAll, injAll), Lift(f1, bi)));
    }

    // ================================================================ W's stages

    private void Graph()
    {
        const string hk = "( ( U e. _V /\\ A e. _V ) /\\ K e. _om )";
        // Each stage is W's step at the last.
        {
            Proof e1 = Imp(hk, "rdgsuc", [Imp(hk, "nnon", [Hyp(hk, "K e. _om")])], q: $"{Rk("suc K")} = ( {Gf} ` {Rk("K")} )");
            Proof e2 = Lift(hk, UseS("fveq1i", [("A", Rk("K"))], Ax("lean-list-gf2")));
            Proof dex = Imp(hk, "lean-list-xsex", [Hyp(hk, "A e. _V"), Lift(hk, Use("dmex", UseG("fvex", $"{Rk("K")} e. _V")))]);
            Proof mex = Imp(hk, "mptexg", [dex], s: [("x", "x"), ("B", Val(Rk("K"), "x"))]);
            Proof e3 = UseS("fvmptd3", [("V", "_V")], UseS("eqid", [("A", Gf2)]), SubEq("q", Rk("K"), Mp("q")), Lift(hk, UseG("fvex", $"{Rk("K")} e. _V")), mex);
            Thm("lean-list-gsuc", "Each stage of W is W's step at the last.", Trans(e1, e2, e3));
        }
        Proof Gsuc(string ctx, string k) => Use("syl", Use("jca", Hyp(ctx, Hv), k == "(/)" ? Lift(ctx, Use("peano1")) : Hyp(ctx, $"{k} e. _om")), T("lean-list-gsuc", ("K", k)));
        Proof DomSuc(string ctx, string k, Proof g) => Trans(Use("dmeqd", g), Lift(ctx, T("lean-list-dmmp", ("R", Rk(k)))));
        Proof dm0 = Use("eqtri", Use("dmeqi", Ax("lean-list-g0")), Use("dm0"));

        // The stages grow.
        {
            string P = $"{Rk("k")} C_ {Rk("suc k")}";
            Proof b = Lift(Hv, Use("eqsstri", Ax("lean-list-g0"), UseS("0ss", [("A", Rk("suc (/)"))])));
            string s = $"( ( j e. _om /\\ {Hv} ) /\\ {Rk("j")} C_ {Rk("suc j")} )";
            Proof g1 = Gsuc(s, "j");
            Proof sj = Imp(s, "peano2", [Hyp(s, "j e. _om")]);
            Proof g2 = Use("syl", Use("jca", Hyp(s, Hv), sj), T("lean-list-gsuc", ("K", "suc j")));
            Proof fun1 = Rw(Lift(s, UseS("funmpt", [("x", "x"), ("A", Dm(Rk("j"))), ("B", Val(Rk("j"), "x"))])), Symm(g1));
            Proof mss = Imp(s, "lean-list-mpss", [fun1, Hyp(s, $"{Rk("j")} C_ {Rk("suc j")}")]);
            Proof st = Use("eqsstrd", g1, Use("sseqtrrd", mss, g2));
            Thm("lean-list-gmono", "Each stage of W is contained in the next.", Use("impcom", _k.Finds("k", "j", P, Hv, b, st, "K")));
        }
        // So any stage is contained in every later one.
        {
            string Ph(string m) => $"( {Hv} -> {Rk("J")} C_ {Rk(m)} )";
            Proof Eqv(string t) => SubBi("m", t, Ph("m"));
            Proof b = Lift("J e. _om", Lift(Hv, UseS("ssid", [("A", Rk("J"))])));
            string hh = "( ( i e. _om /\\ J e. _om ) /\\ J C_ i )";
            string kk = $"( ( {hh} /\\ {Ph("i")} ) /\\ {Hv} )";
            Proof a1 = Use("mpd", Hyp(kk, Hv), Hyp(kk, Ph("i")));
            Proof a2 = Use("syl", Use("jca", Hyp(kk, Hv), Hyp(kk, "i e. _om")), T("lean-list-gmono", ("K", "i")));
            Proof st = Use("ex", Use("ex", Use("sstrd", a1, a2)));
            Proof r = UseS("findsg", [("x", "m"), ("y", "i")], Eqv("J"), Eqv("i"), Eqv("suc i"), Eqv("K"), b, st);
            Thm("lean-list-gss", "Each stage of W is contained in every later stage.", r);
        }
        // Each stage is one-to-one into Word A.
        {
            string P = $"{Rk("k")} : dom {Rk("k")} -1-1-> Word A";
            Proof bi = Use("f1eq123d", Lift(Hv, Ax("lean-list-g0")), Lift(Hv, dm0), _k.Refl(Hv, "Word A"));
            Proof b = Use("mpbird", Lift(Hv, UseS("f10", [("A", "Word A")])), bi);
            string pj = ProofKit.Replace(P, "k", "j");
            string s = $"( ( j e. _om /\\ {Hv} ) /\\ {pj} )";
            Proof g1 = Gsuc(s, "j");
            Proof mf = Imp(s, "lean-list-mpf1", [Hyp(s, pj)]);
            Proof r1 = Rw(mf, Symm(g1));
            Proof r2 = Rw(r1, Symm(DomSuc(s, "j", g1)));
            Thm("lean-list-gf1", "Each stage of W is one-to-one into Word A.", Use("impcom", _k.Finds("k", "j", P, Hv, b, r2, "K")));
        }
        // Their union is one-to-one into Word A.
        {
            const string c = "( ( U e. _V /\\ A e. _V ) /\\ n e. _om )";
            const string c2 = "( " + c + " /\\ m e. _om )";
            Proof pn = T("lean-list-gf1", ("K", "n"));
            Proof ord = Imp(c2, "ordtri2or2", [Imp(c2, "nnord", [Hyp(c2, "n e. _om")]), Imp(c2, "nnord", [Hyp(c2, "m e. _om")])]);
            Proof Ss(string a, string b)
            {
                string c3 = $"( {c2} /\\ {a} C_ {b} )";
                Proof gs = Use("syl", Use("jca", Use("jca", Hyp(c3, $"{b} e. _om"), Hyp(c3, $"{a} e. _om")), Hyp(c3, $"{a} C_ {b}")), T("lean-list-gss", ("K", b), ("J", a)));
                return Use("ex", Use("mpd", Hyp(c3, Hv), gs));
            }
            Proof ch = Use("mpd", ord, Use("orim12d", Ss("n", "m"), Ss("m", "n")));
            Proof all = Use("ralrimiva", Use("jca", pn, Use("ralrimiva", ch)));
            Proof f = Imp(Hv, "f1iun", [all], closed: [SubEq("n", "m", Rk("n")), UseG("fvex", $"{Rk("n")} e. _V")]);
            Thm("lean-list-wf1", "W is one-to-one into Word A, on the union of its stages' domains.", f);
        }
        // The domain of W's stage k is the model's stage k.
        {
            string P = $"dom {Rk("k")} C_ {St("k")}";
            Proof b = Lift(Hv, Use("eqsstri", dm0, UseS("0ss", [("A", St("(/)"))])));
            string pj = ProofKit.Replace(P, "k", "j");
            string s = $"( ( j e. _om /\\ {Hv} ) /\\ {pj} )";
            Proof dsj = DomSuc(s, "j", Gsuc(s, "j"));
            Proof x1 = Imp(s, "lean-list-xss", [Hyp(s, pj)]);
            Proof stj = Use("syl", Use("jca", Hyp(s, Hv), Hyp(s, "j e. _om")), T("lean-list-stagesuc", ("K", "j")));
            Proof x2 = Use("sseqtrrd", Lift(s, UseS("ssun2", [("A", Xs(St("j"))), ("B", St("j"))])), stj);
            Proof r = Use("eqsstrd", dsj, Use("sstrd", x1, x2));
            Proof ss1 = Use("impcom", _k.Finds("k", "j", P, Hv, b, r, "K"));

            string Q = $"{St("k")} C_ dom {Rk("k")}";
            Proof b2 = Lift(Hv, Use("eqsstri", Ax("lean-list-stage0"), UseS("0ss", [("A", $"dom {Rk("(/)")}")])));
            string qj = ProofKit.Replace(Q, "k", "j");
            string s2 = $"( ( j e. _om /\\ {Hv} ) /\\ {qj} )";
            Proof dsj2 = DomSuc(s2, "j", Gsuc(s2, "j"));
            Proof stj2 = Use("syl", Use("jca", Hyp(s2, Hv), Hyp(s2, "j e. _om")), T("lean-list-stagesuc", ("K", "j")));
            Proof mono = Use("syl", Use("jca", Hyp(s2, Hv), Hyp(s2, "j e. _om")), T("lean-list-gmono", ("K", "j")));
            Proof u1 = Use("sstrd", Hyp(s2, qj), Imp(s2, "dmss", [mono]));
            Proof u2 = Use("sseqtrrd", Imp(s2, "lean-list-xss", [Hyp(s2, qj)]), dsj2);
            Proof r2 = Use("eqsstrd", stj2, Use("unssd", u1, u2));
            Proof ss2 = Use("impcom", _k.Finds("k", "j", Q, Hv, b2, r2, "K"));
            Thm("lean-list-gdm", "The domain of W's stage k is the model's stage k.", Use("eqssd", ss1, ss2));
        }
    }

    // ================================================================ W on the model's List

    /// <summary>( ctx -> Hv ) from H0 in the context.</summary>
    private Proof HvOf(string ctx) =>
        Use("jca", Imp(ctx, "elex", [Hyp(ctx, "U e. lean.-tower")]), Imp(ctx, "elex", [Hyp(ctx, "A e. ( U ` (/) )")]));

    /// <summary>( ctx -> E. i e. _om C e. stage i ) from ( ctx -> C e. L ), with H0 in the context.</summary>
    private Proof ExSt(string ctx, Proof inL, string i = "i")
    {
        string c = Cons_(inL);
        string t = c[..c.IndexOf(" e. ", StringComparison.Ordinal)];
        Proof iu = Use("eleqtrd", inL, Imp(ctx, "lean-list-iun", [Hyp(ctx, H0)]));
        Proof ex = Use("sylib", iu, UseS("eliun", [("A", t), ("x", "k"), ("B", "_om"), ("C", St("k"))]));
        return Use("sylib", ex, UseS("cbvrexvw", [("A", "_om")], SubBi("k", i, $"{t} e. {St("k")}")));
    }

    /// <summary>( ctx -> cons B C e. Xs ( S ) ) from ( ctx -> B e. A ) and ( ctx -> C e. S ).</summary>
    private Proof ConsIn(string ctx, string b, string c, string s, Proof pb, Proof pc)
    {
        Proof s1 = Imp(ctx, "ssiun2s", [pc], closed: [SubEq("z", c, $"{{ {Cons(b, "z")} }}")]);
        Proof s2 = Imp(ctx, "ssiun2s", [pb], closed: [SubEq("y", b, $"U_ z e. {s} {{ {Cons("y", "z")} }}")]);
        Proof sn = Lift(ctx, Use("snid", Opex("1o", $"<. (/) , <. {b} , <. {c} , (/) >. >. >.")));
        Proof m = Use("mpd", sn, UseS("sseld", [("C", Cons(b, c))], Use("sstrd", s1, s2)));
        return Imp(ctx, "elun2", [m], q: $"{Cons(b, c)} e. {Xs(s)}");
    }

    private void OnList()
    {
        // The stages are inside the model's List.
        {
            const string h = "( ( U e. lean.-tower /\\ A e. ( U ` (/) ) ) /\\ K e. _om )";
            Proof s = Imp(h, "ssiun2s", [Hyp(h, "K e. _om")], closed: [SubEq("k", "K", St("k"))]);
            Thm("lean-list-stss", "Each stage of the model's List is inside it.", Use("sseqtrrd", s, Imp(h, "lean-list-iun", [Hyp(h, H0)])));
        }
        // nil and cons are in it.
        {
            Proof sn = Use("snid", Opex("(/)", "(/)"));
            Proof inX = Lift(H0, Imp(null, "elun1", [sn], q: $"{Nil} e. {Xs(St("(/)"))}"));
            Proof hv0 = Use("jca", HvOf(H0), Lift(H0, Use("peano1")));
            Proof st1 = Use("syl", hv0, T("lean-list-stagesuc", ("K", "(/)")));
            Proof in1 = Use("mpd", inX, UseS("sseld", [("C", Nil)], Use("sseqtrrd", Lift(H0, UseS("ssun2", [("A", Xs(St("(/)"))), ("B", St("(/)"))])), st1)));
            Proof ss = Imp(H0, "lean-list-stss", [Hyp(H0, H0), Lift(H0, Imp(null, "peano2", [Use("peano1")]))]);
            Thm("lean-list-nilel", "nil is in the model's List.", Use("mpd", in1, UseS("sseld", [("C", Nil)], ss)));
        }
        {
            string c = $"( ( {H0} /\\ B e. A ) /\\ C e. {L} )";
            string d = $"( ( {c} /\\ i e. _om ) /\\ C e. {St("i")} )";
            Proof inX = ConsIn(d, "B", "C", St("i"), Hyp(d, "B e. A"), Hyp(d, $"C e. {St("i")}"));
            Proof sti = Use("syl", Use("jca", HvOf(d), Hyp(d, "i e. _om")), T("lean-list-stagesuc", ("K", "i")));
            Proof ssx = Use("sseqtrrd", Lift(d, UseS("ssun2", [("A", Xs(St("i"))), ("B", St("i"))])), sti);
            Proof ss = Imp(d, "lean-list-stss", [Hyp(d, H0), Imp(d, "peano2", [Hyp(d, "i e. _om")])]);
            Proof m = Use("mpd", inX, UseS("sseld", [("C", Cons("B", "C"))], Use("sstrd", ssx, ss)));
            Proof r = Use("mpd", ExSt(c, Hyp(c, $"C e. {L}")), Use("rexlimdva", Use("ex", m)));
            Thm("lean-list-consel", "cons stays in the model's List.", r);
        }
        // W is one-to-one from the model's List into Word A.
        {
            Proof f = Use("syl", HvOf(H0), Ax("lean-list-wf1"));
            const string c = "( ( U e. lean.-tower /\\ A e. ( U ` (/) ) ) /\\ n e. _om )";
            Proof dn = Use("syl", Use("jca", HvOf(c), Hyp(c, "n e. _om")), T("lean-list-gdm", ("K", "n")));
            Proof iu = UseS("iuneq2dv", [("x", "n"), ("A", "_om")], dn);
            Proof al = Lift(H0, _model.AlphaEq($"U_ n e. _om {St("n")}", $"U_ k e. _om {St("k")}"));
            Proof ie = Trans(iu, al, Symm(Imp(H0, "lean-list-iun", [Hyp(H0, H0)])));
            Thm("lean-list-wf1l", "W is one-to-one from the model's List A into Word A.", Rw(f, ie));
        }
        // Its values on the step's domain.
        {
            string c = $"( ( {Hv} /\\ K e. _om ) /\\ X e. {Dm(Rk("K"))} )";
            Proof g1 = Use("syl", Hyp(c, $"( {Hv} /\\ K e. _om )"), T("lean-list-gsuc", ("K", "K")));
            Proof dsk = Trans(Use("dmeqd", g1), Lift(c, T("lean-list-dmmp", ("R", Rk("K")))));
            Proof xin = Use("eleqtrrd", Hyp(c, $"X e. {Dm(Rk("K"))}"), dsk);
            Proof sub = Imp(c, "ssiun2s", [Imp(c, "peano2", [Hyp(c, "K e. _om")])], closed: [SubEq("n", "suc K", Rk("n"))]);
            Proof fun = Imp(c, "f1fun", [Use("syl", Hyp(c, Hv), Ax("lean-list-wf1"))]);
            Proof e1 = Imp(c, "funssfv", [fun, sub, xin]);
            Proof e2 = Ce("( Y ` X )", g1);
            Proof vex = UseS("ifex", [("ph", $"X = {Nil}")], Use("0ex"), UseS("ovex", [("A", $"<\" {Hd("X")} \">"), ("F", "++"), ("B", $"( {Rk("K")} ` {Tl("X")} )")]));
            Proof e3 = UseS("fvmptd3", [("V", "_V")], UseS("eqid", [("A", Mp(Rk("K")))]), SubEq("x", "X", Val(Rk("K"), "x")), Hyp(c, $"X e. {Dm(Rk("K"))}"), Lift(c, vex));
            Thm("lean-list-wval", "W on its step's domain.", Trans(e1, e2, e3));
        }
        // W ( nil ) = (/).
        {
            Proof sn = Use("snid", Opex("(/)", "(/)"));
            Proof inD = Lift(Hv, Imp(null, "elun1", [sn], q: $"{Nil} e. {Dm(Rk("(/)"))}"));
            Proof wv = Use("syl", Use("jca", Use("jca", UseS("id", [("ph", Hv)]), Lift(Hv, Use("peano1"))), inD), T("lean-list-wval", ("K", "(/)"), ("X", Nil)));
            Proof it = Use("ax-mp", UseS("eqid", [("A", Nil)]),
                UseS("iftrue", [("ph", $"{Nil} = {Nil}"), ("A", "(/)"), ("B", $"( <\" {Hd(Nil)} \"> ++ ( {Rk("(/)")} ` {Tl(Nil)} ) )")]));
            Thm("lean-list-wnil0", "W takes nil to the empty word.", Trans(wv, Lift(Hv, it)));
            Thm("lean-list-wnil", "Bridge: W takes nil to the empty word.", Use("syl", HvOf(H0), Ax("lean-list-wnil0")));
        }
        // W ( cons B C ) = ( <" B "> ++ W ( C ) ).
        {
            string c = $"( ( {H0} /\\ B e. A ) /\\ C e. {L} )";
            string d = $"( ( {c} /\\ i e. _om ) /\\ C e. {St("i")} )";
            Proof hvi = Use("jca", HvOf(d), Hyp(d, "i e. _om"));
            Proof cdm = Use("eleqtrrd", Hyp(d, $"C e. {St("i")}"), Use("syl", hvi, T("lean-list-gdm", ("K", "i"))));
            Proof inD = ConsIn(d, "B", "C", $"dom {Rk("i")}", Hyp(d, "B e. A"), cdm);
            Proof wv = Use("syl", Use("jca", hvi, inD), T("lean-list-wval", ("K", "i"), ("X", Cons("B", "C"))));
            string e0 = $"( <\" {Hd(Cons("B", "C"))} \"> ++ ( {Rk("i")} ` {Tl(Cons("B", "C"))} ) )";
            Proof vf = Imp(d, "iffalse", [Lift(d, T("lean-list-consnnil", ("B", "B"), ("C", "C")))], q: $"{Val(Rk("i"), Cons("B", "C"))} = {e0}");
            Proof bv = Imp(d, "elex", [Hyp(d, "B e. A")]), cv = Imp(d, "elex", [Hyp(d, $"C e. {L}")]);
            Proof hd = Imp(d, "lean-list-hd", [bv, cv]), tl = Imp(d, "lean-list-tl", [bv, cv]);
            Proof e1 = Ce($"( <\" Y \"> ++ ( {Rk("i")} ` {Tl(Cons("B", "C"))} ) )", hd);
            Proof e2 = Ce($"( <\" B \"> ++ ( {Rk("i")} ` Y ) )", tl);
            Proof sub = Imp(d, "ssiun2s", [Hyp(d, "i e. _om")], closed: [SubEq("n", "i", Rk("n"))]);
            Proof fun = Imp(d, "f1fun", [Use("syl", HvOf(d), Ax("lean-list-wf1"))]);
            Proof wc = Imp(d, "funssfv", [fun, sub, cdm]);
            Proof e3 = Ce("( <\" B \"> ++ Y )", Symm(wc));
            Proof r = Trans(wv, vf, e1, e2, e3);
            Thm("lean-list-wcons", "Bridge: W takes cons B C to ( <\" B \"> ++ W ( C ) ).",
                Use("mpd", ExSt(c, Hyp(c, $"C e. {L}")), Use("rexlimdva", Use("ex", r))));
        }
        Onto();
    }

    /// <summary>Every word is W of some list, by induction on its length: a nonempty word is its first letter, then the rest.</summary>
    private void Onto()
    {
        Proof wf1 = Ax("lean-list-wf1l");
        Proof FnW(string ctx) => Imp(ctx, "f1fn", [Use("syl", Hyp(ctx, H0), wf1)]);
        string P(string m) => $"( {H0} -> A. u e. Word A ( ( # ` u ) = {m} -> u e. ran {W} ) )";

        Proof b;
        {
            string c = $"( ( {H0} /\\ u e. Word A ) /\\ ( # ` u ) = 0 )";
            Proof u0 = Use("mpbid", Hyp(c, "( # ` u ) = 0"), Imp(c, "hasheq0", [Hyp(c, "u e. Word A")]));
            Proof wn = Use("syl", Hyp(c, H0), Ax("lean-list-wnil"));
            Proof rn = Imp(c, "fnfvelrn", [FnW(c), Use("syl", Hyp(c, H0), Ax("lean-list-nilel"))]);
            b = Use("ralrimiva", Use("ex", Use("eqeltrd", Trans(u0, Symm(wn)), rn)));
        }
        Proof st;
        {
            string c = $"( ( ( ( i e. NN0 /\\ {P("i")} ) /\\ {H0} ) /\\ w e. Word A ) /\\ ( # ` w ) = ( i + 1 ) )";
            string w1 = "( w substr <. 1 , ( # ` w ) >. )";
            Proof Wne(string x)
            {
                Proof hl = Hyp(x, "( # ` w ) = ( i + 1 )");
                Proof ne0 = Use("eqnetrd", hl, Imp(x, "nnne0", [Imp(x, "nn0p1nn", [Hyp(x, "i e. NN0")])]));
                return Use("mpbid", ne0, Use("necon3bid", Imp(x, "hasheq0", [Hyp(x, "w e. Word A")])));
            }
            Proof One(string x) => Imp(x, "1elfz0hash", [Imp(x, "wrdfin", [Hyp(x, "w e. Word A")]), Wne(x)]);
            Proof Hd0(string x) => Imp(x, "fstwrdne", [Hyp(x, "w e. Word A"), Wne(x)]);
            Proof Dec(string x) => Symm(Rw(Imp(x, "pfxcctswrd", [Hyp(x, "w e. Word A"), One(x)]), Imp(x, "pfx1", [Hyp(x, "w e. Word A"), Wne(x)])));
            Proof hw = Hyp(c, "w e. Word A"), hl = Hyp(c, "( # ` w ) = ( i + 1 )"), hi = Hyp(c, "i e. NN0");
            Proof ih = Use("mpd", Hyp(c, H0), Hyp(c, P("i")));
            Proof w1w = Imp(c, "swrdcl", [hw], q: $"{w1} e. Word A");
            Proof lin = Use("sylib", Imp(c, "lencl", [hw]), UseS("nn0fz0", [("N", "( # ` w )")]));
            Proof len1 = Imp(c, "swrdlen", [hw, One(c), lin]);
            Proof lenEq = Trans(len1, Ce("( Y - 1 )", hl), Imp(c, "pncan", [Imp(c, "nn0cn", [hi]), Lift(c, Use("ax-1cn"))]));
            Proof inRn = Use("mpd", lenEq, Spec("u", $"( ( # ` u ) = i -> u e. ran {W} )", ih, w1w));
            Proof ex = Use("mpbid", inRn, Imp(c, "fvelrnb", [FnW(c)], s: [("x", "l"), ("B", w1)]));
            string d = $"( ( {c} /\\ l e. {L} ) /\\ ( {W} ` l ) = {w1} )";
            Proof prem = Use("jca", Use("jca", Hyp(d, H0), Hd0(d)), Hyp(d, $"l e. {L}"));
            Proof consEl = Imp(d, "lean-list-consel", [prem]);
            Proof wc = Imp(d, "lean-list-wcons", [prem]);
            Proof e = Trans(wc, Ce("( <\" ( w ` 0 ) \"> ++ Y )", Hyp(d, $"( {W} ` l ) = {w1}")), Symm(Dec(d)));
            Proof r = Use("eqeltrrd", e, Imp(d, "fnfvelrn", [FnW(d), consEl]));
            Proof fin = Use("mpd", ex, Use("rexlimdva", Use("ex", r)));
            Proof g2 = Use("ralrimiva", Use("ex", fin));
            Proof g3 = Use("sylib", g2, UseS("cbvralvw", [("A", "Word A")], SubBi("w", "u", $"( ( # ` w ) = ( i + 1 ) -> w e. ran {W} )")));
            st = Use("ex", Use("ex", g3));
        }
        Proof ind = UseS("nn0ind", [("x", "m"), ("y", "i")], SubBi("m", "0", P("m")), SubBi("m", "i", P("m")), SubBi("m", "( i + 1 )", P("m")),
            SubBi("m", "( # ` w )", P("m")), b, st);
        const string sub = "( ( U e. lean.-tower /\\ A e. ( U ` (/) ) ) /\\ w e. Word A )";
        Proof pw = Use("mpd", Hyp(sub, H0), Use("syl", Imp(sub, "lencl", [Hyp(sub, "w e. Word A")]), ind));
        Proof wr = Use("mpd", _k.Refl(sub, "( # ` w )"), Spec("u", $"( ( # ` u ) = ( # ` w ) -> u e. ran {W} )", pw, Hyp(sub, "w e. Word A")));
        Proof ssr = Use("ssrdv", Use("ex", wr));
        Proof f1 = Use("syl", Hyp(H0, H0), wf1);
        Proof frn = Imp(H0, "frn", [Imp(H0, "f1f", [f1])]);
        Thm("lean-list-wrn", "Every word over A is W of an element of the model's List A.", Use("eqssd", frn, ssr));
        Thm("lean-list-wf1o", "Bridge: W is a bijection from the model's List A onto Word A.",
            Use("mpbid", Imp(H0, "f1f1orn", [f1]), Imp(H0, "f1oeq3", [Imp(H0, "lean-list-wrn", [Hyp(H0, H0)])], s: [("F", W), ("C", L)])));
    }

    // ================================================================ induction over the model's List

    /// <summary>
    /// ( ( ph /\ B e. L ) -> P ( B ) ) by induction over the stages of the model's List: the context ph contains H0, and
    /// P is written with the free variable p. From ( ph -> P ( nil ) ) and, for the context
    /// cs = ( ( ( ph /\ y e. A ) /\ z e. L ) /\ P ( z ) ), a proof of ( cs -> P ( cons y z ) ).
    /// </summary>
    private Proof ListInd(string ph, string P, Proof nilP, Func<string, Proof> consP, string target)
    {
        string Pof(string t) => ProofKit.Replace(P, "p", t);
        string Q(string k) => $"A. p e. {St(k)} {P}";
        Proof b0 = Use("mpbir", UseS("ral0", [("x", "p"), ("ph", P)]), Imp(null, "raleq", [Ax("lean-list-stage0")], s: [("x", "p"), ("ph", P)]));
        Proof b = Lift(ph, b0);

        string s = $"( ( j e. _om /\\ {ph} ) /\\ {Q("j")} )";
        string cP = $"( {s} /\\ e e. {St("suc j")} )";
        Proof stj = Use("syl", Use("jca", HvOf(cP), Hyp(cP, "j e. _om")), T("lean-list-stagesuc", ("K", "j")));
        Proof inU = Use("eleqtrd", Hyp(cP, $"e e. {St("suc j")}"), stj);
        Proof or1 = Use("sylib", inU, UseS("elun", [("A", "e"), ("B", St("j")), ("C", Xs(St("j")))]));
        string c1k = $"( {cP} /\\ e e. {St("j")} )";
        Proof c1 = Use("ex", Spec("p", P, Hyp(c1k, Q("j")), Hyp(c1k, $"e e. {St("j")}")));
        Proof c2a;
        {
            string k = $"( {cP} /\\ e e. {{ {Nil} }} )";
            Proof pe = Imp(k, "elsni", [Hyp(k, $"e e. {{ {Nil} }}")]);
            Proof bi = Use("syl", pe, SubBi("e", Nil, Pof("e")));
            c2a = Use("ex", Use("mpbird", Use("syl", Hyp(k, ph), nilP), bi));
        }
        string iuz(string y) => $"U_ z e. {St("j")} {{ {Cons(y, "z")} }}";
        string iu = $"U_ y e. A {iuz("y")}";
        Proof c2b;
        {
            string k3 = $"( ( ( {cP} /\\ y e. A ) /\\ z e. {St("j")} ) /\\ e e. {{ {Cons("y", "z")} }} )";
            Proof pe = Imp(k3, "elsni", [Hyp(k3, $"e e. {{ {Cons("y", "z")} }}")]);
            Proof ss = Imp(k3, "lean-list-stss", [Hyp(k3, H0), Hyp(k3, "j e. _om")]);
            Proof zL = Use("mpd", Hyp(k3, $"z e. {St("j")}"), UseS("sseld", [("C", "z")], ss));
            Proof pz = Spec("p", P, Hyp(k3, Q("j")), Hyp(k3, $"z e. {St("j")}"));
            string cs = $"( ( ( {ph} /\\ y e. A ) /\\ z e. {L} ) /\\ {Pof("z")} )";
            Proof pc = Use("syl", Use("jca", Use("jca", Use("jca", Hyp(k3, ph), Hyp(k3, "y e. A")), zL), pz), consP(cs));
            Proof r = Use("mpbird", pc, Use("syl", pe, SubBi("e", Cons("y", "z"), Pof("e"))));
            Proof i1 = Use("rexlimdva", Use("ex", r));
            Proof i2 = Use("sylbid", Lift($"( {cP} /\\ y e. A )", UseS("eliun", [("A", "e"), ("x", "z"), ("B", St("j")), ("C", $"{{ {Cons("y", "z")} }}")])), i1);
            Proof i3 = Use("rexlimdva", i2);
            c2b = Use("sylbid", Lift(cP, UseS("eliun", [("A", "e"), ("x", "y"), ("B", "A"), ("C", iuz("y"))])), i3);
        }
        Proof c2 = Use("sylbid", Lift(cP, UseS("elun", [("A", "e"), ("B", $"{{ {Nil} }}"), ("C", iu)])), Use("jaod", c2a, c2b));
        Proof all = Use("mpd", or1, Use("jaod", c1, c2));
        Proof st = Use("sylib", Use("ralrimiva", all), UseS("cbvralvw", [("A", St("suc j"))], SubBi("e", "p", Pof("e"))));
        Proof ind = _k.Finds("k", "j", Q("k"), ph, b, st, "i");

        string c = $"( {ph} /\\ {target} e. {L} )";
        string d = $"( ( {c} /\\ i e. _om ) /\\ {target} e. {St("i")} )";
        Proof qi = Use("mpd", Hyp(d, ph), Use("syl", Hyp(d, "i e. _om"), ind));
        Proof pb = Spec("p", P, qi, Hyp(d, $"{target} e. {St("i")}"));
        return Use("mpd", ExSt(c, Hyp(c, $"{target} e. {L}")), Use("rexlimdva", Use("ex", pb)));
    }

    // ================================================================ List.length, List.append and HAppend through W

    public const string N = NatBridge.Nat;
    public static string Len(string l) => $"( ( ( lean.List.length.{{0}} ` U ) ` A ) ` {l} )";
    public static string App(string l, string m) => $"( ( ( ( lean.List.append.{{0}} ` U ) ` A ) ` {l} ) ` {m} )";
    public const string NilM = "( ( lean.List.nil.{0} ` U ) ` A )";
    public static string ConsM(string a, string l) => $"( ( ( ( lean.List.cons.{{0}} ` U ) ` A ) ` {a} ) ` {l} )";

    public void Computation(TheoremTranslator tt)
    {
        Terms t = tt.Terms;
        Expr type0 = t.Sort(t.Succ(t.Zero));
        Expr listC = tt.Const0("List"), nilC = tt.Const0("List.nil"), consC = tt.Const0("List.cons");
        Expr lenC = tt.Const0("List.length"), appC = tt.Const0("List.append");
        Expr zeroC = tt.Const0("Nat.zero"), succC = tt.Const0("Nat.succ");
        Expr ListOf(Expr a) => t.App(listC, a);
        Expr NilOf(Expr a) => t.App(nilC, a);
        Expr ConsOf(Expr a, Expr x, Expr l) => t.App(t.App(t.App(consC, a), x), l);
        Expr LenOf(Expr a, Expr l) => t.App(t.App(lenC, a), l);
        Expr AppOf(Expr a, Expr l, Expr m) => t.App(t.App(t.App(appC, a), l), m);
        Func<IReadOnlyList<Expr>, Expr> Ty = _ => type0, El = v => v[0], Ls = v => ListOf(v[0]);

        void Rule(string label, string comment, IReadOnlyList<Func<IReadOnlyList<Expr>, Expr>> bs, Func<IReadOnlyList<Expr>, (Expr, Expr)> sides, string want)
        {
            var (st, pf) = tt.ProveDefEq(bs, sides);
            _nat.Add(label, comment, st, pf, Required(pf));
            if ($"{st}" != $"|- {want}")
            {
                throw new InvalidOperationException($"{label} came out as {st}, not |- {want}");
            }
        }
        string h1 = $"( {H0} /\\ B e. A )", h2 = $"( {h1} /\\ C e. {L} )";
        Rule("lean-list-len-nilm", "List.length's first computation rule, proved from its definition.", [Ty], v => (LenOf(v[0], NilOf(v[0])), zeroC),
            $"( {H0} -> {Len(NilM)} = {NatBridge.Zero} )");
        Rule("lean-list-len-consm", "List.length's second computation rule, proved from its definition.", [Ty, El, Ls],
            v => (LenOf(v[0], ConsOf(v[0], v[1], v[2])), t.App(succC, LenOf(v[0], v[2]))),
            $"( {h2} -> {Len(ConsM("B", "C"))} = {NatBridge.Succ(Len("C"))} )");
        Rule("lean-list-app-nilm", "List.append's first computation rule, proved from its definition.", [Ty, Ls],
            v => (AppOf(v[0], NilOf(v[0]), v[1]), v[1]), $"( ( {H0} /\\ B e. {L} ) -> {App(NilM, "B")} = B )");
        Rule("lean-list-app-consm", "List.append's second computation rule, proved from its definition.", [Ty, El, Ls, Ls],
            v => (AppOf(v[0], ConsOf(v[0], v[1], v[2]), v[3]), ConsOf(v[0], v[1], AppOf(v[0], v[2], v[3]))),
            $"( ( {h2} /\\ D e. {L} ) -> {App(ConsM("B", "C"), "D")} = {ConsM("B", App("C", "D"))} )");

        // The rules on the tuples nil and cons.
        Proof nileq = Use("lean-list-nileq");
        Thm("lean-list-len-nil", "List.length nil = 0, on the tuple nil.", Rw(Use("lean-list-len-nilm"), nileq));
        Thm("lean-list-len-cons", "List.length ( cons B C ) = succ ( List.length C ), on the tuple cons.", Rw(Use("lean-list-len-consm"), Use("lean-list-conseq")));
        {
            string h = $"( {H0} /\\ B e. {L} )";
            Thm("lean-list-app-nil", "List.append nil B = B, on the tuple nil.", Rw(Use("lean-list-app-nilm"), Imp(h, "lean-list-nileq", [Hyp(h, H0)])));
            string h3 = $"( {h2} /\\ D e. {L} )";
            Thm("lean-list-app-cons", "List.append ( cons B C ) D = cons B ( List.append C D ), on the tuple cons (left side).",
                Rw(Use("lean-list-app-consm"), Imp(h3, "lean-list-conseq", [Hyp(h3, h2)])));
        }

        Proof WF(string ctx) => Imp(ctx, "f1f", [Use("syl", Hyp(ctx, H0), Ax("lean-list-wf1l"))]);
        Proof WinWord(string ctx, string x, Proof inL) => Imp(ctx, "ffvelcdm", [WF(ctx), inL]);

        // Length: F ( List.length l ) = # ( W ( l ) ), carrying List.length l e. N.
        {
            string P = $"( {Len("p")} e. {N} /\\ {NatBridge.Fv(Len("p"))} = ( # ` {Wv("p")} ) )";
            Proof hu = Hyp(H0, "U e. lean.-tower");
            Proof ln = Use("lean-list-len-nil");
            Proof mem0 = Use("eqeltrd", ln, Imp(H0, "lean-nat-zeroel", [hu]));
            Proof f0 = Trans(Ce(NatBridge.Fv("Y"), ln), Imp(H0, "lean-nat-fzero", [hu]));
            Proof h0 = Trans(Ce("( # ` Y )", Use("lean-list-wnil")), Lift(H0, Use("hash0")));
            Proof nilP = Use("jca", mem0, Trans(f0, Symm(h0)));
            Proof ConsP(string cs)
            {
                string pz = ProofKit.Replace(P, "p", "z");
                Proof hu2 = Hyp(cs, "U e. lean.-tower");
                Proof prem = Use("jca", Use("jca", Hyp(cs, H0), Hyp(cs, "y e. A")), Hyp(cs, $"z e. {L}"));
                Proof lc = Imp(cs, "lean-list-len-cons", [prem]);
                Proof lzN = Use("simpld", Hyp(cs, pz));
                Proof fz = Use("simprd", Hyp(cs, pz));
                Proof mem = Use("eqeltrd", lc, Imp(cs, "lean-nat-succel", [hu2, lzN]));
                Proof wz = WinWord(cs, "z", Hyp(cs, $"z e. {L}"));
                Proof s1 = Imp(cs, "s1cl", [Hyp(cs, "y e. A")]);
                Proof fsucc = Imp(cs, "lean-nat-fsucc", [hu2, lzN]);
                Proof hz = Imp(cs, "nn0cn", [Imp(cs, "lencl", [wz])]);
                Proof left = Trans(Ce(NatBridge.Fv("Y"), lc), fsucc, Ce("( Y + 1 )", fz),
                    UseS("addcomd", [("A", $"( # ` {Wv("z")} )")], hz, Lift(cs, Use("ax-1cn"))));
                Proof wc = Imp(cs, "lean-list-wcons", [prem]);
                Proof right = Trans(Ce("( # ` Y )", wc), Imp(cs, "ccatlen", [s1, wz]), Ce($"( Y + ( # ` {Wv("z")} ) )", Lift(cs, UseS("s1len", [("A", "y")]))));
                return Use("jca", mem, Trans(left, Symm(right)));
            }
            Proof r = ListInd(H0, P, nilP, ConsP, "B");
            Thm("lean-list-len", "List.length through W, by induction over the model's List.", r);
            string h = $"( {H0} /\\ B e. {L} )";
            Thm("lean-list-lenel", "List.length stays in the model's Nat.", Use("simpld", Use("lean-list-len")));
            Thm("lean-list-flen", "Bridge: F ( List.length B ) = # ( W ( B ) ): List.length is #.", Use("simprd", Use("lean-list-len")));
            _ = h;
        }
        // Append: W ( List.append l C ) = ( W ( l ) ++ W ( C ) ), carrying List.append l C e. L.
        {
            string ph = $"( {H0} /\\ C e. {L} )";
            string P = $"( {App("p", "C")} e. {L} /\\ {Wv(App("p", "C"))} = ( {Wv("p")} ++ {Wv("C")} ) )";
            Proof an = Imp(ph, "lean-list-app-nil", [Use("jca", Hyp(ph, H0), Hyp(ph, $"C e. {L}"))]);
            Proof wc0 = WinWord(ph, "C", Hyp(ph, $"C e. {L}"));
            Proof e0 = Trans(Ce(Wv("Y"), an), Symm(Imp(ph, "ccatlid", [wc0])), Ce($"( Y ++ {Wv("C")} )", Symm(Imp(ph, "lean-list-wnil", [Hyp(ph, H0)]))));
            Proof nilP = Use("jca", Use("eqeltrd", an, Hyp(ph, $"C e. {L}")), e0);
            Proof ConsP(string cs)
            {
                string pz = ProofKit.Replace(P, "p", "z");
                Proof xL = Use("simpld", Hyp(cs, pz));
                Proof wx = Use("simprd", Hyp(cs, pz));
                string x = App("z", "C");
                Proof ac = Imp(cs, "lean-list-app-cons", [Use("jca", Use("jca", Use("jca", Hyp(cs, H0), Hyp(cs, "y e. A")), Hyp(cs, $"z e. {L}")), Hyp(cs, $"C e. {L}"))]);
                Proof prem = Use("jca", Use("jca", Hyp(cs, H0), Hyp(cs, "y e. A")), xL);
                Proof ce = Imp(cs, "lean-list-conseq", [prem]);
                Proof ac2 = Trans(ac, ce);
                Proof mem = Use("eqeltrd", ac2, Imp(cs, "lean-list-consel", [prem]));
                Proof w1 = Trans(Ce(Wv("Y"), ac2), Imp(cs, "lean-list-wcons", [prem]), Ce("( <\" y \"> ++ Y )", wx));
                Proof s1 = Imp(cs, "s1cl", [Hyp(cs, "y e. A")]);
                Proof wz = WinWord(cs, "z", Hyp(cs, $"z e. {L}"));
                Proof wc = WinWord(cs, "C", Hyp(cs, $"C e. {L}"));
                Proof ass = Symm(Imp(cs, "ccatass", [s1, wz, wc]));
                Proof wcz = Imp(cs, "lean-list-wcons", [Use("jca", Use("jca", Hyp(cs, H0), Hyp(cs, "y e. A")), Hyp(cs, $"z e. {L}"))]);
                Proof back = Ce($"( Y ++ {Wv("C")} )", Symm(wcz));
                _ = x;
                return Use("jca", mem, Trans(w1, ass, back));
            }
            Proof r = ListInd(ph, P, nilP, ConsP, "B");
            Thm("lean-list-app", "List.append through W, by induction over the model's List.", r);
            Thm("lean-list-appel", "List.append stays in the model's List.", Use("simpld", Use("lean-list-app")));
            Thm("lean-list-wapp", "Bridge: W ( List.append B C ) = ( W ( B ) ++ W ( C ) ): List.append is ++.", Use("simprd", Use("lean-list-app")));
        }
        // HAppend.hAppend at List's instances is List.append, so it is ++ too.
        {
            Expr hApp = tt.Const0("HAppend.hAppend"), instH = tt.Const0("instHAppendOfAppend"), instA = tt.Const0("List.instAppend");
            Expr HApp(Expr a, Expr l, Expr m)
            {
                Expr la = ListOf(a);
                Expr inst = t.App(t.App(instH, la), t.App(instA, a));
                return t.App(t.App(t.App(t.App(t.App(t.App(hApp, la), la), la), inst), l), m);
            }
            var (st, pf) = tt.ProveDefEq([Ty, Ls, Ls], v => (HApp(v[0], v[1], v[2]), AppOf(v[0], v[1], v[2])));
            _nat.Add("lean-list-happ", "HAppend.hAppend at List's instances is List.append (its instances unfolded).", st, pf, Required(pf));
            Proof ha = Use("lean-list-happ");
            string h = Ante(ha);
            string hl = Lhs(ha);
            Proof wa = Imp(h, "lean-list-wapp", [Hyp(h, $"( ( {H0} /\\ B e. {L} ) /\\ C e. {L} )")]);
            Thm("lean-list-whapp", "Bridge: W takes HAppend.hAppend on lists (Lean's ++) to set.mm's ++.", Trans(Ce(Wv("Y"), ha), wa));
            _ = hl;
        }
    }

    // ================================================================ Lean's theorems, restated in set.mm's words

    /// <summary>
    /// A Lean theorem ∀ {α} (as bs : List α), (as ++ bs).length = as.length + bs.length, proved through the model from
    /// its proof term, then restated: through W and F it is ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) for words S
    /// and T, which is set.mm's ccatlen. A second theorem proves the same statement from set.mm's own ccatlen.
    /// </summary>
    public void Restate(TheoremTranslator tt, string name)
    {
        Terms t = tt.Terms;
        var ops = new Ops(t);
        string lp = Model.LabelPart(name);
        var (tstmt, tproof) = tt.Prove(t.Of(name));
        _nat.Add($"lean-thm-{lp}", $"The Lean theorem {name}, proved through the model from its proof term.", tstmt, tproof, Required(tproof));

        Expr ty = tt.Type0(name);
        int nb = 0;
        for (Expr e = ty; e is Binder { IsPi: true } pb; e = pb.Body)
        {
            nb++;
        }
        var bts = Enumerable.Range(0, nb).Select(k => (Func<IReadOnlyList<Expr>, Expr>)(fvs =>
        {
            Expr e = ty;
            for (int i = 0; i < k; i++)
            {
                e = ops.Instantiate(((Binder)e).Body, [fvs[i]]);
            }
            return ((Binder)e).Domain;
        })).ToList();
        (Expr L, Expr R) Sides(IReadOnlyList<Expr> fvs)
        {
            Expr e = ty;
            for (int i = 0; i < nb; i++)
            {
                e = ops.Instantiate(((Binder)e).Body, [fvs[i]]);
            }
            if (Ops.Spine(e, out List<Expr> a) is not Const { } eq || !$"{eq.Name}".StartsWith("Eq.{", StringComparison.Ordinal) || a.Count != 3)
            {
                throw new Model.Refused($"{name}: restating needs an equation, not {e}");
            }
            return (a[1], a[2]);
        }
        Expr lenC = tt.Const0("List.length"), appC = tt.Const0("List.append"), addC = tt.Const0("Nat.add");
        Expr LenOf(Expr a, Expr l) => t.App(t.App(lenC, a), l);
        if (nb != 3)
        {
            throw new Model.Refused($"{name}: restating needs ∀ α (as bs : List α)");
        }
        var (ls, lpf) = tt.ProveDefEq(bts, v => (Sides(v).L, LenOf(v[0], t.App(t.App(t.App(appC, v[0]), v[1]), v[2]))));
        var (rs, rpf) = tt.ProveDefEq(bts, v => (Sides(v).R, t.App(t.App(addC, LenOf(v[0], v[1])), LenOf(v[0], v[2]))));
        _nat.Add($"lean-list-{lp}-lhs", $"The left side of {name}, unfolded to List.length and List.append.", ls, lpf, Required(lpf));
        _nat.Add($"lean-list-{lp}-rhs", $"The right side of {name}, unfolded to Nat.add and List.length.", rs, rpf, Required(rpf));
        Proof thm = Use($"lean-thm-{lp}");
        Proof dl = Use($"lean-list-{lp}-lhs"), dr = Use($"lean-list-{lp}-rhs");
        string ph = Ante(thm);
        string want = $"( ( {H0} /\\ B e. {L} ) /\\ C e. {L} )";
        if (ph != want || Ante(dl) != want || Ante(dr) != want)
        {
            throw new Model.Refused($"{name}: hypotheses {ph}, not {want}");
        }
        Proof hu = Hyp(ph, "U e. lean.-tower");
        Proof hb = Use("jca", Hyp(ph, H0), Hyp(ph, $"B e. {L}")), hc = Use("jca", Hyp(ph, H0), Hyp(ph, $"C e. {L}"));
        Proof appL = Imp(ph, "lean-list-appel", [Hyp(ph, ph)]);
        Proof hx = Use("jca", Hyp(ph, H0), appL);
        Proof lenB = Imp(ph, "lean-list-lenel", [hb]), lenC2 = Imp(ph, "lean-list-lenel", [hc]);
        Proof lm = Use("eqeltrd", dl, Imp(ph, "lean-list-lenel", [hx]));
        Proof rm = Use("eqeltrd", dr, Imp(ph, "lean-nat-natadd-el", [hu, Use("jca", lenB, lenC2)]));
        if (!Db.Statements.ContainsKey("lean-Eq.u1-eq"))
        {
            var (es, ep, _) = tt.Model.Equation(t.Of("Eq.{1}"));
            _nat.Add("lean-Eq.u1-eq", "The definitional equation of Eq.{1}.", es, ep, Required(ep));
        }
        Proof tyNat = Imp(ph, "lean-ty-Nat", [hu]);
        Proof eqv = Imp(ph, "lean-Eq.u1-eq", [Use("jca", Use("jca", Use("jca", hu, tyNat), lm), rm)]);
        Proof holds = Rw(thm, eqv);
        string cond = Cons_(holds);
        string rEqL = _pr.Render(ProofKit.Child(ProofKit.Child(_k.Wff(cond), "B"), "ph"));
        Proof rl = Use("sylib", holds, UseS("lean-prop", [("ph", rEqL)]));
        Proof nfEq = Trans(Symm(dl), Symm(rl), dr);
        Thm($"lean-list-{lp}-model", $"The Lean theorem {name} in the model: List.length ( List.append B C ) = Nat.add ( List.length B ) ( List.length C ).", nfEq);

        Proof fEq = Ce(NatBridge.Fv("Y"), nfEq);
        Proof left = Trans(Imp(ph, "lean-list-flen", [hx]), Ce("( # ` Y )", Imp(ph, "lean-list-wapp", [Hyp(ph, ph)])));
        Proof add = Imp(ph, "lean-nat-natadd", [hu, Use("jca", lenB, lenC2)]);
        Proof right = Trans(add, Ce($"( Y + {NatBridge.Fv(Len("C"))} )", Imp(ph, "lean-list-flen", [hb])),
            Ce($"( ( # ` {Wv("B")} ) + Y )", Imp(ph, "lean-list-flen", [hc])));
        Thm($"lean-list-{lp}", $"The Lean theorem {name} through the bridges W and F, for elements of the model's List.", Trans(Symm(left), fEq, right));

        // For words S and T: substitute W's inverse.
        const string q = "( ( U e. lean.-tower /\\ A e. ( U ` (/) ) ) /\\ ( S e. Word A /\\ T e. Word A ) )";
        string Inv(string v) => $"( `' {W} ` {v} )";
        Proof f1o = Imp(q, "lean-list-wf1o", [Hyp(q, H0)]);
        Proof cnvf = Imp(q, "f1of", [Imp(q, "f1ocnv", [f1o])]);
        Proof iS = Imp(q, "ffvelcdm", [cnvf, Hyp(q, "S e. Word A")]), iT = Imp(q, "ffvelcdm", [cnvf, Hyp(q, "T e. Word A")]);
        Proof inst = Use("syl", Use("jca", Use("jca", Hyp(q, H0), iS), iT), T($"lean-list-{lp}", ("U", "U"), ("A", "A"), ("B", Inv("S")), ("C", Inv("T"))));
        Proof r = Rw(inst, Imp(q, "f1ocnvfv2", [f1o, Hyp(q, "S e. Word A")]));
        r = Rw(r, Imp(q, "f1ocnvfv2", [f1o, Hyp(q, "T e. Word A")]));
        Thm($"lean-word-{lp}", $"The Lean theorem {name} for words over A: derived from Lean's proof through the model and the bridges.", Use("ex", r));

        // set.mm's ccatlen allows two alphabets: take their union, a member of the same universe.
        const string ccat = "( ( S e. Word A /\\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) )";
        const string h2 = "( U e. lean.-tower /\\ ( A e. ( U ` (/) ) /\\ B e. ( U ` (/) ) ) )";
        const string k2 = "( " + h2 + " /\\ ( S e. Word A /\\ T e. Word B ) )";
        Proof un = Imp(k2, "gruun", [Imp(k2, "lean-tw-u", [Hyp(k2, "U e. lean.-tower"), Lift(k2, Use("peano1"))]), Hyp(k2, "A e. ( U ` (/) )"), Hyp(k2, "B e. ( U ` (/) )")]);
        Proof sA = Use("mpd", Hyp(k2, "S e. Word A"), Lift(k2, Imp(null, "ssel", [Imp(null, "sswrd", [UseS("ssun1", [("A", "A"), ("B", "B")])])], s: [("C", "S")])));
        Proof sB = Use("mpd", Hyp(k2, "T e. Word B"), Lift(k2, Imp(null, "ssel", [Imp(null, "sswrd", [UseS("ssun2", [("A", "B"), ("B", "A")])])], s: [("C", "T")])));
        Proof w = Use("mpd", Use("jca", sA, sB), Use("syl", Use("jca", Hyp(k2, "U e. lean.-tower"), un), T($"lean-word-{lp}", ("U", "U"), ("A", "( A u. B )"), ("S", "S"), ("T", "T"))));
        Proof headline = Use("ex", w);
        if (Cons_(headline) != ccat)
        {
            throw new InvalidOperationException($"the restatement came out as {Of(headline)}");
        }
        Thm("lean-ccatlen", $"HEADLINE: set.mm's ccatlen, derived from Lean's proof of {name} through the model and the bridges W and F (its consequent is ccatlen's statement, token for token).", headline);
        Thm("lean-ccatlen-setmm", "The same statement as lean-ccatlen, from set.mm's own hand-written ccatlen: two independent proofs of one ZFC statement.",
            UseS("a1i", [("ps", h2)], Ax("ccatlen")));
    }
}
