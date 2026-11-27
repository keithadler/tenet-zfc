using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The parts of the model that aren't inductive types or definitions (docs/milestone3.md, step 5): string literals,
/// axioms, and the built-in quotient.
/// </summary>
public sealed partial class Model
{
    private const string StringCons = "lean.String.-cons", QuotEqv = "lean.Quot.-eqv";

    // ---- the well-ordering that choice depends on --------------------------------------------------------------------

    /// <summary>Where a definition's well-ordering goes while it is translated; a setvar replaces it in <see cref="Emit"/>.</summary>
    private const string WellOrderHole = "ZZW";

    /// <summary>The constants whose value depends on Classical.choice, so take a well-ordering after the universe.</summary>
    private readonly HashSet<string> _choiceDependent = new();

    /// <summary>
    /// A constant at the scope's universe: ( lean.c ` u ), or ( ( lean.c ` u ) ` r ) when c depends on choice, with r
    /// the scope's well-ordering of the universe. The scope then depends on choice too.
    /// </summary>
    private string ConstTerm(Name n, Scope sc)
    {
        string tok = Token(n)!;
        if (!_choiceDependent.Contains(tok))
        {
            return $"( {tok} ` {sc.Universe} )";
        }
        sc.UsesChoice = true;
        return $"( ( {tok} ` {sc.Universe} ) ` {sc.WellOrder} )";
    }

    /// <summary>
    /// A value that depends on choice gets a layer for the well-ordering, right after the universe's:
    /// ( r e. ~P ( u X. u ) |-> value ), with r a set variable the value doesn't bind.
    /// </summary>
    private string WellOrderLayer(string tok, string body, Scope sc)
    {
        if (!sc.UsesChoice)
        {
            return body;
        }
        var tokens = body.Split(' ').ToHashSet();
        string r = FirstVar(v => !sc.Bound.Contains(v) && !tokens.Contains(v));
        sc.Bound.Add(r);
        _choiceDependent.Add(tok);
        string all = WellOrdered(UniverseVar);
        return $"( {r} e. ~P ( {all} X. {all} ) |-> {Subst(body, WellOrderHole, r)} )";
    }

    /// <summary>
    /// What choice's well-ordering orders: the universe u, or in tower mode the tower's union U. ran u, which holds
    /// every level's types. One well-ordering serves every level.
    /// </summary>
    private bool IsUniverse(string dom) => tower ? dom.StartsWith("( U ` ", StringComparison.Ordinal) && OrdinalValue(dom.Split(' ')[3]) is not null && dom.Split(' ').Length == 5 : dom == "U";

    private string WellOrdered(string u) => tower ? $"U. ran {u}" : u;

    /// <summary>A constant's name without an instance's levels: Quot.lift for Quot.lift.{1,1}.</summary>
    private static string BaseName(Name n) => n is StrName { Value: ['{', ..] } inst ? $"{inst.Prefix}" : $"{n}";

    // ---- string literals --------------------------------------------------------------------------------------------

    /// <summary>
    /// A string literal, as the kernel expands it: String.ofList (String.mk before it existed) applied to the list of
    /// its characters, each Char.ofNat of its code point. Each character is one application of lean.String.-cons to
    /// the code point as set.mm's decimal numeral, so a literal stays short:
    /// ( ( lean.String.ofList ` u ) ` ( ( ( lean.String.-cons ` u ) ` ; 9 7 ) ` ( ( lean.List.nil ` u ) ` ( lean.Char ` u ) ) ) ).
    /// </summary>
    private string StringLiteral(string value, Scope sc)
    {
        Name mk = env.Find(t.Of("String.ofList")) is not null ? t.Of("String.ofList") : t.Of("String.mk");
        string u = sc.Universe;
        string str = ConstAt(mk, u);
        if (!_values.ContainsKey(StringCons))
        {
            DefineStringCons();
        }
        string list = $"( {ConstAt(t.Of("List.nil"), u)} ` {ConstAt(t.Of("Char"), u)} )";
        int[] codes = value.EnumerateRunes().Select(r => r.Value).ToArray();
        for (int i = codes.Length - 1; i >= 0; i--)
        {
            list = $"( ( ( {StringCons} ` {u} ) ` {Decimal(codes[i])} ) ` {list} )";
        }
        return $"( {str} ` {list} )";
    }

    /// <summary>( lean.c ` u ), defining c first.</summary>
    private string ConstAt(Name n, string u)
    {
        Define(n);
        if (_choiceDependent.Contains(Token(n)!))
        {
            throw new Refused($"{n} depends on Classical.choice; not expected in a string literal");
        }
        return $"( {Token(n) ?? throw new Refused($"{n}: the name has characters a set.mm token can't")} ` {u} )";
    }

    /// <summary>
    /// lean.String.-cons = ( u e. Univ |-> ( x e. NN0 |-> ( y e. ⟦List Char⟧ |-> ⟦List.cons (Char.ofNat x) y⟧ ) ) ), with
    /// x as a Nat literal (lean.Nat.-lit of lean.Nat.-ofnum). Lean names can't contain "-", so its name can't clash.
    /// </summary>
    private void DefineStringCons()
    {
        _ = NatLiteral(0);   // defines lean.Nat.-lit and lean.Nat.-ofnum
        var sc = NewScope();
        string u = UniverseVar, ch = ConstAt(t.Of("Char"), u);
        string list = $"( {ConstAt(t.Of("List"), u)} ` {ch} )", cons = $"( {ConstAt(t.Of("List.cons"), u)} ` {ch} )";
        string ofNat = ConstAt(t.Of("Char.ofNat"), u);
        string x = FirstVar(v => !sc.Bound.Contains(v)), y = FirstVar(v => !sc.Bound.Contains(v) && v != x);
        sc.Bound.AddRange([x, y]);
        string body = $"( {x} e. NN0 |-> ( {y} e. {list} |-> ( ( {cons} ` ( {ofNat} ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` {x} ) ) ) ) ` {y} ) ) )";
        Emit(t.Of("String.-cons"), StringCons, body, sc, "string literals' character cons (a helper of the model, not a Lean constant):");
    }

    // ---- axioms and the quotient ------------------------------------------------------------------------------------

    /// <summary>
    /// An axiom or a constant of the built-in quotient. One whose type is a proposition is a proof, so (/): propext,
    /// Quot.ind, and Quot.sound when it is used. Quot, Quot.mk and Quot.lift are defined by <see cref="DefineQuot"/>.
    /// Classical.choice is refused: ZFC has no definable global choice function (see docs/milestone3.md).
    /// </summary>
    private void DefineBuiltin(ConstInfo c)
    {
        Name n = c.Name;
        string tok = Token(n) ?? throw new Refused($"{n}: the name has characters a set.mm token can't");
        if (_typing.IsProposition(c.Type, new Dictionary<ulong, Expr>()) == true)
        {
            _defined.Add(n);
            Emit(n, tok, "(/)", NewScope(), c.Kind == ConstKind.Axiom ? "axiom (a proof, so (/))" : "quotient axiom (a proof, so (/))");
            return;
        }
        string baseName = BaseName(n);   // an instance, c.{0,1}, is defined like c
        switch (baseName)
        {
            case "Quot" or "Quot.mk" or "Quot.lift" when c.Kind == ConstKind.Quot:
                DefineQuot(c, baseName);
                return;
            case "Classical.choice":
                {
                    // Hilbert's ε as set.mm's hta emulates it: the least element of α in the well-ordering.
                    var sc = NewScope();
                    Expr ty = c.Type;
                    var ps = Telescope(ref ty, 2, sc);
                    string x = ps[0].Var;
                    string z = Add(sc, FirstVar(v => !sc.Bound.Contains(v))), w = Add(sc, FirstVar(v => !sc.Bound.Contains(v)));
                    sc.UsesChoice = true;
                    _defined.Add(n);
                    Emit(n, tok, Maps(ps, $"( iota_ {z} e. {x} A. {w} e. {x} -. {w} {WellOrderHole} {z} )"), sc,
                        $"axiom of choice, as the least element in a well-ordering of {WellOrdered(UniverseVar)} (Hilbert's epsilon as set.mm's hta emulates it):");
                    return;
                }
        }
        throw new Refused($"{n} is an axiom whose type isn't a proposition; not in the model yet");
    }

    /// <summary>
    /// The quotient. Quot α r is the set of classes of the least equivalence relation on ⟦α⟧ containing r, a helper:
    /// lean.Quot.-eqv = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |->
    ///   ( ( x X. x ) i^i |^| { a e. ~P ( x X. x ) | ( R0 C_ a /\ a Er x ) } ) ) ) ),
    /// with R0 = { <. b , c >. | ( ( b e. x /\ c e. x ) /\ (/) e. ( ( y ` b ) ` c ) ) }, the pairs r relates.
    /// In tower mode x and y range over _V, so one helper serves every level.
    /// - Quot α r is ( x /. E ), its classes.
    /// - Quot.mk α r a is [ a ] E, a's class.
    /// - Quot.lift α r β f h is set.mm's function lift ran ( p e. x |-> <. [ p ] E , ( f ` p ) >. ), f on a
    ///   representative: a function on the classes when f respects E, which h ensures (see <see cref="QuotLiftIota"/>).
    /// None of it needs choice. In tower mode each is defined at its levels (Quot.{1}, Quot.lift.{1,1}, …). At level 0,
    /// where α is a proposition (in 2o), Quot α r is a proposition too, so it is α itself (Quot.mk is then a proof,
    /// (/)), and Quot.lift f h is f.
    /// </summary>
    private void DefineQuot(ConstInfo c, string which)
    {
        EnsureQuotEqv();
        string Rel(List<(string Var, string Dom)> ps) => $"( ( ( {QuotEqv} ` {UniverseVar} ) ` {ps[0].Var} ) ` {ps[1].Var} )";
        var sc = NewScope();
        Expr ty = c.Type;
        var ps = Telescope(ref ty, which switch { "Quot" => 2, "Quot.mk" => 3, _ => 5 }, sc);
        bool prop = tower && ps[0].Dom == "2o";   // α : Prop
        string tok = Token(c.Name)!;
        _defined.Add(c.Name);
        switch (which)
        {
            case "Quot":
                Emit(c.Name, tok, Maps(ps, prop ? ps[0].Var : $"( {ps[0].Var} /. {Rel(ps)} )"), sc,
                    prop ? "quotient of a proposition (the proposition itself)" : "quotient type");
                return;
            case "Quot.mk":
                Emit(c.Name, tok, Maps(ps, $"[ {ps[2].Var} ] {Rel(ps)}"), sc, "quotient's class map");
                return;
            default:
                {
                    string p = Add(sc, FirstVar(v => !sc.Bound.Contains(v)));
                    string body = prop ? ps[3].Var : $"ran ( {p} e. {ps[0].Var} |-> <. [ {p} ] {Rel(ps)} , ( {ps[3].Var} ` {p} ) >. )";
                    Emit(c.Name, tok, Maps(ps, body), sc, prop ? "quotient's lift on a proposition (f itself)" : "quotient's lift");
                    return;
                }
        }
    }

    /// <summary>lean.Quot.-eqv, the quotient's equivalence relation (<see cref="DefineQuot"/>), once.</summary>
    private void EnsureQuotEqv()
    {
        if (_values.ContainsKey(QuotEqv))
        {
            return;
        }
        // Its bound variables come from the end of the alphabet, away from those of Quot.lift's hypothesis h, which
        // the computation rule's context mentions.
        // Its domains are those of Quot's own type, before monomorphization: in tower mode α's level is a parameter,
        // so α ranges over the whole tower, U. ran u, and one helper serves every level.
        var sc = NewScope();
        ConstInfo quot = env.Find(t.Of("Quot")) is { Kind: ConstKind.Quot } q ? q : throw new Refused("Quot is not in the export");
        Expr ty = quot.Type;
        var ps = Telescope(ref ty, 2, sc);
        string Far() => Enumerable.Reverse(Letters).Concat(ExtraSetVars).FirstOrDefault(v => !sc.Bound.Contains(v)) is string v ? Add(sc, Declare(v)) : throw new Refused("more set variables needed than the model declares");   // set.mm's letters first, from the end
        string a = Far(), b = Far(), c = Far();
        string x = ps[0].Var, y = ps[1].Var, sq = $"( {x} X. {x} )";
        string r0 = $"{{ <. {b} , {c} >. | ( ( {b} e. {x} /\\ {c} e. {x} ) /\\ (/) e. ( ( {y} ` {b} ) ` {c} ) ) }}";
        string e = $"( {sq} i^i |^| {{ {a} e. ~P {sq} | ( {r0} C_ {a} /\\ {a} Er {x} ) }} )";
        Emit(t.Of("Quot.-eqv"), QuotEqv, Maps(ps, e), sc, "quotient's equivalence relation (a helper of the model, not a Lean constant): the least one containing r,");
    }

    private static string Add(Scope sc, string v)
    {
        sc.Bound.Add(v);
        return v;
    }

    /// <summary>The child of a term's top syntax axiom bound to its variable <paramref name="var"/>.</summary>
    private string Kid(string type, string term, string var)
    {
        SyntaxTree n = pr.Parse(type, term.Split(' ')) ?? throw new InvalidOperationException($"does not parse: {term}");
        int i = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList().IndexOf(var);
        return i >= 0 ? pr.Render(n.Children[i]) : throw new InvalidOperationException($"{n.Rule.Label} has no {var}");
    }

    /// <summary>Sethood for the forms the builtins use; null for any other form.</summary>
    private Proof? ExistsMore(string ph, SyntaxTree n)
    {
        if (n.Rule.Label is not ("cin" or "cxp" or "crn" or "cqs" or "cpw" or "crio" or "cec"))
        {
            return null;   // before rendering: most calls get here with a class variable, under a large term
        }
        string term = pr.Render(n);
        string K(string v) => Kid("class", term, v);
        switch (n.Rule.Label)
        {
            case "cin":
                return _d.Syl(ExistsIn(ph, K("A")), pr.Apply("inex1g", S(("A", K("A")), ("B", K("B")), ("V", "_V"))));
            case "cxp":
                return _d.Syl(_d.Jca(ExistsIn(ph, K("A")), ExistsIn(ph, K("B"))), pr.Apply("xpexg", S(("A", K("A")), ("B", K("B")), ("V", "_V"), ("W", "_V"))));
            case "crn":
                return _d.Syl(ExistsIn(ph, K("A")), pr.Apply("rnexg", S(("A", K("A")), ("V", "_V"))));
            case "cqs":
                return _d.Syl(ExistsIn(ph, K("A")), pr.Apply("qsexg", S(("A", K("A")), ("R", K("R")), ("V", "_V"))));
            case "cpw":
                return _d.Syl(ExistsIn(ph, K("A")), pr.Apply("pwexg", S(("A", K("A")), ("V", "_V"))));
            case "crio":
                return _d.Lift(ph, pr.Apply("riotaex", S(("x", K("x")), ("A", K("A")), ("ps", K("ph")))));
            case "cec":
                return _d.Syl(ExistsIn(ph, K("R")), pr.Apply("ecexg", S(("A", K("A")), ("R", K("R")), ("B", "_V"))));
        }
        return null;
    }

    /// <summary>
    /// The computation rule of the quotient, Quot.lift f h (Quot.mk r a) = f a, as a set.mm theorem:
    /// ( hypotheses -> ( ( ( ( ( ( ( lean.Quot.lift ` U ) ` A ) ` B ) ` C ) ` D ) ` E ) ` ( ( ( ( lean.Quot.mk ` U ) ` A ) ` B ) ` F ) ) = ( D ` F ) ).
    /// 1. Unfold both: the lift is ran ( p e. A |-> <. [ p ] R , ( D ` p ) >. ), the class is [ F ] R.
    /// 2. set.mm's qliftval evaluates the lift on a class, given that R is an equivalence relation on A and that the
    ///    lift is a function (qliftfund).
    /// 3. R is an equivalence relation: an intersection of them, inside A X. A (riiner).
    /// 4. The lift is a function because D is constant on R's classes: R is inside the kernel of D,
    ///    K = ( `' D o. D ), which is an equivalence relation (fcoinver) containing r, so one of those intersected.
    ///    K contains r because of h: for r b c, h's value at b and c maps (/) into Eq β (D b) (D c), so that is
    ///    nonempty, which says D c = D b.
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) QuotLiftIota() => QuotLiftIota(t.Of("Quot.lift"), t.Of("Quot.mk"));

    /// <summary>
    /// The computation rule for instances: in tower mode Quot.lift.{k,l} with Quot.mk.{k}, for k, l ≥ 1. (At k = 0
    /// Quot.mk is a proof, (/), and at l = 0 Quot.lift is; then there is nothing to compute.)
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) QuotLiftIota(Name liftN, Name mkN)
    {
        Define(liftN);
        Define(mkN);
        string lift = Token(liftN)!, mk = Token(mkN)!;
        if (_values[lift] == "(/)" || _values[mk] == "(/)")
        {
            throw new Refused($"{liftN} or {mkN} is a proof, (/): no computation rule to prove");
        }
        string[] largs = ["A", "B", "C", "D", "E"], margs = ["A", "B", "F"];
        List<string> ld = Domains(lift, largs, 5), md = Domains(mk, margs, 3);
        if (ld[3] != "( C ^m A )" || md[2] != "A" || md[0] != ld[0] || !IsUniverse(ld[0]) || !IsUniverse(ld[2]))
        {
            throw new InvalidOperationException($"Quot.lift's or Quot.mk's domains aren't as expected: {string.Join(", ", ld)}; {string.Join(", ", md)}");
        }
        var hyps = new List<string> { UHyp };
        hyps.AddRange(largs.Select((a, i) => $"{a} e. {ld[i]}"));
        hyps.Add("F e. A");
        string ph = Conj(hyps);
        Proof H(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");

        // 1. Unfold.
        (Proof eqMk, _, _) = Unfold(ph, mk, margs, (i, dom) => H(ph, $"{margs[i]} e. {dom}"));
        (Proof eqL, _, _) = Unfold(ph, lift, largs, (i, dom) => H(ph, $"{largs[i]} e. {dom}"));
        string cls = Rhs(eqMk), g = Rhs(eqL);
        Proof cur = pr.Apply("fveq12d", S(("ph", ph), ("F", Lhs(eqL)), ("G", g), ("A", Lhs(eqMk)), ("B", cls)), eqL, eqMk);
        string mpt = Kid("class", g, "A"), p = Kid("class", mpt, "x"), pair = Kid("class", mpt, "B");
        string rel = Kid("class", Kid("class", pair, "A"), "R"), val = Kid("class", pair, "B");
        if (cls != $"[ F ] {rel}" || val != $"( D ` {p} )")
        {
            throw new InvalidOperationException($"unexpected lift {g} or class {cls}");
        }

        var (erR, fun, lsub, qh, bound) = LiftIsFunction(ph, ld, g, H);
        Proof Same(string to) => _d.Congruence("class", Subst(val, p, "Z"), "Z", pr.Apply("id", S(("ph", $"{p} = {to}"))));
        Proof atF = pr.Apply("qliftval", new Dictionary<string, string>(lsub) { ["B"] = "( D ` F )", ["C"] = "F" }, qh[0], qh[1], erR, qh[2], Same("F"), fun);
        cur = _d.Trans(cur, _d.Syl(_d.Jca(pr.Apply("id", S(("ph", ph))), H(ph, "F e. A")), atF));

        string[] dv = DistinctFor(ld[4].Split(' ').Where(_values.ContainsKey).Concat([lift, mk, QuotEqv]).Distinct(), largs.Append("F"));
        return (cur.Proves, cur.Proof, WithRequired([string.Join(' ', $"{dv[0]} {bound}".Split(' ', StringSplitOptions.RemoveEmptyEntries).Distinct())], cur.Proof));
    }

    /// <summary>
    /// Quot.lift's value g = ran ( p e. A |-> <. [ p ] R , ( D ` p ) >. ) is a function, under the hypotheses on A … E
    /// in ph (steps 3 and 4 of <see cref="QuotLiftIota()"/>). Returns R Er A, Fun g, the substitution and the
    /// hypotheses qliftval and qliftf share, and the bound variables the proof adds.
    /// </summary>
    private (Proof ErR, Proof Fun, Dictionary<string, string> Lsub, Proof[] Qh, string Bound) LiftIsFunction(string ph, List<string> ld, string g, Func<string, string, Proof> H)
    {
        string mpt = Kid("class", g, "A"), p = Kid("class", mpt, "x"), pair = Kid("class", mpt, "B");
        string rel = Kid("class", Kid("class", pair, "A"), "R"), val = Kid("class", pair, "B");
        var (eqE, ebody, sq, sx, pw, Phi, Elrab, r0, cv, erR) = Eqv(ph, ld[0], g, H);
        var used = new HashSet<string>($"{ph} {g} {ebody} {cv}".Split(' '));
        string q = FirstVar(v => !used.Contains(v));

        // 4. R is inside the kernel K of D.
        string k = "( `' D o. D )";
        Proof DMap(string ctx) => _d.Syl(H(ctx, "D e. ( C ^m A )"), pr.Apply("elmapi", S(("A", "D"), ("B", "C"), ("C", "A"))));
        Proof DFn(string ctx) => _d.Syl(DMap(ctx), pr.Apply("ffn", S(("F", "D"), ("A", "A"), ("B", "C"))));
        Proof Kernel(string ctx, string b, string c, Proof bIn, Proof cIn) =>   // ( ctx -> ( b K c <-> ( D ` b ) = ( D ` c ) ) )
            _d.Syl(pr.Apply("3jca", S(("ph", ctx), ("ps", "D Fn A"), ("ch", $"{b} e. A"), ("th", $"{c} e. A")), DFn(ctx), bIn, cIn),
                pr.Apply("fcoinvbr", S(("F", "D"), ("A", "A"), ("X", b), ("Y", c), (".~", k)), pr.Apply("eqid", S(("A", k)))));
        Proof kEr = _d.Syl(DFn(ph), pr.Apply("fcoinver", S(("F", "D"), ("X", "A"))));
        Proof kInPw = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{k} e. {pw}"), ("ch", $"{k} C_ {sq}")),
            _d.Syl(kEr, pr.Apply("erssxp", S(("R", k), ("A", "A")))),
            _d.Syl(Exists(ph, sq), pr.Apply("elpw2g", S(("A", k), ("B", sq), ("V", "_V")))));
        Proof r0InK = R0InKernel(ph, r0, k, ld[4], ld[2], H, Kernel);
        Proof kInS = pr.Apply("sylibr", S(("ph", ph), ("ps", $"( {k} e. {pw} /\\ {Phi(k)} )"), ("ch", $"{k} e. {sx}")),
            _d.Jca(kInPw, _d.Jca(r0InK, kEr)), Elrab(k));
        Proof eInK = pr.Apply("sstrd", S(("ph", ph), ("A", ebody), ("B", $"|^| {sx}"), ("C", k)),
            _d.Lift(ph, pr.Apply("inss2", S(("A", sq), ("B", $"|^| {sx}")))),
            _d.Syl(kInS, pr.Apply("intss1", S(("A", k), ("B", sx)))));
        Proof relInK = pr.Apply("eqsstrd", S(("ph", ph), ("A", rel), ("B", ebody), ("C", k)), eqE, eInK);

        // The lift is a function: ( ( ph /\ p R q ) -> ( D ` p ) = ( D ` q ) ).
        string ctxF = $"( {ph} /\\ {p} {rel} {q} )";
        Proof phF = pr.Apply("simpl", S(("ph", ph), ("ps", $"{p} {rel} {q}"))), pq = pr.Apply("simpr", S(("ph", ph), ("ps", $"{p} {rel} {q}")));
        Proof erF = _d.Syl(phF, erR);
        var er = S(("ph", ctxF), ("R", rel), ("X", "A"), ("A", p), ("B", q));
        Proof pIn = pr.Apply("ercl", er, erF, pq), qIn = pr.Apply("ercl2", er, erF, pq);
        Proof pkq = pr.Apply("mpd", S(("ph", ctxF), ("ps", $"{p} {rel} {q}"), ("ch", $"{p} {k} {q}")), pq,
            pr.Apply("ssbrd", S(("ph", ctxF), ("A", rel), ("B", k), ("C", p), ("D", q)), _d.Syl(phF, relInK)));
        Proof constant = _d.Transport(pkq, Kernel(ctxF, p, q, pIn, qIn));

        // 2. qliftval.
        string valQ = Subst(val, p, q);
        var lsub = S(("ph", ph), ("x", p), ("y", q), ("A", val), ("F", g), ("R", rel), ("X", "A"), ("Y", "C"), ("V", ld[0]));
        Proof q1 = pr.Apply("eqid", S(("A", g)));
        Proof q2 = pr.Apply("ffvelcdmda", S(("ph", ph), ("A", "A"), ("B", "C"), ("C", p), ("F", "D")), DMap(ph));
        Proof q4 = H(ph, $"A e. {ld[0]}");
        Proof Same(string to) => _d.Congruence("class", Subst(val, p, "Z"), "Z", pr.Apply("id", S(("ph", $"{p} = {to}"))));
        Proof fun = pr.Apply("qliftfund", new Dictionary<string, string>(lsub) { ["B"] = valQ }, q1, q2, erR, q4, Same(q), constant);
        return (erR, fun, lsub, [q1, q2, q4], $"{cv} {q}");
    }

    /// <summary>
    /// ( ph -> R0 C_ K ): every pair r relates is in D's kernel, because of h. For r b c, h's value at b and c is in
    /// ( Eq β (D b) (D c) ^m ( ( B ` b ) ` c ) ) with (/) in its domain, so the Eq is nonempty, and it is
    /// if ( ( D ` c ) = ( D ` b ) , 1o , (/) ).
    /// </summary>
    private Proof R0InKernel(string ph, string r0, string k, string hDom, string cDom, Func<string, string, Proof> h,
        Func<string, string, string, Proof, Proof, Proof> kernel)
    {
        string b = Kid("class", r0, "x"), c = Kid("class", r0, "y"), psi = Kid("class", r0, "ph");
        if ($" {ph} ".Contains($" {b} ", StringComparison.Ordinal) || $" {ph} ".Contains($" {c} ", StringComparison.Ordinal))
        {
            throw new Refused($"the relation's variables {b} and {c} occur in the context");
        }
        string ctx = $"( {ph} /\\ {psi} )";
        string bc = $"( {b} e. A /\\ {c} e. A )", rbc = $"(/) e. ( ( B ` {b} ) ` {c} )";
        Proof psiP = pr.Apply("simpr", S(("ph", ph), ("ps", psi)));
        Proof bcP = _d.Syl(psiP, pr.Apply("simpl", S(("ph", bc), ("ps", rbc))));
        Proof bIn = _d.Syl(bcP, pr.Apply("simpl", S(("ph", $"{b} e. A"), ("ps", $"{c} e. A"))));
        Proof cIn = _d.Syl(bcP, pr.Apply("simpr", S(("ph", $"{b} e. A"), ("ps", $"{c} e. A"))));
        Proof rIn = _d.Syl(psiP, pr.Apply("simpr", S(("ph", bc), ("ps", rbc))));

        // ( ctx -> elem e. EQ ), EQ = Eq β (D b) (D c): h at b, at c, and at r b c.
        string elem, eq;
        Proof inEq;
        if (hDom.StartsWith("if ( ", StringComparison.Ordinal))
        {
            // In tower mode h's type is a proposition: if ( A. v e. A (/) e. if ( A. w e. A (/) e. if (
            // A. s e. ( ( B ` v ) ` w ) (/) e. EQ , 1o , (/) ) , 1o , (/) ) , 1o , (/) ), and h is in it, so it holds.
            Proof s1 = PropAt(ctx, hDom, "E", h(ctx, $"E e. {hDom}"), b, bIn, [b, c]);
            string Of(Proof q) => Kid("wff", _d.Split(q.Proves).X, "B");   // ( ctx -> (/) e. X ): X
            Proof s2 = PropAt(ctx, Of(s1), "(/)", s1, c, cIn, [b, c]);
            inEq = PropAt(ctx, Of(s2), "(/)", s2, "(/)", rIn, [b, c]);
            elem = "(/)";
            eq = Of(inEq);
        }
        else
        {
            // h at b, then at c: ( ( E ` b ) ` c ) e. ( EQ ^m ( ( B ` b ) ` c ) ).
            string v = Kid("class", hDom, "x"), inner = Kid("class", hDom, "B");
            string w = Kid("class", inner, "x"), body = Kid("class", inner, "B");
            if (new[] { v, w }.Intersect([b, c]).Any())
            {
                throw new Refused($"the relation's variables {b} and {c} clash with h's {v} and {w}");
            }
            string innerB = Subst(inner, v, b), bodyB = Subst(body, v, b), bodyBC = Subst(bodyB, w, c);
            Proof Ixp(string f, string x, string dom, string bd, string at, string result, Proof fIn, Proof atIn) =>
                _d.Syl(_d.Jca(fIn, atIn), pr.Apply("fvixp", S(("F", f), ("x", x), ("A", dom), ("B", bd), ("C", at), ("D", result)),
                    _d.Congruence("class", Subst(bd, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {at}"))))));
            Proof hb = Ixp("E", v, "A", inner, b, innerB, h(ctx, $"E e. {hDom}"), bIn);
            Proof hbc = Ixp($"( E ` {b} )", w, "A", bodyB, c, bodyBC, hb, cIn);
            string gbc = $"( ( E ` {b} ) ` {c} )", dom = Kid("class", bodyBC, "B");
            eq = Kid("class", bodyBC, "A");
            if (Kid("class", bodyBC, "F") != "^m" || dom != $"( ( B ` {b} ) ` {c} )")
            {
                throw new InvalidOperationException($"h's type isn't as expected: {bodyBC}");
            }
            Proof map = _d.Syl(hbc, pr.Apply("elmapi", S(("A", gbc), ("B", eq), ("C", dom))));
            inEq = pr.Apply("ffvelcdmd", S(("ph", ctx), ("A", dom), ("B", eq), ("C", "(/)"), ("F", gbc)), map, rIn);
            elem = $"( {gbc} ` (/) )";
        }

        // The Eq, unfolded: if ( ( D ` c ) = ( D ` b ) , 1o , (/) ), nonempty, so its condition holds.
        Proof DMapC = _d.Syl(h(ctx, "D e. ( C ^m A )"), pr.Apply("elmapi", S(("A", "D"), ("B", "C"), ("C", "A"))));
        Proof Val(string x, Proof xIn) => pr.Apply("ffvelcdmd", S(("ph", ctx), ("A", "A"), ("B", "C"), ("C", x), ("F", "D")), DMapC, xIn);
        string[] eargs = ["C", $"( D ` {b} )", $"( D ` {c} )"];
        string eqTok = Kid("class", Kid("class", Kid("class", Kid("class", eq, "F"), "F"), "F"), "F");
        (Proof eqEq, _, _) = Unfold(ctx, eqTok, eargs, (i, d) => i == 0 ? h(ctx, $"C e. {cDom}") : Val(i == 1 ? b : c, i == 1 ? bIn : cIn));
        string ite = Rhs(eqEq), cond = Kid("class", ite, "ph");
        Proof inIte = pr.Apply("eleqtrd", S(("ph", ctx), ("A", elem), ("B", eq), ("C", ite)), inEq, eqEq);
        Proof notEmpty = _d.Syl(inIte, pr.Apply("n0i", S(("B", elem), ("A", ite))));
        Proof holds = _d.Syl(notEmpty, pr.Apply("con1i", S(("ph", cond), ("ps", $"{ite} = (/)")),
            pr.Apply("iffalse", S(("ph", cond), ("A", Kid("class", ite, "A")), ("B", Kid("class", ite, "B"))))));
        Proof same = _d.Symm(holds);   // ( D ` b ) = ( D ` c )
        Proof inK = pr.Apply("mpbird", S(("ph", ctx), ("ps", $"{b} {k} {c}"), ("ch", $"( D ` {b} ) = ( D ` {c} )")), same, kernel(ctx, b, c, bIn, cIn));

        Proof imp = pr.Apply("ex", S(("ph", ph), ("ps", psi), ("ch", $"{b} {k} {c}")), inK);
        Proof sub = pr.Apply("ssopab2dv", S(("ph", ph), ("x", b), ("y", c), ("ps", psi), ("ch", $"{b} {k} {c}")), imp);
        return pr.Apply("sstrd", S(("ph", ph), ("A", r0), ("B", $"{{ <. {b} , {c} >. | {b} {k} {c} }}"), ("C", k)),
            sub, _d.Lift(ph, pr.Apply("opabss", S(("x", b), ("y", c), ("R", k)))));
    }

    /// <summary>
    /// The quotient's relation R = ( ( ( lean.Quot.-eqv ` U ) ` A ) ` B ) under ph, which has A e. level and B's
    /// hypothesis: R unfolded (R = ( ( A X. A ) i^i |^| Sx )), the parts of Sx, and R Er A, since R is an intersection
    /// of equivalence relations inside A X. A (riiner, intiin). The bound variable it adds avoids ph and avoid.
    /// </summary>
    private (Proof EqE, string Ebody, string Sq, string Sx, string Pw, Func<string, string> Phi, Func<string, Proof> Elrab, string R0, string Cv, Proof ErR)
        Eqv(string ph, string level, string avoid, Func<string, string, Proof> H)
    {
        string rel = $"( ( ( {QuotEqv} ` U ) ` A ) ` B )";
        // 3. The relation, unfolded: ( ph -> R = ( ( A X. A ) i^i |^| Sx ) ), and an equivalence relation.
        // In tower mode A ranges over U. ran U there, and A's level is inside it.
        Proof EqvArg(int i, string dom) => i == 0 && dom == "U. ran U" && level != dom
            ? pr.Apply("mpd", S(("ph", ph), ("ps", $"A e. {level}"), ("ch", "A e. U. ran U")), H(ph, $"A e. {level}"),
                pr.Apply("sseld", S(("ph", ph), ("A", level), ("B", dom), ("C", "A")), SubOmega(ph, level)))
            : H(ph, $"{(i == 0 ? "A" : "B")} e. {dom}");
        (Proof eqE, _, _) = Unfold(ph, QuotEqv, ["A", "B"], EqvArg);
        string ebody = Rhs(eqE), sq = Kid("class", ebody, "A"), sx = Kid("class", Kid("class", ebody, "B"), "A");
        string sv = Kid("class", sx, "x"), pw = Kid("class", sx, "A"), phi = Kid("class", sx, "ph");
        string r0 = Kid("wff", Kid("wff", phi, "ph"), "A");
        var used = new HashSet<string>($"{ph} {avoid} {ebody}".Split(' '));
        string cv = FirstVar(v => !used.Contains(v));
        string Phi(string s) => Subst(phi, sv, s);
        Proof Elrab(string a) => pr.Apply("elrab", S(("A", a), ("B", pw), ("x", sv), ("ph", phi), ("ps", Phi(a))),
            _d.Congruence("wff", Subst(phi, sv, "Z"), "Z", pr.Apply("id", S(("ph", $"{sv} = {a}")))));

        Proof eachEr = pr.Apply("rgen", S(("x", cv), ("A", sx), ("ph", $"{cv} Er A")),
            _d.Syl(pr.Apply("simprbi", S(("ph", $"{cv} e. {sx}"), ("ps", $"{cv} e. {pw}"), ("ch", Phi(cv))), Elrab(cv)),
                pr.Apply("simpr", S(("ph", $"{r0} C_ {cv}"), ("ps", $"{cv} Er A")))));
        string iin = $"|^|_ {cv} e. {sx} {cv}", sqIin = $"( {sq} i^i {iin} )";
        Proof iinEr = pr.Apply("ax-mp", S(("ph", $"A. {cv} e. {sx} {cv} Er A"), ("ps", $"{sqIin} Er A")),
            eachEr, pr.Apply("riiner", S(("x", cv), ("A", sx), ("R", cv), ("B", "A"))));
        Proof toIin = pr.Apply("ineq2i", S(("A", $"|^| {sx}"), ("B", iin), ("C", sq)), pr.Apply("intiin", S(("x", cv), ("A", sx))));
        Proof eBi = pr.Apply("ax-mp", S(("ph", $"{ebody} = {sqIin}"), ("ps", $"( {ebody} Er A <-> {sqIin} Er A )")),
            toIin, pr.Apply("ereq1", S(("R", ebody), ("S", sqIin), ("A", "A"))));
        Proof eEr = pr.Apply("mpbir", S(("ph", $"{ebody} Er A"), ("ps", $"{sqIin} Er A")), iinEr, eBi);
        Proof erR = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{rel} Er A"), ("ch", $"{ebody} Er A")),
            _d.Lift(ph, eEr), _d.Syl(eqE, pr.Apply("ereq1", S(("R", rel), ("S", ebody), ("A", "A")))));
        return (eqE, ebody, sq, sx, pw, Phi, Elrab, r0, cv, erR);
    }

    /// <summary>
    /// The typing of the quotient's constants for the theorem translator (TheoremTranslator.cs): the label of a lemma
    /// lean-in-c, |- ( ( ( U e. lean.-tower /\ A e. D1 ) /\ … ) -> body e. target ), body being c's value at class
    /// variables and target the codomain of c's type there (read off <paramref name="ty"/>, ⟦type of c⟧). For k ≥ 1:
    /// - Quot.{k}: ( A /. R ) is in A's universe: it is inside ~P A (qsss, R being an equivalence relation), which is
    ///   in the universe (grupw, gruss).
    /// - Quot.mk.{k}: [ C ] R is a class (ecelqsw), and ( A /. R ) is ⟦Quot r⟧.
    /// - Quot.lift.{k,l}: the lift is a function (as for the computation rule, because of h), from the classes to β
    ///   (qliftf), so a member of ( β ^m ⟦Quot r⟧ ) (elmapg). At k = 0 it is f, in ( β ^m α ), and ⟦Quot r⟧ is α.
    /// </summary>
    internal string QuotInLemma(ConstInfo ci, string ty)
    {
        Name n = ci.Name;
        string label = $"lean-in-{LabelPart($"{n}")}";
        if (Has(label))
        {
            return label;
        }
        string tok = Token(n)!, which = BaseName(n);
        int arity = which switch { "Quot" => 2, "Quot.mk" => 3, "Quot.lift" => 5, _ => throw new Refused($"{n}: not a quotient constant with a value") };
        var args = ClassVars.Take(arity).ToList();
        List<string> doms = Domains(tok, args, arity);
        string ph = Conj(new[] { UHyp }.Concat(args.Select((a, i) => $"{a} e. {doms[i]}")));
        Proof H(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");
        (Proof eqV, _, _) = Unfold(ph, tok, args, (i, dom) => H(ph, $"{args[i]} e. {dom}"));
        string body = Rhs(eqV), target = ty;
        foreach (string a in args)
        {
            SyntaxTree tn = pr.Parse("class", target.Split(' '))!;
            target = tn.Rule.Label == "cixp" ? Subst(pr.Render(tn.Children[2]), pr.Render(tn.Children[0]), a)
                : tn.Rule.Label == "co" && pr.Render(tn.Children[2]) == "^m" ? pr.Render(tn.Children[0])
                : throw new Refused($"{n}'s type {ty} has fewer than {arity} arguments");
        }
        // ( ph -> Q = ( A /. R ) ) for Q = ( ( ( lean.Quot.{k} ` U ) ` A ) ` B ), from a target that names it.
        Proof QuotEq(string q)
        {
            string qtok = Kid("class", Kid("class", Kid("class", q, "F"), "F"), "F");
            Define(_tokenNames.TryGetValue(qtok, out Name? qn) ? qn : throw new Refused($"{qtok} isn't a defined constant"));
            (Proof e, _, _) = Unfold(ph, qtok, ["A", "B"], (i, dom) => H(ph, $"{(i == 0 ? "A" : "B")} e. {dom}"));
            return e;
        }
        Proof r;
        switch (which)
        {
            case "Quot" when body == "A":
                r = H(ph, "A e. 2o");   // a quotient of a proposition is the proposition
                break;
            case "Quot":
                {
                    var e = Eqv(ph, doms[0], body, H);
                    string rel = Kid("class", body, "R"), level = doms[0];
                    Proof sub = pr.Apply("qsss", S(("ph", ph), ("A", "A"), ("R", rel)), e.ErR);
                    if (lowered)
                    {
                        throw new Refused("quotients in the lowered tower are not built yet (docs/milestone4.md)");
                    }
                    Proof univ = LevelUniv(ph, level.Split(' ')[3]);
                    Proof pwIn = _d.Syl(_d.Jca(univ, H(ph, $"A e. {level}")), pr.Apply("grupw", S(("U", level), ("A", "A"))));
                    r = _d.Syl(pr.Apply("3jca", S(("ph", ph), ("ps", $"{level} e. Univ"), ("ch", $"~P A e. {level}"), ("th", $"{body} C_ ~P A")), univ, pwIn, sub),
                        pr.Apply("gruss", S(("U", level), ("A", "~P A"), ("B", body))));
                    if (target != level)
                    {
                        throw new Refused($"{n}'s codomain is {target}, not {level}");
                    }
                    break;
                }
            case "Quot.mk":
                {
                    string rel = Kid("class", body, "R");
                    Proof eqQ = QuotEq(target);
                    Proof inQs = _d.Syl(_d.Jca(Exists(ph, rel), H(ph, "C e. A")), pr.Apply("ecelqsw", S(("R", rel), ("V", "_V"), ("B", "C"), ("A", "A"))));
                    r = pr.Apply("eleqtrrd", S(("ph", ph), ("A", body), ("B", Rhs(eqQ)), ("C", target)), inQs, eqQ);
                    break;
                }
            default:
                {
                    string q = Kid("class", target, "B");
                    Proof eqQ = QuotEq(q);
                    string qs = Rhs(eqQ), cod = Kid("class", target, "A");
                    Proof inQs;
                    if (body == "D")
                    {
                        inQs = H(ph, $"D e. ( {cod} ^m A )");   // a quotient of a proposition: Q is α, and the lift is f
                    }
                    else
                    {
                        var (erR, fun, lsub, qh, _) = LiftIsFunction(ph, doms, body, H);
                        Proof f = pr.Apply("mpbid", S(("ph", ph), ("ps", $"Fun {body}"), ("ch", $"{body} : {qs} --> {cod}")), fun,
                            pr.Apply("qliftf", new Dictionary<string, string>(lsub) { ["ph"] = ph }, qh[0], qh[1], erR, qh[2]));
                        Proof bi = _d.Syl(_d.Jca(Exists(ph, cod), Exists(ph, qs)), pr.Apply("elmapg", S(("A", cod), ("B", qs), ("C", body), ("V", "_V"), ("W", "_V"))));
                        inQs = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{body} e. ( {cod} ^m {qs} )"), ("ch", $"{body} : {qs} --> {cod}")), f, bi);
                    }
                    Proof eqT = pr.Apply("oveq2d", S(("ph", ph), ("A", q), ("B", qs), ("C", cod), ("F", "^m")), eqQ);
                    r = pr.Apply("eleqtrrd", S(("ph", ph), ("A", body), ("B", $"( {cod} ^m {qs} )"), ("C", target)), inQs, eqT);
                    break;
                }
        }
        EmitLemma(label, $"The value of {n} is in its type.", r);
        return label;
    }

    /// <summary>
    /// The $d conditions, with those the proof's steps need added: in tower mode the tower's lemmas bring their own
    /// bound variables (lean-tw's n), which must be distinct from U.
    /// </summary>
    private string[] WithRequired(string[] dv, List<string> proof) =>
        dv.Concat(DistinctVars.Required(pr.Database, proof).Select(d => $"{d.Item1} {d.Item2}")).Distinct().ToArray();

    /// <summary>
    /// From ( ctx -> m e. if ( A. x e. D ps , 1o , (/) ) ), a proposition of the tower model with a member, so holding,
    /// and ( ctx -> at e. D ): ( ctx -> ps[x := at] ). By rspcv, which, unlike rspcdv, has no $d between x and ctx.
    /// </summary>
    private Proof PropAt(string ctx, string ite, string m, Proof mIn, string at, Proof atIn, string[] avoid)
    {
        string cond = Kid("class", ite, "ph");
        Proof notEmpty = _d.Syl(mIn, pr.Apply("n0i", S(("B", m), ("A", ite))));
        Proof holds = _d.Syl(notEmpty, pr.Apply("con1i", S(("ph", cond), ("ps", $"{ite} = (/)")),
            pr.Apply("iffalse", S(("ph", cond), ("A", Kid("class", ite, "A")), ("B", Kid("class", ite, "B"))))));
        string x = Kid("wff", cond, "x"), d = Kid("wff", cond, "A"), ps = Kid("wff", cond, "ph");
        if (avoid.Contains(x))
        {
            throw new Refused($"h's bound variable {x} clashes with the relation's {string.Join(" and ", avoid)}");
        }
        string ch = Subst(ps, x, at);
        Proof cong = ps.Split(' ').Contains(x)
            ? _d.Congruence("wff", Subst(ps, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {at}"))))
            : pr.Apply("biidd", S(("ph", $"{x} = {at}"), ("ps", ps)));
        Proof imp = _d.Syl(atIn, pr.Apply("rspcv", S(("x", x), ("A", at), ("B", d), ("ph", ps), ("ps", ch)), cong));
        return pr.Apply("mpd", S(("ph", ctx), ("ps", cond), ("ch", ch)), holds, imp);
    }

    /// <summary>
    /// Classical.choice picks an element: given a well-ordering W of the universe and a proof that α is nonempty,
    /// ( hypotheses /\ W We U ) -> ( ( ( ( lean.Classical.choice ` U ) ` W ) ` A ) ` B ) e. A.
    /// α is in the universe, so inside it (grutr), and nonempty (Nonempty's condition holds, rexn0), so W has a
    /// unique least element on it (wereu), which the definition picks (riotacl).
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) ChoiceSpec()
    {
        return ChoiceSpec(t.Of("Classical.choice"));
    }

    /// <summary>
    /// <see cref="ChoiceSpec()"/> for an instance: in tower mode Classical.choice.{k}, k ≥ 1, with the hypothesis
    /// W We U. ran U (one well-ordering of the tower's union serves every level).
    /// </summary>
    public (MmExpr Statement, List<string> Proof, string[] Distinct) ChoiceSpec(Name n)
    {
        Define(n);
        string tok = Token(n)!;
        string[] args = ["W", "A", "B"];
        List<string> doms = Domains(tok, args, 3);
        if (_values[tok] == "(/)" || !IsUniverse(doms[1]))
        {
            throw new Refused($"{n} is a proof, (/), or its type's domain isn't a universe: {string.Join(", ", doms)}");
        }
        string all = WellOrdered("U"), lev = doms[1];
        var hyps = new List<string> { UHyp };
        hyps.AddRange(args.Select((a, i) => $"{a} e. {doms[i]}"));
        hyps.Add($"W We {all}");
        string ph = Conj(hyps);
        Proof H(string h) => Hyp(ph, h) ?? throw new Refused($"no hypothesis {h}");
        (Proof eq, _, _) = Unfold(ph, tok, args, (i, dom) => H($"{args[i]} e. {dom}"));
        string eps = Rhs(eq), z = Kid("class", eps, "x"), least = Kid("class", eps, "ph");
        string w = Kid("wff", least, "x");

        // α is nonempty: B is in ⟦Nonempty α⟧ = if ( E. y e. A T. , 1o , (/) ), so the condition holds.
        string ne = doms[2];
        string neTok = Kid("class", Kid("class", ne, "F"), "F");
        (Proof neEq, _, _) = Unfold(ph, neTok, ["A"], (_, dom) => H($"A e. {dom}"));
        string ite = Rhs(neEq), cond = Kid("class", ite, "ph");
        Proof inIte = pr.Apply("eleqtrd", S(("ph", ph), ("A", "B"), ("B", ne), ("C", ite)), H($"B e. {ne}"), neEq);
        Proof holds = _d.Syl(_d.Syl(inIte, pr.Apply("n0i", S(("B", "B"), ("A", ite)))),
            pr.Apply("con1i", S(("ph", cond), ("ps", $"{ite} = (/)")), pr.Apply("iffalse", S(("ph", cond), ("A", Kid("class", ite, "A")), ("B", Kid("class", ite, "B"))))));
        Proof nonempty = _d.Syl(holds, pr.Apply("rexn0", S(("x", Kid("wff", cond, "x")), ("A", "A"), ("ph", Kid("wff", cond, "ph")))));

        // α is inside its universe, and so inside what W orders.
        if (lowered)
        {
            throw new Refused("quotients and choice in the lowered tower are not built yet (docs/milestone4.md)");
        }
        Proof univ = tower ? LevelUniv(ph, lev.Split(' ')[3]) : H("U e. Univ");
        Proof tr = _d.Syl(univ, pr.Apply("grutr", S(("U", lev))));
        Proof sub = pr.Apply("mpd", S(("ph", ph), ("ps", $"A e. {lev}"), ("ch", $"A C_ {lev}")), H($"A e. {lev}"),
            _d.Syl(tr, pr.Apply("trss", S(("A", lev), ("B", "A")))));
        if (tower)
        {
            sub = pr.Apply("sstrd", S(("ph", ph), ("A", "A"), ("B", lev), ("C", all)), sub, SubOmega(ph, lev));
        }

        // The least element exists and is unique, so it is in α.
        Proof eu = _d.Syl(_d.Jca(H($"W We {all}"), pr.Apply("3jca", S(("ph", ph), ("ps", $"A e. {lev}"), ("ch", $"A C_ {all}"), ("th", "A =/= (/)")), H($"A e. {lev}"), sub, nonempty)),
            pr.Apply("wereu", S(("R", "W"), ("A", all), ("B", "A"), ("V", lev), ("x", z), ("y", w))));
        Proof inA = _d.Syl(eu, pr.Apply("riotacl", S(("x", z), ("A", "A"), ("ph", least))));
        Proof r = pr.Apply("eqeltrd", S(("ph", ph), ("A", Lhs(eq)), ("B", eps), ("C", "A")), eq, inA);
        return (r.Proves, r.Proof, WithRequired(DistinctFor([tok, neTok], args), r.Proof));
    }
}
