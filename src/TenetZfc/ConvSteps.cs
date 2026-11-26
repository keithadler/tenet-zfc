using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The conversion steps of the theorem translator beyond beta and delta (docs/milestone3.md): iota (a recursor at a
/// constructor, by the constructor's computation rule), projections (a field of a constructor's tuple, by op1st and
/// op2nd), Nat literals (as Nat.zero and Nat.succ, through set.mm's isomorphism of ω and NN0), and cumulativity (a
/// motive into one level of the tower is a motive into the whole tower, as a recursor's motive is typed).
/// </summary>
public sealed partial class Model
{
    /// <summary>Weak head normal form on the Lean side only: beta, delta, zeta, iota (Nat literals too) and projections.</summary>
    private Expr LeanWhnf(Expr e)
    {
        for (int fuel = 0; fuel < 10_000; fuel++)
        {
            e = _typing.Whnf(e);
            Expr head = Ops.Spine(e, out List<Expr> args);
            if (head is Const k && env.Find(k.Name) is { Kind: ConstKind.Recursor } rci && args.Count > rci.MajorIdx)
            {
                Expr maj = LeanWhnf(args[rci.MajorIdx]);
                if (maj is NatLit lit)
                {
                    maj = lit.Value == 0 ? t.Const(t.Of("Nat.zero"), []) : t.App(t.Const(t.Of("Nat.succ"), []), t.Nat(lit.Value - 1));
                }
                if (Ops.Spine(maj, out List<Expr> margs) is Const ck && rci.Rules.FirstOrDefault(r => ReferenceEquals(r.Ctor, ck.Name)) is RecRule rule)
                {
                    ConstInfo cci = env.Find(ck.Name)!;
                    int nrec = rci.NumParams + rci.NumMotives + rci.NumMinors;
                    var inst = args.Take(nrec).Concat(margs.Skip(cci.NumParams)).ToList();
                    Expr rhs = _ops.InstantiateLevels(rule.Rhs, rci.LevelParams, k.Levels);
                    for (int i = 0; i < inst.Count && rhs is Binder { IsPi: false } lam; i++)
                    {
                        rhs = lam.Body;
                    }
                    e = t.MkApp(_ops.InstantiateRev(rhs, inst), args.Skip(rci.MajorIdx + 1));
                    continue;
                }
            }
            if (head is Proj pj && Ops.Spine(LeanWhnf(pj.Struct), out List<Expr> sargs) is Const sk && env.Find(sk.Name) is { Kind: ConstKind.Constructor } sci)
            {
                e = t.MkApp(sargs[sci.NumParams + pj.Idx], args);
                continue;
            }
            return e;
        }
        throw new Refused("Lean-side normalization ran out of fuel");
    }

    /// <summary>Weak head normal form by the conversion steps, with ( ph -> ⟦e⟧ = ⟦e'⟧ ).</summary>
    private (Expr, Proof) WhnfFull(PCtx c, Expr e)
    {
        Proof cur = _d.Refl(c.Ph, TrIn(c, e));
        for (int i = 0; i < 2000; i++)
        {
            if (ConvStep(c, e) is not (Expr next, Proof step))
            {
                return (e, cur);
            }
            cur = _d.Trans(cur, step);
            e = next;
        }
        throw new Refused("weak head normalization ran out of fuel");
    }

    /// <summary>( ph -> ⟦head a0 … an⟧ = the same with argument i rewritten by ( ph -> ⟦ai⟧ = X ) ).</summary>
    private Proof ArgCong(PCtx c, Expr head, List<Expr> args, int i, Proof eq)
    {
        Proof cur = _d.Refl(c.Ph, TrIn(c, head));
        for (int k = 0; k < args.Count; k++)
        {
            string a = TrIn(c, args[k]);
            cur = k == i
                ? pr.Apply("fveq12d", S(("ph", c.Ph), ("F", Lhs(cur)), ("G", Rhs(cur)), ("A", a), ("B", Rhs(eq))), cur, eq)
                : pr.Apply("fveq1d", S(("ph", c.Ph), ("A", a), ("F", Lhs(cur)), ("G", Rhs(cur))), cur);
        }
        return cur;
    }

    /// <summary>A recursor at a constructor: the constructor's computation rule (lean-iota-c).</summary>
    private (Expr, Proof)? IotaStep(PCtx c, Expr e, Const head, ConstInfo rci, List<Expr> args)
    {
        int mi = rci.MajorIdx;
        (Expr maj, Proof pm) = WhnfFull(c, args[mi]);
        if (maj is NatLit lit)
        {
            (Expr ctorForm, Proof pl) = LitToCtor(c, lit.Value);
            (maj, pm) = (ctorForm, _d.Trans(pm, pl));
        }
        if (Ops.Spine(maj, out List<Expr> margs) is not Const ck || env.Find(ck.Name) is not { Kind: ConstKind.Constructor } cci)
        {
            return null;
        }
        ConstInfo ind = env.Find(cci.Induct!)!;
        int np = ind.NumParams, nrec = np + rci.NumMotives + rci.NumMinors;
        if (ind.NumIndices > 0)
        {
            throw new Refused($"iota for the indexed type {ind.Name} isn't supported yet");
        }
        Proof e1 = ArgCong(c, head, args, mi, pm);
        var fields = margs.Skip(np).ToList();
        var largs = new List<(string, Expr, Expr)>();
        List<Expr> recDoms = PiDomains(rci.Type, args.Take(nrec).ToList());
        for (int i = 0; i < nrec; i++)
        {
            largs.Add((ClassVars[i], args[i], recDoms[i]));
        }
        List<Expr> fieldDoms = PiDomains(cci.Type, margs);
        for (int k = 0; k < fields.Count; k++)
        {
            largs.Add((ClassVars[nrec + k], fields[k], fieldDoms[np + k]));
        }
        Proof iota = InstLemma(c, IotaLemma(ck.Name), largs);
        Proof e2 = AppCong(c, iota, args.Skip(mi + 1));
        Proof joined = _d.Trans(_d.Trans(e1, AlphaIn(c.Ph, Rhs(e1), Lhs(e2))), e2);
        // Lean's side: the rule's right-hand side, its binders instantiated.
        RecRule rule = rci.Rules.FirstOrDefault(r => ReferenceEquals(r.Ctor, ck.Name)) ?? throw new Refused($"no computation rule for {ck.Name}");
        Expr rhs = _ops.InstantiateLevels(rule.Rhs, rci.LevelParams, head.Levels);
        var inst = args.Take(nrec).Concat(fields).ToList();
        int strip = 0;
        while (strip < inst.Count && rhs is Binder { IsPi: false } lam)
        {
            rhs = lam.Body;
            strip++;
        }
        if (strip != inst.Count)
        {
            throw new Refused($"{ck.Name}'s computation rule has fewer binders than arguments");
        }
        Expr reduct = t.MkApp(_ops.InstantiateRev(rhs, inst), args.Skip(mi + 1));
        return (reduct, Reconcile(c, joined, reduct));
    }

    /// <summary>A projection out of a constructor's tuple: the field, by the constructor's equation and the simplifier.</summary>
    private (Expr, Proof)? ProjStep(PCtx c, Proj p, List<Expr> args)
    {
        (Expr s, Proof ps) = WhnfFull(c, p.Struct);
        if (Ops.Spine(s, out List<Expr> sargs) is not Const ck || env.Find(ck.Name) is not { Kind: ConstKind.Constructor } cci)
        {
            return null;
        }
        Define(ck.Name);
        string ctok = Token(ck.Name)!;
        List<Expr> doms = PiDomains(cci.Type, sargs);
        var texts = sargs.Select(a => TrIn(c, a)).ToList();
        (Proof eqV, _, _) = Unfold(c.Ph, ctok, texts, (i, dom) => Check(c, sargs[i], doms[i], dom));
        Proof sTuple = _d.Trans(_d.Trans(ps, AlphaIn(c.Ph, Rhs(ps), Lhs(eqV))), eqV);
        Proof cong = _d.Congruence("class", Field("( 2nd ` Z )", p.Idx), "Z", sTuple);
        Proof field = Simp(c.Ph, Rhs(cong)) is Proof sp ? _d.Trans(cong, sp) : cong;
        Proof all = AppCong(c, field, args);
        Expr reduct = t.MkApp(sargs[cci.NumParams + p.Idx], args);
        return (reduct, Reconcile(c, all, reduct));
    }

    // ---- Nat literals ---------------------------------------------------------------------------------------------

    private const string OfnumMap = "( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om )";
    private const string LitMap = "( rec ( ( x e. _V |-> <. 1o , <. (/) , <. x , (/) >. >. >. ) , <. (/) , (/) >. ) |` _om )";

    /// <summary>|- OfnumMap : _om -1-1-onto-> ( ZZ>= ` 0 ), set.mm's isomorphism (om2uzf1oi).</summary>
    private Proof OfnumIso() => pr.Apply("om2uzf1oi", S(("C", "0"), ("G", OfnumMap), ("x", "y")), pr.Apply("0z", S()), pr.Apply("eqid", S(("A", OfnumMap))));

    /// <summary>|- ( lean.Nat.-ofnum ` N ) = ( `' OfnumMap ` N ).</summary>
    private Proof OfnumIs(string n) => pr.Apply("fveq1i", S(("F", "lean.Nat.-ofnum"), ("G", $"`' {OfnumMap}"), ("A", n)), Cite("df-lean.Nat.-ofnum"));

    /// <summary>|- N e. ( ZZ>= ` 0 ) for a numeral 0 … 10.</summary>
    private Proof NumeralUz(int n)
    {
        Proof nn0 = n <= 9 ? pr.Apply($"{n}nn0", S()) : throw new Refused("Nat literals above 10 aren't supported yet");
        return pr.Apply("eleqtri", S(("A", Decimal(n)), ("B", "NN0"), ("C", "( ZZ>= ` 0 )")), nn0, pr.Apply("nn0uz", S()));
    }

    /// <summary>|- ( `' OfnumMap ` N ) e. _om.</summary>
    private Proof OfnumOm(int n)
    {
        Proof cnv = _d.Syl(pr.Apply("a1i", S(("ph", $"{OfnumMap} : _om -1-1-onto-> ( ZZ>= ` 0 )"), ("ps", "T.")), OfnumIso()), pr.Apply("f1ocnv", S(("F", OfnumMap), ("A", "_om"), ("B", "( ZZ>= ` 0 )"))));
        Proof f = _d.Syl(cnv, pr.Apply("f1of", S(("F", $"`' {OfnumMap}"), ("A", "( ZZ>= ` 0 )"), ("B", "_om"))));
        Proof fc = pr.Apply("mptru", S(("ph", $"`' {OfnumMap} : ( ZZ>= ` 0 ) --> _om")), f);
        Proof imp = pr.Apply("ffvelcdmi", S(("F", $"`' {OfnumMap}"), ("A", "( ZZ>= ` 0 )"), ("B", "_om"), ("C", Decimal(n))), fc);
        return pr.Apply("ax-mp", S(("ph", $"{Decimal(n)} e. ( ZZ>= ` 0 )"), ("ps", $"( `' {OfnumMap} ` {Decimal(n)} ) e. _om")), NumeralUz(n), imp);
    }

    /// <summary>|- ( `' OfnumMap ` N ) = O, with O = (/) for 0 and suc ( `' OfnumMap ` N-1 ) after.</summary>
    private (Proof, string) OfnumValue(int n)
    {
        Proof iso = OfnumIso();
        string g = OfnumMap;
        if (n == 0)
        {
            Proof g0 = pr.Apply("om2uz0i", S(("C", "0"), ("G", g), ("x", "y")), pr.Apply("0z", S()), pr.Apply("eqid", S(("A", g))));
            Proof imp = pr.Apply("f1ocnvfv", S(("F", g), ("A", "_om"), ("B", "( ZZ>= ` 0 )"), ("C", "(/)"), ("D", "0")));
            Proof both = pr.Apply("pm3.2i", S(("ph", $"{g} : _om -1-1-onto-> ( ZZ>= ` 0 )"), ("ps", "(/) e. _om")), iso, pr.Apply("peano1", S()));
            return (pr.Apply("ax-mp", S(("ph", $"( {g} ` (/) ) = 0"), ("ps", $"( `' {g} ` 0 ) = (/)")), g0, pr.Apply("ax-mp", S(("ph", $"( {g} : _om -1-1-onto-> ( ZZ>= ` 0 ) /\\ (/) e. _om )"), ("ps", $"( ( {g} ` (/) ) = 0 -> ( `' {g} ` 0 ) = (/) )")), both, imp)), "(/)");
        }
        string prev = Decimal(n - 1), cur = Decimal(n);
        string o = $"( `' {g} ` {prev} )";
        Proof oOm = OfnumOm(n - 1);
        // ( G ` suc o ) = ( ( G ` o ) + 1 ) = ( prev + 1 ) = cur.
        Proof sucEq = pr.Apply("ax-mp", S(("ph", $"{o} e. _om"), ("ps", $"( {g} ` suc {o} ) = ( ( {g} ` {o} ) + 1 )")), oOm,
            pr.Apply("om2uzsuci", S(("C", "0"), ("G", g), ("x", "y"), ("A", o)), pr.Apply("0z", S()), pr.Apply("eqid", S(("A", g)))));
        Proof back = pr.Apply("ax-mp", S(("ph", $"( {g} : _om -1-1-onto-> ( ZZ>= ` 0 ) /\\ {prev} e. ( ZZ>= ` 0 ) )"), ("ps", $"( {g} ` {o} ) = {prev}")),
            pr.Apply("pm3.2i", S(("ph", $"{g} : _om -1-1-onto-> ( ZZ>= ` 0 )"), ("ps", $"{prev} e. ( ZZ>= ` 0 )")), iso, NumeralUz(n - 1)),
            pr.Apply("f1ocnvfv2", S(("F", g), ("A", "_om"), ("B", "( ZZ>= ` 0 )"), ("C", prev))));
        Proof plus = pr.Apply("oveq1i", S(("A", $"( {g} ` {o} )"), ("B", prev), ("C", "1"), ("F", "+")), back);
        Proof step = pr.Apply($"{n - 1}p1e{(n == 10 ? "10" : n.ToString())}", S());
        Proof gsuc = pr.Apply("eqtri", S(("A", $"( {g} ` suc {o} )"), ("B", $"( ( {g} ` {o} ) + 1 )"), ("C", cur)), sucEq,
            pr.Apply("eqtri", S(("A", $"( ( {g} ` {o} ) + 1 )"), ("B", $"( {prev} + 1 )"), ("C", cur)), plus, step));
        Proof sucOm = pr.Apply("ax-mp", S(("ph", $"{o} e. _om"), ("ps", $"suc {o} e. _om")), oOm, pr.Apply("peano2", S(("A", o))));
        Proof both2 = pr.Apply("pm3.2i", S(("ph", $"{g} : _om -1-1-onto-> ( ZZ>= ` 0 )"), ("ps", $"suc {o} e. _om")), iso, sucOm);
        Proof imp2 = pr.Apply("f1ocnvfv", S(("F", g), ("A", "_om"), ("B", "( ZZ>= ` 0 )"), ("C", $"suc {o}"), ("D", cur)));
        Proof r = pr.Apply("ax-mp", S(("ph", $"( {g} ` suc {o} ) = {cur}"), ("ps", $"( `' {g} ` {cur} ) = suc {o}")), gsuc,
            pr.Apply("ax-mp", S(("ph", $"( {g} : _om -1-1-onto-> ( ZZ>= ` 0 ) /\\ suc {o} e. _om )"), ("ps", $"( ( {g} ` suc {o} ) = {cur} -> ( `' {g} ` {cur} ) = suc {o} )")), both2, imp2));
        return (r, $"suc {o}");
    }

    /// <summary>( ph -> ⟦n⟧ = ⟦Nat.zero⟧ ) or ( ph -> ⟦n⟧ = ⟦Nat.succ (n-1)⟧ ).</summary>
    private (Expr, Proof) LitToCtor(PCtx c, System.Numerics.BigInteger value)
    {
        int n = value <= 10 ? (int)value : throw new Refused("Nat literals above 10 aren't supported yet");
        Name zero = t.Of("Nat.zero"), succ = t.Of("Nat.succ");
        Define(zero);
        string lit = TrIn(c, t.Nat(value));
        // ⟦n⟧ = ( LitMap ` ( `' OfnumMap ` N ) )
        Proof l1 = pr.Apply("fveq1i", S(("F", "lean.Nat.-lit"), ("G", LitMap), ("A", $"( lean.Nat.-ofnum ` {Decimal(n)} )")), Cite("df-lean.Nat.-lit"));
        Proof l2 = pr.Apply("fveq2i", S(("F", LitMap), ("A", $"( lean.Nat.-ofnum ` {Decimal(n)} )"), ("B", $"( `' {OfnumMap} ` {Decimal(n)} )")), OfnumIs(Decimal(n)));
        (Proof ov, string o) = OfnumValue(n);
        Proof l3 = pr.Apply("fveq2i", S(("F", LitMap), ("A", $"( `' {OfnumMap} ` {Decimal(n)} )"), ("B", o)), ov);
        Proof toMap = pr.Apply("eqtri", S(("A", lit), ("B", $"( {LitMap} ` ( lean.Nat.-ofnum ` {Decimal(n)} ) )"), ("C", $"( {LitMap} ` {o} )")), l1,
            pr.Apply("eqtri", S(("A", $"( {LitMap} ` ( lean.Nat.-ofnum ` {Decimal(n)} ) )"), ("B", $"( {LitMap} ` ( `' {OfnumMap} ` {Decimal(n)} ) )"), ("C", $"( {LitMap} ` {o} )")), l2, l3));
        Proof lifted = _d.Lift(c.Ph, toMap);
        if (n == 0)
        {
            Proof z = pr.Apply("fr0g", S(("A", "<. (/) , (/) >."), ("B", "_V"), ("F", "( x e. _V |-> <. 1o , <. (/) , <. x , (/) >. >. >. )")));
            Proof zc = pr.Apply("ax-mp", S(("ph", "<. (/) , (/) >. e. _V"), ("ps", $"( {LitMap} ` (/) ) = <. (/) , (/) >.")), pr.Apply("opex", S(("A", "(/)"), ("B", "(/)"))), z);
            Proof toZero = _d.Trans(_d.Trans(lifted, _d.Lift(c.Ph, zc)), _d.Symm(DeltaEq(c.Ph, Token(zero)!)));
            return (t.Const(zero, []), toZero);
        }
        // ( LitMap ` suc o' ) = ( F ` ( LitMap ` o' ) ) = <. 1o , <. (/) , <. ( LitMap ` o' ) , (/) >. >. >.
        string o1 = o[4..];   // o = suc o'
        Proof frs = pr.Apply("ax-mp", S(("ph", $"{o1} e. _om"), ("ps", $"( {LitMap} ` suc {o1} ) = ( ( x e. _V |-> <. 1o , <. (/) , <. x , (/) >. >. >. ) ` ( {LitMap} ` {o1} ) )")),
            OfnumOm(n - 1), pr.Apply("frsuc", S(("A", "<. (/) , (/) >."), ("B", o1), ("F", "( x e. _V |-> <. 1o , <. (/) , <. x , (/) >. >. >. )"))));
        string inner = $"( {LitMap} ` {o1} )";
        string fmap = "( x e. _V |-> <. 1o , <. (/) , <. x , (/) >. >. >. )";
        Proof beta = Beta(c.Ph, pr.Apply("eqid", S(("A", fmap))), "x", "_V", "<. 1o , <. (/) , <. x , (/) >. >. >.", inner, Exists(c.Ph, inner), fmap);
        // ( LitMap ` o' ) is ⟦n-1⟧, back the same way.
        Expr prevLit = t.Nat(value - 1);
        string prevText = TrIn(c, prevLit);
        (Proof pv, _) = OfnumValue(n - 1);
        Proof q1 = pr.Apply("fveq1i", S(("F", "lean.Nat.-lit"), ("G", LitMap), ("A", $"( lean.Nat.-ofnum ` {Decimal(n - 1)} )")), Cite("df-lean.Nat.-lit"));
        Proof q2 = pr.Apply("fveq2i", S(("F", LitMap), ("A", $"( lean.Nat.-ofnum ` {Decimal(n - 1)} )"), ("B", o1)), pr.Apply("eqtri", S(("A", $"( lean.Nat.-ofnum ` {Decimal(n - 1)} )"), ("B", $"( `' {OfnumMap} ` {Decimal(n - 1)} )"), ("C", o1)), OfnumIs(Decimal(n - 1)), pv));
        Proof prevIs = pr.Apply("eqtri", S(("A", prevText), ("B", $"( {LitMap} ` ( lean.Nat.-ofnum ` {Decimal(n - 1)} ) )"), ("C", inner)), q1, q2);
        Proof tagIn = pr.Apply("eqtri", S(("A", $"( {LitMap} ` suc {o1} )"), ("B", $"( {fmap} ` {inner} )"), ("C", Rhs(beta))), frs, pr.Apply("mptru", S(("ph", $"( {fmap} ` {inner} ) = {Rhs(beta)}")), BetaT(fmap, inner)));
        Proof toTag = _d.Trans(lifted, _d.Lift(c.Ph, tagIn));
        // The tag over ( LitMap ` o' ) is the tag over ⟦n-1⟧, which is ⟦Nat.succ (n-1)⟧.
        Proof tagEq = _d.Congruence("class", "<. 1o , <. (/) , <. Z , (/) >. >. >.", "Z", _d.Lift(c.Ph, pr.Apply("eqcomi", S(("A", prevText), ("B", inner)), prevIs)));
        Expr ctorForm = t.App(t.Const(succ, []), prevLit);
        Define(succ);
        (Proof eqSucc, _, _) = Unfold(c.Ph, Token(succ)!, [prevText], (_, dom) => Check(c, prevLit, t.Const(t.Of("Nat"), []), dom));
        Proof r = _d.Trans(_d.Trans(toTag, tagEq), _d.Symm(eqSucc));
        return (ctorForm, r);
    }

    /// <summary>( T. -> ( F ` A ) = B[x := A] ) for F = ( x e. _V |-> B ).</summary>
    private Proof BetaT(string f, string a)
    {
        SyntaxTree m = pr.Parse("class", f.Split(' '))!;
        string x = pr.Render(m.Children[0]), body = pr.Render(m.Children[2]);
        return Beta("T.", pr.Apply("eqid", S(("A", f))), x, "_V", body, a, Exists("T.", a), f);
    }

    /// <summary>A Nat literal is in Nat: as Nat.zero or Nat.succ of the literal before it.</summary>
    private Typed LitMemImpl(PCtx c, NatLit lit)
    {
        Expr nat = t.Const(t.Of("Nat"), []);
        (Expr ctor, Proof eq) = LitToCtor(c, lit.Value);
        Typed m = MemOf(c, ctor);
        string natText = TrIn(c, nat);
        Proof inNat = m.Ty == natText ? m.P : throw new Refused($"a literal's constructor form is in {m.Ty}");
        Proof r = pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", TrIn(c, lit)), ("B", TrIn(c, ctor)), ("C", natText)), eq, inNat);
        return new Typed(r, natText, nat);
    }

    // ---- cumulativity -----------------------------------------------------------------------------------------

    /// <summary>( ph -> G C_ U. ran U ) for G a level of the tower, or 2o.</summary>
    private Proof SubOmega(string ph, string g)
    {
        if (g == "2o")
        {
            // 2o e. ( U ` (/) ), so 2o C_ ( U ` (/) ) C_ U. ran U.
            var c0 = new PCtx { Ph = ph };
            Proof two = UnivMem(c0, "2o", "( U ` (/) )");
            Proof ss = _d.Syl(LevelUniv(ph, "(/)"), pr.Apply("grutr", S(("U", "( U ` (/) )"))));
            Proof twoSs = pr.Apply("mpd", S(("ph", ph), ("ps", "2o e. ( U ` (/) )"), ("ch", "2o C_ ( U ` (/) )")), two, _d.Syl(ss, pr.Apply("trss", S(("A", "( U ` (/) )"), ("B", "2o")))));
            return pr.Apply("sstrd", S(("ph", ph), ("A", "2o"), ("B", "( U ` (/) )"), ("C", "U. ran U")), twoSs, SubOmega(ph, "( U ` (/) )"));
        }
        SyntaxTree n = pr.Parse("class", g.Split(' '))!;
        string k = n.Rule.Label == "cfv" && pr.Render(n.Children[1]) == "U" ? pr.Render(n.Children[0]) : throw new Refused($"not a level of the tower: {g}");
        EnsureTowerLemmas();
        Proof tw = _d.Syl(Hyp(ph, UHyp)!.Value, ApplyId("lean-tw", S(("U", "U"))));
        Proof fn = _d.Syl(pr.Apply("simpld", S(("ph", ph), ("ps", "U : _om --> Univ"), ("ch", "_om e. ( U ` (/) )")),
            pr.Apply("simpld", S(("ph", ph), ("ps", "( U : _om --> Univ /\\ _om e. ( U ` (/) ) )"), ("ch", "A. n e. _om ( U ` n ) e. ( U ` suc n )")), tw)),
            pr.Apply("ffn", S(("F", "U"), ("A", "_om"), ("B", "Univ"))));
        Proof inRan = _d.Syl(_d.Jca(fn, OrdOm(ph, k)), pr.Apply("fnfvelrn", S(("F", "U"), ("A", "_om"), ("B", k))));
        return _d.Syl(inRan, pr.Apply("elssuni", S(("A", g), ("B", "ran U"))));
    }

    /// <summary>From ( ph -> X e. ( G ^m D ) ): ( ph -> X e. ( U. ran U ^m D ) ) (mapss).</summary>
    private Proof Cumulate(string ph, string x, string ty, string target, Proof inTy)
    {
        SyntaxTree n = pr.Parse("class", ty.Split(' '))!;
        SyntaxTree m = pr.Parse("class", target.Split(' '))!;
        if (n.Rule.Label != "co" || m.Rule.Label != "co" || pr.Render(n.Children[2]) != "^m" || pr.Render(m.Children[2]) != "^m"
            || pr.Render(n.Children[1]) != pr.Render(m.Children[1]) || pr.Render(m.Children[0]) != "U. ran U")
        {
            throw new Refused($"no cumulativity from {ty} to {target}");
        }
        string g = pr.Render(n.Children[0]), d = pr.Render(n.Children[1]);
        Proof ss = _d.Syl(_d.Jca(Exists(ph, "U. ran U"), SubOmega(ph, g)), pr.Apply("mapss", S(("A", g), ("B", "U. ran U"), ("C", d), ("V", "_V"))));
        Proof imp = pr.Apply("sseld", S(("ph", ph), ("A", ty), ("B", target), ("C", x)), ss);
        return pr.Apply("mpd", S(("ph", ph), ("ps", $"{x} e. {ty}"), ("ch", $"{x} e. {target}")), inTy, imp);
    }
}
