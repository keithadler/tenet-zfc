namespace TenetZfc;

// Replaying the conclusions: normalization (Whnf, WhnfCore), definitional equality (DefEq and the equality rules that
// rest on premises), and typing (Infer).
//
// A conclusion is checked against the facts recorded before it in the same declaration: reductions, equalities and
// typings. Each of those facts is itself a step with its own verdict, so a declaration is replayed in full only when
// every one of its steps is verified.

public sealed partial class Replayer
{
    /// <summary>Facts established by the steps of one declaration so far.</summary>
    private sealed partial class DeclState
    {
        private readonly Dictionary<Expr, Expr> _parent = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Expr, List<Expr>> _members = new(ReferenceEqualityComparer.Instance);

        /// <summary>The recorded types of each term (Infer conclusions).</summary>
        public readonly Dictionary<Expr, List<Expr>> Types = new(ReferenceEqualityComparer.Instance);

        public Expr Find(Expr e)
        {
            Expr root = e;
            while (_parent.TryGetValue(root, out Expr? p) && !ReferenceEquals(p, root))
            {
                root = p;
            }
            // Path compression.
            while (_parent.TryGetValue(e, out Expr? p) && !ReferenceEquals(p, root))
            {
                _parent[e] = root;
                e = p;
            }
            return root;
        }

        /// <summary>Record that a and b are definitionally equal (a reduction counts too: a ↝ b gives a ≡ b).</summary>
        public void Union(Expr a, Expr b)
        {
            Expr ra = Find(a), rb = Find(b);
            if (ReferenceEquals(ra, rb))
            {
                return;
            }
            List<Expr> ma = Members(ra), mb = Members(rb);
            if (ma.Count < mb.Count)
            {
                (ra, rb, ma, mb) = (rb, ra, mb, ma);
            }
            _parent[rb] = ra;
            _parent.TryAdd(ra, ra);
            ma.AddRange(mb);
            _members.Remove(rb);
        }

        /// <summary>Every term recorded equal to e, e included.</summary>
        public List<Expr> Members(Expr e)
        {
            Expr r = Find(e);
            if (!_members.TryGetValue(r, out List<Expr>? m))
            {
                _members[r] = m = new List<Expr> { r };
                _parent.TryAdd(r, r);
            }
            return m;
        }

        public void AddType(Expr e, Expr t)
        {
            if (!Types.TryGetValue(e, out List<Expr>? l))
            {
                Types[e] = l = new List<Expr>();
            }
            if (!l.Contains(t))
            {
                l.Add(t);
            }
        }

        public IReadOnlyList<Expr> TypesOf(Expr e) => Types.TryGetValue(e, out List<Expr>? l) ? l : [];

        /// <summary>The types recorded for each term in checking mode (Check conclusions).</summary>
        private readonly Dictionary<Expr, List<Expr>> _checked = new(ReferenceEqualityComparer.Instance);

        public void AddChecked(Expr e, Expr t)
        {
            if (!_checked.TryGetValue(e, out List<Expr>? l))
            {
                _checked[e] = l = new List<Expr>();
            }
            if (!l.Contains(t))
            {
                l.Add(t);
            }
        }

        public IReadOnlyList<Expr> CheckedTypesOf(Expr e) => _checked.TryGetValue(e, out List<Expr>? l) ? l : [];
    }

    /// <summary>Equal by the recorded facts, or by congruence over them to a small depth.</summary>
    private bool Equal(Expr a, Expr b, DeclState st, int depth = 3)
    {
        if (ReferenceEquals(a, b) || ReferenceEquals(st.Find(a), st.Find(b)))
        {
            return true;
        }
        switch (a, b)
        {
            case (Sort x, Sort y):
                return _ops.Equivalent(x.Level, y.Level) == true;
            case (Const x, Const y):
                return ReferenceEquals(x.Name, y.Name) && x.Levels.Length == y.Levels.Length
                    && x.Levels.Zip(y.Levels).All(p => _ops.Equivalent(p.First, p.Second) == true);
        }
        if (depth == 0)
        {
            return false;
        }
        switch (a, b)
        {
            case (App, App):
                {
                    Expr fa = Ops.Spine(a, out List<Expr> xa), fb = Ops.Spine(b, out List<Expr> xb);
                    return xa.Count == xb.Count && Equal(fa, fb, st, depth - 1) && xa.Zip(xb).All(p => Equal(p.First, p.Second, st, depth - 1));
                }
            case (Binder x, Binder y):
                return x.IsPi == y.IsPi && Equal(x.Domain, y.Domain, st, depth - 1) && Equal(x.Body, y.Body, st, depth - 1);
            case (Proj x, Proj y):
                return ReferenceEquals(x.StructName, y.StructName) && x.Idx == y.Idx && Equal(x.Struct, y.Struct, st, depth - 1);
        }
        return false;
    }

    /// <summary>The direct premises of a step: the steps in its span that are not inside a nested conclusion.</summary>
    private static List<Step> DirectPremises(Step s, IReadOnlyList<Step> steps)
    {
        var r = new List<Step>();
        for (int j = s.Index - 1; j >= s.From; j = steps[j].From - 1)
        {
            r.Add(steps[j]);
        }
        r.Reverse();
        return r;
    }

    private static bool IsReduction(Step p) =>
        p.Kind is StepKind.Whnf or StepKind.WhnfCore
        || (p.Kind == StepKind.Rule && p.Rule is "Beta" or "Zeta" or "ZetaFVar" or "Delta" or "DeltaLazy" or "Proj" or "Iota"
            or "IotaK" or "QuotLift" or "QuotInd" or "NatLitOp" or "NatLitPred" or "StringLitToCtor" or "UnfoldProjApp");

    // ---- normalization ----

    /// <summary>
    /// e ↝* r: a chain from e to r through the step's direct premises, each used on the whole term or on the head of
    /// an application (normalizing the head first is how weak head normalization proceeds).
    /// </summary>
    private (Verdict, string?) Reduction(Step s, IReadOnlyList<Step> steps)
    {
        List<Step> premises = DirectPremises(s, steps).Where(IsReduction).ToList();
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance) { s.A };
        var queue = new Queue<Expr>();
        queue.Enqueue(s.A);
        while (queue.Count > 0 && seen.Count < ReachLimit)
        {
            Expr x = queue.Dequeue();
            if (ReferenceEquals(x, s.B))
            {
                return (Verdict.Verified, null);
            }
            foreach (Expr y in OneStep(x, premises))
            {
                if (seen.Add(y))
                {
                    queue.Enqueue(y);
                }
            }
        }
        return (Verdict.Failed, "no chain of its premises leads from the term to the recorded normal form");
    }

    private IEnumerable<Expr> OneStep(Expr x, List<Step> premises)
    {
        Expr head = Ops.Spine(x, out List<Expr> args);
        // Prefixes of the application: f, f a₀, f a₀ a₁, …, x itself.
        Expr prefix = head;
        for (int k = 0; ; k++)
        {
            foreach (Step p in premises)
            {
                if (ReferenceEquals(p.A, prefix))
                {
                    yield return _t.MkApp(p.B!, args.Skip(k));
                }
            }
            if (k == args.Count)
            {
                break;
            }
            prefix = _t.App(prefix, args[k]);
        }
    }

    // ---- definitional equality ----

    private (Verdict, string?) DefEqConclusion(Step s, DeclState st) =>
        Equal(s.A, s.B!, st) ? (Verdict.Verified, null) : (Verdict.Failed, "the recorded facts do not make the two sides equal");

    private (Verdict, string?) PremiseRule(Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        Expr a = s.A, b = s.B!;
        switch (s.Rule)
        {
            case "DefEqApp":
                {
                    Expr fa = Ops.Spine(a, out List<Expr> xa), fb = Ops.Spine(b, out List<Expr> xb);
                    bool ok = xa.Count > 0 && xa.Count == xb.Count && Equal(fa, fb, st, 0) && xa.Zip(xb).All(p => Equal(p.First, p.Second, st, 0));
                    return ok ? (Verdict.Verified, null) : (Verdict.Failed, "heads or arguments not recorded equal");
                }
            case "DefEqBinding":
                return Binding(s, steps, st);
            case "DefEqLazyDelta":
                return Equal(a, b, st) ? (Verdict.Verified, null) : (Verdict.Failed, "lazy delta's final terms are not recorded equal");
            case "DefEqLazyDeltaProj":
                {
                    if (a is not Proj pa || b is not Proj pb || !ReferenceEquals(pa.StructName, pb.StructName) || pa.Idx != pb.Idx)
                    {
                        return (Verdict.Failed, "not two projections of the same field");
                    }
                    // Both structures are unfolded lazily; then either the structures are equal, or both have
                    // become constructor applications and the projected fields are equal.
                    List<Expr> xs = Reachable(pa.Struct, st), ys = Reachable(pb.Struct, st);
                    foreach (Expr x in xs)
                    {
                        Expr? fx = FieldOf(x, pa.StructName, pa.Idx);
                        foreach (Expr y in ys)
                        {
                            if (Equal(x, y, st))
                            {
                                return (Verdict.Verified, null);
                            }
                            if (fx is not null && FieldOf(y, pb.StructName, pb.Idx) is Expr fy && Equal(fx, fy, st))
                            {
                                return (Verdict.Verified, null);
                            }
                        }
                    }
                    return (Verdict.Failed, "neither the projected structures nor their fields are recorded equal");
                }
            case "DefEqReflect":
                return b is Const c && ReferenceEquals(c.Name, _boolTrue) && Reachable(a, st).Any(x => x is Const k && ReferenceEquals(k.Name, _boolTrue))
                    ? (Verdict.Verified, null) : (Verdict.Failed, "the term does not reduce to Bool.true in the recorded steps");
            case "DefEqEta":
                return Eta(a, b, st) || Eta(b, a, st) ? (Verdict.Verified, null) : (Verdict.Failed, "no recorded eta expansion makes the sides equal");
            case "DefEqEtaStruct":
                return EtaStruct(a, b, st) || EtaStruct(b, a, st) ? (Verdict.Verified, null) : (Verdict.Failed, "no recorded structure eta makes the sides equal");
            case "DefEqProofIrrel":
                return ProofIrrel(a, b, st) ? (Verdict.Verified, null) : (Verdict.Failed, "not two proofs of one recorded proposition");
            case "DefEqUnitLike":
                return UnitLike(a, b, st) ? (Verdict.Verified, null) : (Verdict.Failed, "not two elements of one recorded unit-like structure");
            case "DefEqStringLit":
                return (Verdict.Unsupported, "string literals are not replayed yet");
            default:
                return (Verdict.NotYet, null);
        }
    }

    /// <summary>Field idx of a constructor application of structure s (the kernel's reduce_proj_core), or null.</summary>
    private Expr? FieldOf(Expr c, Name s, int idx) =>
        Ops.Spine(c, out List<Expr> args) is Const k && _env.Find(k.Name) is { Kind: ConstKind.Constructor } ctor
        && ReferenceEquals(ctor.Induct, s) && ctor.NumParams + idx < args.Count
            ? args[ctor.NumParams + idx] : null;

    /// <summary>
    /// Binders compared as Tenet compares them: walk both telescopes together, compare the domains (when they differ
    /// as written) and then the bodies, with each bound variable replaced by the local the step introduced for it.
    /// </summary>
    private (Verdict, string?) Binding(Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        if (s.A is not Binder t0 || s.B is not Binder s0 || t0.IsPi != s0.IsPi)
        {
            return (Verdict.Failed, "not two binders of one kind");
        }
        var locals = new Queue<Expr>(DirectPremises(s, steps).Where(p => p.Kind == StepKind.Local).Select(p => p.A));
        var subst = new List<Expr>();
        Expr tt = t0, ss = s0;
        Expr dontCare = _t.Const(_t.Of("dontcare"), []);
        do
        {
            var tb = (Binder)tt;
            var sb = (Binder)ss;
            if (!ReferenceEquals(tb.Domain, sb.Domain)
                && !Equal(_ops.InstantiateRev(tb.Domain, subst), _ops.InstantiateRev(sb.Domain, subst), st))
            {
                return (Verdict.Failed, "binder domains not recorded equal");
            }
            if (tb.Body.LooseBVarRange > 0 || sb.Body.LooseBVarRange > 0)
            {
                if (locals.Count == 0)
                {
                    return (Verdict.Failed, "a bound variable with no local introduced for it");
                }
                subst.Add(locals.Dequeue());
            }
            else
            {
                subst.Add(dontCare);
            }
            tt = tb.Body;
            ss = sb.Body;
        }
        while (tt is Binder x && ss is Binder y && x.IsPi == t0.IsPi && y.IsPi == t0.IsPi);
        return Equal(_ops.InstantiateRev(tt, subst), _ops.InstantiateRev(ss, subst), st)
            ? (Verdict.Verified, null) : (Verdict.Failed, "binder bodies not recorded equal");
    }

    /// <summary>t ≡ s by eta: t is a lambda, s is not, s has a Pi type with domain D, and t ≡ fun x : D => s x was recorded.</summary>
    private bool Eta(Expr t, Expr s, DeclState st)
    {
        if (t is not Binder { IsPi: false } || s is Binder { IsPi: false })
        {
            return false;
        }
        foreach (Expr sType in st.TypesOf(s))
        {
            foreach (Expr r in Reachable(sType, st))
            {
                if (r is Binder { IsPi: true } pi)
                {
                    Expr expanded = _t.Binding(false, pi.BinderName, pi.Info, pi.Domain, _t.App(s, _t.BVar(0)));
                    if (Equal(t, expanded, st))
                    {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /// <summary>t ≡ S.mk p̄ f̄ for a non-recursive structure S, when their types are equal and t.i ≡ fᵢ for each field.</summary>
    private bool EtaStruct(Expr t, Expr s, DeclState st)
    {
        if (Ops.Spine(s, out List<Expr> args) is not Const k || _env.Find(k.Name) is not { Kind: ConstKind.Constructor } ctor
            || args.Count > ctor.NumParams + ctor.NumFields || !IsNonRecStructure(ctor.Induct!))
        {
            return false;
        }
        bool typesEqual = st.TypesOf(t).Any(x => st.TypesOf(s).Any(y => Equal(x, y, st)));
        if (!typesEqual)
        {
            return false;
        }
        if (args.Count < ctor.NumParams + ctor.NumFields)
        {
            // Lean 4.37 (lean4#15373): a partially applied constructor is a function, so both sides are applied to
            // fresh locals for the missing fields, walking the constructor application's Pi type as written.
            foreach (Expr sType in st.TypesOf(s))
            {
                Expr ty = sType, tt = t, ss = s;
                var used = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
                while (ty is Binder { IsPi: true } pi)
                {
                    Expr? x = st.LocalOrder.LastOrDefault(v => !used.Contains(v) && ReferenceEquals(st.Locals[((FVar)v).Id].Type, pi.Domain));
                    if (x is null)
                    {
                        break;
                    }
                    used.Add(x);
                    tt = _t.App(tt, x);
                    ss = _t.App(ss, x);
                    ty = _ops.Instantiate(pi.Body, [x]);
                }
                // The types were compared once, before extending; Tenet does not infer the extended terms' types.
                Ops.Spine(ss, out List<Expr> full);
                if (ty is not Binder && full.Count == ctor.NumParams + ctor.NumFields && FieldsMatch(tt, full, ctor, st))
                {
                    return true;
                }
            }
            return false;
        }
        return FieldsMatch(t, args, ctor, st);
    }

    /// <summary>t.i ≡ the i-th field among the constructor's arguments, for every field.</summary>
    private bool FieldsMatch(Expr t, List<Expr> args, ConstInfo ctor, DeclState st)
    {
        for (int i = 0; i < ctor.NumFields; i++)
        {
            if (!Equal(_t.Proj(ctor.Induct!, i, t), args[ctor.NumParams + i], st))
            {
                return false;
            }
        }
        return true;
    }

    private bool IsNonRecStructure(Name ind) =>
        _env.Find(ind) is { Kind: ConstKind.Inductive, IsRec: false, NumIndices: 0, Ctors.Length: 1 };

    /// <summary>Two proofs of one proposition: t : T, s : U, T ≡ U, and T : Prop.</summary>
    private bool ProofIrrel(Expr t, Expr s, DeclState st)
    {
        foreach (Expr tType in st.TypesOf(t))
        {
            if (!IsProp(tType, st))
            {
                continue;
            }
            if (st.TypesOf(s).Any(u => Equal(tType, u, st)))
            {
                return true;
            }
        }
        return false;
    }

    private bool IsProp(Expr type, DeclState st) =>
        st.TypesOf(type).Any(k => Reachable(k, st).Any(x => x is Sort so && _ops.Equivalent(so.Level, _t.Zero) == true));

    /// <summary>Two elements of a non-recursive structure whose one constructor has no fields.</summary>
    private bool UnitLike(Expr t, Expr s, DeclState st)
    {
        foreach (Expr tType in st.TypesOf(t))
        {
            foreach (Expr w in Reachable(tType, st))
            {
                if (Ops.Head(w) is Const i && IsNonRecStructure(i.Name) && _env.Find(_env.Find(i.Name)!.Ctors[0]) is { NumFields: 0 }
                    && st.TypesOf(s).Any(u => Equal(w, u, st)))
                {
                    return true;
                }
            }
        }
        return false;
    }

    // ---- typing ----

    /// <summary>
    /// e : T, recomputed the way the kernel computes it from the recorded types of e's parts. Infer-only and checking
    /// inference give the same type; the trace does not say which ran, so the checks checking mode adds (an argument's
    /// type against the domain, a domain being a type) are not required here. See docs/trace-format.md.
    /// </summary>
    private (Verdict, string?) InferConclusion(Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        Expr e = s.A, T = s.B!;
        bool ok;
        switch (e)
        {
            case Sort so:
                ok = ReferenceEquals(T, _t.Sort(_t.Succ(so.Level)));
                break;
            case Const c:
                {
                    if (_env.Find(c.Name) is not ConstInfo info || info.LevelParams.Length != c.Levels.Length)
                    {
                        return (Verdict.Failed, "an undeclared constant, or wrong number of levels");
                    }
                    ok = ReferenceEquals(T, _ops.InstantiateLevels(info.Type, info.LevelParams, c.Levels));
                    break;
                }
            case FVar f:
                ok = st.Locals.TryGetValue(f.Id, out var d) && ReferenceEquals(d.Type, T);
                break;
            case TenetZfc.NatLit:
                ok = ReferenceEquals(T, _t.Const(_t.Of("Nat"), []));
                break;
            case StrLit:
                ok = ReferenceEquals(T, _t.Const(_t.Of("String"), []));
                break;
            case App:
                ok = InferAppOnly(e, T, st) || InferAppChecked((App)e, T, st);
                break;
            case Binder { IsPi: false }:
                ok = InferLambda(e, T, s, steps, st);
                break;
            case Binder { IsPi: true }:
                ok = InferPi(e, T, s, steps, st);
                break;
            case Let:
                ok = InferLet(e, T, s, steps, st);
                break;
            case Proj p:
                ok = InferProj(p, T, st);
                break;
            default:
                return (Verdict.Failed, "a term that has no type");
        }
        return ok ? (Verdict.Verified, null) : (Verdict.Failed, $"the recorded type is not what inference gives from the recorded facts");
    }

    /// <summary>
    /// e : T in checking mode: the type is computed as in <see cref="InferConclusion"/>, from checking-mode facts about
    /// e's parts, and the checks that mode adds must hold: an argument's type equals its domain, every binder domain
    /// and let type is a type, a let value has its type, and universe levels use only the declaration's parameters.
    /// </summary>
    private (Verdict, string?) CheckConclusion(Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        Expr e = s.A, T = s.B!;
        string? bad = e switch
        {
            Sort so => LevelsOk([so.Level], st) ? null : "a universe level uses a parameter the declaration does not have",
            Const c => LevelsOk(c.Levels, st) ? null : "a universe level uses a parameter the declaration does not have",
            App a => CheckedApp(a, T, st) ? null : "the argument's checked type is not recorded equal to the domain",
            Binder { IsPi: false } => CheckedTelescope(e, s, steps, st) ? null : "a domain or the body was not checked",
            Binder { IsPi: true } => CheckedTelescope(e, s, steps, st) ? null : "a domain or the body was not checked",
            Let => CheckedLets(e, s, steps, st) ? null : "a let's type, value or body was not checked",
            Proj p => st.CheckedTypesOf(p.Struct).Count > 0 ? null : "the structure was not checked",
            _ => null,
        };
        if (bad is not null)
        {
            return (Verdict.Failed, bad);
        }
        if (e is App)
        {
            return (Verdict.Verified, null);   // CheckedApp already compared the type
        }
        return InferConclusion(s, steps, st);
    }

    private static bool LevelsOk(IEnumerable<Level> levels, DeclState st) => st.LevelParams is not Name[] ps || levels.All(l => ParamsIn(l, ps));

    private static bool ParamsIn(Level l, Name[] ps) => l switch
    {
        LParam p => ps.Any(x => ReferenceEquals(x, p.Name)),
        LSucc x => ParamsIn(x.Of, ps),
        LMax m => ParamsIn(m.A, ps) && ParamsIn(m.B, ps),
        LIMax m => ParamsIn(m.A, ps) && ParamsIn(m.B, ps),
        _ => true,
    };

    /// <summary>f a : B[a] where f was checked to have a type that reduces to (x : D) → B, and a was checked to have a type equal to D.</summary>
    private bool CheckedApp(App e, Expr T, DeclState st)
    {
        foreach (Expr fType in st.CheckedTypesOf(e.Fn))
        {
            foreach (Binder pi in PiForms(fType, st))
            {
                if (ReferenceEquals(_ops.Instantiate(pi.Body, [e.Arg]), T)
                    && st.CheckedTypesOf(e.Arg).Any(a => Equal(a, pi.Domain, st)))
                {
                    return true;
                }
            }
        }
        return false;
    }

    /// <summary>A lambda or Pi telescope: every domain was checked to be a type, and the body was checked.</summary>
    private bool CheckedTelescope(Expr e, Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        bool isPi = ((Binder)e).IsPi;
        List<Expr> fvars = TelescopeLocals(s, steps);
        Expr body = e;
        int n = 0;
        while (body is Binder b && b.IsPi == isPi)
        {
            if (n >= fvars.Count)
            {
                return false;
            }
            Expr d = _ops.InstantiateRev(b.Domain, fvars.GetRange(0, n));
            if (CheckedSortOf(d, st) is null)
            {
                return false;
            }
            body = b.Body;
            n++;
        }
        Expr inst = _ops.InstantiateRev(body, fvars.GetRange(0, n));
        return isPi ? CheckedSortOf(inst, st) is not null : st.CheckedTypesOf(inst).Count > 0;
    }

    private bool CheckedLets(Expr e, Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        List<Expr> fvars = TelescopeLocals(s, steps);
        Expr body = e;
        int n = 0;
        while (body is Let l)
        {
            if (n >= fvars.Count)
            {
                return false;
            }
            Expr type = _ops.InstantiateRev(l.Type, fvars.GetRange(0, n));
            Expr val = _ops.InstantiateRev(l.Value, fvars.GetRange(0, n));
            if (CheckedSortOf(type, st) is null || !st.CheckedTypesOf(val).Any(v => Equal(v, type, st)))
            {
                return false;
            }
            body = l.Body;
            n++;
        }
        return st.CheckedTypesOf(_ops.InstantiateRev(body, fvars.GetRange(0, n))).Count > 0;
    }

    /// <summary>The universe of a type, from a checking-mode fact about it.</summary>
    private Level? CheckedSortOf(Expr e, DeclState st)
    {
        foreach (Expr t in st.CheckedTypesOf(e))
        {
            foreach (Expr x in Reachable(t, st))
            {
                if (x is Sort so)
                {
                    return so.Level;
                }
            }
        }
        return null;
    }

    /// <summary>Some Pi type the recorded steps reduce t to (t itself if it is one).</summary>
    private IEnumerable<Binder> PiForms(Expr t, DeclState st) => Reachable(t, st).OfType<Binder>().Where(b => b.IsPi);

    /// <summary>Infer-only mode: the head's type, with its Pi binders instantiated by all the arguments at once.</summary>
    private bool InferAppOnly(Expr e, Expr T, DeclState st)
    {
        Expr f = Ops.Spine(e, out List<Expr> args);
        foreach (Expr fType0 in st.TypesOf(f))
        {
            if (InstantiatePis(fType0, args, 0, 0, T, st))
            {
                return true;
            }
        }
        return false;
    }

    /// <summary>Walk the Pi telescope over args[i..]; j is the first argument not yet substituted. Branches over the recorded Pi forms.</summary>
    private bool InstantiatePis(Expr fType, List<Expr> args, int i, int j, Expr T, DeclState st, int budget = 64)
    {
        for (; i < args.Count; i++)
        {
            if (fType is Binder { IsPi: true } pi)
            {
                fType = pi.Body;
                continue;
            }
            Expr inst = _ops.InstantiateRev(fType, args.GetRange(j, i - j));
            foreach (Binder p in PiForms(inst, st).Take(budget))
            {
                if (InstantiatePis(p.Body, args, i + 1, i, T, st, budget / 2))
                {
                    return true;
                }
            }
            return false;
        }
        return ReferenceEquals(_ops.InstantiateRev(fType, args.GetRange(j, args.Count - j)), T);
    }

    /// <summary>Checking mode: the function's type reduced to a Pi, its body instantiated by the argument.</summary>
    private bool InferAppChecked(App e, Expr T, DeclState st)
    {
        foreach (Expr fType in st.TypesOf(e.Fn))
        {
            foreach (Binder pi in PiForms(fType, st))
            {
                if (ReferenceEquals(_ops.Instantiate(pi.Body, [e.Arg]), T))
                {
                    return true;
                }
            }
        }
        return false;
    }

    /// <summary>The locals a binder-telescope inference introduced, in order: its direct Local premises.</summary>
    private static List<Expr> TelescopeLocals(Step s, IReadOnlyList<Step> steps) =>
        DirectPremises(s, steps).Where(p => p.Kind == StepKind.Local).Select(p => p.A).ToList();

    private bool InferLambda(Expr e, Expr T, Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        List<Expr> fvars = TelescopeLocals(s, steps);
        Expr body = e;
        int n = 0;
        while (body is Binder { IsPi: false } lam)
        {
            if (n >= fvars.Count || !LocalHasType(fvars[n], _ops.InstantiateRev(lam.Domain, fvars.GetRange(0, n)), st))
            {
                return false;
            }
            body = lam.Body;
            n++;
        }
        fvars = fvars.GetRange(0, n);
        Expr inst = _ops.InstantiateRev(body, fvars);
        foreach (Expr r in st.TypesOf(inst))
        {
            if (ReferenceEquals(MkTelescope(fvars, _ops.CheapBetaReduce(r), st, removeDeadLet: false), T))
            {
                return true;
            }
        }
        return false;
    }

    private bool InferPi(Expr e, Expr T, Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        List<Expr> fvars = TelescopeLocals(s, steps);
        var domains = new List<Expr>();
        Expr body = e;
        int n = 0;
        while (body is Binder { IsPi: true } pi)
        {
            Expr d = _ops.InstantiateRev(pi.Domain, fvars.GetRange(0, Math.Min(n, fvars.Count)));
            if (n >= fvars.Count || !LocalHasType(fvars[n], d, st))
            {
                return false;
            }
            domains.Add(d);
            body = pi.Body;
            n++;
        }
        Expr inst = _ops.InstantiateRev(body, fvars.GetRange(0, n));
        // The universe of each domain and of the body, as the kernel's EnsureSort finds it.
        var us = new List<Level>();
        foreach (Expr d in domains)
        {
            Level? u = SortOf(d, st);
            if (u is null)
            {
                return false;
            }
            us.Add(u);
        }
        Level? r = SortOf(inst, st);
        if (r is null)
        {
            return false;
        }
        for (int i = us.Count - 1; i >= 0; i--)
        {
            r = _ops.MkIMax(us[i], r);
        }
        return ReferenceEquals(_t.Sort(r), T);
    }

    private Level? SortOf(Expr e, DeclState st)
    {
        foreach (Expr t in st.TypesOf(e))
        {
            foreach (Expr x in Reachable(t, st))
            {
                if (x is Sort so)
                {
                    return so.Level;
                }
            }
        }
        return null;
    }

    private bool InferLet(Expr e, Expr T, Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        List<Expr> fvars = TelescopeLocals(s, steps);
        Expr body = e;
        int n = 0;
        while (body is Let l)
        {
            if (n >= fvars.Count || fvars[n] is not FVar f || !st.Locals.TryGetValue(f.Id, out var decl)
                || !ReferenceEquals(decl.Type, _ops.InstantiateRev(l.Type, fvars.GetRange(0, n)))
                || !ReferenceEquals(decl.Value, _ops.InstantiateRev(l.Value, fvars.GetRange(0, n))))
            {
                return false;
            }
            body = l.Body;
            n++;
        }
        fvars = fvars.GetRange(0, n);
        foreach (Expr r in st.TypesOf(_ops.InstantiateRev(body, fvars)))
        {
            if (ReferenceEquals(MkTelescope(fvars, _ops.CheapBetaReduce(r), st, removeDeadLet: true), T))
            {
                return true;
            }
        }
        return false;
    }

    private bool LocalHasType(Expr fvar, Expr type, DeclState st) =>
        fvar is FVar f && st.Locals.TryGetValue(f.Id, out var d) && ReferenceEquals(d.Type, type) && d.Value is null;

    /// <summary>Close body under Pi binders for the locals in order; let-bound locals become lets (dropped when unused, if asked).</summary>
    private Expr MkTelescope(List<Expr> fvars, Expr body, DeclState st, bool removeDeadLet)
    {
        Expr r = _ops.Abstract(body, fvars);
        for (int i = fvars.Count - 1; i >= 0; i--)
        {
            var decl = st.Locals[((FVar)fvars[i]).Id];
            List<Expr> prefix = fvars.GetRange(0, i);
            if (decl.Value is Expr val)
            {
                if (!removeDeadLet || Ops.HasLooseBVar(r, 0))
                {
                    r = _t.Let(Name.Anonymous, _ops.Abstract(decl.Type, prefix), _ops.Abstract(val, prefix), r);
                }
                else
                {
                    r = _ops.LowerLooseBVars(r, 1, 1);
                }
            }
            else
            {
                r = _t.Binding(true, Name.Anonymous, BinderKind.Default, _ops.Abstract(decl.Type, prefix), r);
            }
        }
        return r;
    }

    /// <summary>
    /// The type of field i of a structure: the constructor's type at the structure's universe levels, its parameters
    /// instantiated from the structure's type, earlier fields instantiated as projections.
    /// </summary>
    private bool InferProj(Proj e, Expr T, DeclState st)
    {
        foreach (Expr sType in st.TypesOf(e.Struct))
        {
            foreach (Expr w in Reachable(sType, st))
            {
                if (Ops.Spine(w, out List<Expr> args) is not Const ic || !ReferenceEquals(ic.Name, e.StructName)
                    || _env.Find(ic.Name) is not { Kind: ConstKind.Inductive, Ctors.Length: 1 } ind
                    || args.Count != ind.NumParams + ind.NumIndices
                    || _env.Find(ind.Ctors[0]) is not ConstInfo ctor)
                {
                    continue;
                }
                if (ProjType(_ops.InstantiateLevels(ctor.Type, ctor.LevelParams, ic.Levels), args, ind.NumParams, e, ic.Name, T, st))
                {
                    return true;
                }
            }
        }
        return false;
    }

    private bool ProjType(Expr r, List<Expr> args, int nparams, Proj e, Name s, Expr T, DeclState st)
    {
        for (int i = 0; i < nparams; i++)
        {
            Binder? pi = PiForms(r, st).FirstOrDefault();
            if (pi is null)
            {
                return false;
            }
            r = _ops.Instantiate(pi.Body, [args[i]]);
        }
        for (int i = 0; i < e.Idx; i++)
        {
            Binder? pi = PiForms(r, st).FirstOrDefault();
            if (pi is null)
            {
                return false;
            }
            r = pi.Body.LooseBVarRange > 0 ? _ops.Instantiate(pi.Body, [_t.Proj(s, i, e.Struct)]) : pi.Body;
        }
        Binder? last = PiForms(r, st).FirstOrDefault();
        return last is not null && ReferenceEquals(last.Domain, T);
    }
}
