namespace TenetZfc;

/// <summary>
/// Type inference for the model: enough of Lean's typing to tell a proof from data, so that every proof translates to
/// (/) (proof irrelevance, docs/milestone3.md). It infers structurally and normalizes types by beta, delta (unfolding
/// definitions) and zeta reduction.
///
/// It is not trusted. A wrong answer changes what a translated definition says, and its equations then fail to verify;
/// it can't make a verifier accept a false theorem. Whether a definition means what the Lean one means is checked,
/// for the constants a headline statement uses, by bridge theorems such as ⟦Nat.add⟧ = +.
/// </summary>
public sealed class Typing(Terms t, Environment env)
{
    private readonly Ops _ops = new(t);
    private ulong _fresh = 1UL << 57;

    /// <summary>Why inference failed.</summary>
    public sealed class Stuck(string why) : Exception(why);

    /// <summary>When it returns a time in the past, inference throws <see cref="TimeoutException"/> (define-all's budget).</summary>
    public Func<DateTime?>? Deadline { get; init; }

    private void CheckDeadline()
    {
        if (Deadline?.Invoke() is DateTime d && DateTime.UtcNow > d)
        {
            throw new TimeoutException("over its time budget, in type inference");
        }
    }

    /// <summary>
    /// Whether e is a proof: its type's type is Prop. Null when that can't be decided, for example when the type's
    /// sort is a universe parameter that could be zero.
    /// </summary>
    public bool? IsProof(Expr e, IReadOnlyDictionary<ulong, Expr> ctx)
    {
        try
        {
            Expr ty = Infer(e, ctx);
            return Whnf(Infer(ty, ctx)) is Sort s ? Zero(s.Level) : null;
        }
        catch (Stuck)
        {
            return null;
        }
    }

    /// <summary>Whether the type T is a proposition: T : Prop.</summary>
    public bool? IsProposition(Expr ty, IReadOnlyDictionary<ulong, Expr> ctx)
    {
        try
        {
            return Whnf(Infer(ty, ctx)) is Sort s ? Zero(s.Level) : null;
        }
        catch (Stuck)
        {
            return null;
        }
    }

    /// <summary>Definitely zero, definitely not, or unknown (a parameter).</summary>
    private static bool? Zero(Level l) => l switch
    {
        LZero => true,
        LSucc => false,
        LMax m => Zero(m.A) is bool a && Zero(m.B) is bool b ? a && b : (Zero(m.A) == false || Zero(m.B) == false ? false : null),
        LIMax im => Zero(im.B),
        _ => null,
    };

    public Expr Infer(Expr e, IReadOnlyDictionary<ulong, Expr> ctx)
    {
        CheckDeadline();
        switch (e)
        {
            case FVar f:
                return ctx.TryGetValue(f.Id, out Expr? ty) ? ty : throw new Stuck("a free variable of unknown type");
            case Sort s:
                return t.Sort(t.Succ(s.Level));
            case Const c:
                {
                    ConstInfo ci = env.Find(c.Name) ?? throw new Stuck($"{c.Name} is not in the export");
                    return _ops.InstantiateLevels(ci.Type, ci.LevelParams, c.Levels);
                }
            case App:
                {
                    Expr head = Ops.Spine(e, out List<Expr> args);
                    Expr ft = Infer(head, ctx);
                    int i = 0;
                    var pending = new List<Expr>();
                    while (i < args.Count)
                    {
                        if (ft is Binder { IsPi: true } pi)
                        {
                            pending.Add(args[i++]);
                            ft = pi.Body;
                            continue;
                        }
                        ft = Whnf(_ops.InstantiateRev(ft, pending));
                        pending.Clear();
                        if (ft is not Binder { IsPi: true })
                        {
                            throw new Stuck("applying something that isn't a function");
                        }
                    }
                    return _ops.InstantiateRev(ft, pending);
                }
            case Binder { IsPi: false } lam:
                {
                    Expr fv = t.FVar(_fresh++);
                    var inner = new Dictionary<ulong, Expr>(ctx) { [((FVar)fv).Id] = lam.Domain };
                    Expr bodyTy = Infer(_ops.Instantiate(lam.Body, [fv]), inner);
                    return t.Binding(true, lam.BinderName, lam.Info, lam.Domain, _ops.Abstract(bodyTy, [fv]));
                }
            case Binder pi:
                {
                    Level a = SortOf(pi.Domain, ctx);
                    Expr fv = t.FVar(_fresh++);
                    var inner = new Dictionary<ulong, Expr>(ctx) { [((FVar)fv).Id] = pi.Domain };
                    Level b = SortOf(_ops.Instantiate(pi.Body, [fv]), inner);
                    return t.Sort(t.IMax(a, b));
                }
            case Let l:
                return Infer(_ops.Instantiate(l.Body, [l.Value]), ctx);
            case NatLit:
                return t.Const(t.Of("Nat"), []);
            case StrLit:
                return t.Const(t.Of("String"), []);
            case Proj p:
                return InferProj(p, ctx);
        }
        throw new Stuck($"can't infer the type of {e.GetType().Name}");
    }

    private Level SortOf(Expr ty, IReadOnlyDictionary<ulong, Expr> ctx) =>
        Whnf(Infer(ty, ctx)) is Sort s ? s.Level : throw new Stuck("a type whose type isn't a sort");

    /// <summary>A stronger reduction (with iota) to fall back on when a projection's structure type doesn't show.</summary>
    public Func<Expr, Expr>? Reduce { get; set; }

    private Expr InferProj(Proj p, IReadOnlyDictionary<ulong, Expr> ctx)
    {
        Expr st = Whnf(Infer(p.Struct, ctx));
        if (Reduce is not null && (Ops.Spine(st, out _) is not Const sc || env.Find(sc.Name) is not { Kind: ConstKind.Inductive }))
        {
            st = Reduce(st);
        }
        if (Ops.Spine(st, out List<Expr> args) is not Const ic || env.Find(ic.Name) is not { Kind: ConstKind.Inductive, Ctors.Length: 1 } ind)
        {
            throw new Stuck("a projection out of something that isn't a structure");
        }
        ConstInfo ctor = env.Find(ind.Ctors[0])!;
        Expr ct = _ops.InstantiateLevels(ctor.Type, ctor.LevelParams, ic.Levels);
        for (int i = 0; i < ind.NumParams; i++)
        {
            ct = Whnf(ct) is Binder { IsPi: true } b ? _ops.Instantiate(b.Body, [args[i]]) : throw new Stuck("a structure's constructor has too few parameters");
        }
        for (int i = 0; i < p.Idx; i++)
        {
            ct = Whnf(ct) is Binder { IsPi: true } b ? _ops.Instantiate(b.Body, [t.Proj(p.StructName, i, p.Struct)]) : throw new Stuck("too few fields");
        }
        return Whnf(ct) is Binder { IsPi: true } f ? f.Domain : throw new Stuck("too few fields");
    }

    /// <summary>Weak head normal form by beta, delta (definitions only) and zeta. Enough to expose a Π or a sort.</summary>
    public Expr Whnf(Expr e)
    {
        for (int fuel = 0; fuel < 10_000; fuel++)
        {
            CheckDeadline();
            Expr head = Ops.Spine(e, out List<Expr> args);
            switch (head)
            {
                case Binder { IsPi: false } when args.Count > 0:
                    {
                        // Beta: as many arguments as there are lambdas.
                        Expr body = head;
                        int k = 0;
                        while (body is Binder { IsPi: false } lam && k < args.Count)
                        {
                            body = lam.Body;
                            k++;
                        }
                        Expr r = _ops.InstantiateRev(body, args.Take(k).ToList());
                        e = t.MkApp(r, args.Skip(k));
                        continue;
                    }
                case Let l:
                    e = t.MkApp(_ops.Instantiate(l.Body, [l.Value]), args);
                    continue;
                case Const c when env.Find(c.Name) is { Kind: ConstKind.Definition, Value: Expr v } ci:
                    e = t.MkApp(_ops.InstantiateLevels(v, ci.LevelParams, c.Levels), args);
                    continue;
            }
            return e;
        }
        throw new Stuck("normalization ran out of fuel");
    }
}
