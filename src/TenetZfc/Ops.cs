namespace TenetZfc;

/// <summary>Substitution, application spines and universe-level equivalence, over one <see cref="Terms"/> table.</summary>
public sealed class Ops(Terms t)
{
    private readonly Terms _t = t;

    // ---- application spines ----

    public static Expr Head(Expr e)
    {
        while (e is App a)
        {
            e = a.Fn;
        }
        return e;
    }

    /// <summary>The head and the arguments in order: f a₀ a₁ … aₙ₋₁.</summary>
    public static Expr Spine(Expr e, out List<Expr> args)
    {
        args = new List<Expr>();
        while (e is App a)
        {
            args.Add(a.Arg);
            e = a.Fn;
        }
        args.Reverse();
        return e;
    }

    // ---- bound variables ----

    /// <summary>
    /// Replace loose bound variable i by subst[i], for i below subst.Length, and lower the indices of the rest by
    /// subst.Length. This is Lean's instantiate: under a spine of n lambdas, bound variable 0 is the last argument.
    /// </summary>
    public Expr Instantiate(Expr e, IReadOnlyList<Expr> subst)
    {
        if (e.LooseBVarRange == 0 || subst.Count == 0)
        {
            return e;
        }
        var memo = new Dictionary<(Expr, int), Expr>();
        return Inst(e, 0, subst, memo);
    }

    private Expr Inst(Expr e, int depth, IReadOnlyList<Expr> s, Dictionary<(Expr, int), Expr> memo)
    {
        if (e.LooseBVarRange <= depth)
        {
            return e;
        }
        if (memo.TryGetValue((e, depth), out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            BVar b => b.Idx - depth < s.Count ? Lift(s[b.Idx - depth], depth) : _t.BVar(b.Idx - s.Count),
            App a => _t.App(Inst(a.Fn, depth, s, memo), Inst(a.Arg, depth, s, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Inst(b.Domain, depth, s, memo), Inst(b.Body, depth + 1, s, memo)),
            Let l => _t.Let(l.BinderName, Inst(l.Type, depth, s, memo), Inst(l.Value, depth, s, memo), Inst(l.Body, depth + 1, s, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, Inst(p.Struct, depth, s, memo)),
            _ => e,
        };
        memo[(e, depth)] = r;
        return r;
    }

    /// <summary>Lean's instantiate_rev: bound variable i becomes subst[n - 1 - i], so subst is in binder order.</summary>
    public Expr InstantiateRev(Expr e, IReadOnlyList<Expr> subst)
    {
        var rev = new List<Expr>(subst.Count);
        for (int i = subst.Count - 1; i >= 0; i--)
        {
            rev.Add(subst[i]);
        }
        return Instantiate(e, rev);
    }

    /// <summary>Replace free variable fvars[i] by the bound variable that a binder telescope over fvars gives it.</summary>
    public Expr Abstract(Expr e, IReadOnlyList<Expr> fvars)
    {
        if (!e.HasFVar || fvars.Count == 0)
        {
            return e;
        }
        var index = new Dictionary<Expr, int>(ReferenceEqualityComparer.Instance);
        for (int i = 0; i < fvars.Count; i++)
        {
            index[fvars[i]] = i;
        }
        var memo = new Dictionary<(Expr, int), Expr>();
        return Abs(e, 0, index, fvars.Count, memo);
    }

    private Expr Abs(Expr e, int depth, Dictionary<Expr, int> index, int n, Dictionary<(Expr, int), Expr> memo)
    {
        if (!e.HasFVar)
        {
            return e;
        }
        if (memo.TryGetValue((e, depth), out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            FVar => index.TryGetValue(e, out int i) ? _t.BVar(depth + n - 1 - i) : e,
            App a => _t.App(Abs(a.Fn, depth, index, n, memo), Abs(a.Arg, depth, index, n, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Abs(b.Domain, depth, index, n, memo), Abs(b.Body, depth + 1, index, n, memo)),
            Let l => _t.Let(l.BinderName, Abs(l.Type, depth, index, n, memo), Abs(l.Value, depth, index, n, memo), Abs(l.Body, depth + 1, index, n, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, Abs(p.Struct, depth, index, n, memo)),
            _ => e,
        };
        memo[(e, depth)] = r;
        return r;
    }

    /// <summary>Whether bound variable <paramref name="idx"/> occurs loose.</summary>
    public static bool HasLooseBVar(Expr e, int idx)
    {
        if (e.LooseBVarRange <= idx)
        {
            return false;
        }
        return e switch
        {
            BVar b => b.Idx == idx,
            App a => HasLooseBVar(a.Fn, idx) || HasLooseBVar(a.Arg, idx),
            Binder b => HasLooseBVar(b.Domain, idx) || HasLooseBVar(b.Body, idx + 1),
            Let l => HasLooseBVar(l.Type, idx) || HasLooseBVar(l.Value, idx) || HasLooseBVar(l.Body, idx + 1),
            Proj p => HasLooseBVar(p.Struct, idx),
            _ => false,
        };
    }

    /// <summary>Lower every loose bound variable at or above <paramref name="start"/> by <paramref name="by"/>.</summary>
    public Expr LowerLooseBVars(Expr e, int start, int by) => Lower(e, start, by, new Dictionary<(Expr, int), Expr>());

    private Expr Lower(Expr e, int start, int by, Dictionary<(Expr, int), Expr> memo)
    {
        if (e.LooseBVarRange <= start)
        {
            return e;
        }
        if (memo.TryGetValue((e, start), out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            BVar b => b.Idx >= start ? _t.BVar(b.Idx - by) : e,
            App a => _t.App(Lower(a.Fn, start, by, memo), Lower(a.Arg, start, by, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Lower(b.Domain, start, by, memo), Lower(b.Body, start + 1, by, memo)),
            Let l => _t.Let(l.BinderName, Lower(l.Type, start, by, memo), Lower(l.Value, start, by, memo), Lower(l.Body, start + 1, by, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, Lower(p.Struct, start, by, memo)),
            _ => e,
        };
        memo[(e, start)] = r;
        return r;
    }

    /// <summary>Lean's cheap_beta_reduce: beta only when the result is immediate.</summary>
    public Expr CheapBetaReduce(Expr e)
    {
        if (e is not App)
        {
            return e;
        }
        Expr fn = Spine(e, out List<Expr> args);
        if (fn is not Binder { IsPi: false })
        {
            return e;
        }
        int i = 0;
        while (fn is Binder { IsPi: false } l && i < args.Count)
        {
            i++;
            fn = l.Body;
        }
        if (fn.LooseBVarRange == 0)
        {
            return _t.MkApp(fn, args.Skip(i));
        }
        if (fn is BVar b)
        {
            return _t.MkApp(args[i - b.Idx - 1], args.Skip(i));
        }
        return e;
    }

    /// <summary>Raise every loose bound variable of <paramref name="e"/> by <paramref name="by"/>.</summary>
    public Expr Lift(Expr e, int by) => by == 0 || e.LooseBVarRange == 0 ? e : LiftAt(e, 0, by, new Dictionary<(Expr, int), Expr>());

    private Expr LiftAt(Expr e, int depth, int by, Dictionary<(Expr, int), Expr> memo)
    {
        if (e.LooseBVarRange <= depth)
        {
            return e;
        }
        if (memo.TryGetValue((e, depth), out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            BVar b => _t.BVar(b.Idx + by),
            App a => _t.App(LiftAt(a.Fn, depth, by, memo), LiftAt(a.Arg, depth, by, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, LiftAt(b.Domain, depth, by, memo), LiftAt(b.Body, depth + 1, by, memo)),
            Let l => _t.Let(l.BinderName, LiftAt(l.Type, depth, by, memo), LiftAt(l.Value, depth, by, memo), LiftAt(l.Body, depth + 1, by, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, LiftAt(p.Struct, depth, by, memo)),
            _ => e,
        };
        memo[(e, depth)] = r;
        return r;
    }

    // ---- universe parameters ----

    public Expr InstantiateLevels(Expr e, Name[] ps, Level[] us)
    {
        if (ps.Length == 0)
        {
            return e;
        }
        var map = new Dictionary<Name, Level>(ReferenceEqualityComparer.Instance);
        for (int i = 0; i < ps.Length; i++)
        {
            map[ps[i]] = us[i];
        }
        var memo = new Dictionary<Expr, Expr>(ReferenceEqualityComparer.Instance);
        return InstL(e, map, memo);
    }

    private Expr InstL(Expr e, Dictionary<Name, Level> map, Dictionary<Expr, Expr> memo)
    {
        if (memo.TryGetValue(e, out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            Sort s => _t.Sort(Subst(s.Level, map)),
            Const c => c.Levels.Length == 0 ? c : _t.Const(c.Name, c.Levels.Select(l => Subst(l, map)).ToArray()),
            App a => _t.App(InstL(a.Fn, map, memo), InstL(a.Arg, map, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, InstL(b.Domain, map, memo), InstL(b.Body, map, memo)),
            Let l => _t.Let(l.BinderName, InstL(l.Type, map, memo), InstL(l.Value, map, memo), InstL(l.Body, map, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, InstL(p.Struct, map, memo)),
            _ => e,
        };
        memo[e] = r;
        return r;
    }

    /// <summary>
    /// Substitute universe parameters, simplifying each max and imax that changed the way Lean's kernel does
    /// (level::instantiate builds them with mk_max and mk_imax). A max or imax whose sides did not change is kept
    /// as written. The simplification is part of delta and iota: the kernel's reduct carries the simplified level.
    /// </summary>
    public Level Subst(Level l, IReadOnlyDictionary<Name, Level> map)
    {
        if (!l.HasParam)
        {
            return l;
        }
        switch (l)
        {
            case LParam p:
                return map.TryGetValue(p.Name, out Level? v) ? v : l;
            case LSucc s:
                return _t.Succ(Subst(s.Of, map));
            case LMax m:
                {
                    Level a = Subst(m.A, map), b = Subst(m.B, map);
                    return ReferenceEquals(a, m.A) && ReferenceEquals(b, m.B) ? l : MkMax(a, b);
                }
            case LIMax m:
                {
                    Level a = Subst(m.A, map), b = Subst(m.B, map);
                    return ReferenceEquals(a, m.A) && ReferenceEquals(b, m.B) ? l : MkIMax(a, b);
                }
            default:
                return l;
        }
    }

    /// <summary>Lean's mk_max.</summary>
    public Level MkMax(Level a, Level b)
    {
        if (IsExplicit(a, out int ka) && IsExplicit(b, out int kb))
        {
            return ka >= kb ? a : b;
        }
        if (ReferenceEquals(a, b) || b is LZero)
        {
            return a;
        }
        if (a is LZero)
        {
            return b;
        }
        if (b is LMax mb && (ReferenceEquals(mb.A, a) || ReferenceEquals(mb.B, a)))
        {
            return b;
        }
        if (a is LMax ma && (ReferenceEquals(ma.A, b) || ReferenceEquals(ma.B, b)))
        {
            return a;
        }
        (Level ba, int oa) = ToOffset(a);
        (Level bb, int ob) = ToOffset(b);
        if (ReferenceEquals(ba, bb))
        {
            return oa > ob ? a : b;
        }
        return _t.Max(a, b);
    }

    /// <summary>Lean's mk_imax.</summary>
    public Level MkIMax(Level a, Level b)
    {
        if (IsNotZero(b))
        {
            return MkMax(a, b);
        }
        if (b is LZero)
        {
            return b;
        }
        if (a is LZero || (a is LSucc { Of: LZero }))
        {
            return b;
        }
        if (ReferenceEquals(a, b))
        {
            return a;
        }
        return _t.IMax(a, b);
    }

    private static bool IsExplicit(Level l, out int k)
    {
        k = 0;
        while (l is LSucc s)
        {
            l = s.Of;
            k++;
        }
        return l is LZero;
    }

    private static (Level Base, int Offset) ToOffset(Level l)
    {
        int k = 0;
        while (l is LSucc s)
        {
            l = s.Of;
            k++;
        }
        return (l, k);
    }

    /// <summary>Lean's is_not_zero: true when the level is at least 1 under every assignment, as far as its shape shows.</summary>
    private static bool IsNotZero(Level l) => l switch
    {
        LSucc => true,
        LMax m => IsNotZero(m.A) || IsNotZero(m.B),
        LIMax m => IsNotZero(m.B),
        _ => false,
    };

    // ---- level equivalence ----

    /// <summary>Most parameters a level comparison will case-split on (2ⁿ cases).</summary>
    public const int MaxLevelParams = 12;

    /// <summary>
    /// Whether two levels denote the same universe for every assignment of natural numbers to their parameters.
    /// Null when the levels have too many parameters to decide this way.
    ///
    /// Each parameter is split into the case p = 0 and the case p = p' + 1. In every case each imax is then decided
    /// (its right side is either the constant 0 or at least 1), leaving max and succ only. A level built from max and
    /// succ is a maximum of terms "parameter + k" and one constant, which is a canonical form once each parameter keeps
    /// only its largest k and the constant is dropped when some parameter term is at least as large.
    /// </summary>
    public bool? Equivalent(Level a, Level b)
    {
        if (ReferenceEquals(a, b))
        {
            return true;
        }
        var ps = new List<Name>();
        CollectParams(a, ps);
        CollectParams(b, ps);
        if (ps.Count > MaxLevelParams)
        {
            return null;
        }
        for (int mask = 0; mask < 1 << ps.Count; mask++)
        {
            // Bit set: the parameter is a successor (written as the parameter itself plus one).
            var zero = new HashSet<Name>(ReferenceEqualityComparer.Instance);
            for (int i = 0; i < ps.Count; i++)
            {
                if ((mask & (1 << i)) == 0)
                {
                    zero.Add(ps[i]);
                }
            }
            if (!Canon(a, zero).Equals(Canon(b, zero)))
            {
                return false;
            }
        }
        return true;
    }

    private static void CollectParams(Level l, List<Name> ps)
    {
        switch (l)
        {
            case LParam p:
                if (!ps.Any(x => ReferenceEquals(x, p.Name)))
                {
                    ps.Add(p.Name);
                }
                break;
            case LSucc s:
                CollectParams(s.Of, ps);
                break;
            case LMax m:
                CollectParams(m.A, ps);
                CollectParams(m.B, ps);
                break;
            case LIMax m:
                CollectParams(m.A, ps);
                CollectParams(m.B, ps);
                break;
        }
    }

    /// <summary>A level as max(constant, p₁ + k₁, …) in the case where the parameters in zero are 0 and the rest are p' + 1.</summary>
    private readonly record struct CanonLevel(int Const, string Terms);

    private static CanonLevel Canon(Level l, HashSet<Name> zero)
    {
        var terms = new Dictionary<Name, int>(ReferenceEqualityComparer.Instance);
        int c = Eval(l, zero, 0, terms);
        int maxTerm = terms.Count == 0 ? -1 : terms.Values.Max();
        // Every non-zero parameter is at least 1, written p' + 1 with p' ≥ 0, so "p + k" is at least k + 1.
        if (maxTerm >= 0 && c <= maxTerm + 1)
        {
            c = 0;
        }
        string key = string.Join(",", terms.Select(kv => kv.Key + "+" + kv.Value).OrderBy(s => s, StringComparer.Ordinal));
        return new CanonLevel(c, key);
    }

    /// <summary>
    /// Add the level, shifted up by k, into terms (parameter → largest offset, where the parameter stands for p' + 1)
    /// and return the largest constant it contributes.
    /// </summary>
    private static int Eval(Level l, HashSet<Name> zero, int k, Dictionary<Name, int> terms)
    {
        switch (l)
        {
            case LZero:
                return k;
            case LSucc s:
                return Eval(s.Of, zero, k + 1, terms);
            case LParam p:
                if (zero.Contains(p.Name))
                {
                    return k;
                }
                terms[p.Name] = terms.TryGetValue(p.Name, out int old) ? Math.Max(old, k) : k;
                return 0;
            case LMax m:
                return Math.Max(Eval(m.A, zero, k, terms), Eval(m.B, zero, k, terms));
            case LIMax m:
                if (IsZero(m.B, zero))
                {
                    return k;   // imax a 0 = 0
                }
                return Math.Max(Eval(m.A, zero, k, terms), Eval(m.B, zero, k, terms));
            default:
                throw new InvalidOperationException();
        }
    }

    /// <summary>Whether the level is 0 in this case. Every non-zero parameter is at least 1, so this is decided.</summary>
    private static bool IsZero(Level l, HashSet<Name> zero) => l switch
    {
        LZero => true,
        LSucc => false,
        LParam p => zero.Contains(p.Name),
        LMax m => IsZero(m.A, zero) && IsZero(m.B, zero),
        LIMax m => IsZero(m.B, zero),   // imax a 0 = 0, and imax a b = max a b ≥ 1 when b ≥ 1
        _ => throw new InvalidOperationException(),
    };
}
