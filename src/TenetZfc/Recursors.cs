namespace TenetZfc;

// Deriving the recursors of an inductive block from its types and constructors, as the kernel does, and comparing
// them with the export's. Iota reduction uses the export's recursor rules; this is what makes those rules more than
// the exporter's word. Nested blocks are not handled (they are not replayed at all).

public sealed partial class Replayer
{
    /// <summary>A local made while deriving: its free variable and its type. Ids start high to stay clear of the trace's.</summary>
    private sealed class Telescope(Terms t, Ops ops, Func<Expr, Expr>? strip = null)
    {
        private static ulong s_next = 1UL << 62;
        private readonly Dictionary<Expr, Expr> _types = new(ReferenceEqualityComparer.Instance);

        /// <summary>A fresh local of this type. Like the kernel's, its type loses optParam/autoParam/outParam/semiOutParam wrappers.</summary>
        public Expr Local(Expr type)
        {
            Expr v = t.FVar(Interlocked.Increment(ref s_next));
            _types[v] = strip is null ? type : strip(type);
            return v;
        }

        public Expr TypeOf(Expr v) => _types[v];

        /// <summary>Close body under Pi (or lambda) binders for the locals, in order.</summary>
        public Expr Close(bool isPi, IReadOnlyList<Expr> locals, Expr body)
        {
            Expr r = ops.Abstract(body, locals);
            for (int i = locals.Count - 1; i >= 0; i--)
            {
                List<Expr> prefix = locals.Take(i).ToList();
                r = t.Binding(isPi, Name.Anonymous, BinderKind.Default, ops.Abstract(_types[locals[i]], prefix), r);
            }
            return r;
        }
    }

    /// <summary>
    /// Derive the block's recursors and compare them with the export's: types, rule right-hand sides, field counts,
    /// motive/minor/index counts and rule K. Null when they all match; otherwise the first difference.
    /// </summary>
    private string? CheckRecursors(ConstInfo first, DeclState st)
    {
        List<ConstInfo> types = first.BlockMembers.Select(m => _env.Find(m)!).Where(c => c.Kind == ConstKind.Inductive).ToList();
        int np = first.NumParams;
        Level[] levels = first.LevelParams.Select(_t.Param).ToArray();
        var tel = new Telescope(_t, _ops, ConsumeAnnotations);

        // Parameters, from the first type.
        var ps = new List<Expr>();
        Expr ty0 = first.Type;
        for (int i = 0; i < np; i++)
        {
            if (ty0 is not Binder { IsPi: true } pi)
            {
                return "the type has fewer binders than parameters";
            }
            Expr p = tel.Local(_ops.InstantiateRev(pi.Domain, ps));
            ps.Add(p);
            ty0 = pi.Body;
        }

        // The universe motives eliminate into, and rule K.
        Level result = ResultLevel(first);
        bool elimZero = ElimOnlyAtZero(types, np, result, st);
        ConstInfo rec0 = _env.Find(_t.Str(first.Name, "rec")) ?? throw new InvalidOperationException();
        Level elim;
        Level[] recLevels;
        if (elimZero)
        {
            elim = _t.Zero;
            recLevels = levels;
        }
        else
        {
            if (rec0.LevelParams.Length != first.LevelParams.Length + 1)
            {
                return "the recursor should eliminate into any universe, and the export's has no universe for it";
            }
            elim = _t.Param(rec0.LevelParams[0]);
            recLevels = [elim, .. levels];
        }
        if (elimZero && rec0.LevelParams.Length != first.LevelParams.Length)
        {
            return "the recursor should eliminate only into Prop, and the export's has a universe for its motive";
        }

        // Indices, major premise and motive of each type.
        var indices = new List<List<Expr>>();
        var majors = new List<Expr>();
        var motives = new List<Expr>();
        foreach (ConstInfo ind in types)
        {
            Expr t = ind.Type;
            for (int i = 0; i < np; i++)
            {
                t = _ops.Instantiate(((Binder)t).Body, [ps[i]]);
            }
            var idx = new List<Expr>();
            for (int i = 0; i < ind.NumIndices; i++)
            {
                if (t is not Binder { IsPi: true } pi)
                {
                    return $"{ind.Name}'s type has fewer binders than indices";
                }
                Expr x = tel.Local(pi.Domain);
                idx.Add(x);
                t = _ops.Instantiate(pi.Body, [x]);
            }
            Expr major = tel.Local(_t.MkApp(_t.MkApp(_t.Const(ind.Name, levels), ps), idx));
            Expr motive = tel.Local(tel.Close(true, [.. idx, major], _t.Sort(elim)));
            indices.Add(idx);
            majors.Add(major);
            motives.Add(motive);
        }

        // Minor premises, one per constructor, in block order.
        var minors = new List<Expr>();
        var ctorInfo = new List<(ConstInfo Ctor, int TypeIdx, List<Expr> Fields, List<(Expr Field, List<Expr> Xs, int K, List<Expr> Idx)> Recs)>();
        for (int j = 0; j < types.Count; j++)
        {
            foreach (Name cn in types[j].Ctors)
            {
                ConstInfo c = _env.Find(cn)!;
                Expr t = c.Type;
                for (int i = 0; i < np; i++)
                {
                    t = _ops.Instantiate(((Binder)t).Body, [ps[i]]);
                }
                var fields = new List<Expr>();
                var recs = new List<(Expr, List<Expr>, int, List<Expr>)>();
                while (t is Binder { IsPi: true } pi)
                {
                    Expr b = tel.Local(pi.Domain);
                    fields.Add(b);
                    if (RecArgument(pi.Domain, types, np, tel, out List<Expr> xs, out int k, out List<Expr> ridx))
                    {
                        recs.Add((b, xs, k, ridx));
                    }
                    t = _ops.Instantiate(pi.Body, [b]);
                }
                Ops.Spine(t, out List<Expr> resArgs);
                Expr ctorApp = _t.MkApp(_t.MkApp(_t.Const(cn, levels), ps), fields);
                Expr cApp = _t.App(_t.MkApp(motives[j], resArgs.Skip(np)), ctorApp);
                var ihs = new List<Expr>();
                foreach ((Expr u, List<Expr> xs, int k, List<Expr> ridx) in recs)
                {
                    Expr body = _t.App(_t.MkApp(motives[k], ridx), _t.MkApp(u, xs));
                    ihs.Add(tel.Local(tel.Close(true, xs, body)));
                }
                minors.Add(tel.Local(tel.Close(true, [.. fields, .. ihs], cApp)));
                ctorInfo.Add((c, j, fields, recs));
            }
        }

        // Each type's recursor: its type, then its rules.
        for (int j = 0; j < types.Count; j++)
        {
            Name recName = _t.Str(types[j].Name, "rec");
            if (_env.Find(recName) is not { Kind: ConstKind.Recursor } rec)
            {
                return $"{recName} is not in the export";
            }
            Expr recType = tel.Close(true, [.. ps, .. motives, .. minors, .. indices[j], majors[j]],
                _t.App(_t.MkApp(motives[j], indices[j]), majors[j]));
            if (!ReferenceEquals(recType, rec.Type))
            {
                return $"{recName}'s type is not the one its block determines";
            }
            bool k = KTarget(types, np, result);
            if (rec.K != k || rec.NumParams != np || rec.NumMotives != types.Count || rec.NumMinors != minors.Count
                || rec.NumIndices != types[j].NumIndices)
            {
                return $"{recName}'s counts or rule K differ from what its block determines";
            }
            var mine = ctorInfo.Select((x, i) => (x, i)).Where(p => p.x.TypeIdx == j).ToList();
            if (rec.Rules.Length != mine.Count)
            {
                return $"{recName} has {rec.Rules.Length} rules; its type has {mine.Count} constructors";
            }
            for (int r = 0; r < mine.Count; r++)
            {
                ((ConstInfo c, int _, List<Expr> fields, var recs), int mi) = mine[r];
                RecRule rule = rec.Rules[r];
                if (!ReferenceEquals(rule.Ctor, c.Name) || rule.NumFields != fields.Count)
                {
                    return $"{recName}'s rule {r} is for the wrong constructor or field count";
                }
                var ihValues = recs.Select(x =>
                {
                    Expr recK = _t.MkApp(_t.MkApp(_t.MkApp(_t.Const(_t.Str(types[x.K].Name, "rec"), recLevels), ps), motives), minors);
                    return tel.Close(false, x.Xs, _t.App(_t.MkApp(recK, x.Idx), _t.MkApp(x.Field, x.Xs)));
                }).ToList();
                Expr rhs = tel.Close(false, [.. ps, .. motives, .. minors, .. fields],
                    _t.MkApp(_t.MkApp(minors[mi], fields), ihValues));
                if (!ReferenceEquals(rhs, rule.Rhs))
                {
                    return $"{recName}'s rule for {c.Name} is not the one its block determines";
                }
            }
        }
        return null;
    }

    /// <summary>
    /// Strip optParam, autoParam, outParam and semiOutParam wrappers, as the kernel does for the locals of an inductive
    /// declaration. Only a wrapper that the export defines as the identity on its type argument is stripped (Tenet's
    /// hardening against a file that declares its own autoParam; leanbugs lean-0026).
    /// </summary>
    private Expr ConsumeAnnotations(Expr e)
    {
        while (true)
        {
            Expr head = Ops.Spine(e, out List<Expr> args);
            if (head is not Const c)
            {
                return e;
            }
            string n = $"{c.Name}";
            int arity = n is "optParam" or "autoParam" ? 2 : n is "outParam" or "semiOutParam" ? 1 : 0;
            if (arity == 0 || args.Count != arity || !IsIdentityOnFirst(c.Name, arity))
            {
                return e;
            }
            e = args[0];
        }
    }

    /// <summary>Whether a definition is fun (α : Sort u) (… ) => α: the identity on its first argument.</summary>
    private bool IsIdentityOnFirst(Name n, int arity)
    {
        if (_env.Find(n) is not { Kind: ConstKind.Definition, Value: Expr v })
        {
            return false;
        }
        for (int i = 0; i < arity; i++)
        {
            if (v is not Binder { IsPi: false } lam)
            {
                return false;
            }
            v = lam.Body;
        }
        return v is BVar b && b.Idx == arity - 1;
    }

    /// <summary>A field Π xs, I_k params idx for a type I_k of the block: its locals, which type, and its indices.</summary>
    private bool RecArgument(Expr d, List<ConstInfo> types, int np, Telescope tel, out List<Expr> xs, out int k, out List<Expr> idx)
    {
        xs = new List<Expr>();
        k = -1;
        idx = new List<Expr>();
        while (d is Binder { IsPi: true } pi)
        {
            Expr x = tel.Local(pi.Domain);
            xs.Add(x);
            d = _ops.Instantiate(pi.Body, [x]);
        }
        if (Ops.Spine(d, out List<Expr> args) is not Const c)
        {
            return false;
        }
        k = types.FindIndex(t => ReferenceEquals(t.Name, c.Name));
        if (k < 0)
        {
            return false;
        }
        idx = args.Skip(np).ToList();
        return true;
    }

    private static Level ResultLevel(ConstInfo ind)
    {
        Expr t = ind.Type;
        while (t is Binder { IsPi: true } pi)
        {
            t = pi.Body;
        }
        return ((Sort)t).Level;
    }

    /// <summary>Lean's is_not_zero: a level that is at least 1 by its shape.</summary>
    private static bool NotZero(Level l) => l switch
    {
        LSucc => true,
        LMax m => NotZero(m.A) || NotZero(m.B),
        LIMax m => NotZero(m.B),
        _ => false,
    };

    /// <summary>
    /// The kernel's elim_only_at_universe_zero: a type that may be a Prop eliminates only into Prop unless it is
    /// alone in its block with at most one constructor, and every field of that constructor is a proof or appears
    /// among the constructor's result indices.
    /// </summary>
    private bool ElimOnlyAtZero(List<ConstInfo> types, int np, Level result, DeclState st)
    {
        if (NotZero(result))
        {
            return false;
        }
        if (types.Count > 1 || types[0].Ctors.Length > 1)
        {
            return true;
        }
        if (types[0].Ctors.Length == 0)
        {
            return false;
        }
        ConstInfo c = _env.Find(types[0].Ctors[0])!;
        var tel = new Telescope(_t, _ops);
        Expr t = c.Type;
        var locals = new List<Expr>();
        var toCheck = new List<(Expr Local, int Field)>();
        int i = 0;
        while (t is Binder { IsPi: true } pi)
        {
            Expr x = tel.Local(pi.Domain);
            if (i >= np)
            {
                toCheck.Add((x, i - np));
            }
            locals.Add(x);
            t = _ops.Instantiate(pi.Body, [x]);
            i++;
        }
        Ops.Spine(t, out List<Expr> resultArgs);
        List<Level>? fieldLevels = FieldLevelsAny(c, st);
        foreach ((Expr x, int f) in toCheck)
        {
            bool isProof = fieldLevels is not null && f < fieldLevels.Count && fieldLevels[f] is LZero;
            if (!isProof && !resultArgs.Any(a => ReferenceEquals(a, x)))
            {
                return true;
            }
        }
        return false;
    }

    /// <summary>The kernel's K target: alone in its block, in Prop exactly, one constructor with no fields.</summary>
    private bool KTarget(List<ConstInfo> types, int np, Level result)
    {
        if (types.Count != 1 || result is not LZero || types[0].Ctors.Length != 1)
        {
            return false;
        }
        return _env.Find(types[0].Ctors[0])!.NumFields == 0;
    }

    /// <summary>The fields' universes from the trace, or from the constructor type as written when every field's domain is a Prop-valued sort shape the trace does not need.</summary>
    private List<Level>? FieldLevelsAny(ConstInfo ctor, DeclState st) => _fieldSteps is null ? null : FieldLevels(ctor, _fieldSteps, st);

    /// <summary>The steps of the block being replayed, for looking up field universes.</summary>
    private IReadOnlyList<Step>? _fieldSteps;
}
