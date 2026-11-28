namespace TenetZfc;

/// <summary>
/// Monomorphization for the model's tower mode (<see cref="Model"/>, Universes.cs): every constant used at concrete
/// universe levels becomes a constant of its own, with those levels substituted, named c.{l1,l2} (a constant with no
/// level parameters keeps its name). Its type and value are rewritten the same way, so the model only ever sees closed
/// levels, which it can interpret as distinct universes of the tower.
///
/// One parameter stays: a recursor's motive level (its first level parameter, when it has one more than its type).
/// It occurs only as the motive's codomain, which the model interprets as the whole tower; one recursor per type
/// instance then serves every elimination level. The instance of I.rec is named (instance of I).rec, as the model
/// expects.
///
/// The result is an overlay of the original environment: instances first, then the original constants.
/// </summary>
public sealed class Monomorph
{
    private readonly Terms _t;
    private readonly Environment _src;
    private readonly Ops _ops;
    private readonly Dictionary<(Name, string), Name> _instances = new();

    /// <summary>The environment as exported, before any instance was made.</summary>
    public Environment Source => _src;

    public Monomorph(Terms t, Environment src)
    {
        _t = t;
        _src = src;
        _ops = new Ops(t);
        Env = new Environment(src);
    }

    /// <summary>The environment of instances, over the original one.</summary>
    public Environment Env { get; }

    /// <summary>e with every constant replaced by its instance at the levels it is used at (which must be closed).</summary>
    public Expr Rewrite(Expr e) => Rw(e, new Dictionary<Expr, Expr>(ReferenceEqualityComparer.Instance));

    /// <summary>The instance of a constant at closed levels.</summary>
    public Name Instance(Name n, Level[] levels)
    {
        ConstInfo c = _src.Find(n) ?? throw new Model.Refused($"{n} is not in the export");
        if (c.Kind == ConstKind.Recursor && _src.Find(TypeOf(c)) is ConstInfo { Kind: ConstKind.Inductive } ind)
        {
            // I.rec.{v, ls}: the instance of I at ls, then .rec, keeping the motive level v when there is one.
            bool large = c.LevelParams.Length == ind.LevelParams.Length + 1;
            Level[] ls = large ? levels[1..] : levels;
            Name ti = Instance(ind.Name, ls);
            return Make(n, ls, () => _t.Str(ti, ((StrName)c.Name).Value), keep: large ? c.LevelParams[0] : null);
        }
        return Make(n, levels, () => levels.Length == 0 ? n : _t.Str(n, "{" + string.Join(",", levels.Select(Value)) + "}"), keep: null);
    }

    /// <summary>The type a recursor is named after: I for I.rec, and for a nested block's auxiliary recursors I.rec_1, I.rec_2, ….</summary>
    private static Name TypeOf(ConstInfo rec) =>
        rec.Name is StrName s && (s.Value == "rec" || System.Text.RegularExpressions.Regex.IsMatch(s.Value, "^rec_[0-9]+$")) ? s.Prefix : rec.Name;

    private static int Value(Level l) => Model.LevelValue(l) ?? throw new Model.Refused($"a universe level with a parameter ({l}) where a concrete one is needed");

    private Name Make(Name n, Level[] levels, Func<Name> name, Name? keep)
    {
        string key = string.Join(",", levels.Select(Value));
        if (_instances.TryGetValue((n, key), out Name? done))
        {
            return done;
        }
        Name inst = name();
        if (!ReferenceEquals(inst, n) && _src.Find(inst) is not null)
        {
            // An export constant already has the instance's name (a component «{0}»): the two would share a token.
            throw new Model.Refused($"{n}'s instance at levels {{{key}}} would be named {inst}, which the export already has");
        }
        _instances[(n, key)] = inst;  // before rewriting: the type refers to itself through its constructors
        ConstInfo c = _src.Find(n)!;
        Name[] ps = keep is null ? c.LevelParams : c.LevelParams[1..];
        if (ps.Length != levels.Length)
        {
            throw new Model.Refused($"{n} has {ps.Length} universe parameters, used with {levels.Length}");
        }
        Expr Inst(Expr e) => Rewrite(_ops.InstantiateLevels(e, ps, levels));
        Name SameLevels(Name m) => Instance(m, levels);   // constructors and block members share the type's levels
        // A recursor rule's constructor: of the block's own types at the block's levels, but a nested block's auxiliary
        // recursor (I.rec_1 over Array I) has rules on the nested type's constructors (Array.mk), at the levels the
        // nesting uses, which the instantiated recursor type names.
        Name RuleCtor(Name ctor)
        {
            if (_src.Find(ctor)?.Induct is Name ind && LevelsOf(_ops.InstantiateLevels(c.Type, ps, levels), ind) is Level[] ls)
            {
                return Instance(ctor, ls);
            }
            return SameLevels(ctor);
        }
        Env.Add(new ConstInfo
        {
            Name = inst,
            Kind = c.Kind,
            LevelParams = keep is null ? [] : [keep],
            Type = Inst(c.Type),
            Value = c.Value is null ? null : Inst(c.Value),
            OpaqueValue = c.OpaqueValue is null ? null : Inst(c.OpaqueValue),
            Unsafe = c.Unsafe,
            Partial = c.Partial,
            Induct = c.Induct is null ? null : SameLevels(c.Induct),
            NumParams = c.NumParams,
            NumFields = c.NumFields,
            NumMotives = c.NumMotives,
            NumMinors = c.NumMinors,
            NumIndices = c.NumIndices,
            K = c.K,
            Rules = c.Rules.Select(r => new RecRule(RuleCtor(r.Ctor), r.NumFields, Inst(r.Rhs))).ToArray(),
            BlockLevelParams = [],
            BlockMembers = c.Kind == ConstKind.Inductive
                ? c.BlockMembers.Where(m => _src.Find(m)?.Kind is ConstKind.Inductive or ConstKind.Constructor).Select(SameLevels).ToArray()
                : [],
            IsRec = c.IsRec,
            NumNested = c.NumNested,
            Ctors = c.Ctors.Select(SameLevels).ToArray(),
        });
        if (c.Kind == ConstKind.Inductive && _src.Find(_t.Str(n, "rec")) is ConstInfo rec)
        {
            // The model defines a type's recursor with the type, and finds it as (the type's name).rec.
            Instance(rec.Name, rec.LevelParams.Length == levels.Length + 1 ? levels.Prepend(_t.Zero).ToArray() : levels);
            // A nested block's auxiliary recursors, I.rec_1, I.rec_2, …, likewise.
            for (ulong k = 1; _src.Find(_t.Str(n, $"rec_{k}")) is ConstInfo aux; k++)
            {
                Instance(aux.Name, aux.LevelParams.Length == levels.Length + 1 ? levels.Prepend(_t.Zero).ToArray() : levels);
            }
        }
        return inst;
    }

    /// <summary>The levels of the first occurrence of constant n in e, or null.</summary>
    private static Level[]? LevelsOf(Expr e, Name n) => e switch
    {
        Const c when ReferenceEquals(c.Name, n) || $"{c.Name}" == $"{n}" => c.Levels,
        App a => LevelsOf(a.Fn, n) ?? LevelsOf(a.Arg, n),
        Binder b => LevelsOf(b.Domain, n) ?? LevelsOf(b.Body, n),
        Let l => LevelsOf(l.Type, n) ?? LevelsOf(l.Value, n) ?? LevelsOf(l.Body, n),
        Proj p => LevelsOf(p.Struct, n),
        _ => null,
    };

    private Expr Rw(Expr e, Dictionary<Expr, Expr> memo)
    {
        if (memo.TryGetValue(e, out Expr? hit))
        {
            return hit;
        }
        Expr r = e switch
        {
            Const c when _src.Find(c.Name) is ConstInfo ci => RwConst(c, ci),
            App a => _t.App(Rw(a.Fn, memo), Rw(a.Arg, memo)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Rw(b.Domain, memo), Rw(b.Body, memo)),
            Let l => _t.Let(l.BinderName, Rw(l.Type, memo), Rw(l.Value, memo), Rw(l.Body, memo)),
            Proj p => _t.Proj(p.StructName, p.Idx, Rw(p.Struct, memo)),
            _ => e,
        };
        memo[e] = r;
        return r;
    }

    private Expr RwConst(Const c, ConstInfo ci)
    {
        if (ci.Kind == ConstKind.Recursor && _src.Find(TypeOf(ci)) is ConstInfo { Kind: ConstKind.Inductive } ind
            && ci.LevelParams.Length == ind.LevelParams.Length + 1)
        {
            // Keep the motive level as it is used (it may be anything); the model reads it as the whole tower.
            return _t.Const(Instance(c.Name, c.Levels), [c.Levels[0]]);
        }
        return _t.Const(Instance(c.Name, c.Levels), []);
    }
}
