namespace TenetZfc;

// The structural checks the kernel makes of an inductive block, rechecked from the export: constructor shapes,
// strict positivity, and universe levels. Only the universe of each constructor field comes from the trace (the
// checking-mode facts about the constructor's type). Recursor derivation is not rechecked here.

public sealed partial class Replayer
{
    /// <summary>The outcome of rechecking a block: ok, or the first problem, and whether that problem is a case not handled.</summary>
    private readonly record struct BlockCheck(bool Ok, string? Why, bool Unsupported)
    {
        public static readonly BlockCheck Pass = new(true, null, false);
        public static BlockCheck Fail(string why) => new(false, why, false);
        public static BlockCheck Skip(string why) => new(false, why, true);
    }

    /// <summary>
    /// Recheck a block's structure with no trace: constructor shapes and strict positivity are decided from the export
    /// alone; field universes need the trace, so without one a block outside Prop stops at its first field's universe.
    /// Null when the block passes; otherwise the first problem.
    /// </summary>
    public string? RecheckBlockStructure(Name block)
    {
        if (_env.Find(block) is not { Kind: ConstKind.Inductive } info)
        {
            return "not an inductive type in the export";
        }
        BlockCheck r = CheckBlock(info, [], new DeclState(info.BlockLevelParams));
        return r.Ok ? null : r.Why;
    }

    private BlockCheck CheckBlock(ConstInfo first, IReadOnlyList<Step> steps, DeclState st)
    {
        List<ConstInfo> types = first.BlockMembers.Select(m => _env.Find(m)).OfType<ConstInfo>().Where(c => c.Kind == ConstKind.Inductive).ToList();
        List<ConstInfo> ctors = first.BlockMembers.Select(m => _env.Find(m)).OfType<ConstInfo>().Where(c => c.Kind == ConstKind.Constructor).ToList();
        var names = new HashSet<Name>(types.Select(t => t.Name), ReferenceEqualityComparer.Instance);
        int np = types[0].NumParams;

        // Every type: Π params, Π indices, Sort l, with the same parameters and the same l across the block.
        Level? result = null;
        List<Expr>? paramDomains = null;
        foreach (ConstInfo t in types)
        {
            if (t.NumParams != np)
            {
                return BlockCheck.Fail($"{t.Name} has a different number of parameters from the rest of its block");
            }
            var domains = new List<Expr>();
            Expr e = t.Type;
            for (int i = 0; i < np + t.NumIndices; i++)
            {
                if (e is not Binder { IsPi: true } pi)
                {
                    return BlockCheck.Skip($"{t.Name}'s type is not a Pi telescope as written");
                }
                if (i < np)
                {
                    domains.Add(pi.Domain);
                }
                e = pi.Body;
            }
            if (e is not Sort so)
            {
                return BlockCheck.Skip($"{t.Name}'s type does not end in a sort as written");
            }
            if (result is null)
            {
                (result, paramDomains) = (so.Level, domains);
            }
            else if (_ops.Equivalent(result, so.Level) != true)
            {
                return BlockCheck.Fail("the types of a mutual block live in different universes");
            }
            else if (!domains.SequenceEqual(paramDomains!))
            {
                return BlockCheck.Skip("the types' parameters differ as written");
            }
        }
        bool isProp = _ops.Equivalent(result!, _t.Zero) == true;

        foreach (ConstInfo c in ctors)
        {
            ConstInfo ind = _env.Find(c.Induct!)!;
            if (!names.Contains(ind.Name) || c.NumParams != np)
            {
                return BlockCheck.Fail($"{c.Name} does not belong to its block's parameters");
            }
            List<Level>? fieldLevels = FieldLevels(c, steps, st);
            Expr e = c.Type;
            int depth = 0;
            for (; depth < np; depth++)
            {
                if (e is not Binder { IsPi: true } pi || !ReferenceEquals(pi.Domain, paramDomains![depth]))
                {
                    return BlockCheck.Skip($"{c.Name}'s parameters differ as written from its type's");
                }
                e = pi.Body;
            }
            int field = 0;
            while (e is Binder { IsPi: true } pi)
            {
                BlockCheck pos = Positive(pi.Domain, depth, names, np, types[0], c.Name);
                if (!pos.Ok)
                {
                    return pos;
                }
                if (!isProp)
                {
                    if (fieldLevels is null || field >= fieldLevels.Count)
                    {
                        return BlockCheck.Skip($"the trace does not give the universe of {c.Name}'s fields");
                    }
                    if (_ops.Equivalent(_ops.MkMax(result!, fieldLevels[field]), result!) != true)
                    {
                        return BlockCheck.Fail($"field {field} of {c.Name} lives in a universe larger than its type's");
                    }
                }
                e = pi.Body;
                depth++;
                field++;
            }
            if (field != c.NumFields)
            {
                return BlockCheck.Fail($"{c.Name} has {field} fields as written, and the export says {c.NumFields}");
            }
            if (!ValidIndApp(e, depth, np, types[0], out Name? target) || !ReferenceEquals(target, ind.Name))
            {
                return BlockCheck.Fail($"{c.Name} does not return its own type applied to the block's parameters");
            }
        }
        return BlockCheck.Pass;
    }

    /// <summary>
    /// Strict positivity of a field type, at binder depth <paramref name="depth"/>: no block type occurs, or the field
    /// is Π ys, I params indices with no block type in the ys or the indices.
    /// </summary>
    private BlockCheck Positive(Expr a, int depth, HashSet<Name> names, int np, ConstInfo first, Name ctor)
    {
        while (true)
        {
            if (!Occurs(a, names))
            {
                return BlockCheck.Pass;
            }
            if (a is Binder { IsPi: true } pi)
            {
                if (Occurs(pi.Domain, names))
                {
                    return BlockCheck.Fail($"a field of {ctor} is not strictly positive");
                }
                a = pi.Body;
                depth++;
                continue;
            }
            if (ValidIndApp(a, depth, np, first, out _))
            {
                return BlockCheck.Pass;
            }
            // The kernel normalizes the field type first; an occurrence hidden behind a definition is a case this
            // syntactic check cannot decide.
            return Ops.Head(a) is Const h && _env.Find(h.Name) is { Kind: ConstKind.Definition }
                ? BlockCheck.Skip($"a field of {ctor} needs unfolding before its positivity can be checked")
                : BlockCheck.Fail($"a field of {ctor} uses its type other than as I params indices");
        }
    }

    /// <summary>I.{lparams} applied to the block's parameters (as bound variables at this depth) and then indices free of block types.</summary>
    private bool ValidIndApp(Expr e, int depth, int np, ConstInfo first, out Name? ind)
    {
        ind = null;
        if (Ops.Spine(e, out List<Expr> args) is not Const c || _env.Find(c.Name) is not { Kind: ConstKind.Inductive } info
            || !first.BlockMembers.Any(m => ReferenceEquals(m, c.Name)))
        {
            return false;
        }
        if (c.Levels.Length != info.LevelParams.Length || !c.Levels.Zip(info.LevelParams).All(p => p.First is LParam lp && ReferenceEquals(lp.Name, p.Second)))
        {
            return false;
        }
        if (args.Count != np + info.NumIndices)
        {
            return false;
        }
        for (int i = 0; i < np; i++)
        {
            // Parameter i was bound np - i binders before the outermost field; at this depth it is bound variable depth - 1 - i.
            if (args[i] is not BVar b || b.Idx != depth - 1 - i)
            {
                return false;
            }
        }
        var names = new HashSet<Name>(first.BlockMembers, ReferenceEqualityComparer.Instance);
        if (args.Skip(np).Any(x => Occurs(x, names)))
        {
            return false;
        }
        ind = c.Name;
        return true;
    }

    private static bool Occurs(Expr e, HashSet<Name> names)
    {
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var stack = new Stack<Expr>();
        stack.Push(e);
        while (stack.Count > 0)
        {
            Expr x = stack.Pop();
            if (!seen.Add(x))
            {
                continue;
            }
            switch (x)
            {
                case Const c when names.Contains(c.Name): return true;
                case App a: stack.Push(a.Fn); stack.Push(a.Arg); break;
                case Binder b: stack.Push(b.Domain); stack.Push(b.Body); break;
                case Let l: stack.Push(l.Type); stack.Push(l.Value); stack.Push(l.Body); break;
                case Proj p: stack.Push(p.Struct); break;
            }
        }
        return false;
    }

    /// <summary>
    /// The universe of each of the constructor's fields, from the checking-mode facts the trace records about its type:
    /// the Pi telescope's domains, instantiated with the locals that check introduced.
    /// </summary>
    private List<Level>? FieldLevels(ConstInfo ctor, IReadOnlyList<Step> steps, DeclState st)
    {
        Step? check = steps.FirstOrDefault(s => s.Kind == StepKind.Check && ReferenceEquals(s.A, ctor.Type));
        if (check is null)
        {
            return null;
        }
        List<Expr> fvars = TelescopeLocals(check, steps);
        var levels = new List<Level>();
        Expr e = ctor.Type;
        int n = 0;
        while (e is Binder { IsPi: true } pi && n < fvars.Count)
        {
            Level? l = CheckedSortOf(_ops.InstantiateRev(pi.Domain, fvars.GetRange(0, n)), st);
            if (l is null)
            {
                return null;
            }
            if (n >= ctor.NumParams)
            {
                levels.Add(l);
            }
            e = pi.Body;
            n++;
        }
        return levels;
    }
}
