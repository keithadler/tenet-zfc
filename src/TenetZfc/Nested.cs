namespace TenetZfc;

// Nested inductive blocks, replayed the way the kernel checks them.
//
// A nested block (Lean.Syntax holds an Array Syntax) is checked by first replacing every nested occurrence with a new
// auxiliary inductive (_nested.Array_1, and _nested.List_2 for the List Syntax inside Array's constructor), checking
// that plain mutual block in an environment of its own, and translating its recursors back. All three stages are
// redone here from the export: the auxiliary block is built by the same elimination, checked like any other block
// (types from the trace, structure and recursors rechecked), and its recursors, translated back, must be the export's
// Lean.Syntax.rec, Lean.Syntax.rec_1, …. The block's trace was taken in the auxiliary environment and then, for the
// final re-check, in the declaration's own; each step is replayed against the auxiliary environment first and the
// export's second.

public sealed partial class Replayer
{
    private sealed record AuxType(Name Name, Expr Type, List<(Name Name, Expr Type)> Ctors);

    /// <summary>What eliminating a block's nested occurrences produced.</summary>
    private sealed class Elimination
    {
        public required List<Expr> Params { get; init; }
        public required List<AuxType> Types { get; init; }
        public required int NumOriginal { get; init; }

        /// <summary>Auxiliary type name → the nested occurrence it replaces, I applied to its parameters (over <see cref="Params"/>).</summary>
        public required Dictionary<Name, Expr> Aux2Nested { get; init; }
    }

    /// <summary>The kernel's elim_nested_inductive, from the export: the block with every nested occurrence replaced.</summary>
    private (string? Error, Elimination? Result) EliminateNested(ConstInfo first)
    {
        Environment env = _env;
        List<ConstInfo> types = first.BlockMembers.Select(m => env.Find(m)).OfType<ConstInfo>().Where(c => c.Kind == ConstKind.Inductive).ToList();
        int np = first.NumParams;
        Level[] lvls = first.LevelParams.Select(_t.Param).ToArray();
        var tel = new Telescope(_t, _ops);
        Name nestedPrefix = _t.Of("_nested");

        var ps = new List<Expr>();
        Expr ty0 = first.Type;
        for (int i = 0; i < np; i++)
        {
            if (ty0 is not Binder { IsPi: true } pi)
            {
                return ("the type has fewer binders than parameters", null);
            }
            ps.Add(tel.Local(_ops.InstantiateRev(pi.Domain, ps)));
            ty0 = pi.Body;
        }

        var newTypes = types.Select(t => new AuxType(t.Name, t.Type, t.Ctors.Select(c => (c, env.Find(c)!.Type)).ToList())).ToList();
        var nestedAux = new List<(Expr Nested, Name AuxName)>();
        ulong nextIdx = 1;
        string? error = null;

        Name MkUniqueName(Name n)
        {
            while (true)
            {
                Name r = _t.AppendIndexAfter(n, nextIdx++);
                if (env.Find(r) is null)
                {
                    return r;
                }
            }
        }

        Expr ReplaceParams(Expr e, List<Expr> As) => _ops.InstantiateRev(_ops.Abstract(e, As), ps);

        Expr InstantiatePiParams(Expr e, List<Expr> args)
        {
            for (int i = 0; i < args.Count; i++)
            {
                e = ((Binder)e).Body;
            }
            return _ops.InstantiateRev(e, args);
        }

        Expr? ReplaceIfNested(List<Expr> As, Expr e)
        {
            if (e is not App || Ops.Spine(e, out List<Expr> args) is not Const fn || env.Find(fn.Name) is not { Kind: ConstKind.Inductive } info)
            {
                return null;
            }
            int inp = info.NumParams;
            if (inp > args.Count)
            {
                return null;
            }
            var newNames = new HashSet<Name>(newTypes.Select(t => t.Name), ReferenceEqualityComparer.Instance);
            bool isNested = args.Take(inp).Any(a => Occurs(a, newNames));
            if (!isNested)
            {
                return null;
            }
            if (args.Take(inp).Any(a => a.LooseBVarRange > 0))
            {
                error = $"invalid nested inductive datatype '{fn.Name}': its parameters mention bound variables";
                return null;
            }
            Expr iParams = ReplaceParams(_t.MkApp(fn, args.Take(inp)), As);
            foreach ((Expr nested, Name auxName) in nestedAux)
            {
                if (ReferenceEquals(nested, iParams))
                {
                    return _t.MkApp(_t.MkApp(_t.Const(auxName, lvls), As), args.Skip(inp));
                }
            }
            Expr? result = null;
            List<Expr> iArgs = args.Take(inp).ToList();
            foreach (Name jName in info.BlockMembers.Where(m => env.Find(m) is { Kind: ConstKind.Inductive }))
            {
                ConstInfo j = env.Find(jName)!;
                Name auxJ = MkUniqueName(_t.Append(nestedPrefix, jName));
                Expr auxJType = tel.Close(true, As, InstantiatePiParams(_ops.InstantiateLevels(j.Type, j.LevelParams, fn.Levels), iArgs));
                nestedAux.Add((ReplaceParams(_t.MkApp(_t.Const(jName, fn.Levels), iArgs), As), auxJ));
                if (ReferenceEquals(jName, fn.Name))
                {
                    result = _t.MkApp(_t.MkApp(_t.Const(auxJ, lvls), As), args.Skip(inp));
                }
                var ctors = j.Ctors.Select(cn =>
                {
                    ConstInfo c = env.Find(cn)!;
                    Expr ct = tel.Close(true, As, InstantiatePiParams(_ops.InstantiateLevels(c.Type, c.LevelParams, fn.Levels), iArgs));
                    return (_t.ReplacePrefix(cn, jName, auxJ), ct);
                }).ToList();
                newTypes.Add(new AuxType(auxJ, auxJType, ctors));
            }
            return result;
        }

        // Replace pre-order, children left to right, each distinct subterm once: the order decides the auxiliary names.
        Expr ReplaceAll(List<Expr> As, Expr e, int offset, Dictionary<(Expr, int), Expr> memo)
        {
            bool compound = e is App or Binder or Let or Proj;
            if (compound && memo.TryGetValue((e, offset), out Expr? hit))
            {
                return hit;
            }
            Expr r = ReplaceIfNested(As, e) ?? e switch
            {
                App a => _t.App(ReplaceAll(As, a.Fn, offset, memo), ReplaceAll(As, a.Arg, offset, memo)),
                Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, ReplaceAll(As, b.Domain, offset, memo), ReplaceAll(As, b.Body, offset + 1, memo)),
                Let l => _t.Let(l.BinderName, ReplaceAll(As, l.Type, offset, memo), ReplaceAll(As, l.Value, offset, memo), ReplaceAll(As, l.Body, offset + 1, memo)),
                Proj p => _t.Proj(p.StructName, p.Idx, ReplaceAll(As, p.Struct, offset, memo)),
                _ => e,
            };
            if (compound)
            {
                memo[(e, offset)] = r;
            }
            return r;
        }

        for (int q = 0; q < newTypes.Count; q++)
        {
            AuxType t = newTypes[q];
            var ctors = new List<(Name, Expr)>();
            foreach ((Name cn, Expr ct) in t.Ctors)
            {
                // The constructor's own parameter binders, then its fields with nested occurrences replaced.
                var As = new List<Expr>();
                Expr body = ct;
                for (int i = 0; i < np; i++)
                {
                    if (body is not Binder { IsPi: true } pi)
                    {
                        return ($"{cn} has fewer binders than parameters", null);
                    }
                    As.Add(tel.Local(_ops.InstantiateRev(pi.Domain, As)));
                    body = pi.Body;
                }
                body = _ops.InstantiateRev(body, As);
                Expr replaced = ReplaceAll(As, body, 0, new Dictionary<(Expr, int), Expr>());
                if (error is not null)
                {
                    return (error, null);
                }
                ctors.Add((cn, tel.Close(true, As, replaced)));
            }
            newTypes[q] = t with { Ctors = ctors };
        }
        return (null, new Elimination
        {
            Params = ps, Types = newTypes, NumOriginal = types.Count,
            Aux2Nested = nestedAux.ToDictionary(x => x.AuxName, x => x.Nested, ReferenceEqualityComparer.Instance as IEqualityComparer<Name>),
        });
    }

    /// <summary>The auxiliary environment: the eliminated block as plain inductive types over the export.</summary>
    private Environment AuxEnvironment(ConstInfo first, Elimination el)
    {
        var aux = new Environment(_env);
        int np = first.NumParams;
        Name u = _t.Of("u");
        for (ulong n = 1; first.LevelParams.Any(x => ReferenceEquals(x, u)); n++)
        {
            u = _t.Of("u_" + n);
        }
        Name[] members = el.Types.SelectMany(t => new[] { t.Name }.Concat(t.Ctors.Select(c => c.Name)).Append(_t.Str(t.Name, "rec"))).ToArray();
        static int Pis(Expr e) { int k = 0; while (e is Binder { IsPi: true } b) { k++; e = b.Body; } return k; }
        foreach (AuxType t in el.Types)
        {
            aux.Add(new ConstInfo
            {
                Name = t.Name, Kind = ConstKind.Inductive, LevelParams = first.LevelParams, Type = t.Type,
                NumParams = np, NumIndices = Pis(t.Type) - np, Ctors = t.Ctors.Select(c => c.Name).ToArray(),
                BlockMembers = members, BlockLevelParams = [u, .. first.LevelParams],
            });
            foreach ((Name cn, Expr ct) in t.Ctors)
            {
                aux.Add(new ConstInfo
                {
                    Name = cn, Kind = ConstKind.Constructor, LevelParams = first.LevelParams, Type = ct,
                    Induct = t.Name, NumParams = np, NumFields = Pis(ct) - np,
                });
            }
        }
        return aux;
    }

    /// <summary>
    /// The kernel's restore_nested: under the parameters, auxiliary types become the occurrences they replaced,
    /// auxiliary constructors the original constructors, and auxiliary recursors the main type's rec_1, rec_2, ….
    /// </summary>
    private Expr Restore(Expr e, Elimination el, Environment aux, Dictionary<Name, Name> recNames, int np)
    {
        var tel = new Telescope(_t, _ops);
        bool isPi = e is Binder { IsPi: true };
        var As = new List<Expr>();
        for (int i = 0; i < np; i++)
        {
            var b = (Binder)e;
            As.Add(tel.Local(_ops.InstantiateRev(b.Domain, As)));
            e = b.Body;
        }
        e = _ops.InstantiateRev(e, As);
        var memo = new Dictionary<(Expr, int), Expr>();

        Expr Go(Expr t, int offset)
        {
            bool compound = t is App or Binder or Let or Proj;
            if (compound && memo.TryGetValue((t, offset), out Expr? hit))
            {
                return hit;
            }
            Expr? r = null;
            if (t is Const c0 && recNames.TryGetValue(c0.Name, out Name? rn))
            {
                r = _t.Const(rn, c0.Levels);
            }
            else if (Ops.Spine(t, out List<Expr> args) is Const fn)
            {
                if (el.Aux2Nested.TryGetValue(fn.Name, out Expr? nested) && args.Count >= np)
                {
                    r = _t.MkApp(_ops.InstantiateRev(_ops.Abstract(nested, el.Params), As), args.Skip(np));
                }
                else if (aux.Find(fn.Name) is { Kind: ConstKind.Constructor, Induct: Name ind } && el.Aux2Nested.TryGetValue(ind, out Expr? nested2) && args.Count >= np)
                {
                    Expr newNested = _ops.InstantiateRev(_ops.Abstract(nested2, el.Params), As);
                    var I = (Const)Ops.Spine(newNested, out List<Expr> iArgs);
                    r = _t.MkApp(_t.MkApp(_t.Const(_t.ReplacePrefix(fn.Name, ind, I.Name), I.Levels), iArgs), args.Skip(np));
                }
            }
            r ??= t switch
            {
                App a => _t.App(Go(a.Fn, offset), Go(a.Arg, offset)),
                Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Go(b.Domain, offset), Go(b.Body, offset + 1)),
                Let l => _t.Let(l.BinderName, Go(l.Type, offset), Go(l.Value, offset), Go(l.Body, offset + 1)),
                Proj p => _t.Proj(p.StructName, p.Idx, Go(p.Struct, offset)),
                _ => t,
            };
            if (compound)
            {
                memo[(t, offset)] = r;
            }
            return r;
        }

        return tel.Close(isPi, As, Go(e, 0));
    }

    /// <summary>
    /// Check a nested block: eliminate, check the auxiliary block (its types from the trace, its structure and
    /// recursors here), restore, and compare constructors and recursors with the export. Null when all of it holds.
    /// </summary>
    private string? CheckNestedBlock(ConstInfo first, IReadOnlyList<Step> steps, DeclState st, Elimination el, Environment aux)
    {
        Environment main = _env;
        _env = aux;
        try
        {
            ConstInfo auxFirst = aux.Find(el.Types[0].Name)!;
            // Every type of the auxiliary block, its constructors' types and its recursors' types, checked by the trace.
            _fieldSteps = steps;
            (string? derr, List<ConstInfo> recs) = DeriveRecursors(auxFirst, st);
            if (derr is not null)
            {
                return derr;
            }
            foreach (ConstInfo r in recs)
            {
                aux.Add(r);
            }
            Name? unchecked_ = auxFirst.BlockMembers.FirstOrDefault(m => aux.Find(m) is not ConstInfo c || CheckedSortOf(c.Type, st) is null);
            if (unchecked_ is not null)
            {
                return $"the trace does not check the type of {unchecked_}";
            }
            BlockCheck bc = CheckBlock(auxFirst, steps, st);
            if (!bc.Ok)
            {
                return bc.Why;
            }

            // Restore and compare with the export.
            int np = first.NumParams;
            var recNames = new Dictionary<Name, Name>(ReferenceEqualityComparer.Instance);
            for (int k = el.NumOriginal; k < el.Types.Count; k++)
            {
                recNames[_t.Str(el.Types[k].Name, "rec")] = _t.AppendIndexAfter(_t.Str(first.Name, "rec"), (ulong)(k - el.NumOriginal + 1));
            }
            for (int k = 0; k < el.NumOriginal; k++)
            {
                foreach ((Name cn, Expr ct) in el.Types[k].Ctors)
                {
                    if (!ReferenceEquals(Restore(ct, el, aux, recNames, np), main.Find(cn)?.Type))
                    {
                        return $"{cn}, restored from the auxiliary block, is not the export's";
                    }
                }
            }
            foreach (ConstInfo r in recs)
            {
                Name name = recNames.TryGetValue(r.Name, out Name? m) ? m : r.Name;
                var restored = new ConstInfo
                {
                    Name = name, Kind = ConstKind.Recursor, LevelParams = r.LevelParams, Type = Restore(r.Type, el, aux, recNames, np),
                    NumParams = r.NumParams, NumMotives = r.NumMotives, NumMinors = r.NumMinors, NumIndices = r.NumIndices, K = r.K,
                    Rules = r.Rules.Select(rule => new RecRule(
                        recNames.ContainsKey(r.Name) ? RestoreCtorName(rule.Ctor, el, aux) : rule.Ctor,
                        rule.NumFields, Restore(rule.Rhs, el, aux, recNames, np))).ToArray(),
                };
                string? diff = CompareRecursor(restored, main.Find(name));
                if (diff is not null)
                {
                    return diff + " (restored from the auxiliary block)";
                }
            }
            return null;
        }
        finally
        {
            _env = main;
            _fieldSteps = null;
        }
    }

    private Name RestoreCtorName(Name ctor, Elimination el, Environment aux)
    {
        Name ind = aux.Find(ctor)!.Induct!;
        var I = (Const)Ops.Spine(el.Aux2Nested[ind], out _);
        return _t.ReplacePrefix(ctor, ind, I.Name);
    }

}
