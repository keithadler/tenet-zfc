using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Mutual and nested inductive blocks (docs/milestone3.md, step 3, sixth part).
///
/// A block of types I_0 … I_n-1 (with a nested block, its auxiliary mutual block: Lean.Syntax, then the types standing
/// for Array Syntax and List Syntax) is one least fixed point over a tagged sum. Its elements are pairs
/// &lt;. ix , value &gt;., where ix is the type's index ((/), 1o, 2o, suc 2o, …) and value a tagged tuple as for
/// any inductive type.
/// - The step, lean.I_0.-mstep, adds for each constructor of each type the pairs &lt;. ix , tag(fields) &gt;., where a
///   recursive field of type t ranges over ( X " { ix_t } ), the values of type t in the last stage.
/// - The fixed point is the union of its ω-chain of stages, Fix = U_ k e. _om ( rec ( step , (/) ) ` k ), and each
///   original type is its slice, ( Fix " { ix } ).
/// - Constructors build tagged tuples, as for other types.
/// - The recursors are one well-founded recursion over smaller rank on every set, frecs ( RankLt , _V , H ), whose
///   value at a is the tuple of every type's case analysis on a: &lt;. case_0 , &lt;. case_1 , … (/) &gt;. &gt;.. The
///   case analysis is lean.I_0.-mcase. I_t.rec reads component t of the value at its major premise, and a
///   recursive field r of type t' gets component t' of the recursion at r.
///
/// The recursion runs over every set, not just the block, so that its computation rules need no membership: smaller
/// rank is well-founded on any class (lean-rankfr) and set-like on _V (lean-rankse).
/// </summary>
public sealed partial class Model
{
    private sealed record BlockCtor(Name Real, int Minor, int NumFields, List<(int Field, int Type)> Rec);
    private sealed record BlockTypeInfo(string Ix, ConstInfo? Original, Expr? Nested, Name Rec, List<BlockCtor> Ctors);
    private sealed record BlockInfo(string StepTok, string CaseTok, List<BlockTypeInfo> Types, int NumParams, int NumMotives, int NumMinors, List<Expr>? NestedParams);

    /// <summary>Each block, by the names of its recursors and of its original types.</summary>
    private readonly Dictionary<Name, BlockInfo> _blocks = new(ReferenceEqualityComparer.Instance);

    /// <summary>Type t's index in the tagged sum: (/), 1o, 2o, then suc of the one before.</summary>
    private static string Ix(int t) => t switch { 0 => "(/)", 1 => "1o", 2 => "2o", _ => $"suc {Ix(t - 1)}" };

    private static bool IsMutualOrNested(ConstInfo ind, Environment env) =>
        ind.NumNested > 0 || ind.BlockMembers.Count(m => env.Find(m)?.Kind == ConstKind.Inductive) > 1;

    /// <summary>A recursor of a nested block's auxiliary type: I.rec_1, I.rec_2, …</summary>
    private static bool IsAuxRecursorName(Name n) => System.Text.RegularExpressions.Regex.IsMatch($"{n}", @"\.rec_[0-9]+$");

    /// <summary>
    /// Define every type, constructor and recursor of a mutual or nested block (see the class summary). The types have
    /// no indices and are in Type; recursive fields are a type of the block at the block's own parameters.
    /// </summary>
    private void DefineBlock(ConstInfo ind)
    {
        Name n = ind.Name;
        ConstInfo first = env.Find(ind.BlockMembers.First(m => env.Find(m)?.Kind == ConstKind.Inductive))!;
        List<ConstInfo> originals = first.BlockMembers.Select(m => env.Find(m)).OfType<ConstInfo>().Where(c => c.Kind == ConstKind.Inductive).ToList();
        foreach (ConstInfo o in originals)
        {
            if (IsProposition(o))
            {
                throw new Refused($"{n} is a mutual or nested inductive proposition; not in the model yet");
            }
            if (o.NumIndices > 0)
            {
                throw new Refused($"{n} is a mutual or nested indexed inductive type; not in the model yet");
            }
            if (o.NumParams != first.NumParams)
            {
                throw new Refused($"{n}'s block has types with different numbers of parameters");
            }
            _ = Token(o.Name) ?? throw new Refused($"{o.Name}: the name has characters a set.mm token can't");
        }
        int np = first.NumParams;

        // The block as a plain mutual block: a nested block's auxiliary types come after the original ones.
        List<Replayer.BlockType> raw;
        List<Expr>? nestedParams = null;
        if (originals.Any(o => o.NumNested > 0))
        {
            var (err, types, ps0) = new Replayer(t, env).AuxiliaryBlock(first);
            raw = types ?? throw new Refused($"{n}: {err}");
            nestedParams = ps0;
        }
        else
        {
            raw = originals.Select(o => new Replayer.BlockType(o.Name, o.Type,
                o.Ctors.Select(c => (c, (env.Find(c) ?? throw new Refused($"{c} is not in the export")).Type, c)).ToList(), null)).ToList();
        }
        var recNames = new List<Name>();
        for (int k = 0; k < raw.Count; k++)
        {
            recNames.Add(k < originals.Count ? t.Str(originals[k].Name, "rec") : t.AppendIndexAfter(t.Str(first.Name, "rec"), (ulong)(k - originals.Count + 1)));
        }
        List<ConstInfo> recs = recNames.Select(r => env.Find(r) ?? throw new Refused($"{r} is not in the export")).ToList();
        foreach (ConstInfo r in recs)
        {
            _ = Token(r.Name) ?? throw new Refused($"{r.Name}: the name has characters a set.mm token can't");
        }
        foreach (ConstInfo o in originals)
        {
            foreach (Name c in o.Ctors)
            {
                _ = Token(c) ?? throw new Refused($"{c}: the name has characters a set.mm token can't");
            }
        }
        int nmotives = recs[0].NumMotives, nminors = recs[0].NumMinors;
        if (nmotives != raw.Count || nminors != raw.Sum(b => b.Ctors.Count) || recs.Any(r => r.NumMotives != nmotives || r.NumMinors != nminors || r.NumParams != np))
        {
            throw new Refused($"{n}'s recursors don't have one motive per type and one minor premise per constructor");
        }
        string itok = Token(first.Name)!;
        string steptok = itok + ".-mstep", casetok = itok + ".-mcase";
        var blockNames = new HashSet<Name>(raw.Select(b => b.Name), ReferenceEqualityComparer.Instance);
        bool Mentions(Expr e) => e switch
        {
            Const c => blockNames.Contains(c.Name),
            App a => Mentions(a.Fn) || Mentions(a.Arg),
            Binder b => Mentions(b.Domain) || Mentions(b.Body),
            Let l => Mentions(l.Type) || Mentions(l.Value) || Mentions(l.Body),
            Proj p => Mentions(p.Struct),
            _ => false,
        };
        int TypeOf(Expr ty, List<Expr> ps)
        {
            if (Ops.Spine(ty, out List<Expr> a) is Const h && blockNames.Contains(h.Name)
                && a.Count == ps.Count && a.Zip(ps).All(z => ReferenceEquals(z.First, z.Second)))
            {
                return raw.FindIndex(b => ReferenceEquals(b.Name, h.Name));
            }
            return -1;
        }

        // The step, over w = <. <. u , params >. , X >.: ( X u. every constructor's pairs <. ix , tag >. ).
        var info = new List<BlockTypeInfo>();
        var stepBound = new List<string>();
        var avoid = new HashSet<string>();
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = first.Type;
            var ps = Telescope(ref ty, np, sc, pfv);
            // Define the nested types first (List, Array), and keep the block's bound variables apart from theirs: the
            // computation rules substitute their fields into this step's parts, and bound the slices by their stages.
            foreach (Replayer.BlockType bt in raw.Where(b => b.Nested is not null))
            {
                Name jn = ((Const)Ops.Spine(bt.Nested!, out _)).Name;
                Define(jn);   // not its parameters: they mention this block's types, not yet defined
                string jtok = Token(jn)!;
                foreach (string tok in new[] { jtok, jtok + ".-step" }.Where(_values.ContainsKey))
                {
                    avoid.UnionWith(_values[tok].Split(' ').Where(SetVarSet.Contains));
                }
            }
            avoid.Remove(UniverseVar);
            sc.Active.AddRange(avoid.Where(x => !sc.Active.Contains(x)));
            const string hole = "ZZX";
            var parts = new List<string>();
            int minor = 0;
            for (int tt = 0; tt < raw.Count; tt++)
            {
                var ctors = new List<BlockCtor>();
                for (int j = 0; j < raw[tt].Ctors.Count; j++)
                {
                    (Name auxName, Expr cty, Name real) = raw[tt].Ctors[j];
                    Telescope(ref cty, np, sc, reuse: pfv);
                    var fs = new List<(string Var, string Dom)>();
                    var rf = new List<(int, int)>();
                    for (int k = 0; cty is Binder { IsPi: true } b; k++)
                    {
                        string dom;
                        int rt = TypeOf(b.Domain, pfv);
                        if (rt >= 0)
                        {
                            dom = $"( {hole} \" {{ {Ix(rt)} }} )";
                            rf.Add((k, rt));
                        }
                        else if (Mentions(b.Domain))
                        {
                            throw new Refused($"{real} has a recursive field that isn't a type of its block itself (not finitary); not in the model yet");
                        }
                        else
                        {
                            dom = Tr(b.Domain, sc);
                        }
                        string v = Fresh(sc, dom);
                        Expr fv = t.FVar(_fresh++);
                        sc.Vars[((FVar)fv).Id] = v;
                        sc.Types[((FVar)fv).Id] = b.Domain;
                        if (!sc.Bound.Contains(v))
                        {
                            sc.Bound.Add(v);
                        }
                        sc.Active.Add(v);
                        fs.Add((v, dom));
                        cty = _ops.Instantiate(b.Body, [fv]);
                    }
                    foreach (var f in fs)
                    {
                        sc.Active.Remove(f.Var);
                    }
                    ctors.Add(new BlockCtor(real, minor++, fs.Count, rf));
                    string part = $"{{ <. {Ix(tt)} , {Tag(j, Tuple(fs.Select(f => f.Var).ToList()))} >. }}";
                    parts.Add(fs.AsEnumerable().Reverse().Aggregate(part, (acc, f) => $"U_ {f.Var} e. {f.Dom} {acc}"));
                }
                info.Add(new BlockTypeInfo(Ix(tt), tt < originals.Count ? originals[tt] : null, raw[tt].Nested, recNames[tt], ctors));
            }
            string set = parts.Count == 0 ? "(/)" : parts.Skip(1).Aggregate(parts[0], (acc, p) => $"( {acc} u. {p} )");
            string body = $"( {hole} u. {set} )";
            string w = FirstVar(x => !sc.Bound.Contains(x) && !body.Split(' ').Contains(x) && !ps.Any(q => q.Var == x));
            var packed = new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList();
            body = Unpack(body, packed, $"( 1st ` {w} )");
            body = Subst(body, hole, $"( 2nd ` {w} )");
            stepBound.AddRange(sc.Bound.Where(x => x != UniverseVar && !ps.Any(q => q.Var == x)));
            stepBound.Add(w);
            EmitRaw(t.Of($"{first.Name}.-mstep"), steptok, $"( {w} e. _V |-> {body} )", stepBound, "mutual block's stage step, over a packed argument");
        }
        var block = new BlockInfo(steptok, casetok, info, np, nmotives, nminors, nestedParams);
        foreach (Name r in recNames)
        {
            _blocks[r] = block;
        }
        foreach (ConstInfo o in originals)
        {
            _blocks[o.Name] = block;
        }

        // Each original type: ( params |-> ( U_ k e. _om ( rec ( stepf , (/) ) ` k ) " { ix } ) ).
        for (int tt = 0; tt < originals.Count; tt++)
        {
            var sc = NewScope();
            Expr ty = originals[tt].Type;
            var ps = Telescope(ref ty, np, sc);
            string pack = Tuple(new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList());
            string x = FirstVar(v => !sc.Bound.Contains(v) && !stepBound.Contains(v) && !avoid.Contains(v));
            sc.Bound.Add(x);
            string k = FirstVar(v => !sc.Bound.Contains(v) && !stepBound.Contains(v) && !avoid.Contains(v));   // a slice may sit in a context the step's parts are simplified under
            sc.Bound.Add(k);
            string stepf = $"( {x} e. _V |-> ( {steptok} ` <. {pack} , {x} >. ) )";
            _defined.Add(originals[tt].Name);
            Emit(originals[tt].Name, Token(originals[tt].Name)!, Maps(ps, $"( U_ {k} e. _om ( rec ( {stepf} , (/) ) ` {k} ) \" {{ {Ix(tt)} }} )"), sc,
                "inductive type of a mutual or nested block");
        }

        // The constructors of the original types, as for other types (an auxiliary type's are the nested type's own).
        foreach (ConstInfo o in originals)
        {
            for (int j = 0; j < o.Ctors.Length; j++)
            {
                ConstInfo c = env.Find(o.Ctors[j])!;
                var sc = NewScope();
                Expr cty = c.Type;
                var ps = Telescope(ref cty, np, sc);
                var fs = Telescope(ref cty, c.NumFields, sc);
                _defined.Add(c.Name);
                Emit(c.Name, Token(c.Name)!, Maps(ps.Concat(fs), Tag(j, Tuple(fs.Select(f => f.Var).ToList()))), sc, "constructor");
            }
        }

        // The case analysis, over w = <. <. Q , a >. , f >. with Q = <. u , params , motives , minors >.: the tuple of
        // every type's case analysis on a, each minor premise given the fields and, for each recursive field r of type
        // t', component t' of f at r.
        int nb = np + nmotives + nminors;
        {
            var sc = NewScope();
            Expr rty = recs[0].Type;
            var bs = Telescope(ref rty, nb, sc);
            const string ha = "ZZA", hf = "ZZF";
            List<string> minors = bs.Skip(np + nmotives).Select(b => b.Var).ToList();
            string Minor(BlockCtor c, string x) =>
                c.Rec.Aggregate(
                    Enumerable.Range(0, c.NumFields).Aggregate(minors[c.Minor], (acc, k) => $"( {acc} ` {Field(x, k)} )"),
                    (acc, r) => $"( {acc} ` {Field($"( {hf} ` {Field(x, r.Field)} )", r.Type)} )");
            string Case(List<BlockCtor> cs, int j, string x) => cs.Count == 0 ? "(/)" : j == cs.Count - 1
                ? Minor(cs[j], $"( 2nd ` {x} )")
                : $"if ( ( 1st ` {x} ) = (/) , {Minor(cs[j], $"( 2nd ` {x} )")} , {Case(cs, j + 1, $"( 2nd ` {x} )")} )";
            string body = Tuple(info.Select(ti => Case(ti.Ctors, 0, ha)).ToList());
            string w = FirstVar(x => !body.Split(' ').Contains(x) && !bs.Any(q => q.Var == x) && x != UniverseVar);
            var packed = new[] { UniverseVar }.Concat(bs.Select(q => q.Var)).ToList();
            body = Unpack(body, packed, $"( 1st ` ( 1st ` {w} ) )");
            body = Subst(Subst(body, ha, $"( 2nd ` ( 1st ` {w} ) )"), hf, $"( 2nd ` {w} )");
            EmitRaw(t.Of($"{first.Name}.-mcase"), casetok, $"( {w} e. _V |-> {body} )", [w], "mutual block's case analysis, over a packed argument");
        }

        // The recursors: ( params |-> motives |-> minors |-> ( t e. ⟦major type⟧ |->
        //   component ix of ( frecs ( RankLt , _V , ( a e. _V , f e. _V |-> ( case ` <. <. Q , a >. , f >. ) ) ) ` t ) ) ).
        for (int tt = 0; tt < recs.Count; tt++)
        {
            var sc = NewScope();
            Expr rty = recs[tt].Type;
            var bs = Telescope(ref rty, nb + 1, sc);
            string major = bs[^1].Var;
            string q = Tuple(new[] { UniverseVar }.Concat(bs.Take(nb).Select(b => b.Var)).ToList());
            string a = PickRecursionVar(sc), f = PickRecursionVar(sc), rx = PickRecursionVar(sc), ry = PickRecursionVar(sc);
            string rel = $"{{ <. {rx} , {ry} >. | ( rank ` {rx} ) e. ( rank ` {ry} ) }}";
            string g = $"( {a} e. _V , {f} e. _V |-> ( {casetok} ` <. <. {q} , {a} >. , {f} >. ) )";
            _defined.Add(recs[tt].Name);
            Emit(recs[tt].Name, Token(recs[tt].Name)!, Maps(bs, Field($"( frecs ( {rel} , _V , {g} ) ` {major} )", tt)), sc, "recursor of a mutual or nested block");
        }
    }

    /// <summary>The computation rules of a recursor of a mutual or nested block: one for each of its constructors.</summary>
    public List<(Name Ctor, MmExpr Statement, List<string> Proof, string[] Distinct)> RecursorIotas(Name recName)
    {
        Define(recName);
        BlockInfo blk = _blocks.TryGetValue(recName, out BlockInfo? b) ? b : throw new Refused($"{recName} is not the recursor of a mutual or nested block");
        int tt = blk.Types.FindIndex(x => ReferenceEquals(x.Rec, recName));
        var r = new List<(Name, MmExpr, List<string>, string[])>();
        for (int j = 0; j < blk.Types[tt].Ctors.Count; j++)
        {
            var (s, p, d) = BlockIotaAt(blk, tt, j);
            r.Add((blk.Types[tt].Ctors[j].Real, s, p, d));
        }
        return r;
    }

    private (MmExpr Statement, List<string> Proof, string[] Distinct) BlockIota(Name typeName, Name ctorName)
    {
        BlockInfo blk = _blocks[typeName];
        int tt = blk.Types.FindIndex(x => x.Original is ConstInfo o && ReferenceEquals(o.Name, typeName));
        int j = blk.Types[tt].Ctors.FindIndex(c => ReferenceEquals(c.Real, ctorName));
        return BlockIotaAt(blk, tt, j);
    }

    /// <summary>Write lean-rankse (smaller rank is set-like on every set) into the output once.</summary>
    private void EnsureRankSe()
    {
        if (pr.Database.Statements.ContainsKey(Recursion.RankSeLabel))
        {
            return;
        }
        var (stmt, proof, distinct) = new Recursion(pr).RankSe();
        string text = $"""
            $( Smaller rank is set-like on every set: the recursors of mutual and nested blocks rest on it (frr2). $)
            {"${"}
              {string.Join(" ", distinct.Select(d => $"$d {d} $."))}
              {Recursion.RankSeLabel} $p {stmt} $=
                {string.Join(' ', proof)} $.
            {"$}"}

            """;
        _out.AppendLine(text);
        pr.Database.Extend(text);
    }

    /// <summary>
    /// The computation rule of constructor j of type tt of a block:
    /// I_tt.rec params motives minors (c params fields) = minor fields (I_t'.rec params motives minors r) for each
    /// recursive field r, of type t'.
    /// 1. The value is in the major premise's type. For an original type, that is its slice of the fixed point: the
    ///    pair &lt;. ix , tag &gt;. is in a stage after every recursive field's (eliun, lean-stagess, the step, rdgsuc),
    ///    and elimasng reads it back as a member of the slice.
    /// 2. frr2 unfolds the recursion once, over _V (lean-rankfr, lean-rankse).
    /// 3. The case analysis is evaluated on the tag, and component tt of the tuple read off (ovmpog, the simplifier).
    /// 4. The recursion at each recursive field r is component t' of the recursion there, which is I_t'.rec at r:
    ///    r has smaller rank than the value, so it is among its predecessors (elpredg, fvres).
    /// </summary>
    private (MmExpr Statement, List<string> Proof, string[] Distinct) BlockIotaAt(BlockInfo blk, int tt, int j)
    {
        BlockTypeInfo ti = blk.Types[tt];
        BlockCtor bc = ti.Ctors[j];
        ConstInfo ctor = env.Find(bc.Real)!;
        ConstInfo rec = env.Find(ti.Rec)!;
        Define(rec.Name);
        Define(ctor.Name);
        string ctok = Token(ctor.Name) ?? throw new Refused($"{ctor.Name}: the name has characters a set.mm token can't");
        string rtok = Token(rec.Name)!;
        int np = blk.NumParams, nb = np + blk.NumMotives + blk.NumMinors, nf = bc.NumFields;
        if (nb + nf > ClassVars.Length)
        {
            throw new Refused("more arguments than class variables");
        }
        List<string> recArgs = ClassVars.Take(nb).ToList(), ps = recArgs.Take(np).ToList();
        List<string> fields = ClassVars.Skip(nb).Take(nf).ToList();
        // An auxiliary type's constructors are the nested type's own (List.cons), at the nested occurrence's parameters.
        List<string> ctorParams = ti.Original is null ? NestedParams(blk, ti, ps) : ps;
        List<string> ctorArgs = ctorParams.Concat(fields).ToList();
        string v = ctorArgs.Aggregate($"( {ctok} ` U )", (acc, a) => $"( {acc} ` {a} )");

        List<string> rdoms = Domains(rtok, recArgs, nb);
        List<string> cdoms = Domains(ctok, ctorArgs, ctorArgs.Count);
        RefuseBinders(cdoms.Skip(ctorParams.Count).Select(d => ("", d)).ToList(), ctor.Name);
        List<string> paramHyps = ti.Original is null ? ctorParams.Select((a, i) => $"{a} e. {cdoms[i]}").ToList() : [];
        List<string> fieldHyps = fields.Select((a, i) => $"{a} e. {cdoms[ctorParams.Count + i]}").ToList();
        string ph = Conj(new[] { "U e. Univ" }.Concat(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}")).Concat(paramHyps).Concat(fieldHyps));
        Proof Pick(string ctx, string h) => Hyp(ctx, h) ?? throw new Refused($"no hypothesis {h}");
        List<string> baseHyps = new[] { "U e. Univ" }.Concat(ps.Select((a, i) => $"{a} e. {rdoms[i]}")).ToList();
        string small = Conj(baseHyps.Concat(paramHyps).Concat(fieldHyps));
        var extraVars = new List<string>();
        var toks = new List<string> { ctok, rtok, blk.StepTok, blk.CaseTok };

        // 1. Membership of the value in the major premise's type, under the parameters' and fields' hypotheses only.
        Proof eqV0, vInSmall;
        string tag;
        if (ti.Original is ConstInfo orig)
        {
            (eqV0, _, _) = Unfold(small, ctok, ctorArgs, (i, dom) => Pick(small, $"{ctorArgs[i]} e. {dom}"));
            tag = Rhs(eqV0);
            string itok = Token(orig.Name)!;
            toks.Add(itok);
            (Proof eqT0, _, _) = Unfold(small, itok, ps, (i, dom) => Pick(small, $"{ps[i]} e. {dom}"));
            string iapp = Lhs(eqT0), img = Rhs(eqT0);
            string fix = Part(img, "A");
            var bridges = new Dictionary<int, Proof>();
            Proof RInSlice(int field, int type)
            {
                string r = fields[field], dom = cdoms[ctorParams.Count + field];
                string slice = $"( {fix} \" {{ {blk.Types[type].Ix} }} )";
                if (blk.Types[type].Original is not null)
                {
                    return SliceOfOriginal(blk, small, fix, type, ps, r, dom, toks);
                }
                // A field of a nested type: its type is inside the auxiliary type's slice (BridgeNested), whose
                // nested type's parameters are in U, since the field's type is the nested type at them (elfvdm).
                List<string> nps = NestedParams(blk, blk.Types[type], ps);
                if (nps.Count != 1)
                {
                    throw new Refused($"{ctor.Name} has a field of a nested type with {nps.Count} parameters; not in the model's computation rules yet");
                }
                if (nps.Distinct().Count() != 1 || blk.Types.Where(x => x.Original is null).Any(x => NestedParams(blk, x, ps).Any(q => q != nps[0])))
                {
                    throw new Refused($"{ctor.Name}'s nested types have different parameters; not in the model's computation rules yet");
                }
                string jtok = Token(((Const)Ops.Spine(blk.Types[type].Nested!, out _)).Name)!;
                Proof inU = ParamInU(small, r, dom, jtok, nps[0]);
                string pdom = Domains(jtok, nps, 1)[0];
                string ctxB = Conj(baseHyps.Append($"{nps[0]} e. {pdom}"));
                Proof sub = BridgeNested(blk, ctxB, fix, type, ps, toks, extraVars, new HashSet<int>());
                if (_d.Split(sub.Proves).X != $"{dom} C_ {slice}")
                {
                    throw new InvalidOperationException($"the bridge is about {_d.Split(sub.Proves).X}, not {dom}");
                }
                Proof toB = _d.Jca(Restrict(small, Conj(baseHyps)), inU);
                return pr.Apply("sseldd", S(("ph", small), ("A", dom), ("B", slice), ("C", r)), _d.Syl(toB, sub), Pick(small, $"{r} e. {dom}"));
            }
            Proof pairIn = PairInFix(blk, small, fix, tt, j, fields, f => RInSlice(f, bc.Rec.First(x => x.Field == f).Type), extraVars);
            string pair = $"<. {ti.Ix} , {tag} >.";
            Proof tagInImg = pr.Apply("mpbird", S(("ph", small), ("ps", $"{tag} e. {img}"), ("ch", $"{pair} e. {fix}")), pairIn, ImgBi(small, fix, ti.Ix, tag));
            Proof tagIn = pr.Apply("eleqtrrd", S(("ph", small), ("A", tag), ("B", img), ("C", iapp)), tagInImg, eqT0);
            vInSmall = pr.Apply("eqeltrd", S(("ph", small), ("A", v), ("B", tag), ("C", iapp)), eqV0, tagIn);
        }
        else
        {
            // The nested type's own constructor, in the nested type at its parameters.
            Name jn = ((Const)Ops.Spine(ti.Nested!, out _)).Name;
            ConstInfo jind = env.Find(jn)!;
            string jtok = Token(jn)!;
            toks.Add(jtok);
            int jj = Array.IndexOf(jind.Ctors, ctor.Name);
            if (_recursive.TryGetValue(jtok, out RecursiveInfo? jinfo))
            {
                toks.Add(jinfo.StepTok);
                (eqV0, tag, _, vInSmall) = RecursiveMembership(small, ctok, jtok, jinfo, jj, jind.Ctors.Length, ctorParams, fields, extraVars);
            }
            else if (!jind.IsRec && !IsMutualOrNested(jind, env))
            {
                (eqV0, _, _) = Unfold(small, ctok, ctorArgs, (i, dom) => Pick(small, $"{ctorArgs[i]} e. {dom}"));
                tag = Rhs(eqV0);
                (Proof eqT, _, _) = Unfold(small, jtok, ctorParams, (i, dom) => Pick(small, $"{ctorParams[i]} e. {dom}"));
                Proof inSet = MemberUnion(small, tag, Rhs(eqT), jind.Ctors.Length, jj, fields, (_, h) => Pick(small, h));
                Proof iff = pr.Apply("eleq12d", S(("ph", small), ("A", v), ("B", tag), ("C", Lhs(eqT)), ("D", Rhs(eqT))), eqV0, eqT);
                vInSmall = pr.Apply("mpbird", S(("ph", small), ("ps", $"{v} e. {Lhs(eqT)}"), ("ch", $"{tag} e. {Rhs(eqT)}")), inSet, iff);
            }
            else
            {
                throw new Refused($"{rec.Name}: the nested type {jn} is itself mutual, nested or indexed; not in the model's computation rules yet");
            }
        }
        Proof inType = _d.Syl(Restrict(ph, small), vInSmall);
        Proof eqV = _d.Syl(Restrict(ph, small), eqV0);

        // 2. frr2, over _V.
        (Proof eqR, _, _) = Unfold(ph, rtok, recArgs.Append(v).ToList(), (i, dom) => i < nb ? Pick(ph, $"{recArgs[i]} e. {dom}") : inType);
        string comp = Rhs(eqR);   // component tt of ( F ` v )
        string frApp = $"( {FrecsOf(comp)} ` {v} )";
        string fr = FrecsOf(comp);
        string rel = Part(fr, "R"), caseApp = Part(fr, "F");
        string rx = Part(rel, "x"), ry = Part(rel, "y");
        EnsureRankFr();
        EnsureRankSe();
        Proof frOk = _d.Lift(ph, pr.Apply("lean-rankfr", S(("x", rx), ("y", ry), ("A", "_V"))));
        Proof seOk = _d.Lift(ph, pr.Apply(Recursion.RankSeLabel, S(("x", rx), ("y", ry))));
        Proof frEq = pr.Apply("eqid", S(("A", fr)));
        Proof vSet = Exists(ph, v);
        Proof once = _d.Syl(_d.Jca(_d.Jca(frOk, seOk), vSet),
            pr.Apply("frr2", S(("R", rel), ("A", "_V"), ("G", caseApp), ("X", v), ("F", fr)), frEq));
        string pred = $"Pred ( {rel} , _V , {v} )";
        string g = $"( {fr} |` {pred} )";
        Proof cur = _d.Trans(eqR, _d.Congruence("class", comp.Replace(frApp, "Z", StringComparison.Ordinal), "Z", once));

        // 3. The case analysis at the value.
        string a0 = Part(caseApp, "x"), f0 = Part(caseApp, "y"), body0 = Part(caseApp, "C");
        var used = (fr + " " + v + " " + ph).Split(' ').ToHashSet();
        string a = FirstVar(x => !used.Contains(x) && x != a0 && x != f0);
        string f = FirstVar(x => !used.Contains(x) && x != a0 && x != f0 && x != a);
        extraVars.AddRange([a, f]);
        string bodyA = Subst(body0, a0, a), body = Subst(bodyA, f0, f);
        string mpo = $"( {a} e. _V , {f} e. _V |-> {body} )";
        Proof ren2 = pr.Apply("cbvmpov", S(("x", a0), ("y", f0), ("z", a), ("w", f), ("A", "_V"), ("B", "_V"), ("C", body0), ("E", bodyA), ("D", body)),
            _d.Congruence("class", Subst(body0, a0, "Z"), "Z", pr.Apply("id", S(("ph", $"{a0} = {a}")))),
            _d.Congruence("class", Subst(bodyA, f0, "Z"), "Z", pr.Apply("id", S(("ph", $"{f0} = {f}")))));
        string atV = Subst(body, a, v), atVg = Subst(atV, f, g);
        string ovText = $"( {v} {caseApp} {g} )";
        Proof toMpo = pr.Apply("oveqd", S(("ph", ph), ("A", caseApp), ("B", mpo), ("C", v), ("D", g)), _d.Lift(ph, ren2));
        Proof h1 = _d.Congruence("class", Subst(body, a, "Z"), "Z", pr.Apply("id", S(("ph", $"{a} = {v}"))));
        Proof h2 = _d.Congruence("class", Subst(atV, f, "Z"), "Z", pr.Apply("id", S(("ph", $"{f} = {g}"))));
        Proof frFn = _d.Syl(_d.Jca(frOk, seOk), pr.Apply("frr1", S(("R", rel), ("A", "_V"), ("G", caseApp), ("F", fr)), frEq));
        Proof predSet = _d.Syl(_d.Jca(vSet, seOk), pr.Apply("setlikespec", S(("X", v), ("A", "_V"), ("R", rel))));
        Proof gSet = _d.Syl(_d.Jca(_d.Syl(frFn, pr.Apply("fnfun", S(("F", fr), ("A", "_V")))), predSet),
            pr.Apply("resfunexg", S(("A", fr), ("B", pred), ("C", "_V"))));
        _known[(ph, g)] = gSet;
        Proof ov = _d.Syl(pr.Apply("3jca", S(("ph", ph), ("ps", $"{v} e. _V"), ("ch", $"{g} e. _V"), ("th", $"{atVg} e. _V")),
                vSet, gSet, Exists(ph, atVg)),
            pr.Apply("ovmpog", S(("x", a), ("y", f), ("A", v), ("B", g), ("C", "_V"), ("D", "_V"), ("R", body), ("G", atV), ("S", atVg), ("F", mpo), ("H", "_V")),
                h1, h2, pr.Apply("eqid", S(("A", mpo)))));
        Proof caseEq = _d.Trans(_d.Trans(toMpo, ov), UnfoldRaw(ph, blk.CaseTok, Part(atVg, "A")));
        string ctxOv = Rhs(cur).Replace(ovText, "Z", StringComparison.Ordinal);
        cur = _d.Trans(cur, _d.Congruence("class", ctxOv, "Z", caseEq));
        if (Simp(ph, Rhs(cur)) is Proof simp0)
        {
            cur = _d.Trans(cur, simp0);
        }
        const string gHole = "ZZG";
        string ctxTag = Rhs(cur).Replace(g, gHole, StringComparison.Ordinal).Replace(v, "Z", StringComparison.Ordinal).Replace(gHole, g, StringComparison.Ordinal);
        if (ctxTag.Split(' ').Contains("Z"))
        {
            cur = _d.Trans(cur, _d.Congruence("class", ctxTag, "Z", eqV));
        }
        if (Simp(ph, Rhs(cur)) is Proof simp)
        {
            cur = _d.Trans(cur, simp);
        }

        // 4. The recursion at each recursive field is the recursor of its type there.
        string minor = recArgs[np + blk.NumMotives + bc.Minor];
        string want = fields.Aggregate(minor, (acc, x) => $"( {acc} ` {x} )");
        foreach (var (field, type) in bc.Rec)
        {
            string r = fields[field];
            ConstInfo rrec = env.Find(blk.Types[type].Rec)!;
            string rrtok = Token(rrec.Name)!;
            toks.Add(rrtok);
            Proof rankLt = pr.Apply("eleqtrrd", S(("ph", ph), ("A", $"( rank ` {r} )"), ("B", $"( rank ` {tag} )"), ("C", $"( rank ` {v} )")),
                RankChain(ph, r, tag), pr.Apply("fveq2d", S(("ph", ph), ("A", v), ("B", tag), ("F", "rank")), eqV));
            Proof brBi = _d.Syl(_d.Jca(Exists(ph, r), vSet), Brabga(rx, ry, r, v, rel));
            Proof isR = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{r} {rel} {v}"), ("ch", $"( rank ` {r} ) e. ( rank ` {v} )")), rankLt, brBi);
            Proof predBi = _d.Syl(_d.Jca(vSet, Exists(ph, r)), pr.Apply("elpredg", S(("X", v), ("B", "_V"), ("Y", r), ("A", "_V"), ("R", rel))));
            Proof inPred = pr.Apply("mpbird", S(("ph", ph), ("ps", $"{r} e. {pred}"), ("ch", $"{r} {rel} {v}")), isR, predBi);
            Proof e1 = _d.Syl(inPred, pr.Apply("fvres", S(("A", r), ("B", pred), ("F", fr))));
            (Proof back, _, _) = Unfold(ph, rrtok, recArgs.Append(r).ToList(), (i, dom) => Pick(ph, $"{(i < nb ? recArgs[i] : r)} e. {dom}"));
            string here = Field($"( {g} ` {r} )", type);
            if (Rhs(back) != Field($"( {fr} ` {r} )", type))
            {
                throw new InvalidOperationException($"{rrec.Name} at {r} is {Rhs(back)}, not component {type} of {fr} there");
            }
            Proof e = _d.Trans(_d.Congruence("class", Field("Z", type), "Z", e1), _d.Symm(back));
            string ctxText = Rhs(cur).Replace(here, "Z", StringComparison.Ordinal);
            cur = _d.Trans(cur, _d.Congruence("class", ctxText, "Z", e));
            want = $"( {want} ` {Lhs(back)} )";
        }
        if (Rhs(cur) != want)
        {
            throw new InvalidOperationException($"the computation rule came out as {Rhs(cur)}, not {want}");
        }
        string[] dv = DistinctFor(toks.Distinct(), recArgs.Concat(fields));
        return (cur.Proves, cur.Proof, [string.Join(' ', $"{dv[0]} {string.Join(' ', extraVars)}".Split(' ', StringSplitOptions.RemoveEmptyEntries).Distinct())]);
    }

    /// <summary>The frecs term inside a recursor's value: component t of ( frecs ( … ) ` major ) is 1st of 2nd … of it.</summary>
    private string FrecsOf(string comp)
    {
        string cur = comp;
        while (pr.Parse("class", cur.Split(' ')) is SyntaxTree { Rule.Label: "cfv" } n)
        {
            string fn = pr.Render(n.Children[1]), arg = pr.Render(n.Children[0]);
            if (fn is "1st" or "2nd")
            {
                cur = arg;
                continue;
            }
            return pr.Parse("class", fn.Split(' ')) is SyntaxTree { Rule.Label: "cfrecs" } ? fn : throw new InvalidOperationException($"no frecs in {comp}");
        }
        throw new InvalidOperationException($"no frecs in {comp}");
    }

    // ---- membership in a block's fixed point ----------------------------------------------------------------------

    /// <summary>( ctx -> ( B e. ( A " { ix } ) <-> <. ix , B >. e. A ) ), by elimasng.</summary>
    private Proof ImgBi(string ctx, string a, string ix, string x) =>
        _d.Syl(_d.Jca(Exists(ctx, ix), Exists(ctx, x)), pr.Apply("elimasng", S(("A", a), ("B", ix), ("C", x), ("V", "_V"), ("W", "_V"))));

    /// <summary>
    /// The parameters of the nested type an auxiliary type stands for (List's α := Rose A), as classes over the block's
    /// parameters <paramref name="ps"/>.
    /// </summary>
    private List<string> NestedParams(BlockInfo blk, BlockTypeInfo ti, List<string> ps)
    {
        Ops.Spine(ti.Nested!, out List<Expr> args);
        var vars = new Dictionary<ulong, string>();
        for (int i = 0; i < ps.Count; i++)
        {
            vars[((FVar)blk.NestedParams![i]).Id] = ps[i];
        }
        return args.Select(a => Class(a, "U", vars)).ToList();
    }

    /// <summary>( ctx -> r e. ( fix " { ix } ) ) from the hypothesis r e. dom, where dom is original type t of the block.</summary>
    private Proof SliceOfOriginal(BlockInfo blk, string ctx, string fix, int type, List<string> ps, string r, string dom, List<string> toks)
    {
        string otok = Token(blk.Types[type].Original!.Name)!;
        toks.Add(otok);
        (Proof eqO, _, _) = Unfold(ctx, otok, ps, (i, d) => Hyp(ctx, $"{ps[i]} e. {d}") ?? throw new Refused($"no hypothesis {ps[i]} e. {d}"));
        if (Lhs(eqO) != dom || Part(Rhs(eqO), "A") != fix)
        {
            throw new InvalidOperationException($"{r}'s domain {dom} is not the slice {Rhs(eqO)} of {fix}");
        }
        Proof h = Hyp(ctx, $"{r} e. {dom}") ?? throw new Refused($"no hypothesis {r} e. {dom}");
        return pr.Apply("eleqtrd", S(("ph", ctx), ("A", r), ("B", dom), ("C", Rhs(eqO))), h, eqO);
    }

    /// <summary>
    /// ( ctx -> P e. U ) from the hypothesis r e. ( ( jtok ` U ) ` P ): a function value at P has P in its domain
    /// (elfvdm), and ( jtok ` U ) is a map over U (dmmptss).
    /// </summary>
    private Proof ParamInU(string ctx, string r, string dom, string jtok, string p)
    {
        string fn = $"( {jtok} ` U )";
        Proof h = Hyp(ctx, $"{r} e. {dom}") ?? throw new Refused($"no hypothesis {r} e. {dom}");
        Proof inDm = _d.Syl(h, pr.Apply("elfvdm", S(("A", r), ("F", fn), ("B", p))));
        (Proof eqF, _, _) = Unfold(ctx, jtok, [], (_, _) => throw new InvalidOperationException());
        string mpt = Rhs(eqF);
        SyntaxTree m = pr.Parse("class", mpt.Split(' '))!;
        string x = pr.Render(m.Children[0]), d = pr.Render(m.Children[1]), b = pr.Render(m.Children[2]);
        Proof dmEq = pr.Apply("dmeqd", S(("ph", ctx), ("A", fn), ("B", mpt)), eqF);
        Proof inDm2 = pr.Apply("eleqtrd", S(("ph", ctx), ("A", p), ("B", $"dom {fn}"), ("C", $"dom {mpt}")), inDm, dmEq);
        Proof ss = _d.Lift(ctx, pr.Apply("dmmptss", S(("x", x), ("A", d), ("B", b), ("F", mpt)), pr.Apply("eqid", S(("A", mpt)))));
        return pr.Apply("sseldd", S(("ph", ctx), ("A", $"dom {mpt}"), ("B", d), ("C", p)), ss, inDm2);
    }

    /// <summary>
    /// ( ctx -> <. ix_s , tag >. e. Fix ) for constructor j of type s of the block, at the field terms <paramref name="fields"/>:
    /// each recursive field r, of type t', is in its slice ( Fix " { ix_t' } ) by <paramref name="rInSlice"/>, so in
    /// some stage (eliun, elimasng); all of them are in one stage b (lean-stagess), and the pair is in the next
    /// (the step's equation, rdgsuc), so in Fix (ssiun2s). The non-recursive fields' hypotheses are in ctx.
    /// </summary>
    private Proof PairInFix(BlockInfo blk, string ctx, string fix, int s, int j, List<string> fields, Func<int, Proof> rInSlice, List<string> extraVars)
    {
        BlockTypeInfo ti = blk.Types[s];
        BlockCtor bc = ti.Ctors[j];
        Proof Pick(string c, string h) => Hyp(c, h) ?? throw new Refused($"no hypothesis {h}");
        string k = Part(fix, "x"), stageBody = Part(fix, "B");
        string Stage(string x) => Subst(stageBody, k, x);
        string stepApp = Part(Part(Stage("(/)"), "F"), "F");
        int totalParts = blk.Types.Sum(x => x.Ctors.Count);
        string tag = Tag(j, Tuple(fields));
        string pair = $"<. {ti.Ix} , {tag} >.";

        Proof StepAt(string c, string sb) => StepAtOf(c, stepApp, blk.StepTok, sb, extraVars);

        Proof PairInStage(string c, string b, Proof bInOm, Func<int, Proof> rIn)
        {
            string sb = Stage(b);
            Proof eqStep = StepAt(c, sb);
            string un = Rhs(eqStep);
            string fsb = Part(un, "B");
            var recIdx = bc.Rec.Select(r => r.Field).ToList();
            Proof inF = MemberUnion(c, pair, fsb, totalParts, bc.Minor, fields, (kk, h) => recIdx.Contains(kk) ? rIn(kk) : Pick(c, h));
            Proof inUn = _d.Syl(inF, pr.Apply("elun2", S(("A", pair), ("B", fsb), ("C", sb))));
            Proof inStep = pr.Apply("eleqtrrd", S(("ph", c), ("A", pair), ("B", un), ("C", Lhs(eqStep))), inUn, eqStep);
            Proof rdg = _d.Syl(_d.Syl(bInOm, pr.Apply("nnon", S(("A", b)))), pr.Apply("rdgsuc", S(("B", b), ("F", stepApp), ("A", "(/)"))));
            string sucStage = Stage($"suc {b}");
            Proof inSuc = pr.Apply("eleqtrrd", S(("ph", c), ("A", pair), ("B", Lhs(eqStep)), ("C", sucStage)), inStep, rdg);
            Proof sub = _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = suc {b}"))));
            Proof incl = pr.Apply("ssiun2s", S(("x", k), ("A", "_om"), ("B", stageBody), ("C", $"suc {b}"), ("D", sucStage)), sub);
            Proof sub2 = _d.Syl(_d.Syl(bInOm, pr.Apply("peano2", S(("A", b)))), incl);
            Proof imp = pr.Apply("sseld", S(("ph", c), ("A", sucStage), ("B", fix), ("C", pair)), sub2);
            return pr.Apply("mpd", S(("ph", c), ("ps", $"{pair} e. {sucStage}"), ("ch", $"{pair} e. {fix}")), inSuc, imp);
        }

        if (bc.Rec.Count == 0)
        {
            return PairInStage(ctx, "(/)", _d.Lift(ctx, pr.Apply("peano1", S())), _ => throw new InvalidOperationException());
        }
        var stepVars = _values[blk.StepTok].Split(' ').ToHashSet();
        var taken = new HashSet<string>(fix.Split(' ').Concat(ctx.Split(' ')).Concat(stepApp.Split(' ')).Concat(stepVars).Concat(fields)) { k };
        string FreshVar() { string x = FirstVar(y => !taken.Contains(y)); taken.Add(x); extraVars.Add(x); return x; }
        var ms = new List<string>();
        var somes = new List<Proof>();
        var ctxs = new List<string> { ctx };
        var opairs = new List<string>();
        foreach (var (field, type) in bc.Rec)
        {
            string r = fields[field], ix = blk.Types[type].Ix, m = FreshVar();
            string op = $"<. {ix} , {r} >.";
            opairs.Add(op);
            Proof inImg = rInSlice(field);
            string slice = $"( {fix} \" {{ {ix} }} )";
            Proof inFix = pr.Apply("mpbid", S(("ph", ctx), ("ps", $"{r} e. {slice}"), ("ch", $"{op} e. {fix}")), inImg, ImgBi(ctx, fix, ix, r));
            string setM = $"U_ {m} e. _om {Stage(m)}";
            Proof ren = pr.Apply("cbviunv", S(("x", k), ("y", m), ("A", "_om"), ("B", stageBody), ("C", Stage(m))),
                _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = {m}")))));
            Proof inSetM = pr.Apply("eleqtrd", S(("ph", ctx), ("A", op), ("B", fix), ("C", setM)), inFix, _d.Lift(ctx, ren));
            Proof some = pr.Apply("sylib", S(("ph", ctx), ("ps", $"{op} e. {setM}"), ("ch", $"E. {m} e. _om {op} e. {Stage(m)}")),
                inSetM, pr.Apply("eliun", S(("A", op), ("x", m), ("B", "_om"), ("C", Stage(m)))));
            somes.Add(ctxs.Count == 1 ? some : _d.Syl(Restrict(ctxs[^1], ctx), some));
            ms.Add(m);
            ctxs.Add($"( ( {ctxs[^1]} /\\ {m} e. _om ) /\\ {op} e. {Stage(m)} )");
        }
        string top = ctxs[^1];
        var bs = new List<string> { ms[0] };
        Proof bOm = Pick(top, $"{ms[0]} e. _om");
        for (int i = 1; i < ms.Count; i++)
        {
            bs.Add($"( {bs[^1]} u. {ms[i]} )");
            bOm = _d.Syl(_d.Jca(bOm, Pick(top, $"{ms[i]} e. _om")), pr.Apply("omun", S(("A", bs[^2]), ("B", ms[i]))));
        }
        string b = bs[^1];
        Proof SsB(int i, int level) => i == level
            ? (level == 0 ? pr.Apply("ssid", S(("A", ms[0]))) : pr.Apply("ssun2", S(("A", ms[i]), ("B", bs[level - 1]))))
            : pr.Apply("sstri", S(("A", ms[i]), ("B", bs[level - 1]), ("C", bs[level])),
                SsB(i, level - 1), pr.Apply("ssun1", S(("A", bs[level - 1]), ("B", ms[level]))));
        Proof? grows = null;
        Proof RIn(int field)
        {
            int i = bc.Rec.FindIndex(x => x.Field == field);
            string r = fields[field], ix = blk.Types[bc.Rec[i].Type].Ix, op = opairs[i];
            Proof here = Pick(top, $"{op} e. {Stage(ms[i])}");
            if (ms.Count > 1)
            {
                if (grows is null)
                {
                    EnsureStageSs();
                    string z = FreshVar();
                    Proof eqZ = StepAt(ctx, z);
                    grows = pr.Apply("sseqtrrd", S(("ph", ctx), ("A", z), ("B", Rhs(eqZ)), ("C", Lhs(eqZ))),
                        _d.Lift(ctx, pr.Apply("ssun1", S(("A", z), ("B", Part(Rhs(eqZ), "B"))))), eqZ);
                }
                string z0 = _d.Split(grows.Value.Proves).X.Split(' ')[0];
                Proof mono = pr.Apply(Recursion.StageSsLabel, S(("ph", ctx), ("z", z0), ("F", stepApp), ("A", "(/)"), ("M", b), ("N", ms[i])), grows.Value);
                Proof ante = _d.Jca(_d.Jca(bOm, Pick(top, $"{ms[i]} e. _om")), _d.Lift(top, SsB(i, ms.Count - 1)));
                Proof ss = pr.Apply("mpd", S(("ph", top), ("ps", ctx), ("ch", $"{Stage(ms[i])} C_ {Stage(b)}")),
                    Restrict(top, ctx), _d.Syl(ante, mono));
                Proof imp = pr.Apply("sseld", S(("ph", top), ("A", Stage(ms[i])), ("B", Stage(b)), ("C", op)), ss);
                here = pr.Apply("mpd", S(("ph", top), ("ps", $"{op} e. {Stage(ms[i])}"), ("ch", $"{op} e. {Stage(b)}")), here, imp);
            }
            string sl = $"( {Stage(b)} \" {{ {ix} }} )";
            return pr.Apply("mpbird", S(("ph", top), ("ps", $"{r} e. {sl}"), ("ch", $"{op} e. {Stage(b)}")), here, ImgBi(top, Stage(b), ix, r));
        }
        Proof pairIn = PairInStage(top, b, bOm, RIn);
        for (int i = ms.Count - 1; i >= 0; i--)
        {
            string m = ms[i];
            Proof lim = pr.Apply("rexlimdva2", S(("ph", ctxs[i]), ("x", m), ("A", "_om"), ("ps", $"{opairs[i]} e. {Stage(m)}"), ("ch", $"{pair} e. {fix}")), pairIn);
            pairIn = pr.Apply("mpd", S(("ph", ctxs[i]), ("ps", $"E. {m} e. _om {opairs[i]} e. {Stage(m)}"), ("ch", $"{pair} e. {fix}")), somes[i], lim);
        }
        return pairIn;
    }

    /// <summary>
    /// ( ctx -> ⟦J P⟧ C_ ( Fix " { ix_s } ) ) for auxiliary type s, which stands for the nested type J at P: every value
    /// of the nested type is a value of its auxiliary type. ctx holds U e. Univ, the block's parameters' hypotheses and
    /// P e. U.
    /// - J not recursive (Array, Option): each constructor's part U_ fields { tag } is in the slice (iunssd, snssd),
    ///   since &lt;. ix_s , tag &gt;. is in Fix (<see cref="PairInFix"/>).
    /// - J recursive (List): by induction over J's stages (finds): stage (/) is empty (rdg0), and if stage y is in the
    ///   slice, so is stage suc y, the step at stage y (rdgsuc), whose recursive fields range over stage y.
    /// A field of an original type of the block is in that type's slice by its definition; a field of another nested
    /// type, by that type's bridge.
    /// </summary>
    private Proof BridgeNested(BlockInfo blk, string ctx, string fix, int s, List<string> ps, List<string> toks, List<string> extraVars, HashSet<int> visiting)
    {
        if (!visiting.Add(s))
        {
            throw new Refused("nested types that contain each other; not in the model's computation rules yet");
        }
        BlockTypeInfo st = blk.Types[s];
        Name jn = ((Const)Ops.Spine(st.Nested!, out _)).Name;
        ConstInfo jind = env.Find(jn)!;
        string jtok = Token(jn)!;
        toks.Add(jtok);
        List<string> pj = NestedParams(blk, st, ps);
        Proof Pick(string c, string h) => Hyp(c, h) ?? throw new Refused($"no hypothesis {h}");
        (Proof eqJ, _, _) = Unfold(ctx, jtok, pj, (i, dom) => Pick(ctx, $"{pj[i]} e. {dom}"));
        string val = Rhs(eqJ);
        string SliceOf(int type) => $"( {fix} \" {{ {blk.Types[type].Ix} }} )";
        string slice = SliceOf(s);
        (string Ctx2, string Stage, Proof Ih)? ih = null;

        Proof RecIn(string c, string var, string dom, int type)
        {
            Proof h = Pick(c, $"{var} e. {dom}");
            if (ih is var (ctx2, stage, ihp) && dom == stage && type == s)
            {
                return pr.Apply("sseldd", S(("ph", c), ("A", dom), ("B", slice), ("C", var)), _d.Syl(Restrict(c, ctx2), ihp), h);
            }
            if (blk.Types[type].Original is not null)
            {
                return SliceOfOriginal(blk, c, fix, type, ps, var, dom, toks);
            }
            Proof sub = BridgeNested(blk, ctx, fix, type, ps, toks, extraVars, visiting);
            if (_d.Split(sub.Proves).X != $"{dom} C_ {SliceOf(type)}")
            {
                throw new InvalidOperationException($"the bridge is about {_d.Split(sub.Proves).X}, not {dom}");
            }
            return pr.Apply("sseldd", S(("ph", c), ("A", dom), ("B", SliceOf(type)), ("C", var)), _d.Syl(Restrict(c, ctx), sub), h);
        }

        Proof PartSub(string c, string part, int jj, List<string> vars, List<string> doms)
        {
            SyntaxTree n = pr.Parse("class", part.Split(' '))!;
            if (n.Rule.Label == "csn")
            {
                string tag = pr.Render(n.Children[0]);
                if (tag != Tag(jj, Tuple(vars)))
                {
                    throw new InvalidOperationException($"{jn}'s constructor {jj} is {tag}, not {Tag(jj, Tuple(vars))}");
                }
                BlockCtor bc2 = st.Ctors[jj];
                Proof pairIn = PairInFix(blk, c, fix, s, jj, vars, f => RecIn(c, vars[f], doms[f], bc2.Rec.First(r => r.Field == f).Type), extraVars);
                Proof tagIn = pr.Apply("mpbird", S(("ph", c), ("ps", $"{tag} e. {slice}"), ("ch", $"<. {st.Ix} , {tag} >. e. {fix}")), pairIn, ImgBi(c, fix, st.Ix, tag));
                return pr.Apply("snssd", S(("ph", c), ("A", tag), ("B", slice)), tagIn);
            }
            if (n.Rule.Label != "ciun")
            {
                throw new InvalidOperationException($"expected a constructor's part of {jn}, got {part}");
            }
            string x = pr.Render(n.Children[0]), d = pr.Render(n.Children[1]), b = pr.Render(n.Children[2]);
            Proof inner = PartSub($"( {c} /\\ {x} e. {d} )", b, jj, [.. vars, x], [.. doms, d]);
            return pr.Apply("iunssd", S(("ph", c), ("x", x), ("A", d), ("B", b), ("C", slice)), inner);
        }

        Proof PartsSub(string c, string set, int count)
        {
            if (count == 1)
            {
                return PartSub(c, set, 0, [], []);
            }
            SyntaxTree u = pr.Parse("class", set.Split(' '))!;
            string left = pr.Render(u.Children[0]), right = pr.Render(u.Children[1]);
            return pr.Apply("unssd", S(("ph", c), ("A", left), ("B", right), ("C", slice)), PartsSub(c, left, count - 1), PartSub(c, right, count - 1, [], []));
        }

        Proof sub;
        if (_recursive.TryGetValue(jtok, out RecursiveInfo? jinfo))
        {
            toks.Add(jinfo.StepTok);
            string kJ = Part(val, "x"), lsBody = Part(val, "B");
            string LS(string x) => Subst(lsBody, kJ, x);
            string stepAppJ = Part(Part(LS("(/)"), "F"), "F");
            var avoid = new HashSet<string>(ctx.Split(' ').Concat(val.Split(' ')).Concat(slice.Split(' ')).Concat(_values[jinfo.StepTok].Split(' ')).Concat(_values[blk.StepTok].Split(' ')));   // the block's step is simplified under Phi(y)
            string x = FirstVar(q => !avoid.Contains(q));
            avoid.Add(x);
            string y = FirstVar(q => !avoid.Contains(q));
            extraVars.AddRange([x, y]);
            string Phi(string n) => $"( {ctx} -> {LS(n)} C_ {slice} )";

            // Stage (/) is empty.
            Proof base_ = _d.Lift(ctx, pr.Apply("eqsstri", S(("A", LS("(/)")), ("B", "(/)"), ("C", slice)),
                pr.Apply("rdg0", S(("F", stepAppJ), ("A", "(/)")), pr.Apply("0ex", S())), pr.Apply("0ss", S(("A", slice)))));

            // From stage y to stage suc y, under ( ( ctx /\ y e. _om ) /\ Phi(y) ).
            string ctx2 = $"( ( {ctx} /\\ {y} e. _om ) /\\ {Phi(y)} )";
            Proof ihp = pr.Apply("mpd", S(("ph", ctx2), ("ps", ctx), ("ch", $"{LS(y)} C_ {slice}")), Restrict(ctx2, ctx), Pick(ctx2, Phi(y)));
            ih = (ctx2, LS(y), ihp);
            Proof eqStep = StepAtOf(ctx2, stepAppJ, jinfo.StepTok, LS(y), extraVars);
            string un = Rhs(eqStep);
            Proof unSub = pr.Apply("unssd", S(("ph", ctx2), ("A", LS(y)), ("B", Part(un, "B")), ("C", slice)), ihp, PartsSub(ctx2, Part(un, "B"), jind.Ctors.Length));
            Proof s1 = pr.Apply("eqsstrd", S(("ph", ctx2), ("A", Lhs(eqStep)), ("B", un), ("C", slice)), eqStep, unSub);
            Proof rdg = _d.Syl(_d.Syl(Pick(ctx2, $"{y} e. _om"), pr.Apply("nnon", S(("A", y)))), pr.Apply("rdgsuc", S(("B", y), ("F", stepAppJ), ("A", "(/)"))));
            Proof s2 = pr.Apply("eqsstrd", S(("ph", ctx2), ("A", LS($"suc {y}")), ("B", Lhs(eqStep)), ("C", slice)), rdg, s1);
            Proof e3 = pr.Apply("exp31", S(("ph", ctx), ("ps", $"{y} e. _om"), ("ch", Phi(y)), ("th", $"{LS($"suc {y}")} C_ {slice}")), s2);
            Proof stepP = pr.Apply("com3l", S(("ph", ctx), ("ps", $"{y} e. _om"), ("ch", Phi(y)), ("th", $"{LS($"suc {y}")} C_ {slice}")), e3);
            Proof Eq(string to) => _d.Congruence("wff", Phi("Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {to}"))));
            Proof all = pr.Apply("finds", S(("x", x), ("y", y), ("ph", Phi(x)), ("ps", Phi("(/)")), ("ch", Phi(y)), ("th", Phi($"suc {y}")), ("ta", Phi(kJ)), ("A", kJ)),
                Eq("(/)"), Eq(y), Eq($"suc {y}"), Eq(kJ), base_, stepP);
            Proof each = pr.Apply("impcom", S(("ph", $"{kJ} e. _om"), ("ps", ctx), ("ch", $"{LS(kJ)} C_ {slice}")), all);
            sub = pr.Apply("iunssd", S(("ph", ctx), ("x", kJ), ("A", "_om"), ("B", lsBody), ("C", slice)), each);
        }
        else if (!jind.IsRec && !IsMutualOrNested(jind, env))
        {
            sub = PartsSub(ctx, val, jind.Ctors.Length);
        }
        else
        {
            throw new Refused($"the nested type {jn} is itself mutual, nested or indexed; not in the model's computation rules yet");
        }
        visiting.Remove(s);
        return pr.Apply("eqsstrd", S(("ph", ctx), ("A", Lhs(eqJ)), ("B", val), ("C", slice)), eqJ, sub);
    }

    /// <summary>( ctx -> ( stepf ` sb ) = ( sb u. F ( sb ) ) ) for a stage function ( X e. _V |-> ( step ` <. P , X >. ) ).</summary>
    private Proof StepAtOf(string ctx, string stepApp, string stepTok, string sb, List<string> extraVars)
    {
        string sx = Part(stepApp, "x"), sBody = Part(stepApp, "B");
        string y = FirstVar(x => x != sx && !sb.Split(' ').Contains(x) && !sBody.Split(' ').Contains(x) && !ctx.Split(' ').Contains(x));
        extraVars.Add(y);
        string bodyY = Subst(sBody, sx, y), stepY = $"( {y} e. _V |-> {bodyY} )";
        Proof ren = pr.Apply("cbvmptv", S(("x", sx), ("y", y), ("A", "_V"), ("B", sBody), ("C", bodyY)),
            _d.Congruence("class", Subst(sBody, sx, "Z"), "Z", pr.Apply("id", S(("ph", $"{sx} = {y}")))));
        Proof e1 = pr.Apply("fveq1d", S(("ph", ctx), ("A", sb), ("F", stepApp), ("G", stepY)), _d.Lift(ctx, ren));
        Proof e2 = Beta(ctx, pr.Apply("eqid", S(("A", stepY))), y, "_V", bodyY, sb, Exists(ctx, sb), stepY);
        string arg = Subst(bodyY, y, sb);
        Proof e3 = UnfoldRaw(ctx, stepTok, Part(arg, "A"));
        Proof cur = _d.Trans(_d.Trans(e1, e2), e3);
        return Simp(ctx, Rhs(cur)) is Proof sp ? _d.Trans(cur, sp) : cur;
    }
}
