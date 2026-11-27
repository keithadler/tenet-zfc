namespace TenetZfc;

/// <summary>
/// Inductive propositions beyond ω (docs/milestone3.md, "Acc and other non-finitary propositions").
///
/// <see cref="Model.DefineRecursiveProposition"/> builds a recursive proposition in ω stages, which reaches its least
/// fixed point only when every premise is finitary: Nat.le's <c>Nat.le n m</c>. A premise that is a function into the
/// proposition, like Acc's <c>h : ∀ y, r y x → Acc r y</c>, may need a stage for every ordinal below some regular
/// cardinal. Rather than iterating that far, these propositions take the least fixed point at once, as the
/// intersection of every closed set:
///
///   ⟦I params indices⟧ = if ( &lt;. indices &gt;. e. ( lean.I.-least ` &lt;. u , params &gt;. ) , 1o , (/) )
///   lean.I.-least = ( p e. _V |-> |^| { s | ( lean.I.-step ` &lt;. p , s &gt;. ) C_ s } )
///
/// The step is the one ω-stages use, except that a premise mentioning I under binders is translated with each
/// <c>I params e⃗</c> in it read as <c>if ( &lt;. e⃗ &gt;. e. s , 1o , (/) )</c>. Every occurrence is positive, so the step is
/// monotone. A closed set exists, the set of all index tuples of the right types, so the intersection is a set and is
/// the least fixed point (Knaster–Tarski).
///
/// A recursor that eliminates into any sort (Acc.rec) is well-founded recursion on the indices, over the least set:
///
///   ( frecs ( R , least , ( a e. _V , f e. _V |-> ( lean.I.-case ` &lt;. &lt;. q , a &gt;. , f &gt;. ) ) ) ` &lt;. indices &gt;. )
///
/// where R relates the index tuple of each recursive premise to the constructor's result indices, over every value of
/// the other fields. Lean allows such an elimination only for one constructor whose data fields are among its result
/// indices, so the case analysis reads them back from the index tuple a; proofs are (/), and each induction hypothesis
/// is the map over the premise's binders to f at its index tuple. On the least set, R is well-founded and set-like, so
/// frecs computes the recursor there. Its computation rule (frr2 with that well-foundedness) is not written yet.
/// </summary>
public sealed partial class Model
{
    /// <summary>Recursors defined by well-founded recursion on a least fixed point (computation rules not yet written).</summary>
    private readonly HashSet<string> _leastRecursors = new();

    private static bool MentionsConst(Expr e, Name n) => e switch
    {
        Const c => ReferenceEquals(c.Name, n),
        App a => MentionsConst(a.Fn, n) || MentionsConst(a.Arg, n),
        Binder b => MentionsConst(b.Domain, n) || MentionsConst(b.Body, n),
        Let l => MentionsConst(l.Type, n) || MentionsConst(l.Value, n) || MentionsConst(l.Body, n),
        Proj p => MentionsConst(p.Struct, n),
        _ => false,
    };

    /// <summary>Whether the recursor's motive returns Prop.</summary>
    private static bool EliminatesOnlyIntoProp(ConstInfo ind, ConstInfo rec)
    {
        Expr ty = rec.Type;
        for (int i = 0; i < ind.NumParams; i++)
        {
            ty = ((Binder)ty).Body;
        }
        Expr mt = ((Binder)ty).Domain;
        while (mt is Binder { IsPi: true } mb)
        {
            mt = mb.Body;
        }
        return mt is Sort { Level: LZero };
    }

    /// <summary>
    /// Whether a recursive proposition needs the least fixed point at once rather than ω stages: a premise that mentions it
    /// under binders (not finitary), or a recursor that eliminates into any sort.
    /// </summary>
    private static bool NeedsLeastFixedPoint(ConstInfo ind, List<ConstInfo> ctors, ConstInfo rec)
    {
        foreach (ConstInfo c in ctors)
        {
            Expr cty = c.Type;
            for (int i = 0; i < ind.NumParams + c.NumFields && cty is Binder { IsPi: true } b; i++, cty = b.Body)
            {
                if (i >= ind.NumParams && !(Ops.Spine(b.Domain, out _) is Const h && ReferenceEquals(h.Name, ind.Name))
                    && MentionsConst(b.Domain, ind.Name))
                {
                    return true;
                }
            }
        }
        return !EliminatesOnlyIntoProp(ind, rec);
    }

    /// <summary>e with each I params e⃗ in it (at exactly these parameters) replaced by hole e⃗.</summary>
    private Expr ReplaceFamily(Expr e, Name n, IReadOnlyList<Expr> pfv, Expr hole)
    {
        if (!MentionsConst(e, n))
        {
            return e;
        }
        switch (e)
        {
            case App or Const when Ops.Spine(e, out List<Expr> args) is Const h && ReferenceEquals(h.Name, n):
                if (args.Count < pfv.Count || !args.Take(pfv.Count).Zip(pfv).All(z => ReferenceEquals(z.First, z.Second)))
                {
                    throw new Refused($"{n} occurs in a premise at other parameters, or unapplied; not in the model yet");
                }
                return args.Skip(pfv.Count).Aggregate(hole, (acc, x) => t.App(acc, ReplaceFamily(x, n, pfv, hole)));
            case App a:
                return t.App(ReplaceFamily(a.Fn, n, pfv, hole), ReplaceFamily(a.Arg, n, pfv, hole));
            case Binder b:
                return t.Binding(b.IsPi, b.BinderName, b.Info, ReplaceFamily(b.Domain, n, pfv, hole), ReplaceFamily(b.Body, n, pfv, hole));
            default:
                throw new Refused($"{n} occurs in a premise inside a let or a projection; not in the model yet");
        }
    }

    /// <summary>Binds a fresh fvar of the given Lean type to a fresh set variable over dom; returns both.</summary>
    private (Expr Fv, string Var) BindFresh(Scope sc, Expr type, string dom)
    {
        string v = Fresh(sc, dom);
        Expr fv = t.FVar(_fresh++);
        sc.Vars[((FVar)fv).Id] = v;
        sc.Types[((FVar)fv).Id] = type;
        if (!sc.Bound.Contains(v))
        {
            sc.Bound.Add(v);
        }
        sc.Active.Add(v);
        return (fv, v);
    }

    /// <summary>
    /// A recursive inductive proposition as a least fixed point, taken at once (see the class comment), with a recursor
    /// by well-founded recursion when it eliminates into any sort.
    /// </summary>
    private void DefineLeastProposition(ConstInfo ind, string itok, List<ConstInfo> ctors, ConstInfo rec)
    {
        Name n = ind.Name;
        string steptok = itok + ".-step";
        const string hole = "ZZX";

        // The step, over w = <. <. u , params >. , X >., as for ω stages but with non-finitary premises.
        var stepBound = new List<string>();
        {
            var sc = NewScope();
            var pfv = new List<Expr>();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc, pfv);
            Expr family = ty;   // indices → Prop, at the parameters
            var parts = new List<string>();
            foreach (ConstInfo c in ctors)
            {
                Expr cty = c.Type;
                Telescope(ref cty, ind.NumParams, sc, reuse: pfv);
                var fs = new List<(string Var, string Dom)>();
                for (int k = 0; k < c.NumFields; k++)
                {
                    var b = (Binder)cty;
                    string dom;
                    if (Ops.Spine(b.Domain, out List<Expr> ra) is Const h && ReferenceEquals(h.Name, n))
                    {
                        if (ra.Count != ind.NumParams + ind.NumIndices || !ra.Take(ind.NumParams).Zip(pfv).All(z => ReferenceEquals(z.First, z.Second)))
                        {
                            throw new Refused($"{c.Name} has a recursive premise at other parameters; not in the model yet");
                        }
                        dom = $"if ( {Tuple(ra.Skip(ind.NumParams).Select(e => Tr(e, sc)).ToList())} e. {hole} , 1o , (/) )";
                    }
                    else if (MentionsConst(b.Domain, n))
                    {
                        // I params e⃗ under binders: read through a hole, ( i1 e. _V |-> … if ( <. i⃗ >. e. X , 1o , (/) ) ).
                        var ivars = new List<string>();
                        for (int i = 0; i < ind.NumIndices; i++)
                        {
                            string iv = FirstVar(x => !sc.Bound.Contains(x) && !sc.Active.Contains(x) && !sc.Vars.ContainsValue(x));
                            sc.Bound.Add(iv);
                            ivars.Add(iv);
                        }
                        string map = ivars.AsEnumerable().Reverse()
                            .Aggregate($"if ( {Tuple(ivars)} e. {hole} , 1o , (/) )", (acc, iv) => $"( {iv} e. _V |-> {acc} )");
                        Expr hfv = t.FVar(_fresh++);
                        sc.Vars[((FVar)hfv).Id] = map;
                        sc.Types[((FVar)hfv).Id] = family;
                        dom = Tr(ReplaceFamily(b.Domain, n, pfv, hfv), sc);
                        sc.Vars.Remove(((FVar)hfv).Id);
                    }
                    else
                    {
                        dom = Tr(b.Domain, sc);
                    }
                    var (fv, v) = BindFresh(sc, b.Domain, dom);
                    fs.Add((v, dom));
                    cty = _ops.Instantiate(b.Body, [fv]);
                }
                Ops.Spine(cty, out List<Expr> result);
                string tuple = Tuple(result.Skip(ind.NumParams).Select(e => Tr(e, sc)).ToList());
                foreach (var f in fs)
                {
                    sc.Active.Remove(f.Var);
                }
                parts.Add(fs.AsEnumerable().Reverse().Aggregate($"{{ {tuple} }}", (acc, f) => $"U_ {f.Var} e. {f.Dom} {acc}"));
            }
            string set = parts.Count == 0 ? "(/)" : parts.Skip(1).Aggregate(parts[0], (acc, p) => $"( {acc} u. {p} )");
            string body = $"( {hole} u. {set} )";
            string w = FirstVar(x => !sc.Bound.Contains(x) && !body.Split(' ').Contains(x) && !ps.Any(q => q.Var == x));
            var packed = new[] { UniverseVar }.Concat(ps.Select(q => q.Var)).ToList();
            body = Subst(Unpack(body, packed, $"( 1st ` {w} )"), hole, $"( 2nd ` {w} )");
            stepBound.AddRange(sc.Bound.Where(x => x != UniverseVar && !ps.Any(q => q.Var == x)));
            stepBound.Add(w);
            EmitRaw(t.Of($"{n}.-step"), steptok, $"( {w} e. _V |-> {body} )", stepBound, "inductive proposition's step, over a packed argument");
        }

        // The least closed set of index tuples, over a packed argument p = <. u , params >., as a constant of its own:
        // definitions then substitute only into ( lean.I.-least ` p ), never under its class abstraction.
        string leasttok = itok + ".-least";
        {
            string p = FirstVar(_ => true), s = FirstVar(v => v != p);
            EmitRaw(t.Of($"{n}.-least"), leasttok, $"( {p} e. _V |-> |^| {{ {s} | ( {steptok} ` <. {p} , {s} >. ) C_ {s} }} )", [p, s],
                "inductive proposition's least closed set of index tuples, over a packed argument");
        }
        string Least(Scope sc, IEnumerable<string> ps) => $"( {leasttok} ` {Tuple(new[] { UniverseVar }.Concat(ps).ToList())} )";

        // The proposition.
        {
            var sc = NewScope();
            Expr ty = ind.Type;
            var ps = Telescope(ref ty, ind.NumParams, sc);
            var ixs = Telescope(ref ty, ind.NumIndices, sc);
            string least = Least(sc, ps.Select(q => q.Var));
            _defined.Add(n);
            Emit(n, itok, Maps(ps.Concat(ixs), $"if ( {Tuple(ixs.Select(q => q.Var).ToList())} e. {least} , 1o , (/) )"), sc,
                "inductive proposition (a least fixed point)");
        }

        // Constructors: proofs, so (/).
        foreach (ConstInfo c in ctors)
        {
            var sc = NewScope();
            Expr cty = c.Type;
            var bs = Telescope(ref cty, ind.NumParams + c.NumFields, sc);
            _defined.Add(c.Name);
            Emit(c.Name, Token(c.Name)!, Maps(bs, "(/)"), sc, "constructor");
        }

        if (EliminatesOnlyIntoProp(ind, rec))
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bs = Telescope(ref rty, ind.NumParams + rec.NumMotives + rec.NumMinors + ind.NumIndices + 1, sc);
            _intoPropOnly.Add(Token(rec.Name)!);
            _defined.Add(rec.Name);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, "(/)"), sc, "recursor");
            return;
        }
        DefineLeastRecursor(ind, itok, ctors, rec, Least);
    }

    /// <summary>One constructor's fields, classified: for each, its fvar and Lean type, and whether it is a recursive premise.</summary>
    private sealed record LeastField(Expr Fv, Expr Type, bool Recursive);

    /// <summary>A large recursor on a least fixed point: well-founded recursion on its index tuples (see the class comment).</summary>
    private void DefineLeastRecursor(ConstInfo ind, string itok, List<ConstInfo> ctors, ConstInfo rec, Func<Scope, IEnumerable<string>, string> least)
    {
        Name n = ind.Name;
        if (ctors.Count != 1 || rec.NumMotives != 1 || rec.NumMinors != 1)
        {
            throw new Refused($"{rec.Name} eliminates a proposition with {ctors.Count} constructors into any sort; not in the model yet");
        }
        ConstInfo c = ctors[0];
        int np = ind.NumParams, nb = np + rec.NumMotives + rec.NumMinors;
        string casetok = itok + ".-case";
        const string ha = "ZZA", hf = "ZZF";

        // The constructor's fields at the parameters pfv, each with a fresh fvar (not yet translated).
        List<LeastField> Fields(Scope sc, IReadOnlyList<Expr> pfv, out List<Expr> resultIndices)
        {
            Expr cty = c.Type;
            for (int i = 0; i < np; i++)
            {
                cty = _ops.Instantiate(((Binder)cty).Body, [pfv[i]]);
            }
            var fs = new List<LeastField>();
            for (int k = 0; k < c.NumFields; k++)
            {
                var b = (Binder)cty;
                Expr fv = t.FVar(_fresh++);
                sc.Types[((FVar)fv).Id] = b.Domain;
                fs.Add(new LeastField(fv, b.Domain, MentionsConst(b.Domain, n)));
                cty = _ops.Instantiate(b.Body, [fv]);
            }
            Ops.Spine(cty, out List<Expr> result);
            resultIndices = result.Skip(np).ToList();
            return fs;
        }

        // A recursive premise Π zs, I params e⃗: binds zs over their domains (active) and returns them with ⟦e⃗⟧.
        (List<(string Var, string Dom)> Zs, string Index) Premise(Scope sc, Expr type, IReadOnlyList<Expr> pfv)
        {
            var zs = new List<(string, string)>();
            while (type is Binder { IsPi: true } b)
            {
                if (MentionsConst(b.Domain, n))
                {
                    throw new Refused($"{c.Name} has a premise with {n} in a binder's domain; not in the model yet");
                }
                string dom = Tr(b.Domain, sc);
                var (fv, v) = BindFresh(sc, b.Domain, dom);
                zs.Add((v, dom));
                type = _ops.Instantiate(b.Body, [fv]);
            }
            if (Ops.Spine(type, out List<Expr> args) is not Const h || !ReferenceEquals(h.Name, n) || args.Count != np + ind.NumIndices
                || !args.Take(np).Zip(pfv).All(z => ReferenceEquals(z.First, z.Second)))
            {
                throw new Refused($"{c.Name} has a premise mentioning {n} other than as Π …, {n} params indices; not in the model yet");
            }
            return (zs, Tuple(args.Skip(np).Select(e => Tr(e, sc)).ToList()));
        }

        // The case analysis, over w = <. <. q , a >. , f >. with q = <. u , params , motive , minor >.: the minor premise at
        // the fields (data fields read from the index tuple a, proofs (/)) and the induction hypotheses ( zs |-> ( f ` e⃗ ) ).
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bfv = new List<Expr>();
            var bs = Telescope(ref rty, nb, sc, bfv);
            string minor = bs[nb - 1].Var;
            var fs = Fields(sc, bfv, out List<Expr> resIdx);
            foreach (LeastField f in fs)
            {
                ulong id = ((FVar)f.Fv).Id;
                if (_typing.IsProposition(f.Type, sc.Types) == true)
                {
                    sc.Vars[id] = "(/)";
                    continue;
                }
                int pos = resIdx.FindIndex(e => ReferenceEquals(e, f.Fv));
                sc.Vars[id] = pos >= 0 ? Field(ha, pos)
                    : throw new Refused($"{c.Name} has a data field that isn't one of its indices; Lean's large elimination shouldn't allow it");
            }
            string app = fs.Aggregate(minor, (acc, f) => $"( {acc} ` {Tr(f.Fv, sc)} )");
            var caseBound = new List<string>();
            foreach (LeastField f in fs.Where(f => f.Recursive))
            {
                var (zs, index) = Premise(sc, f.Type, bfv);
                app = $"( {app} ` {Maps(zs, $"( {hf} ` {index} )")} )";
                foreach (var z in zs)
                {
                    sc.Active.Remove(z.Var);
                    caseBound.Add(z.Var);
                }
            }
            string body = app;
            string w = FirstVar(x => !body.Split(' ').Contains(x) && !bs.Any(q => q.Var == x) && x != UniverseVar && !caseBound.Contains(x));
            var packed = new[] { UniverseVar }.Concat(bs.Select(q => q.Var)).ToList();
            body = Unpack(body, packed, $"( 1st ` ( 1st ` {w} ) )");
            body = Subst(Subst(body, ha, $"( 2nd ` ( 1st ` {w} ) )"), hf, $"( 2nd ` {w} )");
            EmitRaw(t.Of($"{n}.-case"), casetok, $"( {w} e. _V |-> {body} )", caseBound.Append(w), "recursor's case analysis (on a least fixed point), over a packed argument");
        }

        // The recursor: ( params motive minor indices major |-> ( frecs ( R , least , G ) ` <. indices >. ) ).
        {
            var sc = NewScope();
            Expr rty = rec.Type;
            var bfv = new List<Expr>();
            var bs = Telescope(ref rty, nb + ind.NumIndices + 1, sc, bfv);
            var ps = bs.Take(np).Select(b => b.Var).ToList();
            string q = Tuple(new[] { UniverseVar }.Concat(bs.Take(nb).Select(b => b.Var)).ToList());
            string idx = Tuple(bs.Skip(nb).Take(ind.NumIndices).Select(b => b.Var).ToList());
            string leastSet = least(sc, ps);

            // R: U_ (each other field) ( U_ zs { <. e⃗ , result indices >. } u. … ), over the recursive premises.
            var fs = Fields(sc, bfv.Take(np).ToList(), out List<Expr> resIdx);
            var outer = new List<(string Var, string Dom)>();
            foreach (LeastField f in fs)
            {
                ulong id = ((FVar)f.Fv).Id;
                if (f.Recursive)
                {
                    sc.Vars[id] = "(/)";   // a proof; R ranges over its premise's binders instead
                    continue;
                }
                string dom = Tr(f.Type, sc);
                string v = Fresh(sc, dom);
                sc.Vars[id] = v;
                if (!sc.Bound.Contains(v))
                {
                    sc.Bound.Add(v);
                }
                sc.Active.Add(v);
                outer.Add((v, dom));
            }
            string result = Tuple(resIdx.Select(e => Tr(e, sc)).ToList());
            var pairs = new List<string>();
            foreach (LeastField f in fs.Where(f => f.Recursive))
            {
                var (zs, index) = Premise(sc, f.Type, bfv.Take(np).ToList());
                pairs.Add(zs.AsEnumerable().Reverse().Aggregate($"{{ <. {index} , {result} >. }}", (acc, z) => $"U_ {z.Var} e. {z.Dom} {acc}"));
                foreach (var z in zs)
                {
                    sc.Active.Remove(z.Var);
                }
            }
            if (pairs.Count == 0)
            {
                throw new Refused($"{c.Name} has no recursive premise");
            }
            string inner = pairs.Skip(1).Aggregate(pairs[0], (acc, p) => $"( {acc} u. {p} )");
            string rel = outer.AsEnumerable().Reverse().Aggregate(inner, (acc, o) => $"U_ {o.Var} e. {o.Dom} {acc}");
            foreach (var o in outer)
            {
                sc.Active.Remove(o.Var);
            }
            string a = PickRecursionVar(sc), f2 = PickRecursionVar(sc);
            string g = $"( {a} e. _V , {f2} e. _V |-> ( {casetok} ` <. <. {q} , {a} >. , {f2} >. ) )";
            _defined.Add(rec.Name);
            _leastRecursors.Add(Token(rec.Name)!);
            Emit(rec.Name, Token(rec.Name)!, Maps(bs, $"( frecs ( {rel} , {leastSet} , {g} ) ` {idx} )"), sc,
                "recursor (well-founded recursion on a least fixed point)");
        }
    }
}
