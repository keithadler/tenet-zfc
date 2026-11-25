using System.Numerics;
using System.Text;

namespace TenetZfc;

public enum Verdict : byte
{
    /// <summary>Re-derived here: the rule applies to the recorded terms and gives the recorded result.</summary>
    Verified,

    /// <summary>The recorded result is not what the rule gives, or the step is malformed.</summary>
    Failed,

    /// <summary>A kind of step this replayer can check, in a case it does not handle yet.</summary>
    Unsupported,

    /// <summary>A kind of step this replayer does not check yet (conclusions, and rules justified by their premises).</summary>
    NotYet,
}

public sealed record StepFailure(Name Decl, int Step, string What, string Reason);

/// <summary>Counts per kind of step, and the failures.</summary>
public sealed class ReplayReport
{
    public SortedDictionary<string, int[]> ByKind { get; } = new(StringComparer.Ordinal);
    public List<StepFailure> Failures { get; } = new();
    public List<StepFailure> Unsupported { get; } = new();
    public int Declarations { get; internal set; }

    /// <summary>Declarations whose trace concludes what the kernel checks of them (their type is a type; their value has it).</summary>
    public int Concluded { get; internal set; }

    /// <summary>
    /// Inductive blocks whose every type is checked by the trace and whose structure is rechecked here: constructor
    /// shapes, strict positivity and field universes. Their recursors are not derived.
    /// </summary>
    public int BlocksChecked { get; internal set; }

    /// <summary>Inductive blocks whose every type is checked, in a case the structural recheck does not handle (listed as unsupported).</summary>
    public int BlocksTypesChecked { get; internal set; }

    /// <summary>
    /// Nested inductive blocks. The kernel checks one by building auxiliary inductive types that are not in the
    /// export, and the trace does not record them, so these blocks' steps are counted as unsupported.
    /// </summary>
    public int BlocksNested { get; internal set; }

    /// <summary>Inductive and quotient blocks the trace does not conclude anything about.</summary>
    public int BlocksNotTraced { get; internal set; }
    public int Steps { get; internal set; }

    public int Count(Verdict v) => ByKind.Values.Sum(c => c[(int)v]);
    public bool Ok => Failures.Count == 0;

    internal void Add(string kind, Verdict v)
    {
        if (!ByKind.TryGetValue(kind, out int[]? c))
        {
            ByKind[kind] = c = new int[4];
        }
        c[(int)v]++;
    }

    public string Format(int maxListed = 20)
    {
        var sb = new StringBuilder();
        sb.AppendLine($"{Declarations} declarations, {Steps} steps");
        sb.AppendLine($"  {Concluded} declarations concluded by their trace; {BlocksChecked} inductive blocks checked (types, constructors, positivity, universes; recursors not derived); {BlocksTypesChecked} with only their types checked; {BlocksNested} nested inductive blocks not replayed; {BlocksNotTraced} blocks not concluded");
        sb.AppendLine($"  verified {Count(Verdict.Verified)}, failed {Count(Verdict.Failed)}, unsupported {Count(Verdict.Unsupported)}, not yet replayed {Count(Verdict.NotYet)}");
        sb.AppendLine();
        sb.AppendLine($"  {"step",-24}{"verified",10}{"failed",8}{"unsupp.",9}{"not yet",9}");
        foreach ((string k, int[] c) in ByKind)
        {
            sb.AppendLine($"  {k,-24}{c[0],10}{c[1],8}{c[2],9}{c[3],9}");
        }
        foreach ((string title, List<StepFailure> list) in new[] { ("failed", Failures), ("unsupported", Unsupported) })
        {
            if (list.Count == 0)
            {
                continue;
            }
            sb.AppendLine();
            sb.AppendLine($"{title}:");
            foreach (StepFailure f in list.Take(maxListed))
            {
                sb.AppendLine($"  {f.Decl} step {f.Step} ({f.What}): {f.Reason}");
            }
            if (list.Count > maxListed)
            {
                sb.AppendLine($"  ... and {list.Count - maxListed} more");
            }
        }
        return sb.ToString();
    }
}

/// <summary>
/// Replays Tenet's traces against the export they were made from, without Tenet: each step is re-derived from the
/// definition of its rule, using only the export's declarations and the steps recorded before it.
///
/// This pass checks the single-rule steps (reductions, literal arithmetic, and the equality rules that need no
/// premises), each assuming the earlier steps it relies on. Conclusions over many steps (typing, normalization,
/// equality) and the equality rules justified by their premises are counted as not yet replayed, never as passed.
/// </summary>
public sealed partial class Replayer
{
    private readonly Terms _t;
    private readonly Ops _ops;
    private readonly Environment _env;

    private readonly Name _natZero, _natSucc, _boolTrue, _boolFalse, _quotLift, _quotInd, _quotMk;
    private readonly Dictionary<Name, string> _natOps = new(ReferenceEqualityComparer.Instance);

    /// <summary>Most terms a search for a recorded normal form visits.</summary>
    public int ReachLimit { get; init; } = 100_000;

    public Replayer(Terms t, Environment env)
    {
        _t = t;
        _ops = new Ops(t);
        _env = env;
        _natZero = t.Of("Nat.zero");
        _natSucc = t.Of("Nat.succ");
        _boolTrue = t.Of("Bool.true");
        _boolFalse = t.Of("Bool.false");
        _quotLift = t.Of("Quot.lift");
        _quotInd = t.Of("Quot.ind");
        _quotMk = t.Of("Quot.mk");
        foreach (string op in new[] { "add", "sub", "mul", "div", "mod", "gcd", "beq", "ble", "land", "lor", "xor", "shiftLeft", "shiftRight", "pow", "succ" })
        {
            _natOps[t.Of("Nat." + op)] = op;
        }
    }

    public ReplayReport Replay(IEnumerable<DeclTrace> traces)
    {
        var report = new ReplayReport();
        foreach (DeclTrace d in traces)
        {
            report.Declarations++;
            if (_env.Find(d.Decl) is null)
            {
                report.Failures.Add(new StepFailure(d.Decl, -1, "decl", "not declared in the export"));
            }
            if (_env.Find(d.Decl) is { Kind: ConstKind.Inductive } nested
                && nested.BlockMembers.Any(m => _env.Find(m) is { Kind: ConstKind.Inductive, NumNested: > 0 }))
            {
                report.BlocksNested++;
                foreach (Step s in d.Steps)
                {
                    report.Steps++;
                    report.Add(s.Kind == StepKind.Rule ? s.Rule ?? "?" : s.Kind.ToString(), Verdict.Unsupported);
                }
                report.Unsupported.Add(new StepFailure(d.Decl, -1, "decl", $"a nested inductive block ({d.Steps.Count} steps): Tenet's auxiliary types are not in the trace"));
                continue;
            }
            var state = new DeclState(_env.Find(d.Decl) switch
            {
                { Kind: ConstKind.Inductive } i => i.BlockLevelParams,
                { Kind: ConstKind.Quot } => null,   // the quotient block's four constants carry their own parameters
                ConstInfo c => c.LevelParams,
                null => [],
            });
            foreach (Step s in d.Steps)
            {
                report.Steps++;
                string what = s.Kind == StepKind.Rule ? s.Rule ?? "?" : s.Kind.ToString();
                (Verdict v, string? why) = Check(s, d.Steps, state);
                report.Add(what, v);
                if (v == Verdict.Failed)
                {
                    report.Failures.Add(new StepFailure(d.Decl, s.Index, what, why ?? "rejected"));
                }
                else if (v == Verdict.Unsupported)
                {
                    report.Unsupported.Add(new StepFailure(d.Decl, s.Index, what, why ?? "unsupported"));
                }
                state.Record(s);
            }
            if (_env.Find(d.Decl) is { Kind: ConstKind.Inductive } block)
            {
                if (block.BlockMembers.All(m => _env.Find(m) is ConstInfo c && CheckedSortOf(c.Type, state) is not null))
                {
                    BlockCheck bc = CheckBlock(block, d.Steps, state);
                    if (bc.Ok)
                    {
                        report.BlocksChecked++;
                    }
                    else if (bc.Unsupported)
                    {
                        report.BlocksTypesChecked++;
                        report.Unsupported.Add(new StepFailure(d.Decl, -1, "decl", bc.Why!));
                    }
                    else
                    {
                        report.Failures.Add(new StepFailure(d.Decl, -1, "decl", bc.Why!));
                    }
                }
                else
                {
                    report.Failures.Add(new StepFailure(d.Decl, -1, "decl", "the trace does not check every type of the block"));
                }
                continue;
            }
            switch (Concludes(d.Decl, state))
            {
                case true:
                    report.Concluded++;
                    break;
                case false:
                    report.Failures.Add(new StepFailure(d.Decl, -1, "decl", "the trace does not conclude that the declaration has its declared type"));
                    break;
                case null:
                    report.BlocksNotTraced++;
                    break;
            }
        }
        return report;
    }

    /// <summary>
    /// Whether the trace concludes what the kernel checks of the declaration: its type is a type, and for a
    /// definition, theorem or opaque constant, its value's type equals the declared type. Null for an inductive or
    /// quotient block, whose checks (positivity, universe constraints, recursor derivation) are not one conclusion.
    /// </summary>
    private bool? Concludes(Name decl, DeclState st)
    {
        if (_env.Find(decl) is not ConstInfo info)
        {
            return false;
        }
        if (info.Kind is ConstKind.Inductive or ConstKind.Quot or ConstKind.Constructor or ConstKind.Recursor)
        {
            return null;
        }
        // Both must come from checking-mode facts: an infer-only fact assumes the term is well typed.
        if (CheckedSortOf(info.Type, st) is null)
        {
            return false;
        }
        Expr? value = info.Value ?? info.OpaqueValue;
        return value is null || st.CheckedTypesOf(value).Any(v => Equal(v, info.Type, st));
    }

    // ---- per-declaration state ----

    private sealed partial class DeclState(Name[]? levelParams)
    {
        /// <summary>The universe parameters of the declaration being replayed; null when any are allowed.</summary>
        public readonly Name[]? LevelParams = levelParams;

        public readonly Dictionary<ulong, (Expr Type, Expr? Value)> Locals = new();

        /// <summary>The locals' free variables, in the order they were introduced.</summary>
        public readonly List<Expr> LocalOrder = new();

        /// <summary>Every recorded a ↝ b: single reduction steps and normalization conclusions.</summary>
        public readonly Dictionary<Expr, List<Expr>> Reductions = new(ReferenceEqualityComparer.Instance);

        public void Record(Step s)
        {
            if (s.Kind == StepKind.Local)
            {
                if (Locals.TryAdd(((FVar)s.A).Id, (s.B!, s.V)))
                {
                    LocalOrder.Add(s.A);
                }
                return;
            }
            bool reduction = s.Kind is StepKind.Whnf or StepKind.WhnfCore
                || (s.Kind == StepKind.Rule && s.Rule is "Beta" or "Zeta" or "ZetaFVar" or "Delta" or "DeltaLazy" or "Proj" or "Iota"
                    or "IotaK" or "QuotLift" or "QuotInd" or "NatLitOp" or "NatLitPred" or "StringLitToCtor" or "UnfoldProjApp");
            if (s.Kind is StepKind.Infer or StepKind.Check && s.B is not null)
            {
                AddType(s.A, s.B);
                if (s.Kind == StepKind.Check)
                {
                    AddChecked(s.A, s.B);
                }
                return;
            }
            if (s.B is not null && (reduction || s.Kind == StepKind.DefEq || (s.Kind == StepKind.Rule && s.Rule!.StartsWith("DefEq", StringComparison.Ordinal))))
            {
                Union(s.A, s.B);
            }
            if (reduction && s.B is not null)
            {
                if (!Reductions.TryGetValue(s.A, out List<Expr>? l))
                {
                    Reductions[s.A] = l = new List<Expr>();
                }
                l.Add(s.B);
            }
        }
    }

    /// <summary>The term and everything the recorded steps so far reduce it to.</summary>
    private List<Expr> Reachable(Expr e, DeclState st)
    {
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance) { e };
        var order = new List<Expr> { e };
        for (int i = 0; i < order.Count && order.Count < ReachLimit; i++)
        {
            if (st.Reductions.TryGetValue(order[i], out List<Expr>? next))
            {
                foreach (Expr n in next)
                {
                    if (seen.Add(n))
                    {
                        order.Add(n);
                    }
                }
            }
        }
        return order;
    }

    // ---- dispatch ----

    private (Verdict, string?) Check(Step s, IReadOnlyList<Step> steps, DeclState st)
    {
        string? open = Unintroduced(s, st);
        if (open is not null)
        {
            return (Verdict.Failed, open);
        }
        if (s.Of >= 0)
        {
            return Recall(s, steps);
        }
        switch (s.Kind)
        {
            case StepKind.Local:
                return s.A is FVar f && !st.Locals.ContainsKey(f.Id) && s.B is not null
                    ? (Verdict.Verified, null)
                    : (Verdict.Failed, "a local must be a fresh free variable with a type");
            case StepKind.Rule:
                break;
        }
        if (s.B is null)
        {
            return (Verdict.Failed, "this step needs two terms");
        }
        switch (s.Kind)
        {
            case StepKind.Whnf:
            case StepKind.WhnfCore:
                return Reduction(s, steps);
            case StepKind.DefEq:
                return DefEqConclusion(s, st);
            case StepKind.Infer:
                return InferConclusion(s, steps, st);
            case StepKind.Check:
                return CheckConclusion(s, steps, st);
        }
        return s.Rule switch
        {
            "Beta" => Beta(s.A, s.B),
            "Zeta" => s.A is Let l ? Same(_ops.Instantiate(l.Body, [l.Value]), s.B) : (Verdict.Failed, "not a let"),
            "ZetaFVar" => s.A is FVar f && st.Locals.TryGetValue(f.Id, out var d) && d.Value is not null
                ? Same(d.Value, s.B) : (Verdict.Failed, "not a let-bound local"),
            "Delta" or "DeltaLazy" => Delta(s.A, s.B),
            "Proj" => ProjStep(s.A, s.B, st),
            "Iota" or "IotaK" => Iota(s.A, s.B, st, s.Rule == "IotaK"),
            "QuotLift" or "QuotInd" => Quot(s.A, s.B, st),
            "NatLitOp" or "NatLitPred" => NatLit(s.A, s.B, st),
            "UnfoldProjApp" => Reachable(s.A, st).Contains(s.B)
                ? (Verdict.Verified, null) : (Verdict.Unsupported, "no recorded normalization gives this result"),
            "StringLitToCtor" => (Verdict.Unsupported, "string literals are not replayed yet"),
            "DefEqSyntactic" => Same(s.A, s.B),
            "DefEqFVar" => s.A is FVar && ReferenceEquals(s.A, s.B) ? (Verdict.Verified, null) : (Verdict.Failed, "not the same free variable"),
            "DefEqSort" => SortEq(s.A, s.B),
            "DefEqConst" => ConstEq(s.A, s.B),
            "DefEqOffset" => Offset(s, steps),
            "NativeReduce" or "InferBVar" => (Verdict.Failed, "this rule never appears in a successful check"),
            _ => PremiseRule(s, steps, st),
        };
    }

    /// <summary>A recalled result: the step it names comes earlier, is of the same kind, and concludes the same thing.</summary>
    private static (Verdict, string?) Recall(Step s, IReadOnlyList<Step> steps)
    {
        Step o = steps[s.Of];
        bool same = o.Kind == s.Kind && o.Kind != StepKind.Local && o.Kind != StepKind.Rule
            && (ReferenceEquals(o.A, s.A) && ReferenceEquals(o.B, s.B)
                || (s.Kind == StepKind.DefEq && ReferenceEquals(o.A, s.B) && ReferenceEquals(o.B, s.A)));
        return same ? (Verdict.Verified, null) : (Verdict.Failed, $"recalls step {s.Of}, which concludes something else");
    }

    private static (Verdict, string?) Same(Expr expected, Expr recorded) =>
        ReferenceEquals(expected, recorded) ? (Verdict.Verified, null) : (Verdict.Failed, $"expected {Short(expected)}, recorded {Short(recorded)}");

    private static string Short(Expr e)
    {
        string s = $"{e}";
        return s.Length <= 160 ? s : s[..157] + "...";
    }

    /// <summary>A free variable used before a Local step introduced it.</summary>
    private static string? Unintroduced(Step s, DeclState st)
    {
        foreach (Expr? e in new[] { s.Kind == StepKind.Local ? null : s.A, s.B, s.V })
        {
            if (e is null || !e.HasFVar)
            {
                continue;
            }
            foreach (ulong id in FreeVars(e))
            {
                if (!st.Locals.ContainsKey(id))
                {
                    return $"free variable {id} used before it is introduced";
                }
            }
        }
        return null;
    }

    private static IEnumerable<ulong> FreeVars(Expr e)
    {
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var stack = new Stack<Expr>();
        stack.Push(e);
        while (stack.Count > 0)
        {
            Expr x = stack.Pop();
            if (!x.HasFVar || !seen.Add(x))
            {
                continue;
            }
            switch (x)
            {
                case FVar f: yield return f.Id; break;
                case App a: stack.Push(a.Fn); stack.Push(a.Arg); break;
                case Binder b: stack.Push(b.Domain); stack.Push(b.Body); break;
                case Let l: stack.Push(l.Type); stack.Push(l.Value); stack.Push(l.Body); break;
                case Proj p: stack.Push(p.Struct); break;
            }
        }
    }

    // ---- reductions ----

    /// <summary>(fun x₁ … xₘ => b) a₁ … aₙ ↝ b[x := a] aₘ₊₁ … aₙ, with m as many binders as there are arguments.</summary>
    private (Verdict, string?) Beta(Expr a, Expr b)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        if (head is not Binder { IsPi: false } || args.Count == 0)
        {
            return (Verdict.Failed, "not a lambda applied to arguments");
        }
        Expr body = head;
        int m = 0;
        while (body is Binder { IsPi: false } lam && m < args.Count)
        {
            body = lam.Body;
            m++;
        }
        var subst = new List<Expr>(m);
        for (int i = m - 1; i >= 0; i--)
        {
            subst.Add(args[i]);
        }
        return Same(_t.MkApp(_ops.Instantiate(body, subst), args.Skip(m)), b);
    }

    /// <summary>c.{ū} ā ↝ (the value of c, at ū) ā, for a definition or theorem c.</summary>
    private (Verdict, string?) Delta(Expr a, Expr b)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        if (head is not Const c || _env.Find(c.Name) is not ConstInfo info)
        {
            return (Verdict.Failed, "the head is not a declared constant");
        }
        if (info.Value is null || info.Kind is not (ConstKind.Definition or ConstKind.Theorem))
        {
            return (Verdict.Failed, $"{c.Name} is not a definition or theorem");
        }
        if (c.Levels.Length != info.LevelParams.Length)
        {
            return (Verdict.Failed, "wrong number of universe levels");
        }
        return Same(_t.MkApp(_ops.InstantiateLevels(info.Value, info.LevelParams, c.Levels), args), b);
    }

    /// <summary>(C.mk p̄ f̄).i ↝ fᵢ, where the structure reduces to the constructor by recorded steps.</summary>
    private (Verdict, string?) ProjStep(Expr a, Expr b, DeclState st)
    {
        if (a is not Proj p)
        {
            return (Verdict.Failed, "not a projection");
        }
        bool sawCtor = false;
        foreach (Expr c in Reachable(p.Struct, st))
        {
            if (Ops.Spine(c, out List<Expr> args) is Const k && _env.Find(k.Name) is { Kind: ConstKind.Constructor } ctor
                && ReferenceEquals(ctor.Induct, p.StructName))
            {
                sawCtor = true;
                int i = ctor.NumParams + p.Idx;
                if (i < args.Count && ReferenceEquals(args[i], b))
                {
                    return (Verdict.Verified, null);
                }
            }
        }
        return sawCtor ? (Verdict.Failed, "the field is not the recorded result")
                       : (Verdict.Unsupported, "the structure does not reduce to a constructor in the recorded steps");
    }

    /// <summary>
    /// I.rec p̄ m̄ minors īdx (I.cᵢ … f̄) extra ↝ (the i-th rule's right side) p̄ m̄ minors f̄ extra. The major premise is
    /// taken in any form the recorded steps reduce it to; a Nat literal counts as its constructor form, and a structure
    /// counts as its constructor applied to its projections. Rule K needs no major premise at all.
    /// </summary>
    private (Verdict, string?) Iota(Expr a, Expr b, DeclState st, bool byK)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        if (head is not Const recC || _env.Find(recC.Name) is not { Kind: ConstKind.Recursor } rec)
        {
            return (Verdict.Failed, "the head is not a recursor");
        }
        if (recC.Levels.Length != rec.LevelParams.Length || args.Count <= rec.MajorIdx)
        {
            return (Verdict.Failed, "wrong number of levels or arguments");
        }
        int prefix = rec.NumParams + rec.NumMotives + rec.NumMinors;
        Expr Apply(RecRule rule, IEnumerable<Expr> fields) =>
            _t.MkApp(_t.MkApp(_t.MkApp(_ops.InstantiateLevels(rule.Rhs, rec.LevelParams, recC.Levels), args.Take(prefix)), fields),
                     args.Skip(rec.MajorIdx + 1));

        if (byK)
        {
            if (!rec.K || rec.Rules.Length != 1 || rec.Rules[0].NumFields != 0)
            {
                return (Verdict.Failed, "rule K on a recursor that does not have it");
            }
            // The kernel also checks that the major premise's type is the inductive's; that is a typing fact this
            // pass does not replay.
            return Same(Apply(rec.Rules[0], []), b);
        }

        bool sawCtor = false;
        foreach (Expr major in Reachable(args[rec.MajorIdx], st))
        {
            foreach ((Name ctorName, List<Expr> fieldsAndParams) in CtorForms(major, rec))
            {
                RecRule? rule = rec.Rules.FirstOrDefault(r => ReferenceEquals(r.Ctor, ctorName));
                if (rule is null || rule.NumFields > fieldsAndParams.Count)
                {
                    continue;
                }
                sawCtor = true;
                if (ReferenceEquals(Apply(rule, fieldsAndParams.Skip(fieldsAndParams.Count - rule.NumFields)), b))
                {
                    return (Verdict.Verified, null);
                }
            }
        }
        return sawCtor ? (Verdict.Failed, "no constructor form of the major premise gives the recorded result")
                       : (Verdict.Unsupported, "the major premise does not reduce to a constructor in the recorded steps");
    }

    /// <summary>The ways to read a term as a constructor application: itself, a Nat literal's form, or structure eta.</summary>
    private IEnumerable<(Name Ctor, List<Expr> Args)> CtorForms(Expr e, ConstInfo rec)
    {
        if (e is NatLit n)
        {
            yield return n.Value.IsZero ? (_natZero, new List<Expr>()) : (_natSucc, new List<Expr> { _t.Nat(n.Value - 1) });
            yield break;
        }
        if (Ops.Spine(e, out List<Expr> args) is Const c && _env.Find(c.Name) is { Kind: ConstKind.Constructor })
        {
            yield return (c.Name, args);
            yield break;
        }
        // Structure eta: a term of a structure type is its constructor applied to its projections. Only the fields
        // reach the result, so they are all that is built here.
        if (rec.Rules.Length == 1 && rec.NumIndices == 0 && _env.Find(rec.Rules[0].Ctor) is { Induct: Name ind } ctor)
        {
            var fields = new List<Expr>();
            for (int i = 0; i < ctor.NumFields; i++)
            {
                fields.Add(_t.Proj(ind, i, e));
            }
            yield return (ctor.Name, fields);
        }
    }

    /// <summary>Quot.lift f h (Quot.mk r a) ↝ f a, and Quot.ind h (Quot.mk r a) ↝ h a.</summary>
    private (Verdict, string?) Quot(Expr a, Expr b, DeclState st)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        if (head is not Const c)
        {
            return (Verdict.Failed, "the head is not a constant");
        }
        (int mkPos, int argPos) = ReferenceEquals(c.Name, _quotLift) ? (5, 3) : ReferenceEquals(c.Name, _quotInd) ? (4, 3) : (-1, -1);
        if (mkPos < 0 || args.Count <= mkPos)
        {
            return (Verdict.Failed, "not Quot.lift or Quot.ind applied to its arguments");
        }
        bool sawMk = false;
        foreach (Expr mk in Reachable(args[mkPos], st))
        {
            if (Ops.Spine(mk, out List<Expr> mkArgs) is Const m && ReferenceEquals(m.Name, _quotMk) && mkArgs.Count == 3)
            {
                sawMk = true;
                if (ReferenceEquals(_t.MkApp(_t.App(args[argPos], mkArgs[2]), args.Skip(mkPos + 1)), b))
                {
                    return (Verdict.Verified, null);
                }
            }
        }
        return sawMk ? (Verdict.Failed, "the recorded result is not f a") : (Verdict.Unsupported, "the quotient does not reduce to Quot.mk in the recorded steps");
    }

    /// <summary>
    /// Nat.op x y ↝ the literal it computes, where x and y reduce to literals by recorded steps. The operations are taken
    /// to mean what their names say; Tenet checks that against their definitions once per environment, and that check
    /// is not in the trace (see trace-format.md).
    /// </summary>
    private (Verdict, string?) NatLit(Expr a, Expr b, DeclState st)
    {
        Expr head = Ops.Spine(a, out List<Expr> args);
        if (head is not Const { Levels.Length: 0 } c || !_natOps.TryGetValue(c.Name, out string? op))
        {
            return (Verdict.Failed, "not a Nat operation");
        }
        if ((op == "succ") != (args.Count == 1) || args.Count is < 1 or > 2)
        {
            return (Verdict.Failed, "wrong number of arguments");
        }
        BigInteger? x = LiteralValue(args[0], st);
        BigInteger? y = args.Count == 2 ? LiteralValue(args[1], st) : BigInteger.Zero;
        if (x is null || y is null)
        {
            return (Verdict.Unsupported, "an argument does not reduce to a literal in the recorded steps");
        }
        BigInteger X = x.Value, Y = y.Value;
        object result = op switch
        {
            "succ" => X + 1,
            "add" => X + Y,
            "sub" => X >= Y ? X - Y : BigInteger.Zero,
            "mul" => X * Y,
            "div" => Y.IsZero ? BigInteger.Zero : X / Y,
            "mod" => Y.IsZero ? X : X % Y,
            "gcd" => BigInteger.GreatestCommonDivisor(X, Y),
            "land" => X & Y,
            "lor" => X | Y,
            "xor" => X ^ Y,
            "shiftLeft" => Y > int.MaxValue ? (object)"too large" : X << (int)Y,
            "shiftRight" => Y > int.MaxValue ? BigInteger.Zero : X >> (int)Y,
            "pow" => Y > int.MaxValue ? (object)"too large" : BigInteger.Pow(X, (int)Y),
            "beq" => X == Y,
            "ble" => X <= Y,
            _ => throw new InvalidOperationException(op),
        };
        Expr expected = result switch
        {
            BigInteger r => _t.Nat(r),
            bool p => _t.Const(p ? _boolTrue : _boolFalse, []),
            _ => b,
        };
        if (result is string)
        {
            return (Verdict.Unsupported, "an exponent or shift too large to compute here");
        }
        return Same(expected, b);
    }

    private BigInteger? LiteralValue(Expr e, DeclState st)
    {
        foreach (Expr r in Reachable(e, st))
        {
            if (r is NatLit n)
            {
                return n.Value;
            }
            if (r is Const { Levels.Length: 0 } c && ReferenceEquals(c.Name, _natZero))
            {
                return BigInteger.Zero;
            }
        }
        return null;
    }

    // ---- equality rules that need no premises ----

    private (Verdict, string?) SortEq(Expr a, Expr b)
    {
        if (a is not Sort x || b is not Sort y)
        {
            return (Verdict.Failed, "not two sorts");
        }
        return _ops.Equivalent(x.Level, y.Level) switch
        {
            true => (Verdict.Verified, null),
            false => (Verdict.Failed, $"{x.Level} and {y.Level} are different universes"),
            null => (Verdict.Unsupported, "too many universe parameters to compare"),
        };
    }

    private (Verdict, string?) ConstEq(Expr a, Expr b)
    {
        if (a is not Const x || b is not Const y || !ReferenceEquals(x.Name, y.Name) || x.Levels.Length != y.Levels.Length)
        {
            return (Verdict.Failed, "not the same constant");
        }
        for (int i = 0; i < x.Levels.Length; i++)
        {
            switch (_ops.Equivalent(x.Levels[i], y.Levels[i]))
            {
                case false:
                    return (Verdict.Failed, $"{x.Levels[i]} and {y.Levels[i]} are different universes");
                case null:
                    return (Verdict.Unsupported, "too many universe parameters to compare");
            }
        }
        return (Verdict.Verified, null);
    }

    /// <summary>0 ≡ 0, or succ x ≡ succ y given a recorded x ≡ y among the step's premises.</summary>
    private (Verdict, string?) Offset(Step s, IReadOnlyList<Step> steps)
    {
        if (IsZero(s.A) && IsZero(s.B!))
        {
            return (Verdict.Verified, null);
        }
        Expr? pa = Pred(s.A), pb = Pred(s.B!);
        if (pa is null || pb is null)
        {
            return (Verdict.Failed, "neither both zero nor both successors");
        }
        for (int j = s.From; j < s.Index; j++)
        {
            Step p = steps[j];
            if (p.Kind == StepKind.DefEq && ReferenceEquals(p.A, pa) && ReferenceEquals(p.B, pb))
            {
                return (Verdict.Verified, null);
            }
        }
        return (Verdict.Failed, "no recorded premise that the predecessors are equal");
    }

    private bool IsZero(Expr e) => e is NatLit { Value.IsZero: true } || (e is Const c && ReferenceEquals(c.Name, _natZero));

    private Expr? Pred(Expr e) => e switch
    {
        NatLit { Value.IsZero: false } n => _t.Nat(n.Value - 1),
        App { Fn: Const c } a when ReferenceEquals(c.Name, _natSucc) => a.Arg,
        _ => null,
    };
}
