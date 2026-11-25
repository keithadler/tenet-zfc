using TenetZfc;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// The replayer accepts Tenet's real traces, and rejects each kind of step it claims to check once that step's
/// recorded result is changed. The second half is what makes the first mean anything: a replayer that accepted
/// everything would pass the first half too.
/// </summary>
public class ReplayTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);

    public static TheoryData<string> Exports => new() { "Nat.add_succ", "Nat.add_succ.v3.0", "eta437", "acc436" };

    private static (Terms T, Env Env, List<DeclTrace> Traces) Load(string name)
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture(name + ".ndjson"));
        List<DeclTrace> traces = Reader.ReadTrace(t, Fixture(name + ".trace.ndjson"));
        return (t, env, traces);
    }

    [Theory]
    [MemberData(nameof(Exports))]
    public void TenetsTracesReplayWithNoFailures(string name)
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load(name);
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.True(r.Ok, r.Format());
        Assert.Empty(r.Unsupported);
        // Every step is re-derived: nothing left unsupported or not yet replayed.
        Assert.Equal(r.Steps, r.Count(Verdict.Verified));
    }

    /// <summary>Every kind of step the replayer checks, with a fixture whose trace has one.</summary>
    public static TheoryData<string, string> CheckedSteps => new()
    {
        { "Nat.add_succ", "Beta" }, { "Nat.add_succ", "Delta" }, { "Nat.add_succ", "DeltaLazy" }, { "Nat.add_succ", "Iota" },
        { "Nat.add_succ", "IotaK" }, { "Nat.add_succ", "Proj" }, { "Nat.add_succ", "DefEqSyntactic" }, { "Nat.add_succ", "DefEqOffset" },
        { "Nat.add_succ", "DefEqApp" }, { "Nat.add_succ", "DefEqBinding" }, { "Nat.add_succ", "DefEqLazyDelta" },
        { "Nat.add_succ", "DefEqLazyDeltaProj" }, { "eta437", "DefEqProofIrrel" }, { "eta437", "DefEqEtaStruct" },
        { "Nat.add_succ", "Infer" }, { "Nat.add_succ", "Check" }, { "Nat.add_succ", "Whnf" }, { "Nat.add_succ", "WhnfCore" }, { "Nat.add_succ", "DefEq" },
    };

    private static bool Is(Step s, string what) =>
        s.Kind == StepKind.Rule ? s.Rule == what : s.Kind.ToString() == what;

    [Theory]
    [MemberData(nameof(CheckedSteps))]
    public void ChangingARecordedResultIsCaught(string fixture, string what)
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load(fixture);
        (int d, int i) = Find(traces, s => Is(s, what));
        // A literal no step in these files produces: wrong for every kind of step.
        Replace(traces, d, i, traces[d].Steps[i] with { B = t.Nat(424242) });

        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.False(r.Ok);
        Assert.Contains(r.Failures, f => f.Step == i && f.What == what);
    }

    /// <summary>Each kind of step, every occurrence in the fixture, changed one at a time: all are caught.</summary>
    [Theory]
    [InlineData("Infer")]
    [InlineData("Check")]
    [InlineData("DefEq")]
    [InlineData("WhnfCore")]
    public void EveryOccurrenceIsChecked(string what)
    {
        (Terms t, Env env, List<DeclTrace> pristine) = Load("Nat.add_succ");
        int tried = 0;
        for (int d = 0; d < pristine.Count; d++)
        {
            foreach (Step s in pristine[d].Steps.Where(s => Is(s, what)).Take(25))
            {
                var traces = pristine.ToList();
                Replace(traces, d, s.Index, s with { B = t.Nat(424242) });
                ReplayReport r = new Replayer(t, env).Replay(traces);
                Assert.Contains(r.Failures, f => f.Step == s.Index && f.What == what);
                tried++;
            }
        }
        Assert.True(tried > 25);
    }

    [Fact]
    public void AFalseEqualityBetweenRealTermsIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        (int d, int i) = Find(traces, s => s.Kind == StepKind.DefEq);
        Expr zero = t.Const(t.Of("Nat.zero"), []);
        Expr one = t.App(t.Const(t.Of("Nat.succ"), []), zero);
        Replace(traces, d, i, traces[d].Steps[i] with { A = zero, B = one });

        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Step == i && f.What == "DefEq");
    }

    [Fact]
    public void AWrongButRealTypeIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        // Claim Nat.zero : Prop, a type that exists but is not Nat.zero's.
        (int d, int i) = Find(traces, s => s.Kind is StepKind.Infer or StepKind.Check && s.A is Const c && c.Name.ToString() == "Nat.zero");
        string kind = traces[d].Steps[i].Kind.ToString();
        Replace(traces, d, i, traces[d].Steps[i] with { B = t.Sort(t.Zero) });

        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Step == i && f.What == kind);
    }

    [Fact]
    public void ADroppedLocalIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        // A local some later step mentions: the variable of a non-dependent arrow is introduced and never used.
        (int d, int i) = Find(traces, s => s.Kind == StepKind.Local);
        for (int dd = 0; dd < traces.Count && !UsedLater(traces[d].Steps, i); dd++)
        {
            (d, i) = (dd, -1);
            foreach (Step s in traces[dd].Steps.Where(s => s.Kind == StepKind.Local))
            {
                if (UsedLater(traces[dd].Steps, s.Index))
                {
                    i = s.Index;
                    break;
                }
            }
            if (i >= 0)
            {
                break;
            }
        }
        Assert.True(i >= 0 && UsedLater(traces[d].Steps, i), "no used local in the fixture");
        var steps = traces[d].Steps.ToList();
        // Turn the local into a harmless step that introduces nothing; later uses of its variable must fail.
        steps[i] = steps[i] with { Kind = StepKind.Rule, Rule = "DefEqSyntactic", A = t.Nat(0), B = t.Nat(0), V = null };
        traces[d] = traces[d] with { Steps = steps };

        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Reason.Contains("before it is introduced"));
    }

    [Fact]
    public void ATraceThatDoesNotConcludeItsDeclarationIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        int d = traces.FindIndex(x => x.Decl.ToString() == "Nat.add_succ");
        // Every step valid, but the steps no longer show the theorem has its type: an empty derivation.
        traces[d] = traces[d] with { Steps = [] };
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Decl.ToString() == "Nat.add_succ" && f.Reason.Contains("does not conclude"));
    }

    [Theory]
    [MemberData(nameof(Exports))]
    public void EveryDeclarationThatIsNotABlockIsConcluded(string name)
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load(name);
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Equal(r.Declarations, r.Concluded + r.BlocksChecked + r.BlocksTypesChecked + r.BlocksNested + r.BlocksNotTraced);
        Assert.True(r.BlocksChecked > 0);
        Assert.True(r.Concluded > 0);
    }

    [Fact]
    public void ADeclarationOnlyInferredNotCheckedIsNotConcluded()
    {
        // Infer-only facts assume the term is well typed; a declaration needs checking-mode facts.
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        int d = traces.FindIndex(x => x.Decl.ToString() == "Nat.add_succ");
        traces[d] = traces[d] with { Steps = traces[d].Steps.Select(s => s.Kind == StepKind.Check ? s with { Kind = StepKind.Infer } : s).ToList() };
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Decl.ToString() == "Nat.add_succ" && f.Reason.Contains("does not conclude"));
    }

    [Fact]
    public void AForeignUniverseParameterIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        int d = traces.FindIndex(x => x.Decl.ToString() == "Nat.add_succ");
        Level z = t.Param(t.Of("zzz"));
        var steps = traces[d].Steps.ToList();
        steps.Add(new Step(steps.Count, StepKind.Check, null, t.Sort(z), t.Sort(t.Succ(z)), null, steps.Count));
        traces[d] = traces[d] with { Steps = steps };
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Step == steps.Count - 1 && f.Reason.Contains("parameter"));
    }

    [Fact]
    public void ACheckedApplicationNeedsItsArgumentTypeEqualToTheDomain()
    {
        // Change one checked argument's recorded type: the application that uses it can no longer be checked.
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        for (int d = 0; d < traces.Count; d++)
        {
            List<Step> steps = traces[d].Steps.ToList();
            foreach (Step app in steps.Where(s => s.Kind == StepKind.Check && s.A is App))
            {
                Expr arg = ((App)app.A).Arg;
                int k = steps.FindLastIndex(app.Index, s => s.Kind == StepKind.Check && ReferenceEquals(s.A, arg));
                if (k < 0)
                {
                    continue;
                }
                steps[k] = steps[k] with { B = t.Const(t.Of("NotAType"), []) };
                traces[d] = traces[d] with { Steps = steps };
                ReplayReport r = new Replayer(t, env).Replay(traces);
                Assert.Contains(r.Failures, f => f.Step == app.Index && f.What == "Check");
                return;
            }
        }
        Assert.Fail("no checked application in the fixture");
    }

    [Fact]
    public void ANonPositiveInductiveIsRejected()
    {
        // From Tenet's negative corpus: Bad.mk : (Bad → False) → Bad. Tenet rejects it, so there is no trace; the
        // structural recheck needs none.
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("invalid/nonpositive.ndjson"));
        string? why = new Replayer(t, env).RecheckBlockStructure(t.Of("Bad"));
        Assert.NotNull(why);
        Assert.Contains("not strictly positive", why);
    }

    [Theory]
    [MemberData(nameof(Exports))]
    public void EveryFixtureBlockPassesTheStructuralRecheck(string name)
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load(name);
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.DoesNotContain(r.Failures, f => f.Step < 0);
        Assert.Equal(0, r.BlocksTypesChecked);
    }

    [Fact]
    public void AStepAboutAnUndeclaredDeclarationIsCaught()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        traces[0] = traces[0] with { Decl = t.Of("NotInTheExport") };
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.Contains(r.Failures, f => f.Reason.Contains("not declared"));
    }

    [Fact]
    public void NatArithmeticIsRecomputed()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("Nat.add_succ.ndjson"));
        Expr add = t.Const(t.Of("Nat.add"), []);
        Expr redex = t.App(t.App(add, t.Nat(2)), t.Nat(3));
        Expr beq = t.App(t.App(t.Const(t.Of("Nat.beq"), []), t.Nat(7)), t.Nat(7));
        var good = new DeclTrace(t.Of("Nat.add"), [
            new Step(0, StepKind.Rule, "NatLitOp", redex, t.Nat(5), null, 0),
            new Step(1, StepKind.Rule, "NatLitPred", beq, t.Const(t.Of("Bool.true"), []), null, 1),
        ]);
        var bad = new DeclTrace(t.Of("Nat.add"), [new Step(0, StepKind.Rule, "NatLitOp", redex, t.Nat(6), null, 0)]);

        // These two-step traces are not derivations of Nat.add, so only the steps' own verdicts matter here.
        Assert.DoesNotContain(new Replayer(t, env).Replay([good]).Failures, f => f.Step >= 0);
        ReplayReport r = new Replayer(t, env).Replay([bad]);
        Assert.Single(r.Failures, f => f.Step >= 0);
    }

    private static (int Decl, int Step) Find(List<DeclTrace> traces, Func<Step, bool> p)
    {
        for (int d = 0; d < traces.Count; d++)
        {
            foreach (Step s in traces[d].Steps)
            {
                if (p(s))
                {
                    return (d, s.Index);
                }
            }
        }
        throw new InvalidOperationException("no such step in the fixture");
    }

    private static bool UsedLater(IReadOnlyList<Step> steps, int local)
    {
        if (local < 0)
        {
            return false;
        }
        Expr v = steps[local].A;
        return steps.Skip(local + 1).Any(s => Mentions(s.A, v) || (s.B is not null && Mentions(s.B, v)) || (s.V is not null && Mentions(s.V, v)));
    }

    private static bool Mentions(Expr e, Expr v)
    {
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var stack = new Stack<Expr>();
        stack.Push(e);
        while (stack.Count > 0)
        {
            Expr x = stack.Pop();
            if (ReferenceEquals(x, v))
            {
                return true;
            }
            if (!x.HasFVar || !seen.Add(x))
            {
                continue;
            }
            switch (x)
            {
                case App a: stack.Push(a.Fn); stack.Push(a.Arg); break;
                case Binder b: stack.Push(b.Domain); stack.Push(b.Body); break;
                case Let l: stack.Push(l.Type); stack.Push(l.Value); stack.Push(l.Body); break;
                case Proj p: stack.Push(p.Struct); break;
            }
        }
        return false;
    }

    private static void Replace(List<DeclTrace> traces, int d, int i, Step s)
    {
        var steps = traces[d].Steps.ToList();
        steps[i] = s;
        traces[d] = traces[d] with { Steps = steps };
    }
}

public class LevelTests
{
    private readonly Terms _t = new();
    private Level U => _t.Param(_t.Of("u"));
    private Level V => _t.Param(_t.Of("v"));
    private Level One => _t.Succ(_t.Zero);

    [Fact]
    public void EquivalentLevels()
    {
        var ops = new Ops(_t);
        Assert.True(ops.Equivalent(_t.Max(U, U), U));
        Assert.True(ops.Equivalent(_t.Max(U, V), _t.Max(V, U)));
        Assert.True(ops.Equivalent(_t.IMax(U, _t.Zero), _t.Zero));
        Assert.True(ops.Equivalent(_t.IMax(_t.Zero, U), U));
        Assert.True(ops.Equivalent(_t.Max(_t.Succ(U), One), _t.Succ(U)));
        Assert.True(ops.Equivalent(_t.IMax(U, _t.Succ(V)), _t.Max(U, _t.Succ(V))));
        // v = 0: both are 0. v ≥ 1: both are max u v.
        Assert.True(ops.Equivalent(_t.Max(_t.IMax(U, V), V), _t.IMax(U, V)));
    }

    [Fact]
    public void DifferentLevels()
    {
        var ops = new Ops(_t);
        Assert.False(ops.Equivalent(_t.Max(U, V), U));
        Assert.False(ops.Equivalent(_t.IMax(U, V), _t.Max(U, V)));   // differ when v = 0 and u > 0
        Assert.False(ops.Equivalent(_t.Succ(U), U));
        Assert.False(ops.Equivalent(One, _t.Zero));
    }

    [Fact]
    public void LeansSimplifyingConstructors()
    {
        var ops = new Ops(_t);
        Assert.Same(One, ops.MkMax(One, One));
        Assert.Same(_t.Succ(U), ops.MkMax(U, _t.Succ(U)));
        Assert.Same(U, ops.MkMax(_t.Zero, U));
        Assert.Same(_t.Zero, ops.MkIMax(U, _t.Zero));
        Assert.Same(U, ops.MkIMax(One, U));
        Assert.Same(_t.Max(U, One), ops.MkIMax(U, One));
    }
}
