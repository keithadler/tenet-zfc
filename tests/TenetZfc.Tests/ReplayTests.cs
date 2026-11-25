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
        Assert.True(r.Count(Verdict.Verified) > 0);
        Assert.Equal(r.Steps, r.Count(Verdict.Verified) + r.Count(Verdict.NotYet));
    }

    /// <summary>The rules this replayer checks, each found in the Nat.add_succ trace.</summary>
    public static TheoryData<string> CheckedRules => new()
    {
        "Beta", "Delta", "DeltaLazy", "Iota", "IotaK", "Proj", "DefEqSyntactic", "DefEqOffset",
    };

    [Theory]
    [MemberData(nameof(CheckedRules))]
    public void ChangingARecordedResultIsCaught(string rule)
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load("Nat.add_succ");
        (int d, int i) = Find(traces, s => s.Kind == StepKind.Rule && s.Rule == rule);
        Step s = traces[d].Steps[i];
        // A literal no step in these files produces: wrong for every rule.
        Replace(traces, d, i, s with { B = t.Nat(424242) });

        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.False(r.Ok);
        Assert.Contains(r.Failures, f => f.Step == i && f.What == rule);
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

        Assert.True(new Replayer(t, env).Replay([good]).Ok);
        ReplayReport r = new Replayer(t, env).Replay([bad]);
        Assert.Single(r.Failures);
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
