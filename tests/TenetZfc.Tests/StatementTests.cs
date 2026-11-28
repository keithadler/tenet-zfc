using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;
using MmExpr = TenetZfc.Metamath.Expr;

namespace TenetZfc.Tests;

/// <summary>
/// Statement translation and the set.mm cross-check, on List.length_append and its dependencies (Lean 4.36.0's Init,
/// exported by leanout as `leanout Init -- List.length_append`). The cross-check needs set.mm (TENET_ZFC_SETMM).
/// </summary>
public class StatementTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);

    private static (Terms T, Env Env) Load()
    {
        var t = new Terms();
        return (t, Reader.ReadExport(t, Fixture("lenapp.ndjson")));
    }

    [Theory]
    [InlineData("List.length_append", "|- ( ( B e. Word A /\\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` B ) + ( # ` C ) ) )")]
    [InlineData("Nat.zero_add", "|- ( A e. NN0 -> ( 0 + A ) = A )")]
    [InlineData("Nat.succ_add", "|- ( ( A e. NN0 /\\ B e. NN0 ) -> ( ( A + 1 ) + B ) = ( ( A + B ) + 1 ) )")]
    [InlineData("trivial", "|- T.")]
    public void StatementsTranslate(string thm, string expected)
    {
        (Terms t, Env env) = Load();
        var st = new StatementTranslator(t);
        Assert.Equal(expected, st.Statement(env.Find(t.Of(thm))!.Type));
    }

    [Fact]
    public void ATermOutsideTheTableIsNamed()
    {
        (Terms t, Env env) = Load();
        var st = new StatementTranslator(t);
        // congrArg's statement quantifies over functions: outside the table so far.
        Assert.Null(st.Statement(env.Find(t.Of("congrArg"))!.Type));
        Assert.NotNull(st.Why);
    }

    [Fact]
    public void TheReplayOfTheExportIsComplete()
    {
        (Terms t, Env env) = Load();
        ReplayReport r = new Replayer(t, env).Replay(Reader.ReadTrace(t, Fixture("lenapp.trace.ndjson")));
        Assert.True(r.Ok, r.Format());
        Assert.Equal(r.Steps, r.Count(Verdict.Verified));
    }

    [VerifierFact("TENET_ZFC_SETMM")]
    public void LengthAppendIsCcatlenAndAWrongStatementIsNot()
    {
        string? dir = System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");
        if (dir is null)
        {
            return;
        }
        var pr = new Prover(Database.Read(Path.Combine(dir, "set.mm")));
        var right = MmExpr.Of("|- ( ( B e. Word A /\\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` B ) + ( # ` C ) ) )");
        Assert.Equal("ccatlen", pr.FindInstance(right)?.Label);
        var applied = pr.Apply("ccatlen", pr.FindInstance(right)!.Value.Subst);
        Assert.Equal(right, applied.Proves);
        // The lengths in the wrong order: not what ccatlen says, and no other theorem may be taken for it.
        var wrong = MmExpr.Of("|- ( ( B e. Word A /\\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` C ) + ( # ` B ) ) )");
        Assert.NotEqual("ccatlen", pr.FindInstance(wrong)?.Label);
    }
}
