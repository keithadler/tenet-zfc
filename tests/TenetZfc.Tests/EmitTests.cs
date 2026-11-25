using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// The emitter, on the milestone 2 gate theorem two_add_two : 2 + 2 = 4 (tests/fixtures/Gate.lean, exported by
/// leanout and traced by Tenet). Translation is tested everywhere; proof emission needs set.mm and runs only where
/// TENET_ZFC_SETMM (and, for the verifier check, TENET_ZFC_METAMATH and TENET_ZFC_MMVERIFY) are set.
/// </summary>
public class EmitTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    private static (Terms T, Env Env, List<DeclTrace> Traces) Load()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("gate.ndjson"));
        return (t, env, Reader.ReadTrace(t, Fixture("gate.trace.ndjson")));
    }

    [Fact]
    public void TheGateTraceReplaysInFull()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load();
        ReplayReport r = new Replayer(t, env).Replay(traces);
        Assert.True(r.Ok, r.Format());
        Assert.Equal(r.Steps, r.Count(Verdict.Verified));
    }

    [Fact]
    public void TheStatementTranslatesThroughTheTable()
    {
        (Terms t, Env env, _) = Load();
        ConstInfo thm = env.Find(t.Of("two_add_two"))!;
        Ops.Spine(thm.Type, out List<TenetZfc.Expr> args);
        var e = new Emitter(t, null!, null!);
        Assert.Equal("( 2 + 2 )", e.Translate(args[1]));
        Assert.Equal("4", e.Translate(args[2]));
    }

    private static (Emitter Emitter, Prover Prover)? WithSetMm(Terms t)
    {
        if (SetMm is null)
        {
            return null;
        }
        var db = Database.Read(Path.Combine(SetMm, "set.mm"));
        var pr = new Prover(db);
        return (new Emitter(t, pr, new Bridge(pr, db)), pr);
    }

    [Fact]
    public void TheGateTheoremIsEmittedAndBothVerifiersAcceptIt()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load();
        if (WithSetMm(t) is not (Emitter em, _))
        {
            return;
        }
        DeclTrace d = traces.Single(x => x.Decl.ToString() == "two_add_two");
        (var proof, string? why) = em.EmitEquation(env.Find(d.Decl)!, d);
        Assert.Null(why);
        Assert.Equal("|- ( 2 + 2 ) = 4", proof!.Value.Proves.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc emit test");
        w.Theorem("lean-two_add_two", "test", proof.Value.Proves, proof.Value.Proof);
        string file = Path.Combine(SetMm!, $"tenet-zfc-emit-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            Assert.DoesNotContain("?Error", Run(metamath, SetMm!, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _));
            Run("python3", SetMm!, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void WithoutTheKernelsAdditionInTheTraceNothingIsEmitted()
    {
        // The emitter may only use arithmetic the kernel performed: drop the NatLitOp step and it must refuse.
        (Terms t, Env env, List<DeclTrace> traces) = Load();
        if (WithSetMm(t) is not (Emitter em, _))
        {
            return;
        }
        DeclTrace d = traces.Single(x => x.Decl.ToString() == "two_add_two");
        var stripped = d with { Steps = d.Steps.Where(s => s.Rule != "NatLitOp").ToList() };
        (var proof, string? why) = em.EmitEquation(env.Find(d.Decl)!, stripped);
        Assert.Null(proof);
        Assert.Contains("not a literal addition the kernel performed", why);
    }

    [Fact]
    public void AFalseStatementIsRefused()
    {
        (Terms t, Env env, List<DeclTrace> traces) = Load();
        if (WithSetMm(t) is not (Emitter em, _))
        {
            return;
        }
        DeclTrace d = traces.Single(x => x.Decl.ToString() == "two_add_two");
        ConstInfo thm = env.Find(d.Decl)!;
        // 2 + 2 = 5: the same left side, a wrong right side.
        TenetZfc.Expr head = Ops.Spine(thm.Type, out List<TenetZfc.Expr> args);
        var five = t.Nat(5);
        TenetZfc.Expr wrong = t.MkApp(head, [args[0], args[1], five]);
        typeof(ConstInfo).GetProperty(nameof(ConstInfo.Type))!.SetValue(thm, wrong);
        (var proof, string? why) = em.EmitEquation(thm, d);
        Assert.Null(proof);
        Assert.Contains("evaluate to 4 and 5", why);
    }

    private static string Run(string exe, string dir, string args, out int code)
    {
        var psi = new ProcessStartInfo(exe, args) { WorkingDirectory = dir, RedirectStandardOutput = true, RedirectStandardError = true };
        using Process p = Process.Start(psi)!;
        string output = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd();
        p.WaitForExit();
        code = p.ExitCode;
        return output;
    }
}
