using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using MmExpr = TenetZfc.Metamath.Expr;

namespace TenetZfc.Tests;

/// <summary>
/// The deduction framework and congruence prover, on set.mm's addlid: |- ( A e. CC -> ( 0 + A ) = A ). Needs set.mm
/// (TENET_ZFC_SETMM); the generated theorems are checked by both verifiers when TENET_ZFC_METAMATH and
/// TENET_ZFC_MMVERIFY are set too.
/// </summary>
public class DeductionTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void CongruenceRewritesInsideClassesAndFormulas()
    {
        if (SetMm is null)
        {
            return;
        }
        var sw = Stopwatch.StartNew();
        var db = Database.Read(Path.Combine(SetMm, "set.mm"));
        output.WriteLine($"read {sw.ElapsedMilliseconds}ms");
        var pr = new Prover(db);
        var d = new Deduction(pr);
        var fact = (new List<string> { "cA", "addlid" }, db["addlid"].Expr);

        // A class context with two holes: oveq12d at the top, oveq1d below.
        var cls = d.Congruence("class", "( ( Z + 1 ) + Z )", "Z", fact);
        Assert.Equal("|- ( A e. CC -> ( ( ( 0 + A ) + 1 ) + ( 0 + A ) ) = ( ( A + 1 ) + A ) )", cls.Proves.ToString());

        // A formula: through ->, =, #, <" ">.
        var wff = d.Congruence("wff", "( Z = D -> ( # ` <\" Z \"> ) = E )", "Z", fact);
        Assert.Equal("|- ( A e. CC -> ( ( ( 0 + A ) = D -> ( # ` <\" ( 0 + A ) \"> ) = E ) <-> ( A = D -> ( # ` <\" A \"> ) = E ) ) )", wff.Proves.ToString());

        output.WriteLine($"congruence {sw.ElapsedMilliseconds}ms");
        // Symmetry and transitivity.
        var back = d.Trans(fact, d.Symm(fact));
        Assert.Equal("|- ( A e. CC -> ( 0 + A ) = ( 0 + A ) )", back.Proves.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        output.WriteLine($"symm/trans {sw.ElapsedMilliseconds}ms");
        var w = new Writer("set.mm", "tenet-zfc deduction test");
        w.Theorem("lean-test-cong-class", "test", cls.Proves, cls.Proof);
        w.Theorem("lean-test-cong-wff", "test", wff.Proves, wff.Proof);
        w.Theorem("lean-test-symm-trans", "test", back.Proves, back.Proof);
        string file = Path.Combine(SetMm, $"tenet-zfc-ded-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            Assert.DoesNotContain("?Error", Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _));
            output.WriteLine($"metamath {sw.ElapsedMilliseconds}ms");
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            output.WriteLine($"mmverify {sw.ElapsedMilliseconds}ms");
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
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
