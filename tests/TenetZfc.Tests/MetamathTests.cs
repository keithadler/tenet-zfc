using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using MmExpr = TenetZfc.Metamath.Expr;

namespace TenetZfc.Tests;

/// <summary>
/// The Metamath emitter. Unit tests use a small database written here; the end-to-end test needs set.mm and both
/// verifiers, found through TENET_ZFC_SETMM (the directory holding set.mm), TENET_ZFC_METAMATH (the metamath-exe
/// binary) and TENET_ZFC_MMVERIFY (mmverify.py), and is skipped without them.
/// </summary>
public class MetamathTests
{
    // Implication and modus ponens, with a syntax axiom for wffs: enough to check parsing and proof assembly.
    private const string Tiny = """
        $c ( ) -> wff |- $.
        $v p q r $.
        wp $f wff p $.
        wq $f wff q $.
        wr $f wff r $.
        wi $a wff ( p -> q ) $.
        ${ min $e |- p $. maj $e |- ( p -> q ) $. mp $a |- q $. $}
        ax-1 $a |- ( p -> ( q -> p ) ) $.
        """;

    private static Database TinyDb()
    {
        string path = Path.Combine(Path.GetTempPath(), $"tiny-{Guid.NewGuid():N}.mm");
        File.WriteAllText(path, Tiny);
        try
        {
            return Database.Read(path);
        }
        finally
        {
            File.Delete(path);
        }
    }

    [Fact]
    public void MandatoryHypothesesAreInDatabaseOrder()
    {
        Database db = TinyDb();
        Assert.Equal(["wp", "wq", "min", "maj"], db["mp"].Hyps.Select(h => h.Label));
        Assert.Equal(["wp", "wq"], db["ax-1"].Hyps.Select(h => h.Label));
        Assert.Equal(["wp", "wq"], db["wi"].Hyps.Select(h => h.Label));
    }

    [Fact]
    public void ExpressionsParseIntoSyntaxProofs()
    {
        var pr = new Prover(TinyDb());
        // ( p -> ( q -> p ) ): wi applied to p and to wi applied to q and p.
        Assert.Equal(["wp", "wq", "wp", "wi", "wi"], pr.SyntaxProof(MmExpr.Of("wff ( p -> ( q -> p ) )")));
        Assert.Null(pr.Parse("wff", ["(", "p", "->", ")"]));
    }

    [Fact]
    public void ApplyingAnAssertionBuildsTheKnownProof()
    {
        // From |- p, prove |- ( q -> p ): the proof every Metamath tutorial writes by hand.
        var pr = new Prover(TinyDb());
        var h1 = (new List<string> { "h1" }, MmExpr.Of("|- p"));
        var ax = pr.Apply("ax-1", new Dictionary<string, string> { ["p"] = "p", ["q"] = "q" });
        var th = pr.Apply("mp", new Dictionary<string, string> { ["p"] = "p", ["q"] = "( q -> p )" }, h1, ax);
        Assert.Equal(MmExpr.Of("|- ( q -> p )"), th.Proves);
        Assert.Equal(["wp", "wq", "wp", "wi", "h1", "wp", "wq", "ax-1", "mp"], th.Proof);
    }

    [Fact]
    public void AWrongHypothesisIsRefusedBeforeAnyVerifierSeesIt()
    {
        var pr = new Prover(TinyDb());
        var wrong = (new List<string> { "h1" }, MmExpr.Of("|- q"));
        var ax = pr.Apply("ax-1", new Dictionary<string, string> { ["p"] = "p", ["q"] = "q" });
        Assert.Throws<InvalidOperationException>(() =>
            pr.Apply("mp", new Dictionary<string, string> { ["p"] = "p", ["q"] = "( q -> p )" }, wrong, ax));
    }

    [Fact]
    public void NumeralsAreDecimal()
    {
        Assert.Equal("0", Bridge.Numeral(0));
        Assert.Equal("7", Bridge.Numeral(7));
        Assert.Equal("; 1 2", Bridge.Numeral(12));
        Assert.Equal("; ; 1 0 5", Bridge.Numeral(105));
    }

    /// <summary>Generated arithmetic theorems, checked by both real verifiers against set.mm.</summary>
    [Fact]
    public void GeneratedArithmeticPassesBothVerifiers()
    {
        string? dir = System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");
        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (dir is null || metamath is null || mmverify is null)
        {
            return;   // set.mm and the verifiers are not available here
        }
        var db = Database.Read(Path.Combine(dir, "set.mm"));
        var bridge = new Bridge(new Prover(db), db);
        var w = new Writer("set.mm", "tenet-zfc test output");
        // The table as written, the other order through commutativity, and both zero cases.
        foreach ((long a, long b) in new[] { (0L, 0L), (2L, 2L), (3L, 4L), (7L, 5L), (6L, 0L), (0L, 6L) })
        {
            var p = bridge.Add(a, b)!.Value;
            w.Theorem($"lean-test-add-{a}-{b}", "test", p.Proves, p.Proof);
        }
        string file = Path.Combine(dir, $"tenet-zfc-test-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mmOut = Run(metamath, dir, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mmOut);
            Assert.Contains("verified", mmOut);
            Run("python3", dir, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
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
