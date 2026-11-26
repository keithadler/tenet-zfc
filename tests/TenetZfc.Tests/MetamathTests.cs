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

    [Theory]
    [InlineData(1, "A")]
    [InlineData(20, "T")]
    [InlineData(21, "UA")]
    [InlineData(40, "UT")]
    [InlineData(41, "VA")]
    [InlineData(120, "YT")]
    [InlineData(121, "UUA")]
    [InlineData(620, "YYT")]
    [InlineData(621, "UUUA")]
    public void StepNumbersAreWrittenAsTheMetamathBookSays(int number, string letters)
    {
        var sb = new System.Text.StringBuilder();
        CompressedProof.AppendNumber(sb, number);
        Assert.Equal(letters, sb.ToString());
    }

    private static Func<string, int> ArityIn(Database db) => l => db[l].Kind is 'a' or 'p' ? db[l].Hyps.Count : 0;

    [Fact]
    public void ARepeatedSubproofIsWrittenOnceAndReferredTo()
    {
        Database db = TinyDb();
        // ( ( p -> q ) -> ( p -> q ) ): the subproof of ( p -> q ) twice. p and q are the mandatory hypotheses 1 and 2,
        // wi is label 3, and the saved ( p -> q ) is step 4.
        var flat = new Prover(db).SyntaxProof(MmExpr.Of("wff ( ( p -> q ) -> ( p -> q ) )"));
        Assert.Equal(["wp", "wq", "wi", "wp", "wq", "wi", "wi"], flat);
        var (labels, letters) = CompressedProof.Compress(flat, ["wp", "wq"], ArityIn(db));
        Assert.Equal(["wi"], labels);
        Assert.Equal("ABCZDC", letters);
        Assert.Equal(flat, CompressedProof.Expand(labels, letters, ["wp", "wq"], ArityIn(db)));
    }

    [Fact]
    public void CompressionRoundTripsAndSharesNestedRepeats()
    {
        Database db = TinyDb();
        var pr = new Prover(db);
        // A wff whose repeats nest: X = ( p -> ( q -> r ) ), Y = ( X -> X ), and the whole is ( Y -> ( Y -> X ) ).
        string x = "( p -> ( q -> r ) )", y = $"( {x} -> {x} )";
        var flat = pr.SyntaxProof(MmExpr.Of($"wff ( {y} -> ( {y} -> {x} ) )"));
        var mandatory = db.MandatoryHyps(MmExpr.Of($"|- ( {y} -> ( {y} -> {x} ) )")).Select(h => h.Label).ToList();
        Assert.Equal(["wp", "wq", "wr"], mandatory);
        var (labels, letters) = CompressedProof.Compress(flat, mandatory, ArityIn(db));
        Assert.Equal(flat, CompressedProof.Expand(labels, letters, mandatory, ArityIn(db)));
        // X is built once and saved (E), then Y from it and saved (F); ( q -> r ) repeats only inside X, so it is not.
        Assert.Equal(29, flat.Count);
        Assert.Equal("ABCDDZEDZFEDD", letters);
    }

    [Fact]
    public void ASharedProofCompressesAsItsExpansionDoes()
    {
        // With sharing on, the prover makes long syntax proofs and long proofs into shared steps (@n); compressing the
        // DAG must give exactly what compressing the flat proof gives, and expanding it must give the flat proof.
        Database db = TinyDb();
        var flatPr = new Prover(db);
        var sharedPr = new Prover(db) { Sharing = true };
        string x = "( p -> ( q -> r ) )", y = $"( {x} -> ( {x} -> {x} ) )";
        (List<string>, MmExpr) Build(Prover pr) =>
            pr.Apply("ax-1", new Dictionary<string, string> { ["p"] = y, ["q"] = $"( {y} -> {x} )" });
        var (flat, fe) = Build(flatPr);
        var (dag, de) = Build(sharedPr);
        Assert.Equal(fe, de);
        Assert.Contains(dag, SharedProofs.IsRef);
        Assert.True(dag.Count < flat.Count);
        Assert.Equal(flat, db.Shared.Expand(dag));
        Assert.Equal(flat.Count, db.Shared.Size(dag));
        var mandatory = db.MandatoryHyps(fe).Select(h => h.Label).ToList();
        var (fl, fz) = CompressedProof.Compress(flat, mandatory, ArityIn(db));
        var (dl, dz) = CompressedProof.Compress(dag, mandatory, ArityIn(db), db.Shared);
        Assert.Equal(fl, dl);
        Assert.Equal(fz, dz);
        Assert.Equal(DistinctVars.Required(db, flat), DistinctVars.Required(db, dag));
        // The same syntax twice is one shared step.
        Assert.Equal(dag, Build(sharedPr).Item1);
    }

    [Fact]
    public void AProofThatDoesNotLeaveOneExpressionIsRefused()
    {
        Database db = TinyDb();
        Assert.Throws<InvalidOperationException>(() => CompressedProof.Compress(["wp", "wq"], [], ArityIn(db)));
        Assert.Throws<InvalidOperationException>(() => CompressedProof.Compress(["wp", "wi"], [], ArityIn(db)));
    }

    /// <summary>
    /// Compressed proofs, checked by both real verifiers against set.mm; and the same file with one letter of a proof
    /// changed, which both must reject.
    /// </summary>
    [Fact]
    public void CompressedProofsPassBothVerifiersAndACorruptedOneFails()
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
        var w = new Writer("set.mm", "tenet-zfc compressed proof test", db);
        foreach ((long a, long b) in new[] { (2L, 2L), (7L, 5L), (0L, 6L) })
        {
            var p = bridge.Add(a, b)!.Value;
            w.Theorem($"lean-test-cadd-{a}-{b}", "test", p.Proves, p.Proof);
        }
        string text = w.ToString();
        Assert.Matches(@"\$=\s+\( ", text);
        // Corrupt the first theorem's proof: its last step (the final assertion) becomes the step before it.
        int start = text.IndexOf("$=", StringComparison.Ordinal);
        int end = text.IndexOf(" $.", start, StringComparison.Ordinal);
        int last = end - 1;
        char wrong = text[last] == 'A' ? 'B' : (char)(text[last] - 1);
        string corrupted = text[..last] + wrong + text[(last + 1)..];
        string good = Path.Combine(dir, $"tenet-zfc-test-{Guid.NewGuid():N}.mm");
        string bad = Path.Combine(dir, $"tenet-zfc-test-bad-{Guid.NewGuid():N}.mm");
        File.WriteAllText(good, text);
        File.WriteAllText(bad, corrupted);
        try
        {
            string mmOut = Run(metamath, dir, $"\"read {Path.GetFileName(good)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mmOut);
            Assert.Contains("verified", mmOut);
            Run("python3", dir, $"-I \"{mmverify}\" \"{Path.GetFileName(good)}\"", out int code);
            Assert.Equal(0, code);

            string badOut = Run(metamath, dir, $"\"read {Path.GetFileName(bad)}\" \"verify proof *\" \"exit\"", out _);
            Assert.Contains("?Error", badOut);
            Run("python3", dir, $"-I \"{mmverify}\" \"{Path.GetFileName(bad)}\"", out int badCode);
            Assert.NotEqual(0, badCode);
        }
        finally
        {
            File.Delete(good);
            File.Delete(bad);
        }
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
