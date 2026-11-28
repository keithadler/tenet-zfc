using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>theorem-all (docs/milestone3.md, "Theorems across Init"): chunks of theorems, an outcome per theorem, resuming past a crash.</summary>
public class TheoremAllTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void TargetsAreTheTheoremsInExportOrderAndEveryNthOfThem()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theoremall.ndjson"));
        var run = new TheoremAll(t, env, "set.mm");
        var all = run.Targets();
        Assert.All(all, c => Assert.Equal(ConstKind.Theorem, c.Kind));
        Assert.Contains(all, c => $"{c.Name}" == "congrArg");
        Assert.True(all.FindIndex(c => $"{c.Name}" == "Eq.symm") < all.FindIndex(c => $"{c.Name}" == "HEq.symm"));
        var every3 = run.Targets(3);
        Assert.Equal((all.Count + 2) / 3, every3.Count);
        Assert.Equal(all[3].Name, every3[1].Name);
    }

    [VerifierFact("TENET_ZFC_SETMM")]
    public void AChunkRecordsEachTheoremAndSkipsOneThatCrashedTheProcess()
    {
        if (SetMm is not string dir)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theoremall.ndjson"));
        var run = new TheoremAll(t, env, Path.Combine(dir, "set.mm")) { BudgetSeconds = 120 };
        string outDir = Directory.CreateTempSubdirectory("tenet-zfc-theorem-all").FullName;
        var picked = run.Targets().Where(c => $"{c.Name}" is "Eq.symm" or "And.symm" or "Nat.le_of_succ_le_succ" or "Iff.symm").ToList();
        // A run that ended on Iff.symm leaves its progress file: the next run records it as a crash and goes on.
        File.WriteAllText(Path.Combine(outDir, "chunk-0002.progress"), "now Iff.symm\n3/4\n");
        var outcomes = run.Chunk(2, picked, outDir);
        Assert.Equal("proved", outcomes.Single(o => o.Name == "Eq.symm").Status);
        Assert.Equal("proved", outcomes.Single(o => o.Name == "And.symm").Status);
        // Refused until induction on Nat.le came to the model (RecPropInduction.cs).
        Assert.Equal("proved", outcomes.Single(o => o.Name == "Nat.le_of_succ_le_succ").Status);
        Assert.Equal("crash", outcomes.Single(o => o.Name == "Iff.symm").Status);
        string mm = File.ReadAllText(Path.Combine(outDir, "chunk-0002.mm"));
        Assert.Contains("lean-thm-Eq.symm $p", mm);
        Assert.Contains("lean-thm-And.symm $p", mm);
        Assert.DoesNotContain("lean-thm-Iff.symm $p", mm);
        Assert.Equal(5, File.ReadAllLines(Path.Combine(outDir, "chunk-0002.tsv")).Length);
        Assert.False(File.Exists(Path.Combine(outDir, "chunk-0002.progress")));
    }

    [Fact]
    public void TheThreadClockCountsWorkNotSleep()
    {
        if (ThreadCpu.Seconds() is not double t0)
        {
            return;   // no thread clock on this platform: budgets fall back to wall time
        }
        Thread.Sleep(300);
        double slept = ThreadCpu.Seconds()!.Value - t0;
        Assert.True(slept < 0.2, $"sleeping used {slept}s of CPU");
        // Spinning advances it (on a loaded machine slowly: spin until it moves, for at most 20 s).
        double x = 0, t1 = ThreadCpu.Seconds()!.Value;
        var sw = System.Diagnostics.Stopwatch.StartNew();
        while (ThreadCpu.Seconds()!.Value - t1 < 0.05 && sw.Elapsed.TotalSeconds < 20)
        {
            x += Math.Sqrt(x + 1);
        }
        Assert.True(ThreadCpu.Seconds()!.Value - t1 >= 0.05, $"spinning used no CPU ({x})");
    }
}
