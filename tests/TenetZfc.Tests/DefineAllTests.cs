using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>define-all (docs/milestone3.md, "The Init-wide run"): chunks that stand alone, and refusals that don't stop the run.</summary>
public class DefineAllTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void TargetsAreEveryConstantButTheoremsAndAxiomsInExportOrder()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("natle.ndjson"));
        var targets = new DefineAll(t, env, "set.mm").Targets();
        Assert.DoesNotContain(targets, c => c.Kind is ConstKind.Theorem or ConstKind.Axiom);
        Assert.Contains(targets, c => $"{c.Name}" == "Nat.le.step");
        Assert.True(targets.FindIndex(c => $"{c.Name}" == "Nat") < targets.FindIndex(c => $"{c.Name}" == "Nat.le"));
    }

    [VerifierFact("TENET_ZFC_SETMM")]
    public void AChunkDefinesWhatItUsesAndReportsEachConstant()
    {
        if (SetMm is not string dir)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("natle.ndjson"));
        var run = new DefineAll(t, env, Path.Combine(dir, "set.mm"));
        string outDir = Directory.CreateTempSubdirectory("tenet-zfc-define-all").FullName;
        // Nat.le.refl and Nat.lt alone: the chunk must still define Nat and Nat.le, which they use.
        var picked = run.Targets().Where(c => $"{c.Name}" is "Nat.le.refl" or "Nat.lt").ToList();
        var outcomes = run.Chunk(3, picked, outDir);
        Assert.All(outcomes, o => Assert.Equal("ok", o.Status));
        Assert.Equal("none-needed", outcomes.Single(o => o.Name == "Nat.le.refl").Iota);
        string mm = File.ReadAllText(Path.Combine(outDir, "chunk-0003.mm"));
        Assert.Contains("df-lean.Nat $a", mm);
        Assert.Contains("df-lean.Nat.le $a", mm);
        Assert.Contains("lean-Nat.lt-eq $p", mm);
        Assert.DoesNotContain("lean-Nat-eq $p", mm);   // dependencies are defined, but only the chunk's own constants get theorems
        Assert.Equal(3, File.ReadAllLines(Path.Combine(outDir, "chunk-0003.tsv")).Length);
    }

    [Fact]
    public void RefusalReasonsAreCountedWithoutTheConstantsName()
    {
        Assert.Equal("X: the name has characters a set.mm token can't",
            DefineAll.Category("decidable_of_iff': the name has characters a set.mm token can't"));
        Assert.Equal("X is a mutual or nested inductive type; not in the model yet",
            DefineAll.Category("Lean.Syntax is a mutual or nested inductive type; not in the model yet"));
    }
}
