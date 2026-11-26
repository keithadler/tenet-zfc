using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;

namespace TenetZfc.Tests;

/// <summary>
/// The Nat bridge (docs/bridges.md): the model's Nat is NN0. Needs set.mm (TENET_ZFC_SETMM); both verifiers check the
/// output when TENET_ZFC_METAMATH and TENET_ZFC_MMVERIFY are set.
/// </summary>
public class BridgeTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    private const string F = NatBridge.F;
    private const string Nat = NatBridge.Nat;

    [Fact]
    public void NatIsNN0ThroughTheBridgeAndVerifies()
    {
        if (SetMm is null)
        {
            return;
        }
        var (text, proved) = NatBridge.Emit(Fixture("natadd.ndjson"), Path.Combine(SetMm, "set.mm"), [2, 4, 256]);
        var by = proved.ToDictionary(p => p.Label, p => p.Statement.ToString());

        // The headline statements, in set.mm's vocabulary.
        Assert.Equal($"|- ( U e. Univ -> {F} : {Nat} -1-1-onto-> NN0 )", by["lean-nat-f1o"]);
        Assert.Equal($"|- ( U e. Univ -> ( {F} ` ( lean.Nat.zero ` U ) ) = 0 )", by["lean-nat-fzero"]);
        Assert.Equal($"|- ( ( U e. Univ /\\ A e. {Nat} ) -> ( {F} ` ( ( lean.Nat.succ ` U ) ` A ) ) = ( ( {F} ` A ) + 1 ) )", by["lean-nat-fsucc"]);
        Assert.Equal($"|- ( A e. NN0 -> ( {F} ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` A ) ) ) = A )", by["lean-nat-flitnum"]);
        Assert.Equal($"|- ( {F} ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` ; ; 2 5 6 ) ) ) = ; ; 2 5 6", by["lean-nat-lit-256"]);
        string rules = NatBridge.Rules("( lean.Nat.add ` U )");
        Assert.Equal($"|- ( ( {rules} /\\ ( A e. {Nat} /\\ B e. {Nat} ) ) -> ( {F} ` ( ( ( lean.Nat.add ` U ) ` A ) ` B ) ) = ( ( {F} ` A ) + ( {F} ` B ) ) )",
            by["lean-nat-natadd"]);
        string two = "( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 2 ) )", four = "( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 4 ) )";
        Assert.Equal($"|- ( {rules} -> ( ( ( lean.Nat.add ` U ) ` {two} ) ` {two} ) = {four} )", by["lean-nat-natadd-2p2e4"]);
        Assert.Equal($"|- ( ( ( U e. Univ /\\ A e. ( U ^m {Nat} ) ) /\\ B e. {Nat} ) -> ( ( ( lean.Nat.below ` U ) ` A ) ` B ) = (/) )",
            by["lean-nat-belowempty"]);
        // Nothing is assumed: the output's only $a statements are the model's definitions and their syntax.
        Assert.DoesNotContain(text.Split('\n'), l => l.Contains(" $a |-") && !l.TrimStart().StartsWith("df-lean.", StringComparison.Ordinal));

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-natbridge-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, text);
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            output.WriteLine(mm[Math.Max(0, mm.Length - 2000)..]);
            Assert.DoesNotContain("?Error", mm);
            Assert.Contains("All proofs in the database were verified", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void ABrokenBridgeProofFailsToVerify()
    {
        // The verifiers, not the translator, are what the bridge rests on: break one step and they must refuse it.
        if (SetMm is null)
        {
            return;
        }
        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        if (metamath is null)
        {
            return;
        }
        var (text, _) = NatBridge.Emit(Fixture("natadd.ndjson"), Path.Combine(SetMm, "set.mm"), [], compress: false);
        // lean-nat-zns says the model's zero is not a successor; claim it is.
        string bad = text.Replace("lean-nat-zns $p |- -. <. (/) , (/) >. =", "lean-nat-zns $p |- <. (/) , (/) >. =", StringComparison.Ordinal);
        Assert.NotEqual(text, bad);
        string file = Path.Combine(SetMm, $"tenet-zfc-natbridge-bad-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, bad);
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof lean-nat-zns\" \"exit\"", out _);
            Assert.Contains("?Error", mm);
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
        string o = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd();
        p.WaitForExit();
        code = p.ExitCode;
        return o;
    }
}
