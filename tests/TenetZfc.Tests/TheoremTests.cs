using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// Theorems through the model (docs/milestone3.md, "Theorems through the model"), on theorems.ndjson: Nat.add_zero,
/// Nat.zero_add, Nat.succ_add and List.length_append with their dependencies, from Lean 4.36.0's Init.
/// The fast tests need nothing else. Proving a theorem takes minutes, so it runs only when TENET_ZFC_THEOREMS is set
/// (with TENET_ZFC_SETMM); both verifiers check it when TENET_ZFC_METAMATH and TENET_ZFC_MMVERIFY are set too.
/// </summary>
public class TheoremTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void MonomorphizationNamesEachInstanceAndKeepsARecursorsMotiveLevel()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
        var mono = new Monomorph(t, env);
        Level one = t.Succ(t.Zero);
        Assert.Equal("PProd.{1,0}", $"{mono.Instance(t.Of("PProd"), [one, t.Zero])}");
        Assert.Equal("Nat.add", $"{mono.Instance(t.Of("Nat.add"), [])}");
        // List.rec.{v, u} at u = 0: the instance of List.{0}, then .rec, with v kept as a parameter.
        Name rec = mono.Instance(t.Of("List.rec"), [t.Succ(one), t.Zero]);
        Assert.Equal("List.{0}.rec", $"{rec}");
        Assert.Single(mono.Env.Find(rec)!.LevelParams);
        // The instance's references are instances too: Nat.below.{1} uses Nat.rec at level 2.
        Name below = mono.Instance(t.Of("Nat.below"), [one]);
        Assert.Contains("Nat.rec.{((0+1)+1)}", $"{mono.Env.Find(below)!.Value}");
        Assert.Contains("PProd.{1,1}", $"{mono.Env.Find(below)!.Value}");
    }

    [Fact]
    public void InTowerModeASortValuedMotiveIsInTheRecursorsDomain()
    {
        // The single universe made Nat.below's motive ( z e. Nat |-> U ) need U e. U, so Nat.below was (/). In tower
        // mode the motive returns ( U ` (/) ), and the recursor's motives range over the whole tower, U. ran U.
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
        var mono = new Monomorph(t, env);
        var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true, tower: true);
        Name below = mono.Instance(t.Of("Nat.below"), [t.Succ(t.Zero)]);
        m.Define(below);
        string decls = m.Declarations;
        Assert.Contains("df-lean.-tower $a |- lean.-tower = { f | ( ( f : _om --> Univ /\\ _om e. ( f ` (/) ) ) /\\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ) }", decls);
        Assert.Contains("lean.Nat.rec = ( u e. lean.-tower |-> ( x e. ( U. ran u ^m ( lean.Nat ` u ) ) |->", decls);
        Assert.Contains("( ( lean.Nat.rec ` u ) ` ( z e. ( lean.Nat ` u ) |-> ( u ` (/) ) ) )", decls);
        // Labels can't hold braces: the instance's syntax axiom and definition are labelled c.u1.
        Assert.Contains("clean.Nat.below.u1 $a class lean.Nat.below.{1} $.", decls);
        Assert.Contains("df-lean.Nat.below.u1 $a |- lean.Nat.below.{1} = ", decls);
    }

    [Fact]
    public void ATheoremOutsideTheFragmentIsRefusedWithTheReason()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
        var tr = new TheoremTranslator(t, env, new Prover(new Database()));
        var e = Assert.Throws<Model.Refused>(() => tr.Prove(t.Of("Nat.add")));
        Assert.Equal("Nat.add is not a theorem", e.Message);
        e = Assert.Throws<Model.Refused>(() => tr.Prove(t.Of("No.such.theorem")));
        Assert.Equal("No.such.theorem is not in the export", e.Message);
    }

    [Fact]
    public void NatAddZeroIsProvedThroughTheModelAndVerifies()
    {
        if (SetMm is null || System.Environment.GetEnvironmentVariable("TENET_ZFC_THEOREMS") is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var tr = new TheoremTranslator(t, env, pr);
        var (stmt, proof) = tr.Prove(t.Of("Nat.add_zero"));
        output.WriteLine($"{stmt} ({proof.Count} steps)");
        Assert.StartsWith("|- ( ( U e. lean.-tower /\\ A e. ( lean.Nat ` U ) ) -> (/) e. ( ( ( ( lean.Eq.{1} ` U ) ` ( lean.Nat ` U ) ) ` ", stmt.ToString());
        Assert.EndsWith(" ` A ) )", stmt.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc theorem test", pr.Database);
        w.Raw(tr.Declarations);
        w.Theorem("lean-test-Nat.add_zero", "test", stmt, proof, DistinctVars.Required(pr.Database, proof).Select(p => $"{p.Item1} {p.Item2}"));
        string file = Path.Combine(SetMm, $"tenet-zfc-thm-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
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

    private static string Run(string exe, string dir, string args, out int code)
    {
        var psi = new ProcessStartInfo(exe, args) { WorkingDirectory = dir, RedirectStandardOutput = true, RedirectStandardError = true };
        using var p = Process.Start(psi)!;
        string o = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd();
        p.WaitForExit();
        code = p.ExitCode;
        return o;
    }
}
