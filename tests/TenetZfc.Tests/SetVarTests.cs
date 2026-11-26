using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// Definitions that need more set variables than set.mm's 26 letters (docs/milestone3.md): the output declares its
/// own, xx1, xx2, …, with $v and $f setvar. Lean.Grind.Config.casesOn binds 27 Bool and Nat fields inside its
/// motive's binders, and Lean.Meta.Simp.Config.zeta's structure has more fields than set.mm has letters. Both
/// verifiers check the equations, and mmj2's definitionCheck the definitions, when the tools are set.
/// </summary>
public class SetVarTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void WhenTheLettersRunOutTheOutputDeclaresItsOwnSetVariables()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("setvars.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        m.Define(t.Of("Lean.Grind.Config.casesOn"));
        string d = m.Declarations;
        // Declared once each, before the first definition that binds it, and listed in that definition's $d.
        Assert.Contains("$v xx1 $.\nvxx1 $f setvar xx1 $.", d.Replace("\r", ""));
        Assert.Equal(1, d.Split("$v xx1 $.").Length - 1);
        Assert.True(d.IndexOf("$v xx27 $.", StringComparison.Ordinal) < d.IndexOf("df-lean.Lean.Grind.Config.casesOn $a", StringComparison.Ordinal));
        string casesOn = d[d.IndexOf("df-lean.Lean.Grind.Config.casesOn $a", StringComparison.Ordinal)..];
        Assert.Contains(" xx27 e. ", casesOn);
        string dv = d[..d.IndexOf("df-lean.Lean.Grind.Config.casesOn $a", StringComparison.Ordinal)];
        dv = dv[dv.LastIndexOf("$d ", StringComparison.Ordinal)..];
        Assert.Contains(" xx27 ", dv);
        Assert.Contains(" a ", dv);
    }

    [Fact]
    public void EquationsWithDeclaredSetVariablesVerifyAndTheirDefinitionsPassTheCheck()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("setvars.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, env, pr);
        var eqs = new List<(string, Metamath.Expr, List<string>, string[])>();
        foreach (string n in new[] { "Lean.Grind.Config.casesOn", "Lean.Meta.Simp.Config.zeta" })
        {
            var (stmt, proof, distinct) = m.Equation(t.Of(n));
            output.WriteLine($"{n}: {proof.Count} steps");
            eqs.Add(($"lean-test-{n}-eq", stmt, proof, distinct));
        }
        // casesOn's statement itself binds declared variables: its minor premise ranges over a Π-type of 27 fields.
        Assert.Contains(" xx1 ", eqs[0].Item2.ToString());
        Assert.Contains(" xx1 ", string.Join(' ', eqs[0].Item4));

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc declared set variables test");
        w.Raw(m.Declarations);
        foreach (var (label, stmt, proof, distinct) in eqs)
        {
            w.Theorem(label, "test", stmt, proof, distinct);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-setvars-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Assert.Contains("All proofs in the database were verified", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);

            string? java = System.Environment.GetEnvironmentVariable("TENET_ZFC_JAVA");
            string? mmj2 = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMJ2");
            if (java is null || mmj2 is null)
            {
                return;
            }
            string script = Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "..", "..", "scripts", "check-definitions");
            output.WriteLine(Run(script, SetMm, $"\"{java}\" \"{mmj2}\" \"{file}\"", out int defCode));
            Assert.Equal(0, defCode);
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
