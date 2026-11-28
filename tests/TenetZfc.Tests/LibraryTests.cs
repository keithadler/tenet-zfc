using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// A library of typing lemmas (docs/milestone3.md, "A library of lemmas"): a .mm file that includes set.mm, read
/// with it, whose lemmas a later run cites instead of proving again.
/// </summary>
public class LibraryTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void AFileIsReadAfterTheFilesItIncludes()
    {
        string dir = Directory.CreateTempSubdirectory("tenet-zfc-chain").FullName;
        try
        {
            // The innermost file describes the include statement in a comment, as set.mm's header does.
            File.WriteAllText(Path.Combine(dir, "a.mm"), "$( A file is included with $[ other.mm $] . $)\n$c wff $.\n");
            File.WriteAllText(Path.Combine(dir, "b.mm"), "$( A library. $)\n$[ a.mm $]\n$c class $.\n");
            File.WriteAllText(Path.Combine(dir, "c.mm"), "$( On the library. $)\n$[ b.mm $]\n$c set $.\n");
            Assert.Equal(["a.mm", "b.mm", "c.mm"], Database.IncludeChain(Path.Combine(dir, "c.mm")).Select(Path.GetFileName));
            Assert.Equal(["a.mm"], Database.IncludeChain(Path.Combine(dir, "a.mm")).Select(Path.GetFileName));
            Database db = Database.ReadChain(Path.Combine(dir, "c.mm"));
            Assert.True(db.IsConstant("wff") && db.IsConstant("class") && db.IsConstant("set"));
            File.WriteAllText(Path.Combine(dir, "d.mm"), "$[ d.mm $]\n");
            Assert.Throws<InvalidDataException>(() => Database.IncludeChain(Path.Combine(dir, "d.mm")));
        }
        finally
        {
            Directory.Delete(dir, recursive: true);
        }
    }

    [VerifierFact("TENET_ZFC_SETMM")]
    public void ALibrarysLemmaIsCitedNotProvedAgainAndADifferentOneIsRefused()
    {
        if (SetMm is null)
        {
            return;
        }
        string setmm = Path.Combine(SetMm, "set.mm");
        string lib = Path.Combine(SetMm, $"tenet-zfc-library-{Guid.NewGuid():N}.mm"), bad = lib.Replace(".mm", "-bad.mm");
        try
        {
            // Build: Nat.add_zero's typing lemma, written as a file that includes set.mm.
            var t = new Terms();
            Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
            var pr = new Prover(Database.Read(setmm));
            var build = new TheoremTranslator(t, env, pr);
            Assert.Equal("lean-ty-Nat.add_zero", build.TypeConstant("Nat.add_zero"));
            Assert.Equal("lean-ty-Nat.add_zero", build.TypeConstant("lean-ty-Nat.add_zero"));   // by label: the same lemma
            Assert.Equal(0, build.LibraryLemmas);
            var w = new Writer("set.mm", "a library", pr.Database);
            w.Raw(build.Declarations);
            File.WriteAllText(lib, w.ToString());
            Assert.Contains("lean-ty-Nat.add_zero $p", build.Declarations);

            // Use: a fresh translator on set.mm and the library cites the lemma and writes nothing for it.
            var t2 = new Terms();
            var use = new TheoremTranslator(t2, Reader.ReadExport(t2, Fixture("theorems.ndjson")), new Prover(Database.ReadChain(lib)));
            Assert.Equal("lean-ty-Nat.add_zero", use.TypeConstant("Nat.add_zero"));
            Assert.Equal(1, use.LibraryLemmas);
            Assert.DoesNotContain("lean-ty-Nat.add_zero $p", use.Declarations);
            Assert.DoesNotContain("df-lean.Nat $a", use.Declarations);   // its definitions come from the library too

            // A library whose lemma states something else is refused, by name.
            string text = File.ReadAllText(lib);
            int i = text.IndexOf("lean-ty-Nat.add_zero $p", StringComparison.Ordinal), j = text.IndexOf("$=", i, StringComparison.Ordinal);
            string stmt = text[i..j];
            int k = stmt.LastIndexOf("( lean.Nat ` U )", StringComparison.Ordinal);
            File.WriteAllText(bad, text[..i] + stmt[..k] + "U" + stmt[(k + "( lean.Nat ` U )".Length)..] + text[j..]);
            var t3 = new Terms();
            var refuse = new TheoremTranslator(t3, Reader.ReadExport(t3, Fixture("theorems.ndjson")), new Prover(Database.ReadChain(bad)));
            var e = Assert.Throws<Model.Refused>(() => refuse.TypeConstant("Nat.add_zero"));
            Assert.Contains("the library's lean-ty-Nat.add_zero states something else", e.Message);
        }
        finally
        {
            File.Delete(lib);
            File.Delete(bad);
        }
    }
}
