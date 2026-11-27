using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>Lean names as set.mm tokens and labels (NameEscape.cs; docs/milestone3.md, "Names").</summary>
public class NameEscapeTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);

    /// <summary>A name from components: a string, or a ulong for a numeric part.</summary>
    private static Name N(Terms t, params object[] parts)
    {
        Name n = Name.Anonymous;
        foreach (object p in parts)
        {
            n = p is ulong k ? t.Num(n, k) : t.Str(n, (string)p);
        }
        return n;
    }

    [Fact]
    public void NamesAreWrittenReadably()
    {
        var t = new Terms();
        Assert.Equal("lean.Nat.add", Model.Token(t.Of("Nat.add")));
        Assert.Equal("lean.List.map-q", Model.Token(t.Of("List.map'")));
        Assert.Equal("lean.GetElem-Q.getElem-Q", Model.Token(t.Of("GetElem?.getElem?")));
        Assert.Equal("lean.Array.get-B", Model.Token(t.Of("Array.get!")));
        Assert.Equal("lean.Prod.lex_def.a-u2082", Model.Token(t.Of("Prod.lex_def.a₂")));
        Assert.Equal("lean.foo._-a.Init.Core._hyg.123", Model.Token(N(t, "foo", "_@", "Init", "Core", "_hyg", 123UL)));
        Assert.Equal("lean._private.Init.Data.0.List.go", Model.Token(N(t, "_private", "Init", "Data", 0UL, "List", "go")));
        // «term_<|>_», a parser's name, and a component holding a dot.
        Assert.Equal("lean.term_-u003c-u007c-u003e_", Model.Token(N(t, "term_<|>_")));
        Assert.Equal("lean.a-db", Model.Token(N(t, "a.b")));
        // A level suffix stays readable in tokens and becomes u0_1 in labels.
        Name inst = N(t, "Prod", "{0,1}");
        Assert.Equal("lean.Prod.{0,1}", Model.Token(inst));
        Assert.Equal("Prod.u0_1", Model.LabelOf(inst));
        Assert.Equal("List.map-q.u1", Model.LabelOf(N(t, "List", "map'", "{1}")));
        // Strings a numeric part or a level suffix would also print as.
        Assert.Equal("lean.a.-n0", Model.Token(N(t, "a", "0")));
        Assert.Equal("lean.a.-nu0_1", Model.Token(N(t, "a", "u0_1")));
        Assert.Equal("lean.a.-z", Model.Token(N(t, "a", "")));
        // Beyond the BMP, one code for the character, not two for its UTF-16 halves.
        Assert.Equal("lean.x-U01d4d0", Model.Token(N(t, "x\U0001D4D0")));
    }

    /// <summary>Names chosen to be hard: every case the escaping distinguishes, and near misses of each.</summary>
    private static List<Name> Tricky(Terms t)
    {
        string[] comps = ["a", "A", "a'", "a-q", "a?", "a!", "_@", "@", "-", "--", ".", "a.b", "a-db", "", "0", "00", "12",
            "u", "u1", "u0_1", "u0_", "u_1", "u1a", "{0}", "{0,1}", "{01}", "{", "}", ",", "{a}", "-z", "-n0", "-step",
            "step", "-case", "-lit", "-ofnum", "-tower", "eq", "-eq", "iota", "₂", "a₂", "α", "a-u2082", "\U0001D4D0",
            "\uD800", "x\uDC00y", "$", "term_$__", " ", "a b", "«»", "q", "Q", "B", "d", "m", "n"];
        var names = new List<Name>();
        foreach (string a in comps)
        {
            names.Add(N(t, a));
            names.Add(N(t, "x", a));
            names.Add(N(t, a, 7UL));
            foreach (string b in new[] { "a", "0", "{0}", "", "-" })
            {
                names.Add(N(t, a, b));
            }
        }
        names.Add(N(t, 0UL));
        names.Add(N(t, 12UL, "a"));
        names.Add(N(t, "a", 0UL, 1UL));
        return names;
    }

    /// <summary>Random names over an alphabet heavy in the characters the escaping treats specially.</summary>
    private static List<Name> Random(Terms t, int count, int seed)
    {
        var rng = new System.Random(seed);
        string alphabet = "ab0_19u{},.-'?!@zqnd₂α$ 𝓐";
        var names = new List<Name>();
        for (int i = 0; i < count; i++)
        {
            Name n = Name.Anonymous;
            int parts = rng.Next(1, 4);
            for (int j = 0; j < parts; j++)
            {
                if (rng.Next(6) == 0)
                {
                    n = t.Num(n, (ulong)rng.Next(0, 30));
                    continue;
                }
                var sb = new System.Text.StringBuilder();
                int len = rng.Next(0, 5);
                for (int k = 0; k < len; k++)
                {
                    sb.Append(alphabet[rng.Next(alphabet.Length)]);
                }
                n = t.Str(n, sb.ToString());
            }
            names.Add(n);
        }
        return names;
    }

    private static void AssertInjectiveAndReversible(Terms t, IEnumerable<Name> names)
    {
        var byToken = new Dictionary<string, Name>();
        var byLabel = new Dictionary<string, Name>();
        foreach (Name n in names.Distinct())
        {
            string esc = NameEscape.Escape(n);
            string tok = Model.Token(n)!, label = Model.LabelOf(n);
            // Round trip: Terms interns names, so the same name is the same object.
            Assert.Same(n, NameEscape.Unescape(t, esc));
            // A token is printable ASCII without $; a label only letters, digits, - _ and .
            Assert.All(tok, ch => Assert.True(ch is > ' ' and <= '~' and not '$', $"{n}: {tok}"));
            Assert.All(label, ch => Assert.True(char.IsAsciiLetterOrDigit(ch) || ch is '-' or '_' or '.', $"{n}: {label}"));
            // No component is one of the model's own, and no escape can be read as a label suffix (-eq, -iota, -N).
            Assert.DoesNotContain("--", esc);
            foreach (string part in esc.Split('.'))
            {
                Assert.DoesNotContain(part, new[] { "-step", "-case", "-lit", "-ofnum", "-tower" });
            }
            Assert.DoesNotMatch(@"-[ei0-9]", esc);
            Assert.True(byToken.TryAdd(tok, n), $"{n} and {(byToken.TryGetValue(tok, out var o1) ? o1 : null)} share the token {tok}");
            Assert.True(byLabel.TryAdd(label, n), $"{n} and {(byLabel.TryGetValue(label, out var o2) ? o2 : null)} share the label {label}");
        }
    }

    [Fact]
    public void EscapingIsOneToOneAndReversibleOnHardNames()
    {
        var t = new Terms();
        AssertInjectiveAndReversible(t, Tricky(t));
    }

    [Fact]
    public void EscapingIsOneToOneAndReversibleOnRandomNames()
    {
        var t = new Terms();
        AssertInjectiveAndReversible(t, Random(t, 20_000, 1));
    }

    [Fact]
    public void EscapingIsOneToOneAndReversibleOnTheFixturesNames()
    {
        var t = new Terms();
        var names = new List<Name>();
        foreach (string f in new[] { "syntax.ndjson", "strings.ndjson", "library.ndjson", "theorems.ndjson", "axioms.ndjson" })
        {
            Env env = Reader.ReadExport(t, Fixture(f));
            names.AddRange(env.All.Select(c => c.Name));
        }
        Assert.Contains(names, n => $"{n}".Contains('\''));
        AssertInjectiveAndReversible(t, names);
    }

    [Fact]
    public void UnescapingRejectsWhatEscapingNeverWrites()
    {
        var t = new Terms();
        foreach (string bad in new[] { "a-", "a-x", "a-e", "-step", "-nab", "-n", "u1", "a.u0_1", "a-u20", "a-u20G1", "a-uABCD",
            "a-U00ffff", "a.-z1", "a b", "a'", "a..b", "{0" })
        {
            Assert.Throws<System.FormatException>(() => NameEscape.Unescape(t, bad));
        }
    }

    [Fact]
    public void MonomorphRefusesAnInstanceNamedLikeAnExportConstant()
    {
        // An export constant named c.«{0}», next to a polymorphic c: c's instance at 0 would take its name and token.
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("model.ndjson"));
        ConstInfo id = env.All.First(c => c.LevelParams.Length == 1 && c.Kind == ConstKind.Definition);
        Env clash = new Monomorph(t, env).Env;   // an overlay of the export, to add the twin to
        var twin = new ConstInfo { Name = t.Str(id.Name, "{0}"), Kind = id.Kind, LevelParams = [], Type = id.Type, Value = id.Value };
        typeof(Env).GetMethod("Add", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)!.Invoke(clash, [twin]);
        var mono = new Monomorph(t, clash);
        var e = Assert.Throws<Model.Refused>(() => mono.Instance(id.Name, [t.Zero]));
        Assert.Contains("already has", e.Message);
    }

    [Fact]
    public void CommentsHoldOnlyPrintableAsciiWithoutDollars()
    {
        Assert.Equal("The definitional equation of a\\u{2082}.", NameEscape.CommentText("The definitional equation of a₂."));
        Assert.Equal("term_\\u{24}__", NameEscape.CommentText("term_$__"));
        Assert.Equal("x\\u{1d4d0}", NameEscape.CommentText("x\U0001D4D0"));
    }
}
