using System.Globalization;
using System.Numerics;
using System.Text.Json;

namespace TenetZfc;

public enum ConstKind : byte { Axiom, Definition, Theorem, Opaque, Quot, Inductive, Constructor, Recursor }

public sealed record RecRule(Name Ctor, int NumFields, Expr Rhs);

/// <summary>A constant as the export declares it. Only what replay needs is kept.</summary>
public sealed class ConstInfo
{
    public required Name Name { get; init; }
    public required ConstKind Kind { get; init; }
    public required Name[] LevelParams { get; init; }
    public required Expr Type { get; init; }

    /// <summary>The body, for a definition or theorem: the constants delta reduction may unfold.</summary>
    public Expr? Value { get; init; }

    /// <summary>Unsafe: may not be used by a safe or partial declaration.</summary>
    public bool Unsafe { get; init; }

    /// <summary>A partial definition: may not be used by a safe declaration.</summary>
    public bool Partial { get; init; }

    /// <summary>The body of an opaque constant: type-checked, never unfolded.</summary>
    public Expr? OpaqueValue { get; init; }

    // constructors
    public Name? Induct { get; init; }
    public int NumParams { get; init; }
    public int NumFields { get; init; }

    // recursors
    public int NumMotives { get; init; }
    public int NumMinors { get; init; }
    public int NumIndices { get; init; }
    public bool K { get; init; }
    public RecRule[] Rules { get; init; } = [];

    // inductive types
    /// <summary>The universe parameters of every constant in this type's block (types, constructors, recursors).</summary>
    public Name[] BlockLevelParams { get; init; } = [];

    /// <summary>Every constant of this type's block: types, constructors and recursors.</summary>
    public Name[] BlockMembers { get; init; } = [];
    public bool IsRec { get; init; }

    /// <summary>For a nested inductive (one whose constructors mention another inductive applied to it), how many nestings.</summary>
    public int NumNested { get; init; }
    public Name[] Ctors { get; init; } = [];

    public int MajorIdx => NumParams + NumMotives + NumMinors + NumIndices;
}

/// <summary>The constants of an export, by name.</summary>
public sealed class Environment
{
    private readonly Dictionary<Name, ConstInfo> _consts = new(ReferenceEqualityComparer.Instance);
    public string? LeanVersion { get; internal set; }
    public int Count => _consts.Count;
    public ConstInfo? Find(Name n) => _consts.TryGetValue(n, out ConstInfo? c) ? c : null;
    internal void Add(ConstInfo c) => _consts[c.Name] = c;
}

public enum StepKind : byte { Rule, Infer, WhnfCore, Whnf, DefEq, Local, Check }

/// <summary>One step of a trace. <see cref="From"/> is the first of its premises; a step with none has From = its own index.</summary>
/// <summary>
/// One step of a trace. <see cref="From"/> is the first of its premises; a step with none has From = its own index.
/// <see cref="Of"/>, when not -1, says the step recalls the earlier step it names instead of deriving its result again.
/// </summary>
public sealed record Step(int Index, StepKind Kind, string? Rule, Expr A, Expr? B, Expr? V, int From, int Of = -1);

public sealed record DeclTrace(Name Decl, IReadOnlyList<Step> Steps);

public sealed class FormatException(long line, string message) : Exception($"line {line}: {message}");

/// <summary>
/// Reads lean4export files and Tenet trace files. Both number names ("in"), levels ("il") and expressions ("ie")
/// per file and refer to them by number; this maps each file's numbers into one shared <see cref="Terms"/> table.
/// </summary>
public sealed class Reader
{
    private readonly Terms _t;
    private readonly List<Name> _names = new();
    private readonly List<Level> _levels = new();
    private readonly List<Expr> _exprs = new();
    private long _line;

    private Reader(Terms t)
    {
        _t = t;
        _names.Add(Name.Anonymous);
        _levels.Add(t.Zero);
    }

    public static Environment ReadExport(Terms t, string path)
    {
        var r = new Reader(t);
        var env = new Environment();
        foreach (string line in File.ReadLines(path))
        {
            r._line++;
            if (line.Length == 0)
            {
                continue;
            }
            using JsonDocument doc = JsonDocument.Parse(line);
            JsonElement o = doc.RootElement;
            if (r.TryTable(o))
            {
                continue;
            }
            r.ReadDecl(o, env);
        }
        return env;
    }

    public static List<DeclTrace> ReadTrace(Terms t, string path)
    {
        var r = new Reader(t);
        var decls = new List<DeclTrace>();
        Name? current = null;
        List<Step>? steps = null;
        int expected = 0;
        void Close()
        {
            if (current is not null)
            {
                if (steps!.Count != expected)
                {
                    throw new FormatException(r._line, $"{current} declares {expected} steps and has {steps.Count}");
                }
                decls.Add(new DeclTrace(current, steps));
            }
        }
        foreach (string line in File.ReadLines(path))
        {
            r._line++;
            if (line.Length == 0)
            {
                continue;
            }
            using JsonDocument doc = JsonDocument.Parse(line);
            JsonElement o = doc.RootElement;
            if (r.TryTable(o))
            {
                continue;
            }
            if (o.TryGetProperty("trace", out JsonElement tr))
            {
                if (tr.GetString() != "tenet" || o.GetProperty("version").GetInt32() != 1)
                {
                    throw new FormatException(r._line, "not a version 1 Tenet trace");
                }
                continue;
            }
            if (o.TryGetProperty("decl", out JsonElement d))
            {
                Close();
                current = r.N(d);
                steps = new List<Step>();
                expected = o.GetProperty("steps").GetInt32();
                continue;
            }
            if (o.TryGetProperty("s", out JsonElement s))
            {
                if (steps is null)
                {
                    throw new FormatException(r._line, "a step before any declaration");
                }
                int i = s.GetInt32();
                if (i != steps.Count)
                {
                    throw new FormatException(r._line, $"step {i} out of order");
                }
                StepKind kind = Enum.Parse<StepKind>(o.GetProperty("k").GetString()!);
                string? rule = o.TryGetProperty("r", out JsonElement rr) ? rr.GetString() : null;
                Expr a = r.E(o.GetProperty("a"));
                Expr? b = o.TryGetProperty("b", out JsonElement bb) ? r.E(bb) : null;
                Expr? v = o.TryGetProperty("v", out JsonElement vv) ? r.E(vv) : null;
                int from = o.TryGetProperty("from", out JsonElement f) ? f.GetInt32() : i;
                if (from < 0 || from > i)
                {
                    throw new FormatException(r._line, $"step {i} has premises from {from}");
                }
                int of = o.TryGetProperty("of", out JsonElement ofe) ? ofe.GetInt32() : -1;
                if (of >= i)
                {
                    throw new FormatException(r._line, $"step {i} recalls step {of}, which does not come before it");
                }
                steps.Add(new Step(i, kind, rule, a, b, v, from, of));
                continue;
            }
            throw new FormatException(r._line, "unknown line");
        }
        Close();
        return decls;
    }

    // ---- tables ----

    private bool TryTable(JsonElement o)
    {
        if (o.TryGetProperty("in", out JsonElement ni))
        {
            int id = ni.GetInt32();
            Name n;
            if (o.TryGetProperty("str", out JsonElement s))
            {
                n = _t.Str(N(s.GetProperty("pre")), s.GetProperty("str").GetString()!);
            }
            else if (o.TryGetProperty("num", out JsonElement m))
            {
                n = _t.Num(N(m.GetProperty("pre")), m.GetProperty("i").GetUInt64());
            }
            else if (o.TryGetProperty("anon", out _))
            {
                n = Name.Anonymous;
            }
            else
            {
                throw new FormatException(_line, "unknown name");
            }
            Put(_names, id, n);
            return true;
        }
        if (o.TryGetProperty("il", out JsonElement li))
        {
            int id = li.GetInt32();
            Level l;
            if (o.TryGetProperty("succ", out JsonElement s))
            {
                l = _t.Succ(L(s));
            }
            else if (o.TryGetProperty("max", out JsonElement m))
            {
                l = _t.Max(L(m[0]), L(m[1]));
            }
            else if (o.TryGetProperty("imax", out JsonElement im))
            {
                l = _t.IMax(L(im[0]), L(im[1]));
            }
            else if (o.TryGetProperty("param", out JsonElement p))
            {
                l = _t.Param(N(p));
            }
            else if (o.TryGetProperty("zero", out _))
            {
                l = _t.Zero;
            }
            else
            {
                throw new FormatException(_line, "unknown level");
            }
            Put(_levels, id, l);
            return true;
        }
        if (o.TryGetProperty("ie", out JsonElement ei))
        {
            Put(_exprs, ei.GetInt32(), ReadExpr(o));
            return true;
        }
        return false;
    }

    private void Put<T>(List<T> table, int id, T v)
    {
        if (id == table.Count)
        {
            table.Add(v);
        }
        else if (id >= 0 && id < table.Count)
        {
            // Only the built-in entries (the anonymous name and level zero) are ever written again.
            table[id] = v;
        }
        else
        {
            throw new FormatException(_line, $"id {id} skips ahead of {table.Count}");
        }
    }

    private Expr ReadExpr(JsonElement o)
    {
        if (o.TryGetProperty("bvar", out JsonElement b))
        {
            return _t.BVar(b.GetInt32());
        }
        if (o.TryGetProperty("fvar", out JsonElement fv))
        {
            return _t.FVar(fv.GetUInt64());
        }
        if (o.TryGetProperty("sort", out JsonElement s))
        {
            return _t.Sort(L(s));
        }
        if (o.TryGetProperty("const", out JsonElement c))
        {
            return _t.Const(N(c.GetProperty("name")), c.GetProperty("us").EnumerateArray().Select(L).ToArray());
        }
        if (o.TryGetProperty("app", out JsonElement a))
        {
            return _t.App(E(a.GetProperty("fn")), E(a.GetProperty("arg")));
        }
        if (o.TryGetProperty("lam", out JsonElement lam))
        {
            return Binding(false, lam);
        }
        if (o.TryGetProperty("forallE", out JsonElement pi))
        {
            return Binding(true, pi);
        }
        if (o.TryGetProperty("letE", out JsonElement let))
        {
            return _t.Let(N(let.GetProperty("name")), E(let.GetProperty("type")), E(let.GetProperty("value")), E(let.GetProperty("body")));
        }
        if (o.TryGetProperty("proj", out JsonElement pr))
        {
            return _t.Proj(N(pr.GetProperty("typeName")), pr.GetProperty("idx").GetInt32(), E(pr.GetProperty("struct")));
        }
        if (o.TryGetProperty("natVal", out JsonElement nv))
        {
            return _t.Nat(BigInteger.Parse(nv.GetString()!, NumberStyles.None, CultureInfo.InvariantCulture));
        }
        if (o.TryGetProperty("strVal", out JsonElement sv))
        {
            return _t.Str(sv.GetString()!);
        }
        if (o.TryGetProperty("mdata", out JsonElement md))
        {
            return E(md.GetProperty("expr"));
        }
        throw new FormatException(_line, "unknown expression");
    }

    private Expr Binding(bool isPi, JsonElement b)
    {
        BinderKind info = b.TryGetProperty("binderInfo", out JsonElement bi) ? bi.GetString() switch
        {
            "implicit" => BinderKind.Implicit,
            "strictImplicit" => BinderKind.StrictImplicit,
            "instImplicit" => BinderKind.InstImplicit,
            _ => BinderKind.Default,
        } : BinderKind.Default;
        return _t.Binding(isPi, N(b.GetProperty("name")), info, E(b.GetProperty("type")), E(b.GetProperty("body")));
    }

    private Name N(JsonElement e) => Lookup(_names, e.GetInt32(), "name");
    private Level L(JsonElement e) => Lookup(_levels, e.GetInt32(), "level");
    private Expr E(JsonElement e) => Lookup(_exprs, e.GetInt32(), "expression");

    private T Lookup<T>(List<T> table, int id, string what) =>
        id >= 0 && id < table.Count ? table[id] : throw new FormatException(_line, $"{what} {id} used before it is defined");

    // ---- declarations ----

    private Name[] Params(JsonElement o) => o.GetProperty("levelParams").EnumerateArray().Select(N).ToArray();

    private void ReadDecl(JsonElement o, Environment env)
    {
        if (o.TryGetProperty("meta", out JsonElement meta))
        {
            if (meta.TryGetProperty("lean", out JsonElement lean) && lean.TryGetProperty("version", out JsonElement v))
            {
                env.LeanVersion = v.GetString();
            }
            return;
        }
        if (o.TryGetProperty("axiom", out JsonElement ax))
        {
            foreach (JsonElement x in Each(ax)) { env.Add(Simple(x, ConstKind.Axiom, null)); }
        }
        else if (o.TryGetProperty("def", out JsonElement d))
        {
            foreach (JsonElement x in Each(d)) { env.Add(Simple(x, ConstKind.Definition, E(x.GetProperty("value")))); }
        }
        else if (o.TryGetProperty("thm", out JsonElement th))
        {
            foreach (JsonElement x in Each(th)) { env.Add(Simple(x, ConstKind.Theorem, E(x.GetProperty("value")))); }
        }
        else if (o.TryGetProperty("opaque", out JsonElement op))
        {
            // An opaque constant's value is checked but never unfolded, so it is kept apart from Value.
            foreach (JsonElement x in Each(op))
            {
                ConstInfo c = Simple(x, ConstKind.Opaque, null);
                env.Add(new ConstInfo { Name = c.Name, Kind = c.Kind, LevelParams = c.LevelParams, Type = c.Type, OpaqueValue = E(x.GetProperty("value")), Unsafe = c.Unsafe });
            }
        }
        else if (o.TryGetProperty("quot", out JsonElement q))
        {
            env.Add(Simple(q, ConstKind.Quot, null));
        }
        else if (o.TryGetProperty("inductive", out JsonElement ind))
        {
            // Checking a block checks its recursors too, whose motive universe is a parameter the types lack.
            Name[] blockParams = new[] { "types", "ctors", "recs" }
                .SelectMany(k => Arr(ind, k, k switch { "types" => "inductiveVals", "ctors" => "constructorVals", _ => "recursorVals" }).EnumerateArray())
                .SelectMany(Params).Distinct().ToArray();
            Name[] members = new[] { "types", "ctors", "recs" }
                .SelectMany(k => Arr(ind, k, k switch { "types" => "inductiveVals", "ctors" => "constructorVals", _ => "recursorVals" }).EnumerateArray())
                .Select(x => N(x.GetProperty("name"))).ToArray();
            foreach (JsonElement t in Arr(ind, "types", "inductiveVals").EnumerateArray())
            {
                env.Add(new ConstInfo
                {
                    BlockLevelParams = blockParams,
                    BlockMembers = members,
                    Name = N(t.GetProperty("name")), Kind = ConstKind.Inductive, LevelParams = Params(t), Type = E(t.GetProperty("type")), Unsafe = Unsafe(t),
                    NumParams = t.GetProperty("numParams").GetInt32(), NumIndices = t.GetProperty("numIndices").GetInt32(),
                    IsRec = t.GetProperty("isRec").GetBoolean(),
                    NumNested = t.TryGetProperty("numNested", out JsonElement nn) ? nn.GetInt32() : 0, Ctors = t.GetProperty("ctors").EnumerateArray().Select(N).ToArray(),
                });
            }
            foreach (JsonElement c in Arr(ind, "ctors", "constructorVals").EnumerateArray())
            {
                env.Add(new ConstInfo
                {
                    Name = N(c.GetProperty("name")), Kind = ConstKind.Constructor, LevelParams = Params(c), Type = E(c.GetProperty("type")), Unsafe = Unsafe(c),
                    Induct = N(c.GetProperty("induct")), NumParams = c.GetProperty("numParams").GetInt32(), NumFields = c.GetProperty("numFields").GetInt32(),
                });
            }
            foreach (JsonElement r in Arr(ind, "recs", "recursorVals").EnumerateArray())
            {
                env.Add(new ConstInfo
                {
                    Name = N(r.GetProperty("name")), Kind = ConstKind.Recursor, LevelParams = Params(r), Type = E(r.GetProperty("type")), Unsafe = Unsafe(r),
                    NumParams = r.GetProperty("numParams").GetInt32(), NumMotives = r.GetProperty("numMotives").GetInt32(),
                    NumMinors = r.GetProperty("numMinors").GetInt32(), NumIndices = r.GetProperty("numIndices").GetInt32(),
                    K = r.GetProperty("k").GetBoolean(),
                    Rules = r.GetProperty("rules").EnumerateArray()
                        .Select(x => new RecRule(N(x.GetProperty("ctor")), x.GetProperty("nfields").GetInt32(), E(x.GetProperty("rhs")))).ToArray(),
                });
            }
        }
        else
        {
            throw new FormatException(_line, "unknown declaration");
        }
    }

    /// <summary>One declaration, or the members of a mutual block written as an array (format 3.0 writes every definition that way).</summary>
    private static IEnumerable<JsonElement> Each(JsonElement e) => e.ValueKind == JsonValueKind.Array ? e.EnumerateArray() : [e];

    /// <summary>An inductive block's list, under its format 3.1 name or its format 3.0 name.</summary>
    private JsonElement Arr(JsonElement ind, string name, string v30Name) =>
        ind.TryGetProperty(name, out JsonElement a) ? a
        : ind.TryGetProperty(v30Name, out JsonElement b) ? b
        : throw new FormatException(_line, $"an inductive block without {name}");

    private ConstInfo Simple(JsonElement o, ConstKind kind, Expr? value) => new()
    {
        Name = N(o.GetProperty("name")), Kind = kind, LevelParams = Params(o), Type = E(o.GetProperty("type")), Value = value,
        Unsafe = Unsafe(o), Partial = o.TryGetProperty("safety", out JsonElement sf) && sf.GetString() == "partial",
    };

    private static bool Unsafe(JsonElement o) =>
        (o.TryGetProperty("isUnsafe", out JsonElement u) && u.GetBoolean())
        || (o.TryGetProperty("safety", out JsonElement s) && s.GetString() == "unsafe");
}
