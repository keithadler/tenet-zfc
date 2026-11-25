using System.Numerics;

namespace TenetZfc;

// Lean's kernel terms, written independently of Tenet.
//
// Every name, level and expression is built through a Terms table, which keeps exactly one object per distinct
// term. Binder names and binder annotations are ignored when deciding whether two terms are the same, as the kernel
// ignores them, so structural equality is reference equality and costs nothing.

public abstract class Name
{
    public abstract Name? Prefix { get; }
    public static readonly Name Anonymous = new AnonymousName();
    public bool IsAnonymous => ReferenceEquals(this, Anonymous);

    private sealed class AnonymousName : Name
    {
        public override Name? Prefix => null;
        public override string ToString() => "[anonymous]";
    }
}

public sealed class StrName(Name prefix, string value) : Name
{
    public override Name Prefix { get; } = prefix;
    public string Value { get; } = value;
    public override string ToString() => Prefix.IsAnonymous ? Value : Prefix + "." + Value;
}

public sealed class NumName(Name prefix, ulong value) : Name
{
    public override Name Prefix { get; } = prefix;
    public ulong Value { get; } = value;
    public override string ToString() => Prefix.IsAnonymous ? Value.ToString() : Prefix + "." + Value;
}

public abstract class Level
{
    /// <summary>True when the level mentions a universe parameter.</summary>
    public abstract bool HasParam { get; }
}

public sealed class LZero : Level
{
    public override bool HasParam => false;
    public override string ToString() => "0";
}

public sealed class LSucc(Level of) : Level
{
    public Level Of { get; } = of;
    public override bool HasParam => Of.HasParam;
    public override string ToString() => $"({Of}+1)";
}

public sealed class LMax(Level a, Level b) : Level
{
    public Level A { get; } = a;
    public Level B { get; } = b;
    public override bool HasParam => A.HasParam || B.HasParam;
    public override string ToString() => $"max {A} {B}";
}

public sealed class LIMax(Level a, Level b) : Level
{
    public Level A { get; } = a;
    public Level B { get; } = b;
    public override bool HasParam => A.HasParam || B.HasParam;
    public override string ToString() => $"imax {A} {B}";
}

public sealed class LParam(Name name) : Level
{
    public Name Name { get; } = name;
    public override bool HasParam => true;
    public override string ToString() => $"{Name}";
}

public enum BinderKind : byte { Default, Implicit, StrictImplicit, InstImplicit }

public abstract class Expr
{
    /// <summary>One more than the largest loose bound variable index, or 0 when the term is closed under binders.</summary>
    public int LooseBVarRange { get; protected init; }

    /// <summary>True when the term mentions a free variable.</summary>
    public bool HasFVar { get; protected init; }
}

public sealed class BVar : Expr
{
    public int Idx { get; }
    internal BVar(int idx) { Idx = idx; LooseBVarRange = idx + 1; }
    public override string ToString() => "#" + Idx;
}

public sealed class FVar : Expr
{
    public ulong Id { get; }
    internal FVar(ulong id) { Id = id; HasFVar = true; }
    public override string ToString() => "_fv" + Id;
}

public sealed class Sort : Expr
{
    public Level Level { get; }
    internal Sort(Level level) => Level = level;
    public override string ToString() => $"Sort {Level}";
}

public sealed class Const : Expr
{
    public Name Name { get; }
    public Level[] Levels { get; }
    internal Const(Name name, Level[] levels) { Name = name; Levels = levels; }
    public override string ToString() => Levels.Length == 0 ? $"{Name}" : $"{Name}.{{{string.Join(", ", Levels.Select(l => $"{l}"))}}}";
}

public sealed class App : Expr
{
    public Expr Fn { get; }
    public Expr Arg { get; }
    internal App(Expr fn, Expr arg)
    {
        Fn = fn;
        Arg = arg;
        LooseBVarRange = Math.Max(fn.LooseBVarRange, arg.LooseBVarRange);
        HasFVar = fn.HasFVar || arg.HasFVar;
    }
    public override string ToString() => $"({Fn} {Arg})";
}

/// <summary>A lambda (<see cref="IsPi"/> false) or a Pi type (true).</summary>
public sealed class Binder : Expr
{
    public bool IsPi { get; }
    public Name BinderName { get; }
    public BinderKind Info { get; }
    public Expr Domain { get; }
    public Expr Body { get; }
    internal Binder(bool isPi, Name name, BinderKind info, Expr domain, Expr body)
    {
        IsPi = isPi;
        BinderName = name;
        Info = info;
        Domain = domain;
        Body = body;
        LooseBVarRange = Math.Max(domain.LooseBVarRange, Math.Max(body.LooseBVarRange - 1, 0));
        HasFVar = domain.HasFVar || body.HasFVar;
    }
    public override string ToString() => IsPi ? $"(({BinderName} : {Domain}) → {Body})" : $"(fun {BinderName} : {Domain} => {Body})";
}

public sealed class Let : Expr
{
    public Name BinderName { get; }
    public Expr Type { get; }
    public Expr Value { get; }
    public Expr Body { get; }
    internal Let(Name name, Expr type, Expr value, Expr body)
    {
        BinderName = name;
        Type = type;
        Value = value;
        Body = body;
        LooseBVarRange = Math.Max(Math.Max(type.LooseBVarRange, value.LooseBVarRange), Math.Max(body.LooseBVarRange - 1, 0));
        HasFVar = type.HasFVar || value.HasFVar || body.HasFVar;
    }
    public override string ToString() => $"(let {BinderName} : {Type} := {Value}; {Body})";
}

public sealed class NatLit : Expr
{
    public BigInteger Value { get; }
    internal NatLit(BigInteger v) => Value = v;
    public override string ToString() => Value.ToString();
}

public sealed class StrLit : Expr
{
    public string Value { get; }
    internal StrLit(string v) => Value = v;
    public override string ToString() => System.Text.Json.JsonSerializer.Serialize(Value);
}

public sealed class Proj : Expr
{
    public Name StructName { get; }
    public int Idx { get; }
    public Expr Struct { get; }
    internal Proj(Name s, int idx, Expr e)
    {
        StructName = s;
        Idx = idx;
        Struct = e;
        LooseBVarRange = e.LooseBVarRange;
        HasFVar = e.HasFVar;
    }
    public override string ToString() => $"{Struct}.{Idx + 1}";
}

/// <summary>
/// The table every term is built through. One instance per run: an export and the traces checked against it must
/// share a table, so that a constant in a trace is the same object as that constant in the export.
/// </summary>
public sealed class Terms
{
    private readonly Dictionary<(Name, string), Name> _str = new();
    private readonly Dictionary<(Name, ulong), Name> _num = new();
    private readonly Dictionary<object, Level> _levels = new();
    private readonly Dictionary<object, Expr> _exprs = new();
    private readonly Dictionary<Name, Level> _params = new(ReferenceEqualityComparer.Instance);

    public readonly Level Zero = new LZero();

    public Name Str(Name pre, string s) => Get(_str, (pre, s), () => new StrName(pre, s));
    public Name Num(Name pre, ulong n) => Get(_num, (pre, n), () => new NumName(pre, n));

    /// <summary>Lean's Name.appendIndexAfter: the last string component gets "_idx" (u becomes u_1).</summary>
    public Name AppendIndexAfter(Name n, ulong idx) => n is StrName s ? Str(s.Prefix, s.Value + "_" + idx) : Str(n, "_" + idx);

    /// <summary>Lean's Name.append: b's components after a's.</summary>
    public Name Append(Name a, Name b) => b switch
    {
        StrName s => Str(Append(a, s.Prefix), s.Value),
        NumName m => Num(Append(a, m.Prefix), m.Value),
        _ => a,
    };

    /// <summary>Lean's Name.replacePrefix: n with the prefix query replaced by newPrefix (n unchanged if query is not a prefix).</summary>
    public Name ReplacePrefix(Name n, Name query, Name newPrefix)
    {
        if (ReferenceEquals(n, query))
        {
            return newPrefix;
        }
        return n switch
        {
            StrName s => Str(ReplacePrefix(s.Prefix, query, newPrefix), s.Value),
            NumName m => Num(ReplacePrefix(m.Prefix, query, newPrefix), m.Value),
            _ => n,
        };
    }

    public Name Of(string dotted)
    {
        Name n = Name.Anonymous;
        foreach (string part in dotted.Split('.'))
        {
            n = Str(n, part);
        }
        return n;
    }

    public Level Succ(Level l) => GetL(("succ", l), () => new LSucc(l));
    public Level Max(Level a, Level b) => GetL(("max", a, b), () => new LMax(a, b));
    public Level IMax(Level a, Level b) => GetL(("imax", a, b), () => new LIMax(a, b));
    public Level Param(Name n) => _params.TryGetValue(n, out Level? l) ? l : _params[n] = new LParam(n);

    public Expr BVar(int i) => GetE(("bvar", i), () => new BVar(i));
    public Expr FVar(ulong id) => GetE(("fvar", id), () => new FVar(id));
    public Expr Sort(Level l) => GetE(("sort", l), () => new Sort(l));

    public Expr Const(Name n, Level[] us) =>
        GetE(("const", n, new LevelList(us)), () => new Const(n, us));

    public Expr App(Expr f, Expr a) => GetE(("app", f, a), () => new App(f, a));

    public Expr Binding(bool isPi, Name name, BinderKind info, Expr dom, Expr body) =>
        GetE((isPi ? "pi" : "lam", dom, body), () => new Binder(isPi, name, info, dom, body));

    public Expr Let(Name name, Expr type, Expr value, Expr body) =>
        GetE(("let", type, value, body), () => new Let(name, type, value, body));

    public Expr Nat(BigInteger v) => GetE(("nat", v), () => new NatLit(v));
    public Expr Str(string s) => GetE(("str", s), () => new StrLit(s));
    public Expr Proj(Name s, int idx, Expr e) => GetE(("proj", s, idx, e), () => new Proj(s, idx, e));

    public Expr MkApp(Expr f, IEnumerable<Expr> args)
    {
        foreach (Expr a in args)
        {
            f = App(f, a);
        }
        return f;
    }

    private static T Get<TK, T>(Dictionary<TK, T> d, TK k, Func<T> mk) where TK : notnull
    {
        if (!d.TryGetValue(k, out T? v))
        {
            v = mk();
            d[k] = v;
        }
        return v;
    }

    private Level GetL(object key, Func<Level> mk) => Get(_levels, key, mk);
    private Expr GetE(object key, Func<Expr> mk) => Get(_exprs, key, mk);

    /// <summary>A level list compared element by element, by reference (levels are interned).</summary>
    private readonly struct LevelList(Level[] items) : IEquatable<LevelList>
    {
        private readonly Level[] _items = items;
        public bool Equals(LevelList o) => _items.Length == o._items.Length && _items.AsSpan().SequenceEqual(o._items);
        public override bool Equals(object? obj) => obj is LevelList o && Equals(o);
        public override int GetHashCode()
        {
            var h = new HashCode();
            foreach (Level l in _items)
            {
                h.Add(l);
            }
            return h.ToHashCode();
        }
    }
}
