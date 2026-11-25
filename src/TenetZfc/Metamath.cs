using System.Text;

namespace TenetZfc.Metamath;

// Just enough of Metamath to write proofs against set.mm: read its statements (with each assertion's mandatory
// hypotheses, in order), parse expressions with its syntax axioms, and assemble proofs. Nothing here checks a proof;
// the two external verifiers do that, and their verdict is the only one that counts.

/// <summary>An expression: a typecode and its symbols, as Metamath writes it.</summary>
public sealed record Expr(string Type, IReadOnlyList<string> Symbols)
{
    public static Expr Of(string text)
    {
        string[] t = text.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        return new Expr(t[0], t[1..]);
    }

    public override string ToString() => Type + " " + string.Join(' ', Symbols);
    public bool Equals(Expr? o) => o is not null && Type == o.Type && Symbols.SequenceEqual(o.Symbols);
    public override int GetHashCode() => HashCode.Combine(Type, string.Join(' ', Symbols));
}

/// <summary>An $f, $e, $a or $p statement.</summary>
public sealed class Statement
{
    public required string Label { get; init; }
    public required char Kind { get; init; }   // 'f', 'e', 'a' or 'p'
    public required Expr Expr { get; init; }

    /// <summary>For an assertion, its mandatory hypotheses in the order a proof must supply them.</summary>
    public IReadOnlyList<Statement> Hyps { get; init; } = [];

    /// <summary>For an $f: the variable it types.</summary>
    public string? Var => Kind == 'f' ? Expr.Symbols[0] : null;
}

/// <summary>The statements of a Metamath database, by label, and its syntax axioms by typecode.</summary>
public sealed class Database
{
    private readonly Dictionary<string, Statement> _byLabel = new();
    private readonly HashSet<string> _constants = new();
    private readonly Dictionary<string, Statement> _floatOf = new();   // variable → its (last) $f

    public IReadOnlyDictionary<string, Statement> Statements => _byLabel;
    public Dictionary<string, List<Statement>> SyntaxByType { get; } = new();

    public Statement this[string label] => _byLabel.TryGetValue(label, out Statement? s) ? s : throw new KeyNotFoundException(label);
    public bool IsConstant(string sym) => _constants.Contains(sym);
    public Statement? FloatOf(string var) => _floatOf.TryGetValue(var, out Statement? f) ? f : null;

    public static Database Read(string path)
    {
        var db = new Database();
        db.Parse(Tokens(File.ReadAllText(path)));
        return db;
    }

    private static IEnumerable<string> Tokens(string text)
    {
        int i = 0, n = text.Length;
        while (i < n)
        {
            while (i < n && char.IsWhiteSpace(text[i]))
            {
                i++;
            }
            int start = i;
            while (i < n && !char.IsWhiteSpace(text[i]))
            {
                i++;
            }
            if (i > start)
            {
                string tok = text[start..i];
                if (tok == "$(")
                {
                    int close = text.IndexOf("$)", i, StringComparison.Ordinal);
                    i = close < 0 ? n : close + 2;
                    continue;
                }
                yield return tok;
            }
        }
    }

    private void Parse(IEnumerable<string> tokens)
    {
        // Scope: the hypotheses active at each nesting level, in order of appearance.
        var scopes = new List<List<Statement>> { new() };
        using IEnumerator<string> it = tokens.GetEnumerator();
        string? label = null;
        List<string> Until(string end)
        {
            var r = new List<string>();
            while (it.MoveNext() && it.Current != end)
            {
                r.Add(it.Current);
            }
            return r;
        }
        while (it.MoveNext())
        {
            string tok = it.Current;
            switch (tok)
            {
                case "${":
                    scopes.Add(new List<Statement>());
                    break;
                case "$}":
                    scopes.RemoveAt(scopes.Count - 1);
                    break;
                case "$c":
                    foreach (string c in Until("$."))
                    {
                        _constants.Add(c);
                    }
                    break;
                case "$v":
                case "$d":
                    Until("$.");
                    break;
                case "$[":
                    Until("$]");
                    break;
                case "$f":
                case "$e":
                    {
                        List<string> body = Until("$.");
                        var s = new Statement { Label = label!, Kind = tok[1], Expr = new Expr(body[0], body.Skip(1).ToList()) };
                        _byLabel[label!] = s;
                        scopes[^1].Add(s);
                        if (s.Kind == 'f')
                        {
                            _floatOf[s.Var!] = s;
                        }
                        label = null;
                        break;
                    }
                case "$a":
                case "$p":
                    {
                        List<string> body = Until(tok == "$a" ? "$." : "$=");
                        if (tok == "$p")
                        {
                            Until("$.");   // the proof: not needed here
                        }
                        var expr = new Expr(body[0], body.Skip(1).ToList());
                        var s = new Statement { Label = label!, Kind = tok[1], Expr = expr, Hyps = Mandatory(scopes, expr) };
                        _byLabel[label!] = s;
                        if (s.Kind == 'a' && expr.Type != "|-")
                        {
                            if (!SyntaxByType.TryGetValue(expr.Type, out List<Statement>? l))
                            {
                                SyntaxByType[expr.Type] = l = new List<Statement>();
                            }
                            l.Add(s);
                        }
                        label = null;
                        break;
                    }
                default:
                    if (!tok.StartsWith('$'))
                    {
                        label = tok;
                    }
                    break;
            }
        }
    }

    /// <summary>The $e hypotheses in scope, and the $f hypotheses of every variable they or the assertion mention, in order of appearance.</summary>
    private static List<Statement> Mandatory(List<List<Statement>> scopes, Expr assertion)
    {
        var active = scopes.SelectMany(s => s).ToList();
        var vars = new HashSet<string>(assertion.Symbols);
        foreach (Statement e in active.Where(h => h.Kind == 'e'))
        {
            vars.UnionWith(e.Expr.Symbols);
        }
        return active.Where(h => h.Kind == 'e' || (h.Kind == 'f' && vars.Contains(h.Var!))).ToList();
    }
}

/// <summary>A parsed expression: the syntax axiom (or $f) at its root and its children, one per variable of the axiom.</summary>
public sealed record SyntaxTree(Statement Rule, IReadOnlyList<SyntaxTree> Children);

/// <summary>Parses set.mm expressions with its syntax axioms, and assembles proofs.</summary>
public sealed class Prover
{
    private readonly Database _db;
    public Prover(Database db) => _db = db;

    /// <summary>The syntax tree of an expression of this typecode, or null if it does not parse.</summary>
    public SyntaxTree? Parse(string type, IReadOnlyList<string> syms)
    {
        var memo = new Dictionary<(string, int), List<(int End, SyntaxTree Tree)>>();
        foreach ((int end, SyntaxTree tree) in ParseAt(type, syms, 0, memo))
        {
            if (end == syms.Count)
            {
                return tree;
            }
        }
        return null;
    }

    private List<(int, SyntaxTree)> ParseAt(string type, IReadOnlyList<string> syms, int pos, Dictionary<(string, int), List<(int, SyntaxTree)>> memo)
    {
        if (memo.TryGetValue((type, pos), out var known))
        {
            return known;
        }
        var results = new List<(int, SyntaxTree)>();
        memo[(type, pos)] = results;   // a left-recursive call sees no results yet
        // A variable of this typecode.
        if (pos < syms.Count && _db.FloatOf(syms[pos]) is Statement f && f.Expr.Type == type)
        {
            results.Add((pos + 1, new SyntaxTree(f, [])));
        }
        if (!_db.SyntaxByType.TryGetValue(type, out List<Statement>? rules))
        {
            return results;
        }
        foreach (Statement rule in rules)
        {
            IReadOnlyList<string> pat = rule.Expr.Symbols;
            // Quick reject: the first symbol, if a constant, must match.
            if (pat.Count > 0 && _db.IsConstant(pat[0]) && (pos >= syms.Count || syms[pos] != pat[0]))
            {
                continue;
            }
            foreach ((int end, Dictionary<string, SyntaxTree> binds) in Match(pat, 0, syms, pos, new Dictionary<string, SyntaxTree>(), memo))
            {
                // Children in the order of the rule's mandatory $f hypotheses.
                var children = rule.Hyps.Where(h => h.Kind == 'f').Select(h => binds[h.Var!]).ToList();
                results.Add((end, new SyntaxTree(rule, children)));
            }
        }
        return results;
    }

    private IEnumerable<(int, Dictionary<string, SyntaxTree>)> Match(IReadOnlyList<string> pat, int pi, IReadOnlyList<string> syms, int pos,
        Dictionary<string, SyntaxTree> binds, Dictionary<(string, int), List<(int, SyntaxTree)>> memo)
    {
        if (pi == pat.Count)
        {
            yield return (pos, binds);
            yield break;
        }
        string p = pat[pi];
        if (_db.IsConstant(p))
        {
            if (pos < syms.Count && syms[pos] == p)
            {
                foreach (var r in Match(pat, pi + 1, syms, pos + 1, binds, memo))
                {
                    yield return r;
                }
            }
            yield break;
        }
        string vt = _db.FloatOf(p)!.Expr.Type;
        foreach ((int end, SyntaxTree t) in ParseAt(vt, syms, pos, memo).ToList())
        {
            var b = new Dictionary<string, SyntaxTree>(binds) { [p] = t };
            foreach (var r in Match(pat, pi + 1, syms, end, b, memo))
            {
                yield return r;
            }
        }
    }

    /// <summary>The symbols a syntax tree stands for.</summary>
    public string Render(SyntaxTree n)
    {
        if (n.Rule.Kind == 'f')
        {
            return n.Rule.Var!;
        }
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
        return string.Join(' ', n.Rule.Expr.Symbols.Select(s => vars.IndexOf(s) is int i and >= 0 ? Render(n.Children[i]) : s));
    }

    private List<(Statement Thm, Dictionary<string, int> Consts)>? _theorems;

    /// <summary>
    /// A set.mm theorem (a $p with no essential hypotheses) whose statement becomes the target under some substitution
    /// of its variables: the theorem's label and that substitution. Null when there is none.
    /// </summary>
    public (string Label, Dictionary<string, string> Subst)? FindInstance(Expr target)
    {
        _theorems ??= _db.Statements.Values
            .Where(s => s.Kind == 'p' && s.Expr.Type == "|-" && s.Hyps.All(h => h.Kind == 'f'))
            .Select(s => (s, Bag(s.Expr.Symbols)))
            .ToList();
        SyntaxTree? goal = Parse("wff", target.Symbols);
        if (goal is null)
        {
            return null;
        }
        Dictionary<string, int> have = Bag(target.Symbols);
        foreach ((Statement thm, Dictionary<string, int> need) in _theorems)
        {
            // Every constant of the theorem survives substitution, so the target must have at least as many of each.
            if (need.Any(kv => !have.TryGetValue(kv.Key, out int n) || n < kv.Value))
            {
                continue;
            }
            if (Parse("wff", thm.Expr.Symbols) is not SyntaxTree pattern)
            {
                continue;
            }
            var binds = new Dictionary<string, SyntaxTree>();
            if (Match(pattern, goal, binds))
            {
                return (thm.Label, binds.ToDictionary(kv => kv.Key, kv => Render(kv.Value)));
            }
        }
        return null;
    }

    private Dictionary<string, int> Bag(IEnumerable<string> syms)
    {
        var d = new Dictionary<string, int>();
        foreach (string s in syms.Where(_db.IsConstant))
        {
            d[s] = d.TryGetValue(s, out int n) ? n + 1 : 1;
        }
        return d;
    }

    private bool Match(SyntaxTree pattern, SyntaxTree target, Dictionary<string, SyntaxTree> binds)
    {
        if (pattern.Rule.Kind == 'f')
        {
            // A variable matches any subtree of its type, the same subtree at each occurrence. A setvar must stay a
            // setvar: substituting a term for it is not an instance.
            string v = pattern.Rule.Var!;
            if (pattern.Rule.Expr.Type == "setvar" && target.Rule.Kind != 'f')
            {
                return false;
            }
            if (binds.TryGetValue(v, out SyntaxTree? bound))
            {
                return Render(bound) == Render(target);
            }
            if (!ReferenceEquals(TypeOf(target), pattern.Rule.Expr.Type) && TypeOf(target) != pattern.Rule.Expr.Type)
            {
                return false;
            }
            binds[v] = target;
            return true;
        }
        if (pattern.Rule.Label != target.Rule.Label || pattern.Children.Count != target.Children.Count)
        {
            return false;
        }
        for (int i = 0; i < pattern.Children.Count; i++)
        {
            if (!Match(pattern.Children[i], target.Children[i], binds))
            {
                return false;
            }
        }
        return true;
    }

    private static string TypeOf(SyntaxTree n) => n.Rule.Expr.Type;

    /// <summary>The proof (labels in reverse Polish order) that builds an expression's syntax.</summary>
    public List<string> SyntaxProof(Expr e)
    {
        SyntaxTree t = Parse(e.Type, e.Symbols) ?? throw new InvalidOperationException($"does not parse: {e}");
        var r = new List<string>();
        void Go(SyntaxTree n)
        {
            foreach (SyntaxTree c in n.Children)
            {
                Go(c);
            }
            r.Add(n.Rule.Label);
        }
        Go(t);
        return r;
    }

    /// <summary>
    /// Apply an assertion: the substitution gives each of its variables an expression (its symbols); the proofs of its
    /// $e hypotheses come in order. Returns the proof and what it proves.
    /// </summary>
    public (List<string> Proof, Expr Proves) Apply(string label, IReadOnlyDictionary<string, string> subst, params (List<string> Proof, Expr Proves)[] essentials)
    {
        Statement a = _db[label];
        var sub = subst.ToDictionary(kv => kv.Key, kv => kv.Value.Split(' ', StringSplitOptions.RemoveEmptyEntries));
        Expr Inst(Expr e) => new(e.Type, e.Symbols.SelectMany(s => sub.TryGetValue(s, out string[]? v) ? v : [s]).ToList());
        var proof = new List<string>();
        int ei = 0;
        foreach (Statement h in a.Hyps)
        {
            if (h.Kind == 'f')
            {
                if (!sub.TryGetValue(h.Var!, out string[]? v))
                {
                    throw new InvalidOperationException($"{label}: no substitution for {h.Var}");
                }
                proof.AddRange(SyntaxProof(new Expr(h.Expr.Type, v)));
            }
            else
            {
                (List<string> p, Expr proves) = essentials[ei++];
                Expr want = Inst(h.Expr);
                if (!want.Equals(proves))
                {
                    throw new InvalidOperationException($"{label}: hypothesis {h.Label} needs {want}, given {proves}");
                }
                proof.AddRange(p);
            }
        }
        proof.Add(label);
        return (proof, Inst(a.Expr));
    }
}

/// <summary>Writes a .mm file that includes set.mm and adds theorems with their proofs.</summary>
public sealed class Writer
{
    private readonly StringBuilder _sb = new();

    public Writer(string include, string header)
    {
        _sb.AppendLine($"$( {header} $)");
        _sb.AppendLine($"$[ {include} $]");
        _sb.AppendLine();
    }

    public void Theorem(string label, string comment, Expr statement, IEnumerable<string> proof)
    {
        _sb.AppendLine($"  $( {comment} $)");
        _sb.AppendLine($"  {label} $p {statement} $=");
        _sb.AppendLine("    " + string.Join(' ', proof) + " $.");
        _sb.AppendLine();
    }

    /// <summary>A theorem in its own scope, with distinct-variable conditions (each line a $d list).</summary>
    public void Theorem(string label, string comment, Expr statement, IEnumerable<string> proof, IEnumerable<string> distinct)
    {
        _sb.AppendLine("  ${");
        foreach (string d in distinct)
        {
            _sb.AppendLine($"    $d {d} $.");
        }
        Theorem(label, comment, statement, proof);
        _sb.AppendLine("  $}");
        _sb.AppendLine();
    }

    public override string ToString() => _sb.ToString();
}
