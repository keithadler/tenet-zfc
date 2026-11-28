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

    /// <summary>For an assertion, its mandatory distinct-variable pairs.</summary>
    public IReadOnlyList<(string, string)> Distinct { get; init; } = [];
}

/// <summary>The statements of a Metamath database, by label, and its syntax axioms by typecode.</summary>
public sealed class Database
{
    private readonly Dictionary<string, Statement> _byLabel = new();
    private readonly HashSet<string> _constants = new();
    private readonly Dictionary<string, Statement> _floatOf = new();   // variable → its (last) $f
    private readonly List<List<Statement>> _scopes = [new()];          // the hypotheses active at each nesting level
    private readonly List<List<List<string>>> _dScopes = [new()];      // the $d lists active at each nesting level

    public IReadOnlyDictionary<string, Statement> Statements => _byLabel;

    /// <summary>Subproofs shared between the proofs made against this database (<see cref="Prover.Sharing"/>).</summary>
    public SharedProofs Shared { get; } = new();
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

    /// <summary>
    /// The file and the files it includes, the innermost first: set.mm, then a library of lemmas written against it,
    /// then one written against that. Each of tenet-zfc's outputs includes one file by name, from its own directory.
    /// </summary>
    public static List<string> IncludeChain(string path)
    {
        var chain = new List<string>();
        for (string? p = Path.GetFullPath(path); p is not null;)
        {
            if (chain.Contains(p))
            {
                throw new InvalidDataException($"{p} includes itself");
            }
            chain.Insert(0, p);
            // The include comes before any statement, in the first lines; set.mm has none.
            using var reader = new StreamReader(p);
            string head = string.Join('\n', Enumerable.Range(0, 200).Select(_ => reader.ReadLine()).TakeWhile(l => l is not null));
            // Outside comments: set.mm's own header describes the include statement in one.
            head = System.Text.RegularExpressions.Regex.Replace(head, @"(?s)\$\(.*?(\$\)|$)", " ");
            var m = System.Text.RegularExpressions.Regex.Match(head, @"(?m)^\s*\$\[ (\S+) \$\]");
            p = m.Success ? Path.Combine(Path.GetDirectoryName(p)!, m.Groups[1].Value) : null;
        }
        return chain;
    }

    /// <summary>Read a file with what it includes (<see cref="IncludeChain"/>): set.mm alone, or set.mm and a library.</summary>
    public static Database ReadChain(string path)
    {
        var db = new Database();
        foreach (string p in IncludeChain(path))
        {
            db.Parse(Tokens(File.ReadAllText(p)));
        }
        return db;
    }

    /// <summary>Read more statements into the database, as if they followed what it has read: the translator's own definitions.</summary>
    public void Extend(string text) => Parse(Tokens(text));

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
        List<List<Statement>> scopes = _scopes;
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
                    _dScopes.Add(new List<List<string>>());
                    break;
                case "$}":
                    scopes.RemoveAt(scopes.Count - 1);
                    _dScopes.RemoveAt(_dScopes.Count - 1);
                    break;
                case "$c":
                    foreach (string c in Until("$."))
                    {
                        _constants.Add(c);
                    }
                    break;
                case "$v":
                    Until("$.");
                    break;
                case "$d":
                    _dScopes[^1].Add(Until("$."));
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
                        List<Statement> hyps = Mandatory(scopes, expr);
                        var s = new Statement { Label = label!, Kind = tok[1], Expr = expr, Hyps = hyps, Distinct = MandatoryDistinct(hyps) };
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

    /// <summary>The active $d pairs between two mandatory variables.</summary>
    private List<(string, string)> MandatoryDistinct(List<Statement> hyps)
    {
        var vars = hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToHashSet();
        var r = new HashSet<(string, string)>();
        foreach (List<string> d in _dScopes.SelectMany(x => x))
        {
            for (int i = 0; i < d.Count; i++)
            {
                for (int j = i + 1; j < d.Count; j++)
                {
                    if (vars.Contains(d[i]) && vars.Contains(d[j]) && d[i] != d[j])
                    {
                        r.Add(string.CompareOrdinal(d[i], d[j]) < 0 ? (d[i], d[j]) : (d[j], d[i]));
                    }
                }
            }
        }
        return r.ToList();
    }

    /// <summary>The mandatory hypotheses, in order, of an assertion with this statement made where the database ends.</summary>
    public IReadOnlyList<Statement> MandatoryHyps(Expr assertion) => Mandatory(_scopes, assertion);

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

    /// <summary>The database the prover parses and applies against.</summary>
    public Database Database => _db;

    /// <summary>
    /// Share subproofs (<see cref="SharedProofs"/>): a long syntax proof, and each proof longer than a few dozen
    /// steps, becomes one shared step. Proofs made this way must be expanded or compressed through the database's
    /// <see cref="Database.Shared"/> before they are written.
    /// </summary>
    public bool Sharing { get; set; }

    private const int ShareAbove = 48, ShareSyntaxAbove = 12;
    private readonly Dictionary<string, List<string>> _syntaxShared = new();

    /// <summary>
    /// When set, parsing or applying after this time throws <see cref="TimeoutException"/>: a time budget per proof, so
    /// that one pathological constant can't stall a long run (define-all).
    /// </summary>
    public DateTime? Deadline { get; set; }

    /// <summary>
    /// When set, a budget in CPU time rather than wall time: once <see cref="Deadline"/> passes, this is asked how many
    /// seconds of budget are left, and while some are, the deadline moves forward by that much. On a loaded machine a
    /// wall-clock budget times out proofs that a quiet one finishes (theorem-all; see ThreadCpu).
    /// </summary>
    public Func<double>? BudgetLeft { get; set; }

    /// <summary>The deadline in force now, moved forward first if <see cref="BudgetLeft"/> says budget is left.</summary>
    public DateTime? CurrentDeadline()
    {
        if (Deadline is DateTime d && DateTime.UtcNow > d && BudgetLeft is { } left && left() is double r && r > 0)
        {
            Deadline = DateTime.UtcNow.AddSeconds(Math.Max(r, 0.25));
        }
        return Deadline;
    }

    private void CheckDeadline()
    {
        if (CurrentDeadline() is DateTime d && DateTime.UtcNow > d)
        {
            throw new TimeoutException("over its time budget");
        }
    }

    /// <summary>The syntax tree of an expression of this typecode, or null if it does not parse.</summary>
    public SyntaxTree? Parse(string type, IReadOnlyList<string> syms)
    {
        using var prof = Prof.Time("Parse");
        CheckDeadline();
        // Successful parses are cached: proofs re-parse the same long terms many times. (A parse stays valid when the
        // database grows; a failure might not, so failures aren't cached.)
        string key = type + " " + string.Join(' ', syms);
        if (_parsed.TryGetValue(key, out SyntaxTree? hit))
        {
            return hit;
        }
        using var miss = Prof.Time("Parse miss");
        if (Prof.On) Prof.Add("Parse miss symbols", syms.Count);
        var memo = new Dictionary<(string, int), List<(int End, SyntaxTree Tree)>>();
        // Where each "(" closes: a class term starting with "(" ends at its ")", so a known parse of that span is the parse.
        var close = new int[syms.Count];
        var open = new Stack<int>();
        for (int i = 0; i < syms.Count; i++)
        {
            close[i] = -1;
            if (syms[i] == "(")
            {
                open.Push(i);
            }
            else if (syms[i] == ")" && open.Count > 0)
            {
                close[open.Pop()] = i;
            }
        }
        _close = close;
        foreach ((int end, SyntaxTree tree) in ParseAt(type, syms, 0, memo))
        {
            if (end == syms.Count)
            {
                Remember(key, tree);
                return tree;
            }
        }
        return null;
    }

    private readonly Dictionary<string, SyntaxTree> _parsed = new();
    private long _parsedChars;

    /// <summary>Cache a parse; the cache is emptied when its keys pass about 100 million characters.</summary>
    private void Remember(string key, SyntaxTree tree)
    {
        if (_parsed.TryAdd(key, tree))
        {
            _parsedChars += key.Length;
            if (_parsedChars > 100_000_000)
            {
                _parsed.Clear();
                _rendered.Clear();
                _parsedChars = 0;
            }
        }
    }
    private int[] _close = [];

    private List<(int, SyntaxTree)> ParseAt(string type, IReadOnlyList<string> syms, int pos, Dictionary<(string, int), List<(int, SyntaxTree)>> memo)
    {
        if (memo.TryGetValue((type, pos), out var known))
        {
            return known;
        }
        CheckDeadline();   // a single parse of a long expression can outlast the budget
        var results = new List<(int, SyntaxTree)>();
        memo[(type, pos)] = results;   // a left-recursive call sees no results yet
        if (type == "class" && pos < syms.Count && syms[pos] == "(" && _close[pos] > pos
            && _parsed.TryGetValue("class " + string.Join(' ', syms.Skip(pos).Take(_close[pos] - pos + 1)), out SyntaxTree? span))
        {
            results.Add((_close[pos] + 1, span));
            return results;
        }
        // A variable of this typecode.
        if (pos < syms.Count && _db.FloatOf(syms[pos]) is Statement f && f.Expr.Type == type)
        {
            results.Add((pos + 1, new SyntaxTree(f, [])));
        }
        if (!_db.SyntaxByType.TryGetValue(type, out List<Statement>? all))
        {
            return results;
        }
        // Only the rules that can start here: those starting with this symbol, and those starting with a variable.
        RuleIndex ix = IndexOf(type, all);
        List<(int, Statement)> byConst = pos < syms.Count && ix.ByFirst.TryGetValue(syms[pos], out var bc) ? bc : [];
        foreach (Statement rule in MergeInOrder(byConst, ix.VarFirst))
        {
            IReadOnlyList<string> pat = rule.Expr.Symbols;
            foreach ((int end, Dictionary<string, SyntaxTree> binds) in Match(pat, 0, syms, pos, new Dictionary<string, SyntaxTree>(), memo))
            {
                // Children in the order of the rule's mandatory $f hypotheses.
                var children = rule.Hyps.Where(h => h.Kind == 'f').Select(h => binds[h.Var!]).ToList();
                results.Add((end, new SyntaxTree(rule, children)));
            }
        }
        return results;
    }

    private sealed record RuleIndex(int Count, Dictionary<string, List<(int, Statement)>> ByFirst, List<(int, Statement)> VarFirst);

    private readonly Dictionary<string, RuleIndex> _ruleIndex = new();

    /// <summary>A typecode's syntax rules by their first symbol (rebuilt when the database has grown).</summary>
    private RuleIndex IndexOf(string type, List<Statement> rules)
    {
        if (_ruleIndex.TryGetValue(type, out RuleIndex? ix) && ix.Count == rules.Count)
        {
            return ix;
        }
        var byFirst = new Dictionary<string, List<(int, Statement)>>();
        var varFirst = new List<(int, Statement)>();
        for (int i = 0; i < rules.Count; i++)
        {
            IReadOnlyList<string> pat = rules[i].Expr.Symbols;
            if (pat.Count > 0 && _db.IsConstant(pat[0]))
            {
                if (!byFirst.TryGetValue(pat[0], out var l))
                {
                    byFirst[pat[0]] = l = [];
                }
                l.Add((i, rules[i]));
            }
            else
            {
                varFirst.Add((i, rules[i]));
            }
        }
        return _ruleIndex[type] = new RuleIndex(rules.Count, byFirst, varFirst);
    }

    /// <summary>Two lists of rules, each in database order, merged in database order.</summary>
    private static IEnumerable<Statement> MergeInOrder(List<(int I, Statement S)> a, List<(int I, Statement S)> b)
    {
        int i = 0, j = 0;
        while (i < a.Count || j < b.Count)
        {
            yield return j >= b.Count || (i < a.Count && a[i].I < b[j].I) ? a[i++].S : b[j++].S;
        }
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
        if (_rendered.TryGetValue(n, out string? known))
        {
            return known;
        }
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
        string text = string.Join(' ', n.Rule.Expr.Symbols.Select(s => vars.IndexOf(s) is int i and >= 0 ? Render(n.Children[i]) : s));
        // A rendered subtree is a parse of its text (the grammar is unambiguous): parsing that text again, as proofs
        // that take terms apart do all the time, finds it in the cache.
        if (_rendered.Count > 2_000_000)
        {
            _rendered.Clear();
        }
        _rendered[n] = text;
        Remember(n.Rule.Expr.Type + " " + text, n);
        return text;
    }

    private readonly Dictionary<SyntaxTree, string> _rendered = new(ReferenceEqualityComparer.Instance);

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
        using var prof = Prof.Time("Apply");
        CheckDeadline();
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
                proof.AddRange(Sharing ? SharedSyntax(h.Expr.Type, v) : SyntaxProof(new Expr(h.Expr.Type, v)));
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
        Expr result = Inst(a.Expr);
        if (Sharing && proof.Count > ShareAbove)
        {
            proof = [_db.Shared.Add(proof, result)];
        }
        return (proof, result);
    }

    /// <summary>The syntax proof of an expression, as one shared step when it is long, made once per expression.</summary>
    private List<string> SharedSyntax(string type, string[] syms)
    {
        string key = type + " " + string.Join(' ', syms);
        if (!_syntaxShared.TryGetValue(key, out List<string>? p))
        {
            var e = new Expr(type, syms);
            p = SyntaxProof(e);
            if (p.Count > ShareSyntaxAbove)
            {
                p = [_db.Shared.Add(p, e)];
            }
            if (_syntaxShared.Count > 500_000)
            {
                _syntaxShared.Clear();
            }
            _syntaxShared[key] = p;
        }
        return p;
    }
}


/// <summary>
/// Metamath's compressed proof format (the Metamath book, appendix B), with every repeated subproof shared: a proof is
/// <c>( labels ) LETTERS</c>, where the letters number the steps — the theorem's mandatory hypotheses first, then the
/// listed labels, then the steps saved by <c>Z</c> — and a repeated subproof is written once, saved, and referred to by
/// number after that. A flat proof repeats every subterm in full; this writes each distinct one once.
/// </summary>
public static class CompressedProof
{
    /// <summary>
    /// Compress a proof (labels in reverse Polish order). <paramref name="mandatory"/> are the theorem's mandatory
    /// hypotheses, in order; <paramref name="arity"/> gives the number of hypotheses of every other label the proof uses.
    /// Returns the label list and the letters, without the parentheses.
    /// </summary>
    public static (List<string> Labels, string Letters) Compress(IReadOnlyList<string> proof, IReadOnlyList<string> mandatory, Func<string, int> arity, SharedProofs? shared = null)
    {
        using var prof = Prof.Time("Compress");
        var hypNumber = new Dictionary<string, int>();
        for (int i = 0; i < mandatory.Count; i++)
        {
            hypNumber.TryAdd(mandatory[i], i + 1);
        }

        // The proof as a tree, with equal subproofs as one node: a node is its label and its children's nodes.
        var nodeLabel = new List<string>();
        var nodeChildren = new List<int[]>();
        var intern = new Dictionary<string, int>();
        var key = new StringBuilder();
        // A shared subproof (SharedProofs) is one node, found once: those a proof reaches are interned first, in
        // increasing order, so each one's own shared steps are already nodes.
        var sharedNode = new Dictionary<int, int>();
        List<int> Run(IReadOnlyList<string> labels)
        {
            var stack = new List<int>();
            foreach (string label in labels)
            {
                if (shared is not null && SharedProofs.IsRef(label))
                {
                    stack.Add(sharedNode[SharedProofs.IdOf(label)]);
                    continue;
                }
                int k = hypNumber.ContainsKey(label) ? 0 : arity(label);
                if (k > stack.Count)
                {
                    throw new InvalidOperationException($"compressing a proof: {label} needs {k} hypotheses, the stack has {stack.Count}");
                }
                int[] children = stack.GetRange(stack.Count - k, k).ToArray();
                stack.RemoveRange(stack.Count - k, k);
                key.Clear().Append(label);
                foreach (int c in children)
                {
                    key.Append(' ').Append(c);
                }
                string ks = key.ToString();
                if (!intern.TryGetValue(ks, out int id))
                {
                    id = nodeLabel.Count;
                    nodeLabel.Add(label);
                    nodeChildren.Add(children);
                    intern[ks] = id;
                }
                stack.Add(id);
            }
            return stack;
        }
        if (shared is not null)
        {
            foreach (int sid in shared.Reachable(proof))
            {
                List<int> st = Run(shared.Body(sid));
                if (st.Count != 1)
                {
                    throw new InvalidOperationException($"compressing a proof: shared subproof @{sid} leaves {st.Count} expressions on the stack");
                }
                sharedNode[sid] = st[0];
            }
        }
        List<int> stack = Run(proof);
        if (stack.Count != 1)
        {
            throw new InvalidOperationException($"compressing a proof: it leaves {stack.Count} expressions on the stack, not 1");
        }
        int root = stack[0];

        // Which subproofs the written proof meets more than once. A shared one is not descended into again, so a
        // subproof that repeats only inside a shared one is met once. A single step costs no more to repeat than to
        // refer to, so only steps with hypotheses are shared.
        int n = nodeLabel.Count;
        var met = new int[n];
        var todo = new Stack<int>();
        todo.Push(root);
        while (todo.Count > 0)
        {
            int id = todo.Pop();
            if (met[id]++ > 0)
            {
                continue;
            }
            foreach (int c in nodeChildren[id])
            {
                todo.Push(c);
            }
        }

        // The steps, in order: a label (≥ 0, its node), a saved step (< 0: -1 - its index), or Z (int.MinValue).
        const int Z = int.MinValue;
        var steps = new List<int>();
        var saved = new Dictionary<int, int>();
        var uses = new Dictionary<string, int>();
        var walk = new Stack<(int Id, bool Done)>();
        walk.Push((root, false));
        while (walk.Count > 0)
        {
            (int id, bool done) = walk.Pop();
            if (!done)
            {
                if (saved.TryGetValue(id, out int s))
                {
                    steps.Add(-1 - s);
                    continue;
                }
                walk.Push((id, true));
                int[] ch = nodeChildren[id];
                for (int i = ch.Length - 1; i >= 0; i--)
                {
                    walk.Push((ch[i], false));
                }
                continue;
            }
            steps.Add(id);
            string l = nodeLabel[id];
            if (!hypNumber.ContainsKey(l))
            {
                uses[l] = uses.GetValueOrDefault(l) + 1;
            }
            if (met[id] > 1 && nodeChildren[id].Length > 0 && !saved.ContainsKey(id))
            {
                saved[id] = saved.Count;
                steps.Add(Z);
            }
        }

        // The labels, most used first so that they get the shortest numbers.
        var labels = uses.OrderByDescending(kv => kv.Value).ThenBy(kv => kv.Key, StringComparer.Ordinal).Select(kv => kv.Key).ToList();
        var labelNumber = new Dictionary<string, int>(hypNumber);
        for (int i = 0; i < labels.Count; i++)
        {
            labelNumber[labels[i]] = mandatory.Count + i + 1;
        }
        int firstSaved = mandatory.Count + labels.Count + 1;
        var letters = new StringBuilder();
        foreach (int st in steps)
        {
            if (st == Z)
            {
                letters.Append('Z');
            }
            else if (st < 0)
            {
                AppendNumber(letters, firstSaved + (-1 - st));
            }
            else
            {
                AppendNumber(letters, labelNumber[nodeLabel[st]]);
            }
        }
        return (labels, letters.ToString());
    }

    /// <summary>A step number in letters: the last digit A–T (1–20), the ones before it U–Y (1–5).</summary>
    public static void AppendNumber(StringBuilder sb, int number)
    {
        int n = number - 1;
        var digits = new Stack<char>();
        digits.Push((char)('A' + n % 20));
        n /= 20;
        while (n > 0)
        {
            n--;
            digits.Push((char)('U' + n % 5));
            n /= 5;
        }
        while (digits.Count > 0)
        {
            sb.Append(digits.Pop());
        }
    }

    /// <summary>
    /// Expand a compressed proof back to labels in reverse Polish order, each shared subproof written out again: the
    /// inverse of <see cref="Compress"/>, for checking it.
    /// </summary>
    public static List<string> Expand(IReadOnlyList<string> labels, string letters, IReadOnlyList<string> mandatory, Func<string, int> arity)
    {
        var all = mandatory.Concat(labels).ToList();
        var stack = new List<List<string>>();
        var saved = new List<List<string>>();
        int number = 0;
        foreach (char c in letters)
        {
            if (char.IsWhiteSpace(c))
            {
                continue;
            }
            if (c == 'Z')
            {
                saved.Add(stack[^1]);
                continue;
            }
            if (c is >= 'U' and <= 'Y')
            {
                number = number * 5 + (c - 'U' + 1);
                continue;
            }
            if (c is < 'A' or > 'T')
            {
                throw new InvalidOperationException($"not a compressed proof letter: {c}");
            }
            number = number * 20 + (c - 'A' + 1);
            if (number <= all.Count)
            {
                string label = all[number - 1];
                int k = number <= mandatory.Count ? 0 : arity(label);
                var step = new List<string>();
                foreach (List<string> h in stack.GetRange(stack.Count - k, k))
                {
                    step.AddRange(h);
                }
                stack.RemoveRange(stack.Count - k, k);
                step.Add(label);
                stack.Add(step);
            }
            else
            {
                stack.Add(saved[number - all.Count - 1]);
            }
            number = 0;
        }
        if (stack.Count != 1)
        {
            throw new InvalidOperationException($"the proof leaves {stack.Count} expressions on the stack, not 1");
        }
        return stack[0];
    }
}

/// <summary>
/// Writes a .mm file that includes set.mm and adds theorems with their proofs. Given the database the proofs were made
/// against, it writes them compressed, sharing every repeated subproof (<see cref="CompressedProof"/>); without one,
/// as flat label lists.
/// </summary>
public sealed class Writer
{
    private readonly StringBuilder _sb = new();
    private readonly Database? _db;
    private readonly Dictionary<string, int> _written = new();   // the number of hypotheses of each theorem written here

    public Writer(string include, string header) : this(include, header, null)
    {
    }

    /// <param name="compressAgainst">The database the proofs are made against, to compress them; null for flat proofs.</param>
    public Writer(string include, string header, Database? compressAgainst)
    {
        _db = compressAgainst;
        _sb.AppendLine($"$( {NameEscape.CommentText(header)} $)");
        _assumptionsAt = _sb.Length;
        _sb.AppendLine($"$[ {include} $]");
        _sb.AppendLine();
    }

    public bool Compressed => _db is not null;

    private readonly int _assumptionsAt;

    /// <summary>State the output's assumptions (Model.Assumptions) in a comment after the header.</summary>
    public void Assumptions(string text)
    {
        _sb.Insert(_assumptionsAt, $"$(\n{NameEscape.CommentText(text.TrimEnd())}\n$)\n");
    }

    public void Theorem(string label, string comment, Expr statement, IEnumerable<string> proof)
    {
        _sb.AppendLine($"  $( {NameEscape.CommentText(comment)} $)");
        _sb.AppendLine($"  {label} $p {statement} $=");
        AppendProof(_sb, "    ", statement, proof.ToList());
        _sb.AppendLine(" $.");
        _sb.AppendLine();
        if (_db is not null)
        {
            _written[label] = _db.MandatoryHyps(statement).Count;
        }
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

    private static readonly System.Text.RegularExpressions.Regex RawTheorem = new(
        @"(?<head>(?<label>[^\s$]+)\s+\$p\s+(?<stmt>[^$]*?)\s+\$=)(?<ws>\s+)(?<proof>[^\s($][^$]*?)\s+\$\.",
        System.Text.RegularExpressions.RegexOptions.Singleline);

    /// <summary>
    /// Text written as it is: declarations and definitions. When compressing, a theorem in it (<c>label $p … $= … $.</c>)
    /// has its flat proof compressed too, unless the text has $e hypotheses: their scopes are not tracked here.
    /// </summary>
    public void Raw(string text)
    {
        if (_db is not null && text.Contains("$p") && !text.Contains("$e"))
        {
            text = RawTheorem.Replace(text, m =>
            {
                Expr stmt = Expr.Of(m.Groups["stmt"].Value);
                var flat = m.Groups["proof"].Value.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries).ToList();
                var sb = new StringBuilder(m.Groups["head"].Value).AppendLine();
                string indent = m.Groups["ws"].Value.Split('\n')[^1];
                AppendProof(sb, indent, stmt, flat);
                return sb.Append(" $.").ToString();
            });
        }
        _sb.AppendLine(text);
    }

    private void AppendProof(StringBuilder sb, string indent, Expr statement, List<string> proof)
    {
        if (_db is null)
        {
            sb.Append(indent).Append(string.Join(' ', proof));
            return;
        }
        var mandatory = _db.MandatoryHyps(statement).Select(h => h.Label).ToList();
        (List<string> labels, string letters) = CompressedProof.Compress(proof, mandatory, Arity, _db.Shared);
        AppendCompressed(sb, indent, labels, letters);
    }

    /// <summary>A compressed proof, <c>( labels ) LETTERS</c>, wrapped as metamath-exe wraps them.</summary>
    public static void AppendCompressed(StringBuilder sb, string indent, IReadOnlyList<string> labels, string letters)
    {
        // Wrapped at 79 columns, as metamath-exe writes compressed proofs.
        const int Width = 79;
        int col = 0;
        void Word(string w)
        {
            if (col > indent.Length && col + 1 + w.Length > Width)
            {
                sb.AppendLine();
                col = 0;
            }
            if (col == 0)
            {
                sb.Append(indent);
                col = indent.Length;
            }
            else
            {
                sb.Append(' ');
                col++;
            }
            sb.Append(w);
            col += w.Length;
        }
        Word("(");
        foreach (string l in labels)
        {
            Word(l);
        }
        Word(")");
        // The letters fill each line; whitespace may fall anywhere among them.
        for (int i = 0; i < letters.Length;)
        {
            int room = Width - col - 1;
            if (room < 1)
            {
                room = Width - indent.Length;
            }
            int take = Math.Min(room, letters.Length - i);
            Word(letters.Substring(i, take));
            i += take;
        }
    }

    private int Arity(string label)
    {
        if (_written.TryGetValue(label, out int n))
        {
            return n;
        }
        Statement s = _db![label];
        return s.Kind is 'a' or 'p' ? s.Hyps.Count : 0;
    }

    public override string ToString() => _sb.ToString();
}
