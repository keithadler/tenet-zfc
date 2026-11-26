using System.Globalization;

namespace TenetZfc.Metamath;

/// <summary>
/// Subproofs shared between proofs, as Lean's kernel shares terms: a proof step <c>@n</c> stands for the whole subproof
/// number n, built once. A proof is then a DAG rather than a flat list, so a typing step that repeats a large type
/// (its syntax proof, or the same membership proved twice) costs one step wherever it is used, not its full size.
///
/// The prover makes these when <see cref="Prover.Sharing"/> is on. Nothing outside reads a shared step: proofs are
/// written compressed straight from the DAG (<see cref="CompressedProof.Compress"/>), or expanded first
/// (<see cref="Expand"/>). A subproof only refers to subproofs made before it, so numbers order them topologically.
/// </summary>
public sealed class SharedProofs
{
    private readonly List<string[]> _body = new();
    private readonly List<Expr> _proves = new();
    private readonly List<long> _size = new();
    private readonly Dictionary<string[], string> _intern = new(new StepsComparer());

    /// <summary>Equal step lists, compared by their steps (labels are interned strings, so mostly by reference).</summary>
    private sealed class StepsComparer : IEqualityComparer<string[]>
    {
        public bool Equals(string[]? a, string[]? b) => a!.AsSpan().SequenceEqual(b);

        public int GetHashCode(string[] a)
        {
            var h = new HashCode();
            foreach (string s in a)
            {
                h.Add(s);
            }
            return h.ToHashCode();
        }
    }

    public static bool IsRef(string step) => step.Length > 1 && step[0] == '@';

    public static int IdOf(string step) => int.Parse(step.AsSpan(1), NumberStyles.None, CultureInfo.InvariantCulture);

    public int Count => _body.Count;

    public IReadOnlyList<string> Body(int id) => _body[id];

    public Expr Proves(int id) => _proves[id];

    /// <summary>A step standing for this proof of this expression. Equal proofs get the same step.</summary>
    public string Add(List<string> proof, Expr proves)
    {
        string[] key = [.. proof];
        if (_intern.TryGetValue(key, out string? known))
        {
            return known;
        }
        string r = "@" + _body.Count.ToString(CultureInfo.InvariantCulture);
        _body.Add(key);
        _proves.Add(proves);
        _size.Add(Size(proof));
        _intern[key] = r;
        return r;
    }

    /// <summary>The proof's length written flat, every shared step expanded.</summary>
    public long Size(IEnumerable<string> proof)
    {
        long n = 0;
        foreach (string s in proof)
        {
            n += IsRef(s) ? _size[IdOf(s)] : 1;
        }
        return n;
    }

    public static bool AnyRef(IEnumerable<string> proof) => proof.Any(IsRef);

    /// <summary>The proof written flat, every shared step expanded.</summary>
    public List<string> Expand(IEnumerable<string> proof)
    {
        var r = new List<string>();
        var todo = new Stack<IEnumerator<string>>();
        todo.Push(proof.GetEnumerator());
        while (todo.Count > 0)
        {
            IEnumerator<string> e = todo.Peek();
            if (!e.MoveNext())
            {
                todo.Pop();
                continue;
            }
            if (IsRef(e.Current))
            {
                todo.Push(((IEnumerable<string>)_body[IdOf(e.Current)]).GetEnumerator());
            }
            else
            {
                r.Add(e.Current);
            }
        }
        return r;
    }

    /// <summary>The shared subproofs a proof reaches, directly or through others, in increasing order (each after those it uses).</summary>
    public List<int> Reachable(IEnumerable<string> proof)
    {
        var seen = new HashSet<int>();
        var todo = new Stack<int>();
        foreach (string s in proof)
        {
            if (IsRef(s) && seen.Add(IdOf(s)))
            {
                todo.Push(IdOf(s));
            }
        }
        while (todo.Count > 0)
        {
            foreach (string s in _body[todo.Pop()])
            {
                if (IsRef(s) && seen.Add(IdOf(s)))
                {
                    todo.Push(IdOf(s));
                }
            }
        }
        var r = seen.ToList();
        r.Sort();
        return r;
    }

    /// <summary>The labels a proof uses anywhere, shared subproofs included.</summary>
    public HashSet<string> Labels(IEnumerable<string> proof)
    {
        var r = new HashSet<string>();
        foreach (string s in proof)
        {
            if (!IsRef(s))
            {
                r.Add(s);
            }
        }
        foreach (int id in Reachable(proof))
        {
            foreach (string s in _body[id])
            {
                if (!IsRef(s))
                {
                    r.Add(s);
                }
            }
        }
        return r;
    }

    /// <summary>
    /// The proof with labels replaced as the map says, inside shared subproofs too (copied where they change), and
    /// variables in their conclusions as <paramref name="vars"/> says: a consistent renaming of variables.
    /// </summary>
    public List<string> Rename(IReadOnlyList<string> proof, IReadOnlyDictionary<string, string> labels, IReadOnlyDictionary<string, string> vars)
    {
        var moved = new Dictionary<int, string>();
        string Map(string s) => IsRef(s) ? (moved.TryGetValue(IdOf(s), out string? m) ? m : s) : labels.TryGetValue(s, out string? l) ? l : s;
        foreach (int id in Reachable(proof))
        {
            string[] body = _body[id];
            var nb = body.Select(Map).ToList();
            if (!nb.SequenceEqual(body))
            {
                Expr e = _proves[id];
                moved[id] = Add(nb, new Expr(e.Type, e.Symbols.Select(v => vars.TryGetValue(v, out string? w) ? w : v).ToList()));
            }
        }
        return proof.Select(Map).ToList();
    }

    // ---- distinct-variable conditions, per shared subproof ----------------------------------------------------------

    private readonly Dictionary<int, (string, string)[]> _distinct = new();

    /// <summary>The $d pairs a shared subproof needs (and its hypotheses checked), computed once.</summary>
    internal IReadOnlyList<(string, string)> DistinctOf(int id, Func<IReadOnlyList<string>, List<(string, string)>> required)
    {
        if (_distinct.TryGetValue(id, out var known))
        {
            return known;
        }
        // Those it uses that aren't known yet, in increasing order, so that the computation below never recurses deeply.
        var seen = new HashSet<int> { id };
        var todo = new Stack<int>();
        todo.Push(id);
        while (todo.Count > 0)
        {
            foreach (string s in _body[todo.Pop()])
            {
                if (IsRef(s) && !_distinct.ContainsKey(IdOf(s)) && seen.Add(IdOf(s)))
                {
                    todo.Push(IdOf(s));
                }
            }
        }
        seen.Remove(id);
        foreach (int k in seen.Order())
        {
            _distinct[k] = [.. required(_body[k])];
        }
        return _distinct[id] = [.. required(_body[id])];
    }
}
