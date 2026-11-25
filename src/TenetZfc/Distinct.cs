namespace TenetZfc.Metamath;

/// <summary>
/// The distinct-variable conditions a flat proof needs: replay it, and for each assertion it applies, each of the
/// assertion's $d pairs, instantiated, gives every pair of variables in the two substituted expressions. A blanket
/// $d over all variables would be simpler, but it would also constrain every later use of the theorem (a lemma whose
/// class variable is later instantiated with a term that binds z can't carry $d z A).
/// </summary>
public static class DistinctVars
{
    /// <summary>The pairs, each ordered, or a failure when the proof needs a variable distinct from itself.</summary>
    public static List<(string, string)> Required(Database db, IReadOnlyList<string> proof)
    {
        var stack = new List<string[]>();
        var need = new HashSet<(string, string)>();
        bool IsVar(string s) => db.FloatOf(s) is not null && !db.IsConstant(s);
        foreach (string label in proof)
        {
            Statement st = db[label];
            if (st.Kind is 'f' or 'e')
            {
                stack.Add([.. st.Expr.Symbols.Prepend(st.Expr.Type)]);
                continue;
            }
            int n = st.Hyps.Count;
            if (stack.Count < n)
            {
                throw new InvalidOperationException($"{label}: the proof stack underflows");
            }
            var args = stack.GetRange(stack.Count - n, n);
            stack.RemoveRange(stack.Count - n, n);
            var sub = new Dictionary<string, string[]>();
            for (int i = 0; i < n; i++)
            {
                if (st.Hyps[i].Kind == 'f')
                {
                    sub[st.Hyps[i].Var!] = args[i][1..];
                }
            }
            for (int i = 0; i < n; i++)
            {
                // The essential hypotheses must match exactly: this replay is also a check of the proof.
                if (st.Hyps[i].Kind == 'e')
                {
                    var want = new List<string> { st.Hyps[i].Expr.Type };
                    want.AddRange(st.Hyps[i].Expr.Symbols.SelectMany(s => sub.TryGetValue(s, out string[]? v) ? v : [s]));
                    if (!want.SequenceEqual(args[i]))
                    {
                        throw new InvalidOperationException($"{label}: hypothesis {st.Hyps[i].Label} needs {string.Join(' ', want)}, got {string.Join(' ', args[i])}");
                    }
                }
            }
            foreach ((string a, string b) in st.Distinct)
            {
                foreach (string x in sub[a].Where(IsVar))
                {
                    foreach (string y in sub[b].Where(IsVar))
                    {
                        if (x == y)
                        {
                            throw new InvalidOperationException($"{label} needs {a} and {b} distinct, but both contain {x}");
                        }
                        need.Add(string.CompareOrdinal(x, y) < 0 ? (x, y) : (y, x));
                    }
                }
            }
            var concl = new List<string> { st.Expr.Type };
            concl.AddRange(st.Expr.Symbols.SelectMany(s => sub.TryGetValue(s, out string[]? v) ? v : [s]));
            stack.Add([.. concl]);
        }
        return need.OrderBy(p => p.Item1, StringComparer.Ordinal).ThenBy(p => p.Item2, StringComparer.Ordinal).ToList();
    }
}
