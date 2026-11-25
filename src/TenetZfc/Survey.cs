namespace TenetZfc;

/// <summary>
/// Measures how much of an export the translator covers: which theorem statements the statement table translates,
/// and which constants stand in the way, for statements alone and for statements with their proofs. The ranking says
/// what to add to the table next, and the cumulative counts say how far each addition goes.
/// </summary>
public sealed class Survey(Terms t, Environment env)
{
    /// <summary>The constants the statement table and the proof translator already give a meaning to.</summary>
    public static readonly string[] Covered =
    [
        "Nat", "Nat.add", "Add.add", "HAdd.hAdd", "instHAdd", "instAddNat", "OfNat.ofNat", "instOfNatNat", "Nat.zero", "Nat.succ",
        "Eq", "True", "List", "List.length", "List.nil", "List.cons", "List.append", "HAppend.hAppend", "instHAppendOfAppend",
        "List.instAppend",
    ];

    public sealed record Result(int Theorems, int StatementsTranslated, List<(string Why, int Count)> Reasons,
        List<(Name Const, int Statements, int WithProofs)> Blockers, List<(int Added, int Statements, int WithProofs)> Curve);

    public Result Run(int top = 40)
    {
        var covered = new HashSet<Name>(Covered.Select(t.Of), ReferenceEqualityComparer.Instance);
        var st = new StatementTranslator(t);
        List<ConstInfo> thms = env.All.Where(c => c.Kind == ConstKind.Theorem).OrderBy(c => c.Name.ToString(), StringComparer.Ordinal).ToList();
        int translated = 0;
        var reasons = new Dictionary<string, int>();
        var stmtSets = new List<HashSet<Name>>();
        var fullSets = new List<HashSet<Name>>();
        foreach (ConstInfo th in thms)
        {
            if (st.Statement(th.Type) is not null)
            {
                translated++;
            }
            else
            {
                string why = Classify(st.Why);
                reasons[why] = reasons.GetValueOrDefault(why) + 1;
            }
            var s = new HashSet<Name>(ReferenceEqualityComparer.Instance);
            Collect(th.Type, s, new HashSet<Expr>(ReferenceEqualityComparer.Instance));
            s.ExceptWith(covered);
            stmtSets.Add(s);
            var f = new HashSet<Name>(s, ReferenceEqualityComparer.Instance);
            if (th.Value is not null)
            {
                Collect(th.Value, f, new HashSet<Expr>(ReferenceEqualityComparer.Instance));
            }
            f.ExceptWith(covered);
            fullSets.Add(f);
        }

        // Rank by how many statements mention each constant.
        var freq = new Dictionary<Name, (int S, int F)>(ReferenceEqualityComparer.Instance);
        foreach (HashSet<Name> s in stmtSets)
        {
            foreach (Name n in s)
            {
                freq[n] = (freq.GetValueOrDefault(n).S + 1, freq.GetValueOrDefault(n).F);
            }
        }
        foreach (HashSet<Name> f in fullSets)
        {
            foreach (Name n in f)
            {
                freq[n] = (freq.GetValueOrDefault(n).S, freq.GetValueOrDefault(n).F + 1);
            }
        }
        List<Name> ranked = freq.OrderByDescending(kv => kv.Value.S).ThenByDescending(kv => kv.Value.F).Select(kv => kv.Key).ToList();
        var curve = new List<(int, int, int)>();
        foreach (int k in new[] { 0, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000, ranked.Count })
        {
            if (k > ranked.Count)
            {
                continue;
            }
            var add = new HashSet<Name>(ranked.Take(k), ReferenceEqualityComparer.Instance);
            curve.Add((k, stmtSets.Count(s => s.IsSubsetOf(add)), fullSets.Count(f => f.IsSubsetOf(add))));
        }
        return new Result(thms.Count, translated,
            reasons.OrderByDescending(kv => kv.Value).Select(kv => (kv.Key, kv.Value)).ToList(),
            ranked.Take(top).Select(n => (n, freq[n].S, freq[n].F)).ToList(), curve);
    }

    private static string Classify(string? why) => why switch
    {
        null => "unknown",
        _ when why.StartsWith("a term outside the table") => "a constant outside the table",
        _ when why.StartsWith("a proposition outside the table") => "a proposition outside the table (∀ over a dependent type, ∧, ∨, ¬, ↔, ∃, a predicate)",
        _ when why.StartsWith("an application whose head") => "a bound variable or λ applied to arguments",
        _ => why,
    };

    private static void Collect(Expr e, HashSet<Name> into, HashSet<Expr> seen)
    {
        while (true)
        {
            if (!seen.Add(e))
            {
                return;
            }
            switch (e)
            {
                case Const c:
                    into.Add(c.Name);
                    return;
                case App a:
                    Collect(a.Fn, into, seen);
                    e = a.Arg;
                    continue;
                case Binder b:
                    Collect(b.Domain, into, seen);
                    e = b.Body;
                    continue;
                case Let l:
                    Collect(l.Type, into, seen);
                    Collect(l.Value, into, seen);
                    e = l.Body;
                    continue;
                case Proj p:
                    into.Add(p.StructName);
                    e = p.Struct;
                    continue;
                default:
                    return;
            }
        }
    }
}
