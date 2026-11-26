namespace TenetZfc;

/// <summary>
/// Universe levels for the model (docs/milestone3.md, "Universe levels"). With one universe U for every level, a
/// motive that returns a sort, like Nat.below's ( z e. Nat |-> U ), must lie in ( U ^m Nat ), which needs U e. U; it
/// doesn't, so Nat.below is (/), and so is every function defined by structural recursion through Nat.brecOn.
///
/// In tower mode the universe argument is a tower instead: U e. lean.-tower says U is an increasing ω-sequence of
/// Grothendieck universes, the first containing ω. Then:
/// - Prop is 2o, and Sort (k+1) for a concrete level k is ( U ` k ), so Sort k : Sort (k+1) holds;
/// - a level that mentions a universe parameter means the whole tower, U. ran U. Constants are monomorphized first
///   (<see cref="Monomorph"/>), so the only parameter left is a recursor's motive level, which occurs only as the
///   motive's codomain, where the whole tower is right;
/// - a Π-type into Prop is a proposition, if ( A. x e. ⟦A⟧ (/) e. ⟦B⟧ , 1o , (/) ), so that a proof, (/), is in it
///   exactly when it holds.
/// </summary>
public sealed partial class Model
{
    public const string TowerToken = "lean.-tower";

    /// <summary>Each defined constant by its token.</summary>
    private readonly Dictionary<string, Name> _tokenNames = new();

    /// <summary>The class the universe argument ranges over: Univ, or the towers.</summary>
    private string UniverseDomain => tower ? TowerToken : "Univ";

    /// <summary>The hypothesis on the universe argument U.</summary>
    private string UHyp => $"U e. {UniverseDomain}";

    /// <summary>A name as part of a label: labels allow only letters, digits and - _ . (c.{0,1} becomes c.u0_1).</summary>
    public static string LabelPart(string name) => name.Replace("{", "u").Replace(",", "_").Replace("}", "");

    /// <summary>A closed level's value, or null when it mentions a parameter.</summary>
    public static int? LevelValue(Level l) => l switch
    {
        LZero => 0,
        LSucc s => LevelValue(s.Of) + 1,
        LMax m => LevelValue(m.A) is int a && LevelValue(m.B) is int b ? Math.Max(a, b) : null,
        LIMax im => LevelValue(im.B) is int b ? (b == 0 ? 0 : LevelValue(im.A) is int a ? Math.Max(a, b) : null) : null,
        _ => null,
    };

    /// <summary>The ordinal k as set.mm writes it.</summary>
    public static string Ordinal(int k) => k switch
    {
        0 => "(/)",
        >= 1 and <= 4 => $"{k}o",
        _ => throw new Refused($"universe level {k + 1} is above what the model writes (4o)"),
    };

    private static string TowerSort(Level l, string universe) => LevelValue(l) switch
    {
        0 => "2o",
        int k => $"( {universe} ` {Ordinal(k - 1)} )",
        null => $"U. ran {universe}",
    };

    /// <summary>A Π-type into Prop: if ( A. x e. ⟦A⟧ (/) e. ⟦B⟧ , 1o , (/) ).</summary>
    private string PropPi(Binder b, Scope sc)
    {
        string dom = Tr(b.Domain, sc);
        string x = Fresh(sc, dom);
        Expr fv = t.FVar(_fresh++);
        sc.Vars[((FVar)fv).Id] = x;
        sc.Types[((FVar)fv).Id] = b.Domain;
        if (!sc.Bound.Contains(x))
        {
            sc.Bound.Add(x);
        }
        sc.Active.Add(x);
        string body = Tr(_ops.Instantiate(b.Body, [fv]), sc);
        sc.Active.RemoveAt(sc.Active.Count - 1);
        sc.Vars.Remove(((FVar)fv).Id);
        return $"if ( A. {x} e. {dom} (/) e. {body} , 1o , (/) )";
    }

    /// <summary>In tower mode, define lean.-tower once, before the first constant.</summary>
    private void EnsureTower()
    {
        if (!tower || _values.ContainsKey(TowerToken))
        {
            return;
        }
        EmitRaw(t.Of("-tower"), TowerToken,
            "{ f | ( ( f : _om --> Univ /\\ _om e. ( f ` (/) ) ) /\\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ) }",
            ["f", "n"], "universe towers: increasing omega-sequences of Grothendieck universes, the first containing omega");
    }

    /// <summary>
    /// The universe analysis of docs/spec.md, for an output's header: which universes the definitions written so far
    /// use, and which declarations use each level directly (a declaration that only uses others needs what they need).
    /// </summary>
    public string Assumptions()
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("Assumptions (the universe analysis of docs/spec.md).");
        if (!tower)
        {
            sb.AppendLine("Universes: one Grothendieck universe for every universe level. Each theorem has the hypothesis");
            sb.AppendLine("U e. Univ. In this model Sort u is not a member of Sort (u+1), so a structurally recursive definition");
            sb.AppendLine("(through Nat.below and brecOn) collapses to (/): its equations verify, but it does not mean what");
            sb.AppendLine("Lean means (docs/milestone3.md). The default model is the tower; this output asked for one universe.");
            return Ascii(sb.ToString());
        }
        var byLevel = new SortedDictionary<int, List<string>>();
        var whole = new List<string>();
        var open = new List<string>();
        foreach (var (tok, body) in _values)
        {
            if (!_tokenNames.TryGetValue(tok, out Name? n))
            {
                continue;
            }
            string[] w = body.Split(' ');
            var levels = new SortedSet<int>();
            bool all = false;
            for (int i = 0; i + 4 < w.Length; i++)
            {
                if (w[i] == "(" && w[i + 1] == UniverseVar && w[i + 2] == "`" && w[i + 4] == ")" && OrdinalValue(w[i + 3]) is int k)
                {
                    levels.Add(k);
                }
            }
            for (int i = 0; i + 2 < w.Length; i++)
            {
                all |= w[i] == "U." && w[i + 1] == "ran" && w[i + 2] == UniverseVar;
            }
            foreach (int k in levels)
            {
                (byLevel.TryGetValue(k, out var l) ? l : byLevel[k] = new()).Add($"{n}");
            }
            if (all)
            {
                (env.Find(n)?.Kind == ConstKind.Recursor ? whole : open).Add($"{n}");
            }
        }
        sb.AppendLine("Universes: a tower U of Grothendieck universes. Each theorem has the hypothesis U e. lean.-tower: U is");
        sb.AppendLine("an increasing omega-sequence of Grothendieck universes, the first containing omega, and Lean's Sort (k+1)");
        sb.AppendLine("is ( U ` k ). ZFC does not prove that such a tower exists (that needs inaccessible cardinals), so each");
        sb.AppendLine("theorem holds in every model of ZFC that has one. No axiom is added.");
        if (byLevel.Count == 0)
        {
            sb.AppendLine("Levels used: none (Prop only" + (whole.Count > 0 ? ", apart from recursors' motives" : "") + ").");
        }
        else
        {
            int top = byLevel.Keys.Max();
            sb.AppendLine(top == 0
                ? "Levels used: 1 universe, ( U ` (/) ) (Lean's Type 0)."
                : $"Levels used: {top + 1} universes, ( U ` (/) ) to ( U ` {Ordinal(top)} ) (Lean's Type 0 to Type {top}).");
        }
        foreach (var (k, names) in byLevel)
        {
            Wrap(sb, $"( U ` {Ordinal(k)} ) (Type {k}) is used directly by: ", names);
        }
        if (whole.Count > 0)
        {
            Wrap(sb, "U. ran U, the whole tower, is the codomain of the motives of: ", whole);
            sb.AppendLine("  (a recursor's motive level is left open, so one recursor serves every elimination level)");
        }
        if (open.Count > 0)
        {
            Wrap(sb, "U. ran U also stands for a universe parameter left open, in: ", open);
            sb.AppendLine("  (a projection names its structure without universe levels, so the structure is defined with them open)");
        }
        return Ascii(sb.ToString());
    }

    private static int? OrdinalValue(string s) => s switch
    {
        "(/)" => 0,
        "1o" => 1,
        "2o" => 2,
        "3o" => 3,
        "4o" => 4,
        _ => null,
    };

    private static void Wrap(System.Text.StringBuilder sb, string head, List<string> names)
    {
        string line = head;
        for (int i = 0; i < names.Count; i++)
        {
            string item = names[i] + (i + 1 < names.Count ? "," : ".");
            if (line.Length + item.Length + 1 > 110)
            {
                sb.AppendLine(line);
                line = "  ";
            }
            line += (line.EndsWith(' ') ? "" : " ") + item;
        }
        sb.AppendLine(line);
    }

    /// <summary>Text safe in a Metamath comment: ASCII, and no $( or $).</summary>
    private static string Ascii(string s) => new string(s.Where(ch => ch < 128).ToArray()).Replace("$(", "$ (").Replace("$)", "$ )");
}
