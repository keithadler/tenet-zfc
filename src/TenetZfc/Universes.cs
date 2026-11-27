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

    /// <summary>
    /// The lowered tower (docs/milestone4.md): an increasing ω-sequence of reflecting weak universes, the first containing
    /// ω. ZFC proves one exists (lean-wit-tw), so a theorem whose statement doesn't mention U holds outright.
    /// </summary>
    public const string LoweredTowerToken = "lean.-wtower";

    /// <summary>Reflecting weak universes: weak universes W with ( R1 ` ( ( rank ` x ) +o _om ) ) e. W for each x e. W.</summary>
    public const string WuniToken = "lean.-wuni";

    /// <summary>The token of the tower in use: lean.-tower, or lean.-wtower when lowered.</summary>
    public string Tower => lowered ? LoweredTowerToken : TowerToken;

    /// <summary>What each level of the tower is: Univ (Grothendieck universes), or lean.-wuni when lowered.</summary>
    public string UClass => lowered ? WuniToken : "Univ";

    /// <summary>Theorems proved with no universe hypothesis (lowered tower, discharged), for the header.</summary>
    public List<string> PlainZfc { get; } = new();

    /// <summary>Whether the tower is lowered to weak universes (docs/milestone4.md).</summary>
    public bool Lowered => lowered;

    /// <summary>Each defined constant by its token.</summary>
    private readonly Dictionary<string, Name> _tokenNames = new();

    /// <summary>The class the universe argument ranges over: Univ, or the towers.</summary>
    private string UniverseDomain => tower ? Tower : "Univ";

    /// <summary>The hypothesis on the universe argument U.</summary>
    private string UHyp => $"U e. {UniverseDomain}";

    /// <summary>A name as part of a label: labels allow only letters, digits and - _ . (c.{0,1} becomes c.u0_1).</summary>
    public static string LabelPart(string name)
    {
        string r = name.Replace("{", "u").Replace(",", "_").Replace("}", "");
        // Labels allow only letters, digits, '_', '-' and '.': any other character (congrFun' has a quote) is written
        // as its code, between hyphens, which no Lean identifier contains.
        if (r.All(ch => char.IsAsciiLetterOrDigit(ch) || ch is '_' or '-' or '.'))
        {
            return r;
        }
        var sb = new System.Text.StringBuilder();
        foreach (char ch in r)
        {
            if (char.IsAsciiLetterOrDigit(ch) || ch is '_' or '-' or '.')
            {
                sb.Append(ch);
            }
            else
            {
                sb.Append('-').Append(((int)ch).ToString("x", System.Globalization.CultureInfo.InvariantCulture)).Append('-');
            }
        }
        return sb.ToString();
    }

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
        if (!tower || _values.ContainsKey(Tower))
        {
            return;
        }
        if (lowered)
        {
            EmitRaw(t.Of("-wuni"), WuniToken, "{ w e. WUni | A. x e. w ( R1 ` ( ( rank ` x ) +o _om ) ) e. w }",
                ["w", "x"], "reflecting weak universes: weak universes that contain, with each member x, the weak universe R1 at rank x plus omega");
            EmitRaw(t.Of("-wtower"), LoweredTowerToken, TowerBody("f"),
                ["f", "n"], "lowered universe towers: increasing omega-sequences of reflecting weak universes, the first containing omega (ZFC proves one exists)");
            return;
        }
        EmitRaw(t.Of("-tower"), TowerToken, TowerBody("f"),
            ["f", "n"], "universe towers: increasing omega-sequences of Grothendieck universes, the first containing omega");
    }

    /// <summary>In the lowered tower, define the witness lean.-wit once (<see cref="TowerWitness"/>).</summary>
    public void EnsureWitness()
    {
        EnsureTower();
        if (lowered && !_values.ContainsKey(TowerWitness.Wit))
        {
            EmitRaw(t.Of("-wit"), TowerWitness.Wit, TowerWitness.Definiens, ["n"],
                "witness that ZFC proves a lowered tower exists: R1 at the limit ordinals omega^2 (n + 1)");
        }
    }

    /// <summary>The class lean.-tower (or lean.-wtower) abbreviates, with its bound variable named f.</summary>
    public string TowerBody(string f) => $"{{ {f} | {TowerCondition(f)} }}";

    /// <summary>What f e. lean.-tower says: ( ( f : _om --> Univ /\ _om e. ( f ` (/) ) ) /\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ).</summary>
    public string TowerCondition(string f) =>
        $"( ( {f} : _om --> {UClass} /\\ _om e. ( {f} ` (/) ) ) /\\ A. n e. _om ( {f} ` n ) e. ( {f} ` suc n ) )";

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
            ChoiceAssumption(sb);
            return Ascii(sb.ToString());
        }
        var byLevel = new SortedDictionary<int, List<string>>();
        var whole = new List<string>();
        var open = new List<string>();
        var helpers = new List<string>();
        foreach (var (tok, body) in _values)
        {
            if (!_tokenNames.TryGetValue(tok, out Name? n))
            {
                continue;
            }
            // The well-ordering layer of a constant that uses choice ranges over the tower's union; that is not an open level.
            string[] w = body.Replace($"~P ( U. ran {UniverseVar} X. U. ran {UniverseVar} )", "~P W", StringComparison.Ordinal).Split(' ');
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
                (tok == QuotEqv ? helpers : env.Find(n)?.Kind == ConstKind.Recursor ? whole : open).Add($"{n}");
            }
        }
        if (lowered)
        {
            sb.AppendLine("Universes: lowered (docs/milestone4.md). Lemmas have the hypothesis U e. lean.-wtower: U is an increasing");
            sb.AppendLine("omega-sequence of reflecting weak universes (lean.-wuni: weak universes containing, with each member x, the");
            sb.AppendLine("weak universe R1 at rank x + omega), the first containing omega, and Lean's Sort (k+1) is ( U ` k ). ZFC");
            sb.AppendLine("proves such a tower exists: lean-wit-tw, for lean.-wit = R1 at the limit ordinals omega^2 (n + 1). So a");
            sb.AppendLine("theorem whose statement doesn't mention U holds outright: the universe hypothesis is discharged.");
            sb.AppendLine("No ax-groth: weak universes are closed under pairs, unions, power sets and function spaces, which ZF proves;");
            sb.AppendLine("indexed unions, which they lack, were bounded (by a product of the components' sets, or, for a recursive");
            sb.AppendLine("type's stages, by R1 at rank 0 + omega, a member of every level: the reflection step).");
            if (PlainZfc.Count > 0)
            {
                Wrap(sb, "Plain ZFC (no universe hypothesis, no ax-groth; scripts/check-axioms checks both): ", PlainZfc);
            }
        }
        else
        {
            sb.AppendLine("Universes: a tower U of Grothendieck universes. Each theorem has the hypothesis U e. lean.-tower: U is");
            sb.AppendLine("an increasing omega-sequence of Grothendieck universes, the first containing omega, and Lean's Sort (k+1)");
            sb.AppendLine("is ( U ` k ). ZFC does not prove that such a tower exists (that needs inaccessible cardinals), so each");
            sb.AppendLine("theorem holds in every model of ZFC that has one. No axiom is added.");
            sb.AppendLine("Plain ZFC: no theorem here; each needs the tower hypothesis. The universe elimination of docs/milestone4.md");
            sb.AppendLine("(--lowered) discharges it where every universe fact the proof uses holds in weak universes.");
        }
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
            sb.AppendLine("  (a projection names its structure without universe levels, so the structure, and what its type uses, is defined with them open)");
        }
        if (helpers.Count > 0)
        {
            Wrap(sb, "U. ran U is the domain of the quotient's relation, in: ", helpers);
            sb.AppendLine("  (the least equivalence relation containing r, on a type at any level: one helper serves Quot.{k} for every k)");
        }
        ChoiceAssumption(sb);
        return Ascii(sb.ToString());
    }

    /// <summary>
    /// The choice part of the header: which constants take a well-ordering because they use Classical.choice, and what
    /// a theorem about them assumes (ModelBuiltins.cs). Nothing when no constant uses choice.
    /// </summary>
    private void ChoiceAssumption(System.Text.StringBuilder sb)
    {
        var uses = _values.Keys.Where(_choiceDependent.Contains).Select(tok => _tokenNames.TryGetValue(tok, out Name? n) ? $"{n}" : tok).ToList();
        if (uses.Count == 0)
        {
            return;
        }
        string all = WellOrdered("U");
        sb.AppendLine($"Choice: Classical.choice is the least element in a well-ordering W of {all}" + (tower ? ", the tower's union, so one" : ", so the"));
        sb.AppendLine("well-ordering serves every level. ZFC defines no global choice function, so W is a parameter (as set.mm's hta");
        sb.AppendLine($"emulates Hilbert's epsilon): each constant below takes W e. ~P ( {all} X. {all} ) after U, and a theorem that");
        sb.AppendLine($"needs choice to pick an element has the hypothesis W We {all}. ZFC proves such a W exists (weth), so no axiom is added.");
        Wrap(sb, "Constants that take W: ", uses);
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
