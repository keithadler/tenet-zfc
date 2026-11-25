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
            ["f", "n"], "universe towers: increasing ω-sequences of Grothendieck universes, the first containing ω");
    }
}
