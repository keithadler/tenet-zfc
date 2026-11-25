namespace TenetZfc;

/// <summary>
/// Translates a Lean theorem's statement into a set.mm statement, by the table of docs/interpretation.md: bound
/// variables become class variables (A, B, …), a variable of a type T becomes a hypothesis x e. ⟦T⟧, a type variable
/// becomes a class variable with no hypothesis, a premise that is a proposition becomes an antecedent, and the
/// conclusion becomes a wff. Everything outside the table makes the translation fail, naming the term.
/// </summary>
public sealed class StatementTranslator(Terms t)
{
    private static readonly string[] ClassVars = "A B C D E F G H I J K L M N O P Q R S T U V W X Y Z".Split(' ');

    private readonly Name _nat = t.Of("Nat"), _natAdd = t.Of("Nat.add"), _addAdd = t.Of("Add.add"), _hAdd = t.Of("HAdd.hAdd"),
        _instHAdd = t.Of("instHAdd"), _instAddNat = t.Of("instAddNat"), _ofNat = t.Of("OfNat.ofNat"), _instOfNatNat = t.Of("instOfNatNat"),
        _zero = t.Of("Nat.zero"), _succ = t.Of("Nat.succ"), _eq = t.Of("Eq"), _true = t.Of("True"),
        _list = t.Of("List"), _length = t.Of("List.length"), _nil = t.Of("List.nil"), _cons = t.Of("List.cons"),
        _append = t.Of("List.append"), _hAppend = t.Of("HAppend.hAppend"), _instHAppend = t.Of("instHAppendOfAppend"),
        _listInstAppend = t.Of("List.instAppend");

    private readonly Dictionary<ulong, string> _vars = new();
    private string? _why;

    /// <summary>Why the last translation failed.</summary>
    public string? Why => _why;

    /// <summary>Translate the free variable <paramref name="fvar"/> as the class variable <paramref name="name"/>.</summary>
    public void Bind(Expr fvar, string name) => _vars[((FVar)fvar).Id] = name;

    /// <summary>Forget every binding.</summary>
    public void Reset()
    {
        _vars.Clear();
        _why = null;
    }

    private bool Is(Expr e, Name n) => e is Const c && ReferenceEquals(c.Name, n);

    private string? Fail(string why)
    {
        _why ??= why;
        return null;
    }

    /// <summary>⟦e⟧ as a set.mm class, or null outside the table.</summary>
    public string? Class(Expr e)
    {
        if (e is FVar f)
        {
            return _vars.TryGetValue(f.Id, out string? v) ? v : Fail("a free variable");
        }
        if (e is NatLit n)
        {
            return n.Value <= 1_000_000 ? Bridge.Numeral((long)n.Value) : Fail("a very large literal");
        }
        if (Is(e, _nat))
        {
            return "NN0";
        }
        if (Is(e, _zero))
        {
            return "0";
        }
        Expr head = Ops.Spine(e, out List<Expr> a);
        if (head is not Const c)
        {
            return Fail($"an application whose head is not a constant: {e}");
        }
        Name h = c.Name;
        string? Bin(string op, Expr x, Expr y) => Class(x) is string l && Class(y) is string r ? $"( {l} {op} {r} )" : null;
        if (ReferenceEquals(h, _ofNat) && a.Count == 3 && Is(a[0], _nat) && a[1] is NatLit lit
            && Ops.Spine(a[2], out List<Expr> ia) is Const ic && ReferenceEquals(ic.Name, _instOfNatNat) && ia.Count == 1 && ReferenceEquals(ia[0], a[1]))
        {
            return Class(lit);
        }
        if (ReferenceEquals(h, _natAdd) && a.Count == 2)
        {
            return Bin("+", a[0], a[1]);
        }
        if (ReferenceEquals(h, _addAdd) && a.Count == 4 && Is(a[0], _nat) && Is(a[1], _instAddNat))
        {
            return Bin("+", a[2], a[3]);
        }
        if (ReferenceEquals(h, _hAdd) && a.Count == 6 && Is(a[0], _nat) && Is(a[1], _nat) && Is(a[2], _nat)
            && Ops.Spine(a[3], out List<Expr> ha) is Const hc && ReferenceEquals(hc.Name, _instHAdd) && ha.Count == 2 && Is(ha[0], _nat) && Is(ha[1], _instAddNat))
        {
            return Bin("+", a[4], a[5]);
        }
        if (ReferenceEquals(h, _succ) && a.Count == 1)
        {
            return Class(a[0]) is string s ? $"( {s} + 1 )" : null;
        }
        if (ReferenceEquals(h, _list) && a.Count == 1)
        {
            return Class(a[0]) is string s ? $"Word {s}" : null;
        }
        if (ReferenceEquals(h, _length) && a.Count == 2)
        {
            return Class(a[1]) is string s ? $"( # ` {s} )" : null;
        }
        if (ReferenceEquals(h, _nil) && a.Count == 1)
        {
            return "(/)";
        }
        if (ReferenceEquals(h, _cons) && a.Count == 3)
        {
            return Class(a[1]) is string x && Class(a[2]) is string l ? $"( <\" {x} \"> ++ {l} )" : null;
        }
        if (ReferenceEquals(h, _append) && a.Count == 3)
        {
            return Bin("++", a[1], a[2]);
        }
        // HAppend.hAppend (List α) (List α) (List α) (instHAppendOfAppend (List α) (List.instAppend α)) l m
        if (ReferenceEquals(h, _hAppend) && a.Count == 6 && Ops.Spine(a[3], out List<Expr> pa) is Const pc && ReferenceEquals(pc.Name, _instHAppend)
            && pa.Count == 2 && Ops.Spine(pa[1], out _) is Const lc && ReferenceEquals(lc.Name, _listInstAppend))
        {
            return Bin("++", a[4], a[5]);
        }
        return Fail($"a term outside the table: {h}");
    }

    /// <summary>⟦p⟧ for a proposition, as a set.mm wff, or null outside the table.</summary>
    public string? Wff(Expr p)
    {
        if (Is(p, _true))
        {
            return "T.";
        }
        if (p is Binder { IsPi: true } pi && pi.Body.LooseBVarRange == 0)
        {
            return Wff(pi.Domain) is string lhs && Wff(pi.Body) is string rhs ? $"( {lhs} -> {rhs} )" : null;
        }
        if (Ops.Spine(p, out List<Expr> a) is Const c && ReferenceEquals(c.Name, _eq) && a.Count == 3)
        {
            return Class(a[1]) is string l && Class(a[2]) is string r ? $"{l} = {r}" : null;
        }
        return Fail($"a proposition outside the table: {p}");
    }

    /// <summary>
    /// The set.mm statement for a theorem's type: |- ( hypotheses -> conclusion ), the hypotheses joined by /\, or
    /// |- conclusion when there are none. Null (see <see cref="Why"/>) when anything is outside the table.
    /// </summary>
    public string? Statement(Expr type)
    {
        _vars.Clear();
        _why = null;
        var hyps = new List<string>();
        int next = 0;
        ulong fresh = 1UL << 61;
        while (type is Binder { IsPi: true } pi)
        {
            if (next >= ClassVars.Length)
            {
                return Fail("more bound variables than set.mm has class variables");
            }
            if (pi.Domain is Sort)
            {
                // A type variable: any class will do, with no hypothesis.
                Expr v = t.FVar(fresh++);
                _vars[((FVar)v).Id] = ClassVars[next++];
                type = new Ops(t).Instantiate(pi.Body, [v]);
                continue;
            }
            if (pi.Body.LooseBVarRange == 0 && Wff(pi.Domain) is string premise)
            {
                hyps.Add(premise);
                type = pi.Body;
                continue;
            }
            _why = null;
            if (Class(pi.Domain) is not string dom)
            {
                return null;
            }
            Expr x = t.FVar(fresh++);
            string name = ClassVars[next++];
            _vars[((FVar)x).Id] = name;
            hyps.Add($"{name} e. {dom}");
            type = new Ops(t).Instantiate(pi.Body, [x]);
        }
        if (Wff(type) is not string concl)
        {
            return null;
        }
        string body = hyps.Count switch
        {
            0 => concl,
            1 => $"( {hyps[0]} -> {concl} )",
            2 => $"( ( {hyps[0]} /\\ {hyps[1]} ) -> {concl} )",
            3 => $"( ( {hyps[0]} /\\ {hyps[1]} /\\ {hyps[2]} ) -> {concl} )",
            _ => $"( {hyps.Skip(1).Aggregate(hyps[0], (acc, h) => $"( {acc} /\\ {h} )")} -> {concl} )",
        };
        return "|- " + body;
    }
}
