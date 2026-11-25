using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Emits set.mm theorems for Lean theorems, from their replayed traces. This first emitter covers equations between
/// Nat arithmetic terms (literals, addition, successor, zero): the milestone 2 gate.
///
/// The statement is translated through the definition table below (the shallow translation of
/// docs/interpretation.md). The proof evaluates both sides; every addition it computes must be a NatLitOp step of the
/// declaration's trace, so each arithmetic fact the proof uses is one the kernel used, now proved in set.mm.
/// </summary>
public sealed class Emitter(Terms t, Prover pr, Bridge bridge)
{
    // The definition table: each Lean form of Nat addition, of literals, of zero and successor. Its entries are where a
    // translated statement's meaning is trusted (spec, "Testing and trust"); the trace's delta and projection steps show
    // the kernel unfolding each form to Nat.add, and Nat.add's defining equations are nna0 and nnasuc.
    private readonly Name _nat = t.Of("Nat"), _natAdd = t.Of("Nat.add"), _addAdd = t.Of("Add.add"), _hAdd = t.Of("HAdd.hAdd"),
        _instHAdd = t.Of("instHAdd"), _instAddNat = t.Of("instAddNat"), _ofNat = t.Of("OfNat.ofNat"), _instOfNatNat = t.Of("instOfNatNat"),
        _zero = t.Of("Nat.zero"), _succ = t.Of("Nat.succ"), _eq = t.Of("Eq");

    private enum Shape { Literal, Add, Succ, Other }

    private bool IsC(Expr e, Name n) => e is Const c && ReferenceEquals(c.Name, n);
    private bool IsNat(Expr e) => IsC(e, _nat);

    /// <summary>What a term is under the table, with its operands.</summary>
    private (Shape Shape, long Value, Expr? A, Expr? B) Classify(Expr e)
    {
        if (e is NatLit n && n.Value <= 10_000)
        {
            return (Shape.Literal, (long)n.Value, null, null);
        }
        if (IsC(e, _zero))
        {
            return (Shape.Literal, 0, null, null);
        }
        Expr head = Ops.Spine(e, out List<Expr> a);
        // OfNat.ofNat Nat n (instOfNatNat n)
        if (IsC(head, _ofNat) && a.Count == 3 && IsNat(a[0]) && a[1] is NatLit lit && lit.Value <= 10_000
            && Ops.Spine(a[2], out List<Expr> ia) is Const ic && ReferenceEquals(ic.Name, _instOfNatNat) && ia.Count == 1 && ReferenceEquals(ia[0], a[1]))
        {
            return (Shape.Literal, (long)lit.Value, null, null);
        }
        if (IsC(head, _natAdd) && a.Count == 2)
        {
            return (Shape.Add, 0, a[0], a[1]);
        }
        // Add.add Nat instAddNat x y
        if (IsC(head, _addAdd) && a.Count == 4 && IsNat(a[0]) && IsC(a[1], _instAddNat))
        {
            return (Shape.Add, 0, a[2], a[3]);
        }
        // HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x y
        if (IsC(head, _hAdd) && a.Count == 6 && IsNat(a[0]) && IsNat(a[1]) && IsNat(a[2])
            && Ops.Spine(a[3], out List<Expr> ha) is Const hc && ReferenceEquals(hc.Name, _instHAdd) && ha.Count == 2 && IsNat(ha[0]) && IsC(ha[1], _instAddNat))
        {
            return (Shape.Add, 0, a[4], a[5]);
        }
        if (IsC(head, _succ) && a.Count == 1)
        {
            return (Shape.Succ, 0, a[0], null);
        }
        return (Shape.Other, 0, null, null);
    }

    /// <summary>⟦e⟧ under the table, or null outside it.</summary>
    public string? Translate(Expr e)
    {
        var (shape, v, a, b) = Classify(e);
        return shape switch
        {
            Shape.Literal => Bridge.Numeral(v),
            Shape.Add => Translate(a!) is string x && Translate(b!) is string y ? $"( {x} +o {y} )" : null,
            Shape.Succ => Translate(a!) is string z ? $"suc {z}" : null,
            _ => null,
        };
    }

    /// <summary>
    /// Proof of |- ⟦e⟧ = ⟦v⟧ for the numeral v the term denotes. Each addition must be licensed by the trace: a
    /// NatLitOp step adding the same two values.
    /// </summary>
    private (long Value, Proof Proof)? Evaluate(Expr e, HashSet<(long, long)> licensed, List<string> problems)
    {
        var (shape, v, a, b) = Classify(e);
        switch (shape)
        {
            case Shape.Literal:
                return (v, pr.Apply("eqid", new Dictionary<string, string> { ["A"] = Bridge.Numeral(v) }));
            case Shape.Succ:
                {
                    if (Evaluate(a!, licensed, problems) is not (long x, Proof px))
                    {
                        return null;
                    }
                    // suc ⟦a⟧ = suc ⟦x⟧, which is ⟦x + 1⟧ as written.
                    Proof p = pr.Apply("ax-mp", S(("ph", $"{Translate(a!)} = {Bridge.Numeral(x)}"), ("ps", $"suc {Translate(a!)} = {Bridge.Numeral(x + 1)}")),
                        px, pr.Apply("suceq", S(("A", Translate(a!)!), ("B", Bridge.Numeral(x)))));
                    return (x + 1, p);
                }
            case Shape.Add:
                {
                    if (Evaluate(a!, licensed, problems) is not (long x, Proof px) || Evaluate(b!, licensed, problems) is not (long y, Proof py))
                    {
                        return null;
                    }
                    if (!licensed.Contains((x, y)))
                    {
                        problems.Add($"{x} + {y} is not a literal addition the kernel performed in this trace");
                        return null;
                    }
                    string ta = Translate(a!)!, tb = Translate(b!)!;
                    // ( ⟦a⟧ +o ⟦b⟧ ) = ( ⟦x⟧ +o ⟦y⟧ ) = ⟦x + y⟧
                    Proof cong = pr.Apply("oveq12i", S(("A", ta), ("B", Bridge.Numeral(x)), ("C", tb), ("D", Bridge.Numeral(y)), ("F", "+o")), px, py);
                    Proof sum = bridge.Add(x, y);
                    Proof p = pr.Apply("eqtri", S(("A", $"( {ta} +o {tb} )"), ("B", $"( {Bridge.Numeral(x)} +o {Bridge.Numeral(y)} )"), ("C", Bridge.Numeral(x + y))), cong, sum);
                    return (x + y, p);
                }
            default:
                problems.Add($"a term outside the Nat arithmetic table: {e}");
                return null;
        }
    }

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>
    /// The set.mm theorem for a Lean theorem `@Eq Nat lhs rhs`, or why there is none. The declaration's trace must
    /// already have replayed in full (the caller checks); here it supplies the licensed additions.
    /// </summary>
    public (Proof? Proof, string? Why) EmitEquation(ConstInfo thm, DeclTrace trace)
    {
        if (Ops.Spine(thm.Type, out List<Expr> args) is not Const eq || !ReferenceEquals(eq.Name, _eq) || args.Count != 3 || !IsNat(args[0]))
        {
            return (null, "not an equation between natural numbers");
        }
        if (Translate(args[1]) is null || Translate(args[2]) is null)
        {
            return (null, "a side is outside the Nat arithmetic table");
        }
        // The additions the kernel performed: NatLitOp steps of Nat.add on two values that reduce to literals.
        var licensed = new HashSet<(long, long)>();
        foreach (Step s in trace.Steps.Where(s => s.Kind == StepKind.Rule && s.Rule == "NatLitOp"))
        {
            if (Ops.Spine(s.A, out List<Expr> xs) is Const add && ReferenceEquals(add.Name, _natAdd) && xs.Count == 2
                && Classify(xs[0]) is (Shape.Literal, long x, _, _) && Classify(xs[1]) is (Shape.Literal, long y, _, _)
                && s.B is NatLit r && r.Value == x + y)
            {
                licensed.Add((x, y));
            }
        }
        var problems = new List<string>();
        if (Evaluate(args[1], licensed, problems) is not (long l, Proof pl) || Evaluate(args[2], licensed, problems) is not (long r2, Proof pr2))
        {
            return (null, string.Join("; ", problems));
        }
        if (l != r2)
        {
            return (null, $"the sides evaluate to {l} and {r2}");
        }
        string L = Translate(args[1])!, R = Translate(args[2])!;
        Proof proof = pr.Apply("eqtr4i", S(("A", L), ("B", Bridge.Numeral(l)), ("C", R)), pl, pr2);
        return (proof, null);
    }
}
