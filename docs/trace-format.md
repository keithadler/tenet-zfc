# Trace format (draft, milestone 1)

Milestone 1 adds tracing to Tenet: every step Tenet takes while checking a declaration is written to a certificate that can be replayed without Tenet's search. This file is the draft format. Nothing here is implemented yet.

## Where it hooks in

Tenet calls `Rules.Hit(Rule r)` at every place a kernel rule fires (about 40 call sites, almost all in `TypeChecker.cs`). Today that only increments a counter. Tracing widens the call to carry the terms involved:

```csharp
// in Tenet.Kernel (proposed)
public interface ITraceSink
{
    // e ↝ e'  or  t ≡ s  or  Γ ⊢ e : T, depending on the rule
    void Step(Rule rule, Expr lhs, Expr rhs, ReadOnlySpan<int> premises);
}
```

`Rules.Hit` stays as it is for counting. A traced run passes an `ITraceSink` to the `TypeChecker`; an untraced run passes none and pays one null check per step. This change belongs in Tenet itself, as a pull request there, so it ships with Tenet's own tests and CI.

## What a step records

Each step gets an integer id, in the order it was proved.

```
<id> <rule> <lhs-term-id> <rhs-term-id> [<premise-id> ...]
```

- `rule`: the `Rule` enum name, for example `Beta`, `DefEqProofIrrel`, `InferApp`.
- Terms are hash-consed: each distinct `Expr` is written once in a term table and referred to by id. That is what keeps the trace (and later the `set.mm` output) near linear rather than exponential; see the spec's Size and performance section.
- Premises are the ids of earlier steps this one depends on (for `DefEqApp`, the step for the heads and one per argument; for `InferApp`, the typing of `f`, the typing of `a`, and the domain equality).
- Failed branches are not recorded. Tenet's definitional-equality check tries things and backtracks (lazy delta, eta, proof irrelevance); the trace keeps only the derivation that succeeded.

Per declaration:

```
decl <name> <levels>
term <id> <expr>          # term table, lean4export-style expression encoding
step ...                  # the steps above
root <step-id>            # the step that proves the declaration's value has its declared type
```

## Replay (the milestone 1 gate)

A separate replayer, which does not call Tenet's search, reads a trace and checks each step locally: that the rule applies to the recorded terms, and that its premises are earlier steps proving what this step needs. The gate is that replay re-derives every check Tenet made on all of Lean core.

The replayer is also the template for the emitter: replay checks a step, emission prints the `set.mm` lemma application for it.

## Open points

- Lazy delta records each unfolding as a `Delta` step; does the replayer need the height heuristic, or only the unfoldings? (Only the unfoldings, if failed branches are dropped.)
- Level normalization for `DefEqSort` and `DefEqConst`: record it, or require universe elimination first so levels are numerals? See [rule-map.md](rule-map.md#not-in-the-enum).
- Nat literal arithmetic (`NatLitOp`): record the operands and result only, and leave the proof to the decimal-arithmetic library at emission.
