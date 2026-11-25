# Milestone 3: from a definition table to the whole kernel

Milestone 3's gate is that all of Lean core translates and verifies. This document measures how far the milestone 2 translator is from that, and says what has to change. Nothing below the survey is built yet.

## The survey

`tenet-zfc survey <export>` runs the statement translator on every theorem in an export. It reports why each refused statement was refused, and ranks the constants outside the table by how many theorems mention them. On `Init` from Lean 4.36.0 (exported by leanout):

| | Theorems |
|---|---|
| In `Init` | 45,588 |
| Statement translated by the milestone 2 table | 119 |
| Refused: a constant outside the table | 35,943 |
| Refused: a bound variable or λ applied to arguments | 7,520 |
| Refused: a proposition form outside the table (∧, ∨, ¬, ↔, ∃, ∀ over a dependent type, a predicate) | 2,006 |

The most common constants outside the table are `<` and `≤` on `Nat`, `Bool`, `Int`, `Not`, `Iff`, `Array`, `False`, subtraction, `Option`, `BitVec` and `String.Slice`.

Adding constants to the table in that order, one at a time, covers this many theorems:

| Constants added | Statements covered | Statements and proofs covered |
|---|---|---|
| 0 | 309 | 7 |
| 100 | 5,660 | 21 |
| 1,000 | 24,165 | 1,457 |
| 5,000 | 43,049 | 6,996 |
| all 37,118 | 45,588 | 45,588 |

("Covered" here means only that every constant has an entry. It's an upper bound on what would translate.)

## What this means

**The hand table can't reach the gate.** Proofs use far more constants than statements do. Even with 5,000 hand-written entries, only 6,996 theorems would have every constant in their proof translated, out of 45,588. Each entry is a claim that someone checks by hand, so tens of thousands of entries would also defeat the point of the spec's trust story ("a small, hand-checked table").

**So the translation must be generic.** Every Lean definition, inductive type and recursor gets its set-theoretic meaning computed from its own definition, following Carneiro's model, rather than looked up. That is how the spec's feature table already reads ("each Lean feature has a fixed set-theoretic meaning"); milestone 2 took the shallow shortcut because two theorems didn't need more.

**The table stays, with a different job.** An entry like `Nat.add ↦ +` becomes a proved theorem in the output, `|- ⟦Nat.add⟧ = ( x e. NN0 , y e. NN0 |-> ( x + y ) )`, rather than an assumption. Headline statements are then restated in `set.mm`'s own vocabulary through those theorems, and `set.mm`'s own versions are cross-checked against them, as `ccatlen` was. The trusted part shrinks to the definitions of the model itself.

## Design

1. **The model, once.** A `set.mm` section (written once, checked by both verifiers) that interprets the kernel's type theory:
   - `Prop` as `2o`, proofs as `(/)`;
   - Π-types as `X_` and λ as maps-to;
   - universes as `( R1 ` A )` for a limit ordinal `A` fixed per output, with the reflection argument of milestone 4 deciding `A`.
   This is the bridge library the spec's milestone 2 described in general.
2. **Inductive types as least fixed points.** Each inductive block becomes the least set closed under its constructors, built by `set.mm`'s well-founded recursion (`df-recs`/`df-rdg`). Its recursor becomes the function defined by recursion on that set, and its computation rules (the replayer's iota steps) become theorems about it. Nested and mutual blocks go through the same reduction the replayer already uses (`Nested.cs`).
3. **Definitions as definitions.** Each Lean definition `c := v` becomes a `set.mm` definition `df-lean.c $a |- lean.c = ⟦v⟧`. Unfolding a definition everywhere it is used instead would blow the output up exponentially; that is the spec's "sharing" requirement.
4. **Proofs from the trace.** Each replayed step becomes one `set.mm` step:
   - reductions and definitional equalities become equalities of interpretations, by the model's beta, delta, iota, eta and proof-irrelevance lemmas;
   - typing judgments become membership facts.
   The milestone 2 proof translator becomes the special case where every constant had a table entry.
5. **Quotients and choice.**
   - `Quot` becomes the set of equivalence classes of the smallest equivalence relation containing the given relation.
   - `Classical.choice` becomes a fixed global choice function from `set.mm`'s axiom of choice.
   Both are theorems about the model, proved once.

## The decision this needs

**Step 3 changes the output's trust story.** Milestone 2's outputs add only `$p` theorems to `set.mm`. Interpretation.md says no new definitions "until a definition checker is part of the pipeline".

Generic translation needs that checker. A definition `$a` is safe only if it is conservative: a new constant, defined once, not circular, with no free variables on the right. `set.mm` checks its own `df-` axioms this way in CI, with mmj2's `definitionCheck` macro (by Mario Carneiro).

The plan is therefore to add a third check to the pipeline: every `$a` the translator writes must pass a definition checker. It should be one the translator doesn't share code with. The candidates are mmj2's `definitionCheck`, which `set.mm` already trusts, or a small independent checker for the restricted form the translator writes: `df-lean.c $a |- lean.c = <class term over earlier constants> $.`

## Order of work

1. The model section, with its beta, Π, λ and application lemmas. Gate: `id`, `Function.comp` and `Function.const`, with their definitional equations, verify.
2. Definitions with the definition checker in CI. Gate: every non-recursive definition in `Init.Prelude` translates.
3. Inductive types and recursors. Gate: `Nat`, `Bool`, `List`, `Option` and `Prod` with their iota rules; then all inductive blocks in `Init`.
4. Proofs from traces, generically. Gate: `List.length_append` again, now through `lean.List.length` and a proved `⟦List.length⟧ = #` bridge instead of the table.
5. Quotients, choice, literals and `String`. Gate: the milestone's own, all of `Init`.

`survey` is rerun after each step and its counts recorded here.
