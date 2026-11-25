# Rule map: Tenet's kernel rules to bridge lemmas

Tenet already names every typing, reduction and definitional-equality rule of the Lean 4 kernel, one entry per rule, in [`src/Tenet.Kernel/Rules.cs`](https://github.com/keithadler/tenet/blob/main/src/Tenet.Kernel/Rules.cs) (the `Rule` enum), and calls `Rules.Hit(rule)` at the point each one fires. That catalog is the starting checklist for the bridge library: every rule that can fire needs at least one `set.mm` lemma saying it is sound under the set-theoretic interpretation.

Lemma names below are placeholders (`lean-` prefix, to stay clear of `set.mm`'s own labels). The milestone column says when each is needed; see [spec.md](spec.md#milestones).

⟦e⟧ is the interpretation of a Lean term as a set, as in the spec's Interpretation stage.

## Typing (Γ ⊢ e : T)

| Tenet rule | What the bridge lemma states in ZFC | Lemma | Milestone |
|---|---|---|---|
| `InferBVar` | Error path only; never appears in a successful trace | none | — |
| `InferFVar` | A variable in context is an element of its type's set | `lean-var` | 2 |
| `InferSort` | ⟦Sort u⟧ ∈ ⟦Sort (u+1)⟧ | `lean-sort` | 2 |
| `InferConst` | A declared constant, instantiated at its levels, is in its type's set | `lean-const` | 2 |
| `InferApp` | f ∈ Π, a ∈ A ⇒ f(a) ∈ B[a] | `lean-app` | 2 |
| `InferLam` | The function x ↦ ⟦b⟧ is in the Π set | `lean-lam` | 2 |
| `InferPi` | The Π set lies in ⟦Sort (imax u v)⟧ (impredicative case when v is Prop) | `lean-pi`, `lean-pi-prop` | 2 |
| `InferLet` | Typing a `let` is typing its body with the value substituted | `lean-let` | 2 |
| `InferProj` | The i-th field of a structure element is in the i-th field's set | `lean-proj-type` | 3 |
| `InferLit` | Nat literals are in ω; string literals are in ⟦String⟧ | `lean-natlit`, `lean-strlit` | 2 / 3 |

## Reduction (e ↝ e', proved as ⟦e⟧ = ⟦e'⟧)

| Tenet rule | What the bridge lemma states in ZFC | Lemma | Milestone |
|---|---|---|---|
| `Beta` | Applying x ↦ b to a gives b[x := a] | `lean-beta` | 2 |
| `Zeta` | ⟦let x := v; b⟧ = ⟦b[x := v]⟧ | `lean-zeta` | 2 |
| `ZetaFVar` | A let-bound local equals its value | `lean-zeta-fvar` | 2 |
| `Delta`, `DeltaLazy` | A definition's constant equals its interpreted value (one lemma per unfolded definition, emitted, not hand-written) | `def-<name>` | 2 |
| `Iota` | The recursor's value on a constructor is its minor premise (per inductive, from the fixed-point construction) | `lean-iota` + per-inductive | 2 (simple), 3 (mutual/nested) |
| `IotaK` | K-like reduction: the single fieldless constructor stands in for any proof of the proposition | `lean-iota-k` | 3 |
| `Proj` | (S.mk ā).i = aᵢ | `lean-proj` | 3 |
| `QuotLift` | Lifting f over the class of a gives f(a) | `lean-quot-lift` | 3 |
| `QuotInd` | Quotient induction on the class of a | `lean-quot-ind` | 3 |
| `NatLitOp` | add, sub, mul, div, mod, pow, gcd, bitwise on ω agree with the computed literal | `lean-nat-<op>` via the decimal library | 2 (add, mul), 3 (rest) |
| `NatLitPred` | decEq, beq, ble on ω agree with the computed Bool | `lean-nat-<pred>` | 2 |
| `StringLitToCtor` | A string literal equals its constructor form over a list of characters | `lean-str-ctor` | 3 |
| `NativeReduce` | Tenet refuses `Lean.reduceBool` / `Lean.reduceNat`; reaching it is a rejection, so it never appears in a trace (spec non-goal) | none | — |

## Definitional equality (t ≡ s, proved as ⟦t⟧ = ⟦s⟧)

| Tenet rule | What the bridge lemma states in ZFC | Lemma | Milestone |
|---|---|---|---|
| `DefEqSyntactic` | Equality is reflexive (binder names and annotations are not part of ⟦·⟧) | `eqid` (already in `set.mm`) | 2 |
| `DefEqSort` | Equivalent levels give the same universe set | `lean-sort-eq` + level normalization lemmas | 2 |
| `DefEqConst` | Pointwise-equivalent level lists give the same constant | `lean-const-eq` | 2 |
| `DefEqApp` | Congruence of application | `lean-app-cong` | 2 |
| `DefEqBinding` | Congruence under a binder (Π and λ) | `lean-pi-cong`, `lean-lam-cong` | 2 |
| `DefEqEta` | f = (x ↦ f(x)) for f a set-theoretic function on the domain | `lean-eta` | 2 |
| `DefEqEtaStruct` | s = S.mk s.1 … s.n | `lean-eta-struct` | 3 |
| `DefEqUnitLike` | Any two elements of a one-element set are equal | `lean-unit-like` | 3 |
| `DefEqProofIrrel` | Every proof is ∅, so any two proofs of p are equal | `lean-proof-irrel` | 2 |
| `DefEqStringLit` | Unreachable on current Lean (Tenet's own note); keep the lemma for older exports | `lean-str-eq` | 3 |
| `DefEqFVar` | Subsumed by `DefEqSyntactic` (Tenet's `Rules.SubsumedBy`) | none | — |
| `DefEqReflect` | A closed term reduced fully to `Bool.true` (proofs by reflection; usually the biggest traces) | chain of reduction lemmas | 3 |
| `DefEqLazyDeltaProj` | Two projections of one field are equal once their structures are unfolded | `lean-proj-cong` | 3 |
| `UnfoldProjApp` | A projection function applied to arguments unfolds to the projection | `lean-proj-app` | 3 |
| `DefEqOffset` | n + k = m + k' by arithmetic on ω | `lean-nat-offset` | 2 |
| `DefEqLazyDelta` | Not a lemma of its own: a strategy. The trace records which side was unfolded, and each unfolding is a `Delta` step | via `def-<name>` | 2 |

## Not in the enum

Some steps the translator needs are not kernel rules Tenet counts today:

- **Level normalization.** `DefEqSort` and `DefEqConst` rest on Tenet deciding two universe levels equal. The trace has to record enough to replay that decision, or the interpretation has to be invariant under it (it is, once all levels are instantiated to numerals at universe elimination).
- **Inductive declarations.** Checking an inductive block (positivity, universe constraints, recursor derivation in `Inductive.cs`) is what licenses the fixed-point construction. It is checked once per inductive, not per use, so it becomes one emitted lemma per inductive type.
- **The three axioms.** `propext`, `Quot.sound` and `Classical.choice` appear as constants, so they arrive through `InferConst`; each needs a one-off proof that its interpretation holds (see the spec's feature table).

## Coverage

Tenet can print per-rule hit counts after a run (`Rules.All()`, with `TypeChecker.Stats.Enabled`). Running it on the milestone 2 gate theorems gives the exact list of lemmas milestone 2 has to supply, before writing any of them.
