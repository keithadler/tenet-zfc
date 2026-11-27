# Examples

## `Primes.lean`: the candidate headline theorem

The infinitude of primes (Euclid), in core Lean with no mathlib:

```lean
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

theorem infinitude_of_primes (n : Nat) : ∃ p, n < p ∧ Prime p
```

It is the candidate for milestone 5 because `set.mm` proves the same fact independently (`infpn`), with a statement of the same shape, so the translated theorem can meet a hand-written one, as `List.length_append` meets `ccatlen`.

**Written for the translator.** Core's `Nat` and `∣` only; structural recursion (the prime-factor lemma inducts on a bound instead of using well-founded recursion); proofs as plain terms with `induction`, `cases` and `rw`, and no `omega`, `decide` or `simp`. Classical reasoning is `Classical.em` alone: core's `Classical.not_forall` and `Classical.not_imp` go through `Decidable` instances built from `Classical.choice`, which is choice used as data, so the two facts needed are proved in the file from the excluded middle (`not_forall`, `not_imp`). Lean 4.36 accepts it, on the axioms `propext`, `Classical.choice` and `Quot.sound`; the translator proves `Classical.em`'s statement in the model directly, where a proposition is a member of `2o`.

**Its dependency cone**, exported with `leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes`:

| | count |
|---|---|
| definitions | 169, all of which `model-survey` translates together with everything they use |
| theorems | 146 |
| inductive types | 28 |
| axioms | 3 |

**Not done yet:**

- No theorem of the cone has been proved through the model yet. The workflow `.github/workflows/headline.yml` runs `tenet-zfc run examples/Primes.lean` on GitHub's runners and reports each theorem as proved, refused or failed in its summary. The definitions translating says nothing about how many of the 146 proofs go through.
- The bridges the restatement needs don't exist: `Nat.mul` to `x.`, `<` and `≤` to `set.mm`'s, `∣` to `||`, and `Prime` to the statement in `infpn`.
- Plain ZFC: the result would still carry the universe hypothesis until `--lowered` covers `theorem`.

To reproduce the export and the survey:

```
lean -o Primes.olean examples/Primes.lean
LEAN_PATH=. leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes
tenet-zfc model-survey primes.ndjson
```
