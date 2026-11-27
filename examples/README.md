# Examples

## `Primes.lean`: the candidate headline theorem

The infinitude of primes (Euclid), in core Lean with no mathlib:

```lean
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

theorem infinitude_of_primes (n : Nat) : ∃ p, n < p ∧ Prime p
```

It is the candidate for milestone 5 because `set.mm` proves the same fact independently (`infpn`), with a statement of the same shape, so the translated theorem can meet a hand-written one, as `List.length_append` meets `ccatlen`.

**Written for the translator.** Core's `Nat` and `∣` only; structural recursion (the prime-factor lemma inducts on a bound instead of using well-founded recursion); proofs as plain terms with `induction` and `cases`, and no `omega`, `decide` or `simp`. Lean 4.36 accepts it, on the axioms `propext`, `Classical.choice` and `Quot.sound`: the excluded middle decides whether a number is prime, and the rest come from core's lemmas.

**Its dependency cone**, exported with `leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes`:

| | count |
|---|---|
| definitions | 169, all of which `model-survey` translates together with everything they use |
| theorems | 146 |
| inductive types | 28 |
| axioms | 3 |

**Not done yet:**

- No theorem of the cone has been run through `tenet-zfc theorem`. The definitions translating says nothing about how many of the 146 proofs go through.
- The bridges the restatement needs don't exist: `Nat.mul` to `x.`, `<` and `≤` to `set.mm`'s, `∣` to `||`, and `Prime` to the statement in `infpn`.
- Plain ZFC: the result would still carry the universe hypothesis until `--lowered` covers `theorem`.

To reproduce the export and the survey:

```
lean -o Primes.olean examples/Primes.lean
LEAN_PATH=. leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes
tenet-zfc model-survey primes.ndjson
```
