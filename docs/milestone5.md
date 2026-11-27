# Milestone 5: toward the headline theorem (the map)

The candidate is the infinitude of primes, in core Lean with no mathlib: [examples/Primes.lean](../examples/Primes.lean), `theorem infinitude_of_primes (n : Nat) : ∃ p, n < p ∧ Prime p`. set.mm proves the same fact by hand (`infpn`), so a translated proof can be checked against an independent one, as `List.length_append` is checked against `ccatlen` ([demo.md](demo.md)).

This document measures what the translator does with the theorem's cone today, lists what is missing, and estimates the work. It is a map, not the finished proof.

## The cone

`leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes` (Lean 4.36.0) exports 169 definitions, 146 theorems, 28 inductive types and 3 axioms (`propext`, `Classical.choice`, `Quot.sound`). All 169 definitions translate ([examples/README.md](../examples/README.md)).

## Theorems through the model, measured

`tenet-zfc theorem-all primes.ndjson set.mm out --chunk-size 10`, one process per chunk, two at a time, budget 120 s; every chunk then checked by `scripts/verify-all` (metamath-exe, mmverify.py, mmj2's `definitionCheck`).

| Build | Proved, of 146 | Chunks passing all three checkers |
|---|---|---|
| `main` (first run, 27 November) | none of the headline lemmas; the main theorem refused at `Exists.rec` | |
| keithadler/tenet-zfc#20: literals, `Decidable`, `Nat.le`'s constructors, `$d` fixes | 81 | |
| … and eliminating `Exists` | 86 | 15 of 15 |
| … and induction on `Nat.le` | **114 (78%)** | **15 of 15** |

The five theorems of `Primes.lean` itself:

| Theorem | Status | What stops it |
|---|---|---|
| `fact_pos` | **proved** (131 lemmas) | |
| `dvd_fact` | refused | introducing an existential whose witness's variable occurs in the hypotheses (`rspcedvd`'s `$d`) |
| `exists_prime_factor_le` | refused | `Classical.choose`, through `Classical.propDecidable`: the file decides primality by the excluded middle |
| `exists_prime_factor` | refused | the same, and the lemma above |
| `infinitude_of_primes` | refused | the same, and the lemmas above |

**All 32 not proved** (the four headline theorems above included), by reason:

| Reason | Theorems |
|---|---|
| A conversion between two Π-propositions that the translator can't show (`can't show if ( A. z e. ( lean.Nat ` U ) …`); e.g. `Nat.le_of_dvd`, `Nat.dvd_add`, `Nat.sub_eq_zero_of_le`, `Nat.mul_sub_left_distrib` | 10 |
| Depends on `Classical.choice` (`Classical.choose`, `Classical.propDecidable`) | 8 |
| An existential introduced with a witness whose variable occurs in the hypotheses | 6 |
| Over the time budget (type inference, `Congruence`, `RenameProof`) | 4 |
| "can't infer a type: applying something that isn't a function" | 3 |
| `( y ` (/) )` not shown to be in the universe | 1 |

## The gap list

What stands between the cone and a proof of `infinitude_of_primes` in set.mm's own vocabulary, in plain ZFC:

1. **Choice in theorems.** `Classical.choice` is in the tower model (a well-ordering of the tower's union, [milestone3.md](milestone3.md#quotients-and-choice-in-the-tower-built)), but the theorem translator refuses theorems that go through it. The cone needs `Classical.propDecidable`, so `Decidable p` for any `p`, and `Classical.choose`. This blocks the three headline theorems that remain after `dvd_fact`, so it is the main gap. Another option: write `Primes.lean` with a decidable `Prime`, which core's `Nat.decEq` and bounded quantifiers allow.
2. **Existential introduction, the `$d` trap.** `Exists.intro` at a witness whose variable is also in the hypotheses (`rspcedvd` needs them distinct). The fix is the renaming used elsewhere: rename the bound variable apart first. It blocks `dvd_fact` and 6 others.
3. **Conversions between Π-propositions** (10 theorems): definitional unfolding under a binder whose body is a proposition, where the two sides' texts differ by more than alpha-equivalence.
4. **Bridges**, so that the statement lands in set.mm's terms ([bridges.md](bridges.md)):
   - `Nat.mul` to `x.`: done in keithadler/tenet-zfc#21.
   - `Nat.le` and `Nat.lt` to `<_` and `<` on `NN0`. The model's `Nat.le` is now typed and has induction (#20). The bridge is induction over its stages one way, and `B = A + k` the other.
   - `∣` (`Nat.instDvdNat`, `∃ c, b = a * c`) to set.mm's `||`.
   - `Prime` to set.mm's statement. `infpn` reads `( N e. NN -> E. j e. NN ( N < j /\ A. k e. NN ( ( j / k ) e. NN -> ( k = 1 \/ k = j ) ) ) )`. Lean's version quantifies over `NN0`, uses `∣` and has `2 ≤ p`. A cross-check theorem in set.mm proves the two statements equivalent, as `lean-nat-2p2e4-iff` does for addition.
   - `fact` is used only inside the proof, not in the statement, so it needs no bridge.
5. **Plain ZFC.** `--lowered` covers `nat-bridge` today ([milestone4.md](milestone4.md)), not `theorem`. Until it does, the result holds under the universe hypothesis `U e. lean.-tower` (tasks2.md, task 3).

## Estimate

| Item | Work | Confidence |
|---|---|---|
| Existential introduction's `$d` | hours: the renaming pattern exists | high |
| Conversions under Π-propositions | a day or two, one case at a time | medium |
| Choice in theorems, or a decidable `Prime` in `Primes.lean` | 2–4 days for choice; under a day to rewrite the file | medium; low for choice |
| Bridges: `≤`/`<`, `∣`, `Prime`, and the `infpn` cross-check | 3–5 days | medium |
| `--lowered` for `theorem` | depends on task 3: the reflection schema for unions over type families | low |

With the file rewritten to avoid choice, the main theorem through the model (under the tower hypothesis) is about a week of work. Restated in set.mm's vocabulary and cross-checked against `infpn`, about two weeks. Plain ZFC waits on milestone 4.

## To reproduce

```
lean -o Primes.olean examples/Primes.lean
LEAN_PATH=. leanout Primes -o primes.ndjson -- Headline.infinitude_of_primes
tenet-zfc theorem-all primes.ndjson set.mm out --chunk-size 10 --budget 120
scripts/verify-all -j 2 out && scripts/summarize-all out
```
