/-
The infinitude of primes, in core Lean with no mathlib: the candidate headline theorem for tenet-zfc.

Written for the translator. Everything is stated over `Nat` with core's `∣`, the recursion is structural, and the
proofs are plain terms and `induction`/`cases`: no `omega`, `decide` or `simp`, so the proof terms stay small and
cite only a few of core's lemmas. `Prime` has the shape of the statement in set.mm's own `infpn`.

Classical reasoning is `Classical.em` alone. Core's `Classical.not_forall` and `Classical.not_imp` go through
`Decidable` instances built from `Classical.choice`, which is choice used as data; the two facts needed are proved
here from the excluded middle instead (`not_forall`, `not_imp`).
-/
namespace Headline

/-- `p` is prime: at least 2, and divisible only by 1 and itself. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- The factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

/-- If not every number has `P`, some number doesn't: from the excluded middle alone. -/
theorem not_forall {P : Nat → Prop} (h : ¬ ∀ m, P m) : ∃ m, ¬ P m :=
  (Classical.em (∃ m, ¬ P m)).elim id
    (fun hne => absurd (fun m => (Classical.em (P m)).elim id (fun hn => absurd ⟨m, hn⟩ hne)) h)

/-- If `a` doesn't imply `b`, then `a` holds and `b` doesn't: from the excluded middle alone. -/
theorem not_imp {a b : Prop} (h : ¬ (a → b)) : a ∧ ¬ b :=
  ⟨(Classical.em a).elim id (fun na => absurd (fun ha => absurd ha na) h), fun hb => h (fun _ => hb)⟩

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

/-- Every positive number up to `n` divides `n!`. -/
theorem dvd_fact (n : Nat) : ∀ m : Nat, 0 < m → m ≤ n → m ∣ fact n := by
  induction n with
  | zero => exact fun m hm h => absurd hm (Nat.not_lt.mpr h)
  | succ n ih =>
    intro m hm h
    rw [fact_succ]
    cases Nat.lt_or_eq_of_le h with
    | inl hlt => exact Nat.dvd_trans (ih m hm (Nat.le_of_lt_succ hlt)) (Nat.dvd_mul_left (fact n) (n + 1))
    | inr heq => rw [heq]; exact Nat.dvd_mul_right (n + 1) (fact n)

/-- Every number from 2 up has a prime factor. Induction on a bound `k`, so the recursion is structural. -/
theorem exists_prime_factor_le (k : Nat) : ∀ n : Nat, n ≤ k → 2 ≤ n → ∃ p, Prime p ∧ p ∣ n := by
  induction k with
  | zero => exact fun n hn h2 => absurd (Nat.le_trans h2 hn) (Nat.not_succ_le_zero 1)
  | succ k ih =>
    intro n hn h2
    cases Classical.em (Prime n) with
    | inl hp => exact ⟨n, hp, Nat.dvd_refl n⟩
    | inr hnp =>
      have hnot : ¬ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n := fun h => hnp ⟨h2, h⟩
      cases not_forall hnot with
      | intro m hm =>
        have hmn : m ∣ n ∧ ¬ (m = 1 ∨ m = n) := not_imp hm
        have npos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) h2
        have hlt : m < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd npos hmn.1) (fun e => hmn.2 (Or.inr e))
        have hm2 : 2 ≤ m :=
          match m, hmn with
          | 0, h => absurd (Nat.eq_zero_of_zero_dvd h.1) (Nat.ne_of_gt npos)
          | 1, h => absurd (Or.inl rfl) h.2
          | m + 2, _ => Nat.le_add_left 2 m
        cases ih m (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hn)) hm2 with
        | intro p hp => exact ⟨p, hp.1, Nat.dvd_trans hp.2 hmn.1⟩

theorem exists_prime_factor (n : Nat) (h2 : 2 ≤ n) : ∃ p, Prime p ∧ p ∣ n :=
  exists_prime_factor_le n n (Nat.le_refl n) h2

/-- **The infinitude of primes** (Euclid): above every number there is a prime. -/
theorem infinitude_of_primes (n : Nat) : ∃ p, n < p ∧ Prime p := by
  cases exists_prime_factor (fact n + 1) (Nat.succ_le_succ (fact_pos n)) with
  | intro p hp =>
    refine ⟨p, Nat.lt_of_not_le (fun hle => ?_), hp.1⟩
    have ppos : 0 < p := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hp.1.1
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_fact n p ppos hle)).mp hp.2
    exact Nat.not_succ_le_self 1 (Nat.le_trans hp.1.1 (Nat.le_of_dvd Nat.zero_lt_one h1))

end Headline
