/-
A type the kernel reduces silently, which the translator has to reduce too: Nat.noConfusion's type at two successors
is a function type only after Nat.rec's computation rule, and under a lambda that type has to be inferred.
Export: leanout Iota -o iota.ndjson -- succ_inj_lam (Lean 4.36.0).
-/
theorem succ_inj_lam (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b :=
  (fun (k : Nat.succ a = Nat.succ b) => Nat.noConfusion k (fun h' => h')) h
