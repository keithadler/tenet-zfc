/-
Function extensionality. Lean proves funext through the quotient (Quot.sound, Quot.liftOn); in the model functions
are ZFC functions, and the translator proves funext's statement directly (docs/milestone3.md).
Export: leanout Funext -o funext.ndjson -- add_zero_fn const_fn (Lean 4.36.0).
-/
theorem add_zero_fn (f : Nat → Nat) : (fun x => f x + 0) = f :=
  funext (fun x => Nat.add_zero (f x))

theorem const_fn (a : Nat) : (fun (_ : Nat) => a + 0) = (fun _ => a) :=
  funext (fun _ => Nat.add_zero a)
