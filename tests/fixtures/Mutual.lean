/-
A mutual block and a nested type, for the model's mutual and nested inductives (docs/milestone3.md, step 3).
`Tm` and `Args` are defined together; `Rose` holds a `List (Rose α)`, which the kernel reduces to an auxiliary
mutual block.
Compiled with `lean -o Mutual.olean Mutual.lean` under Lean 4.36.0 and exported with
`leanout Mutual -- Tm.rec Args.rec Rose.rec Rose.rec_1`.
-/
mutual
  inductive Tm (α : Type u) where
    | var : α → Tm α
    | app : Tm α → Args α → Tm α
  inductive Args (α : Type u) where
    | nil : Args α
    | cons : Tm α → Args α → Args α
end

inductive Rose (α : Type u) where
  | node : α → List (Rose α) → Rose α
