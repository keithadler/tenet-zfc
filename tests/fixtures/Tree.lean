/-
A binary tree: `node` has two recursive fields, so its recursor's computation rule needs both subtrees in one stage
of the type's ω-chain (docs/milestone3.md, step 3).
Compiled with `lean -o Tree.olean Tree.lean` under Lean 4.36.0 and exported with `leanout Tree -- Tree.rec`.
-/
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
