# Fixtures

The `.ndjson` exports are copied from Tenet's test fixtures (github.com/keithadler/tenet, `tests/fixtures`), which say how each was made, except `quot.ndjson`, `syntax.ndjson`, `gate.ndjson`, `lenapp.ndjson`, `tree.ndjson`, `mutual.ndjson`, `strings.ndjson`, `axioms.ndjson` and `quotthm.ndjson`, made here with [leanout](https://github.com/keithadler/leanout):

| Export | Lean | Format |
|---|---|---|
| `Nat.add_succ.ndjson` | 4.34.0-rc2 | lean4export 3.1.0 |
| `Nat.add_succ.v3.0.ndjson` | 4.27.0-rc1 | lean4export 3.0.0 |
| `eta437.ndjson` | 4.37.0-rc1 | lean4export 3.1.0 |
| `acc436.ndjson` | 4.36.0 | lean4export 3.1.0 |
| `quot.ndjson` | 4.36.0 | leanout (`leanout Init -- Quot.sound`): the quotient block, Eq and Quot.sound |
| `gate.ndjson` | 4.36.0 | `Gate.lean` (here), compiled with `lean -o Gate.olean Gate.lean` and exported with `leanout Gate -- two_add_two`: the milestone 2 gate theorem `2 + 2 = 4` and its 22 dependencies |
| `lenapp.ndjson` | 4.36.0 | leanout (`leanout Init -- List.length_append`): `List.length_append` and its 59 dependencies, 12 of them theorems |
| `tree.ndjson` | 4.36.0 | `Tree.lean` (here), compiled with `lean -o Tree.olean Tree.lean` and exported with `leanout Tree -- Tree.rec`: a binary tree, whose `node` has two recursive fields |
| `strings.ndjson` | 4.36.0 | leanout (`leanout Init -- Lean.origin String.instInhabited instToStringBool`): definitions with string literals, and `String.ofList`, `Char.ofNat` and what they use |
| `axioms.ndjson` | 4.36.0 | leanout (`leanout Init -- Quot.lift Quot.ind propext Classical.choice Classical.choose Classical.propDecidable`): the quotient block, Init's two axioms, and definitions that use choice |
| `quotthm.ndjson` | 4.36.0 | leanout (`leanout Init -- Quot.inductionOn Quot.exists_rep Quot.liftBeta Quot.indBeta Quot.liftOn`): theorems about the quotient, for `tenet-zfc theorem` in the tower |
| `mutual.ndjson` | 4.36.0 | `Mutual.lean` (here), compiled with `lean -o Mutual.olean Mutual.lean` and exported with `leanout Mutual -- Tm.rec Args.rec Rose.rec Rose.rec_1`: a mutual block (`Tm`, `Args`) and a nested type (`Rose`, holding a `List (Rose α)`) |
| `syntax.ndjson` | 4.36.0 | leanout (`leanout Init -- Lean.Syntax`): the nested inductive `Lean.Syntax` (it holds an `Array Syntax`) with its 272 dependencies; the same file as Tenet's `tests/fixtures/nested/Lean.Syntax.ndjson` |
| `setvars.ndjson` | 4.36.0 | leanout (`leanout Init -- Lean.Grind.Config.casesOn Lean.Meta.Simp.Config.zeta`): two definitions that need more set variables than set.mm's 26 letters |
| `natadd.ndjson` | 4.36.0 | leanout (`leanout Init -- Nat.add`): `Nat.add` with `Nat`, `Nat.below`, `Nat.brecOn` and its other dependencies, for `tenet-zfc nat-bridge` |
| `theorems.ndjson` | 4.36.0 | leanout (`leanout Init -- Nat.add_zero Nat.zero_add Nat.succ_add List.length_append`): the first theorems proved through the model, for `tenet-zfc theorem` |
| `library.ndjson` | 4.36.0 | leanout (`leanout Init -- Nat.add_zero Nat.zero_add Nat.succ_add Nat.add_succ Nat.add_one Nat.succ_eq_add_one Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.add_right_comm Nat.succ_ne_zero Nat.mul_zero Nat.mul_succ Nat.zero_mul Nat.pred_succ Nat.pred_zero Nat.sub_zero Nat.succ_sub_succ Nat.le_refl List.length_nil List.length_cons List.append_nil List.nil_append List.cons_append List.append_assoc List.length_append List.map_nil List.map_cons List.length_map List.reverse_nil`): the starter library of theorems through the model (docs/milestone3.md) |

Each `.trace.ndjson` was made from the export beside it by Tenet's main branch (commit `125fd3d` or later), which records checking-mode inference as `Check` and recalls earlier conclusions with `"of"`:

```bash
tenet check Nat.add_succ.ndjson --trace Nat.add_succ.trace.ndjson
```

Regenerate them when the trace format changes.

`Example.lean` has no committed export: it is the README's worked example, and CI's `run-example` job compiles, exports, traces, translates and verifies it from source with `tenet-zfc run tests/fixtures/Example.lean`.
