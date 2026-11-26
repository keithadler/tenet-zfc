# Fixtures

The `.ndjson` exports are copied from Tenet's test fixtures (github.com/keithadler/tenet, `tests/fixtures`), which say how each was made, except `quot.ndjson`, `syntax.ndjson`, `gate.ndjson`, `lenapp.ndjson`, `tree.ndjson`, `mutual.ndjson`, `strings.ndjson` and `axioms.ndjson`, made here with [leanout](https://github.com/keithadler/leanout):

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
| `mutual.ndjson` | 4.36.0 | `Mutual.lean` (here), compiled with `lean -o Mutual.olean Mutual.lean` and exported with `leanout Mutual -- Tm.rec Args.rec Rose.rec Rose.rec_1`: a mutual block (`Tm`, `Args`) and a nested type (`Rose`, holding a `List (Rose α)`) |
| `syntax.ndjson` | 4.36.0 | leanout (`leanout Init -- Lean.Syntax`): the nested inductive `Lean.Syntax` (it holds an `Array Syntax`) with its 272 dependencies; the same file as Tenet's `tests/fixtures/nested/Lean.Syntax.ndjson` |
| `setvars.ndjson` | 4.36.0 | leanout (`leanout Init -- Lean.Grind.Config.casesOn Lean.Meta.Simp.Config.zeta`): two definitions that need more set variables than set.mm's 26 letters |

Each `.trace.ndjson` was made from the export beside it by Tenet's main branch (commit `125fd3d` or later), which records checking-mode inference as `Check` and recalls earlier conclusions with `"of"`:

```bash
tenet check Nat.add_succ.ndjson --trace Nat.add_succ.trace.ndjson
```

Regenerate them when the trace format changes.
