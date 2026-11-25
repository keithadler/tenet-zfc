# Trace format (milestone 1)

Milestone 1 adds tracing to Tenet: every step Tenet takes while accepting a declaration is written to a file that can later be replayed without Tenet's search. Recording is on Tenet's main branch, not yet in a release. Replay of single-rule steps is in this repository (see [Replay](#replay)). The milestone 1 gate isn't met yet.

```
tenet check Foo.ndjson --trace Foo.trace.ndjson
```

`--trace` works on export files. It checks declarations one at a time, in order, and bypasses the kernel's caches, so it is much slower than a normal check. Without `--trace`, Tenet behaves exactly as before.

## How it hooks in

- `KernelTrace` (in `Tenet.Kernel`) holds the steps of one declaration. `KernelTrace.Scope` attaches one to the current thread.
- A `TypeChecker` created while a scope is open records into it. It also skips its inference, normalization and success caches, because a cache hit would skip the steps that justify the result. A checker created with no scope open records nothing and pays one null check per step.
- Code that has no checker at hand (`Inductive.cs` for iota, `Quot.cs` for quotient reduction, `LocalContext` for new variables) records through the thread's current trace.
- Every place Tenet already calls `Rules.Hit(rule)` on a successful path also records a step that carries the terms involved.

## Only the successful derivation is kept

Definitional equality backtracks: lazy delta, proof irrelevance and eta are tried and abandoned. Each `IsDefEqCore` call takes a mark on entry. On success it records a `DefEq` conclusion over everything since the mark. On failure it rolls back to the mark. Normalization does the same: a `Whnf` or `WhnfCore` call that changes nothing leaves no steps behind. If Tenet's fast mode rejects a declaration and re-checks it in faithful mode, the first attempt's steps are discarded too.

## Step kinds

| Kind | Meaning | Lhs / Rhs |
|---|---|---|
| `Rule` | One kernel rule fired; `r` names it (Tenet's `Rule` enum, see [rule-map.md](rule-map.md)) | the rule's two terms, such as redex and reduct |
| `Infer` | Γ ⊢ e : T | e, T |
| `WhnfCore` | e ↝* e' without unfolding definitions | e, e' |
| `Whnf` | e ↝* e' with unfolding and literal arithmetic | e, e' |
| `DefEq` | t ≡ s | t, s |
| `Local` | a free variable enters the context | the variable, its type (`v`: its value, for a `let`) |

Steps are stored in the order they finish, so premises always come before the step that uses them. Each step's premises are the steps from its `from` index up to the step itself. Its direct premises are found by walking back from the step before it, jumping to each premise's own `from`.

## File format

Newline-delimited JSON. Names, levels and expressions use the same shapes as lean4export, and each is written once for the whole file, the first time it is needed:

```
{"trace":"tenet","version":1}
{"in":1,"str":{"pre":0,"str":"Nat"}}                      name 1
{"il":0,"zero":true}                                       level 0
{"ie":7,"app":{"fn":5,"arg":6}}                            expression 7
{"decl":1,"steps":78}                                      a declaration, by name id, and its step count
{"s":0,"k":"Local","a":3,"b":2}                            step 0
{"s":5,"k":"Rule","r":"Beta","a":9,"b":11}                 step 5: expression 9 beta-reduces to 11
{"s":9,"k":"DefEq","a":4,"b":12,"from":0}                  step 9: 4 ≡ 12, premises are steps 0..8
```

Step numbers restart at 0 for each declaration. Free variables are written by their numeric id (`{"fvar":n}`), and each is introduced by a `Local` step before any step mentions it.

## Tested

Tenet's `TraceTests` cover all 16 export fixtures in its repository, including the negative corpus:

- Tracing never changes a verdict: the same declarations are accepted and rejected with and without it.
- There is one trace per accepted declaration and none for a rejected one.
- Every trace is closed: premises come first, and every free variable is introduced before it is used.
- A failed equality leaves no steps. A successful one ends in its own `DefEq` conclusion, whose derivation is the whole trace.
- The writer writes each expression once.

On `Nat.add_succ.ndjson` (20 declarations), the trace has 2,200 steps, and 13 of Tenet's rules fire.

## Not yet recorded

These gaps are for the replayer to settle:

- **Congruence is implicit.** When normalization rewrites the head of an application, or lazy delta unfolds one side, the trace records the inner step but not the congruence that lifts it to the whole term. The replayer has to supply it.
- **Literal ↔ constructor.** A Nat literal used as a recursor's major premise is turned into `Nat.succ` form with no step of its own. It shows up only in the iota step's terms.
- **Primitive checks.** Tenet checks once per environment that `Nat.add` and the rest are the primitives they claim to be. Those checks are cached on the environment, so they are recorded in whichever declaration first needs them, or not at all if that happened inside a branch that was rolled back.
- **Level equivalence.** `DefEqSort` and `DefEqConst` steps assert that two universe levels are equivalent without recording why. This stops mattering once universe elimination makes every level a numeral.
- **Inductive declarations.** Positivity, universe constraints and recursor derivation are checked but traced only as the inference and equality steps they use, not as one "this inductive is well formed" conclusion.

## Replay

```bash
tenet-zfc replay Foo.ndjson Foo.trace.ndjson
```

The replayer (`src/TenetZfc`) reads the export and the trace and re-derives each step from the definition of its rule. It shares no code with Tenet: it has its own terms, substitution, universe-level arithmetic and reduction rules. Each step is checked locally, using the export's declarations and the steps recorded before it.

Every step gets one of four verdicts:

| Verdict | Meaning |
|---|---|
| verified | The rule applies to the recorded terms and gives the recorded result |
| failed | It doesn't, or the step is malformed (for example, it uses a free variable no step introduced) |
| unsupported | A kind of step the replayer checks, in a case it doesn't handle yet |
| not yet replayed | A kind of step the replayer doesn't check yet |

Checked so far:

- **Reductions:** `Beta`, `Zeta`, `ZetaFVar`, `Delta`, `DeltaLazy`, `Proj`, `Iota`, `IotaK`, `QuotLift`, `QuotInd`, `UnfoldProjApp`.
- **Literal arithmetic:** `NatLitOp` and `NatLitPred`, recomputed with big integers.
- **Equality rules that need no premises:** `DefEqSyntactic`, `DefEqFVar`, `DefEqSort`, `DefEqConst` (universe levels are compared by case-splitting each parameter on zero or successor), and `DefEqOffset`.
- **Locals:** each must be fresh, and nothing may use a variable before its `Local` step.

Delta and iota substitute universe levels with Lean's simplifying `mk_max` and `mk_imax`, because the kernel's reduct carries the simplified level.

Not yet replayed: the `Infer`, `Whnf`, `WhnfCore` and `DefEq` conclusions, and the equality rules that rest on their premises (`DefEqApp`, `DefEqBinding`, `DefEqEta`, `DefEqEtaStruct`, `DefEqProofIrrel`, `DefEqUnitLike`, `DefEqLazyDelta`, `DefEqLazyDeltaProj`, `DefEqReflect`, `DefEqStringLit`). `StringLitToCtor` is reported as unsupported. The report never counts these as passed.

Two assumptions are made explicitly:
- **Nat operations** are taken to mean what their names say. Tenet checks that against their definitions once per environment, and that check isn't in the trace.
- **Rule K** is checked for the reduct only. The kernel also checks the major premise's type, which is a typing fact.

Results on the four committed fixtures (`tests/fixtures`):

| Export | Steps | Verified | Failed | Unsupported | Not yet |
|---|---|---|---|---|---|
| `Nat.add_succ` | 2,200 | 747 | 0 | 0 | 1,453 |
| `Nat.add_succ.v3.0` | 2,178 | 740 | 0 | 0 | 1,438 |
| `eta437` | 1,257 | 397 | 0 | 0 | 860 |
| `acc436` | 1,082 | 388 | 0 | 0 | 694 |

The tests also change the recorded result of each checked rule and require the replayer to fail that step. A replayer that accepted everything would pass the clean fixtures too, so the clean results mean little without these.

The milestone 1 gate (every step re-derived on all of Lean core) is not met. Two things are left: replaying the conclusions, and running on a full `Init` export. The replayer is also the template for the emitter: where replay checks a step, emission will print the `set.mm` proof step for it.
