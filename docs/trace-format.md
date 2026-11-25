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
| `Infer` | Γ ⊢ e : T, computed in infer-only mode (the term is assumed well typed) | e, T |
| `Check` | Γ ⊢ e : T, computed in checking mode (argument types against domains, domains are types, levels use only declared parameters) | e, T |
| `WhnfCore` | e ↝* e' without unfolding definitions | e, e' |
| `Whnf` | e ↝* e' with unfolding and literal arithmetic | e, e' |
| `DefEq` | t ≡ s | t, s |
| `Local` | a free variable enters the context | the variable, its type (`v`: its value, for a `let`) |

A step may instead recall an earlier one. Tenet remembers each result by the step that concluded it, and when the same inference, normalization or equality is asked for again, it records a step of the same kind with `"of": j` instead of deriving the result again. Before each recall it checks that step j is still in the trace and still says the same thing, because a rollback can remove it. Replay checks the same: step j comes earlier, has the same kind, and concludes the same thing (for an equality, in either order).

This is what keeps traces finite in practice. Tracing has to bypass the kernel's own caches, because a cache hit skips the steps that justify it, and without recall some declarations redo the same work until the trace runs to many gigabytes. On a 998-declaration sample of `Init`, recall took the trace from 13,955,110 steps (826 MB) to 1,184,351 steps (117 MB).

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
{"s":40,"k":"Whnf","a":17,"b":21,"of":12}                  step 40: 17 ↝* 21, as step 12 already concluded
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

The replayer (`src/TenetZfc`) reads the export and the trace and re-derives every step from the definition of its rule. It shares no code with Tenet: it has its own terms, substitution, universe-level arithmetic, reduction rules and type inference. Each step is checked against the export's declarations and the facts recorded before it in the same declaration: reductions, equalities and typings. Each of those facts is a step with its own verdict, so a declaration is replayed in full only when every one of its steps is verified.

Every step gets one of four verdicts:

| Verdict | Meaning |
|---|---|
| verified | Re-derived: the rule applies to the recorded terms and gives the recorded result |
| failed | It doesn't, or the step is malformed (for example, it uses a free variable no step introduced) |
| unsupported | A kind of step the replayer checks, in a case it doesn't handle yet |
| not yet replayed | A kind of step the replayer doesn't check yet |

What is checked:

- **Single rules.**
  - Reductions: `Beta`, `Zeta`, `ZetaFVar`, `Delta`, `DeltaLazy`, `Proj`, `Iota` (including literal and structure-eta major premises), `IotaK`, `QuotLift`, `QuotInd`, `UnfoldProjApp`.
  - Literal arithmetic: `NatLitOp` and `NatLitPred`.
  - String literals: `StringLitToCtor` must give exactly Lean's expansion (`String.ofList`, or `String.mk` before it existed, applied to the `Char.ofNat` code points).
  - Equality rules that need no premises: `DefEqSyntactic`, `DefEqFVar`, `DefEqSort`, `DefEqConst` (universe levels are compared by case-splitting each parameter on zero or successor) and `DefEqOffset`.
- **Equality rules that rest on premises.** `DefEqApp`, `DefEqBinding` (walking both telescopes with the locals the step introduced), `DefEqEta`, `DefEqEtaStruct` (including Lean 4.37's partially applied constructors), `DefEqProofIrrel`, `DefEqUnitLike`, `DefEqLazyDelta`, `DefEqLazyDeltaProj`, `DefEqReflect` and `DefEqStringLit`.
- **Normalization.** `Whnf` and `WhnfCore`: there must be a chain from the term to its normal form through the step's direct premises. Each premise is used on the whole term or on the head of an application.
- **Equality.** `DefEq`: the two sides must be equal by the recorded facts, or by congruence over them.
- **Typing.**
  - `Infer`: the type is recomputed the way the kernel computes it for every form of term: sorts, constants, locals, literals, applications, lambdas and Pis (with their locals), lets (dead lets removed), and projections.
  - `Check`: the same computation, from checking-mode facts about the term's parts. It also requires the checks that mode adds. An argument's checked type must be recorded equal to its domain. Every binder domain and `let` type must be checked to be a type. A `let` value must have its type. Universe levels may use only the declaration's parameters; for an inductive block, that means the parameters of any of its types, constructors or recursors.
- **Recalls.** A step with `"of"` must name an earlier step of the same kind that concludes the same thing.
- **Locals.** Each must be fresh, and nothing may use a variable before its `Local` step.
- **Inductive blocks.**
  - **Types.** Every type, constructor type and recursor type in the block must be checked by the trace to be a type.
  - **Structure, rechecked from the export.** The block's types share their parameters, and each constructor takes exactly those parameters. Each field is strictly positive: a type of the block appears only as I params indices, at the end of the field's arrows. Each field's universe fits within the type's, unless the type is a Prop; the field universes come from the trace's checking-mode facts about the constructor's type. Each constructor returns its own type applied to the parameters.
  - **Recursors, derived here.** Each recursor's type and computation rules are derived from the block the way the kernel derives them, and must match the export's exactly (up to binder names). That covers motives, minor premises, induction hypotheses for recursive fields, elimination into Prop only versus into any universe, rule K, and annotation stripping on the derivation's locals (only for `optParam`, `autoParam`, `outParam` and `semiOutParam` defined as the identity). Iota steps therefore use rules the replayer has rederived, not just the exporter's.
  - Tenet's non-positive `Bad` from its negative corpus is rejected by the structural recheck alone, and a recursor rule swapped for another constructor's is caught.
- **Nested inductive blocks** (such as `Lean.Syntax`, which holds an `Array Syntax`) are checked the way the kernel checks them, with all three stages redone from the export:
  1. **Elimination.** Each nested occurrence is replaced by an auxiliary type (`_nested.Array_1`, and `_nested.List_2` for the `List Syntax` inside `Array`'s constructor). Names and order follow the kernel's traversal.
  2. **The auxiliary block** is checked like any other: its types from the trace, its structure and recursors rechecked.
  3. **Restoration.** Its recursors and constructors are translated back and must equal the export's `Lean.Syntax.rec`, `rec_1`, `rec_2` and constructors.

  The block's trace was taken partly in the auxiliary environment and partly, for the kernel's final re-check, in the declaration's own. Each step is replayed against the auxiliary environment first and the export's second. Both environments are verified to agree through step 3.
- **The quotient block.** The kernel builds `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` in rather than deriving them, so there's nothing to replay. Instead, the export's four constants must have exactly the built-in types, and the `Eq` they mention must be the standard inductive with the standard `Eq.refl`.
- **Each declaration.** Its trace must conclude, from checking-mode facts, what the kernel checks of it: its type is a type, and the value of a definition, theorem or opaque constant has that type. Without this check, a trace of valid steps that didn't add up to the declaration would pass. Infer-only facts don't count here, because they assume the term is well typed. The declaration must also obey the kernel's safety rule: a safe declaration mentions no unsafe or partial constant, and a partial one mentions no unsafe constant.

Delta and iota substitute universe levels with Lean's simplifying `mk_max` and `mk_imax`, because the kernel's reduct carries the simplified level.

## What replay does not establish yet

- **Structural cases not handled.** A field whose block-type occurrence is hidden behind a definition, or parameters that differ only up to definitional equality, are reported as unsupported rather than decided.
- **`Check` and recall need Tenet's `trace-recall` branch.** Tenet's main branch writes every inferred type as `Infer` and doesn't recall. Traces from it replay step by step, but no declaration in them is concluded, and some traces get very large.
- **Nat operations** are taken to mean what their names say. Tenet checks that against their definitions once per environment, and that check isn't in the trace.
- **Rule K** is checked for the reduct only. The kernel's check on the major premise's type is a typing fact the step doesn't cite.

## Results

### All of Lean core

The `Init` library of Lean 4.36.0, exported by [leanout](https://github.com/keithadler/leanout), has 64,045 declarations. Every one was traced by Tenet (its `trace-recall` branch) and replayed, in 1,000-declaration chunks:

| | |
|---|---|
| Declarations traced and replayed | 64,045 (all of them) |
| Steps | 86,172,037 |
| Verified | 86,172,037 |
| Failed | **0** |
| Not replayed | 0 |
| Definitions, theorems, opaque constants and axioms concluded by their trace | 63,435 of 63,435 |
| Inductive blocks checked, recursors derived and matching | 606 of 606, including the nested `Lean.Syntax` |
| Quotient constants matching the built-in types | 4 of 4 |

What this rests on: the replayer's own code, the export as `leanout` wrote it, and the assumptions listed above (the meaning of the Nat operations, and the typing side condition of rule K). The milestone 1 gate is to re-derive every check Tenet made on all of Lean core. That is met.

Running it showed three things that small fixtures didn't:
- **Tracing without caches blows up.** Some declarations redid the same work until one 1,000-declaration chunk passed 4.9 GB, which is why Tenet's traces now recall earlier conclusions.
- **Recall needs the environment as part of the key.** Without it, nested inductives broke, because their auxiliary types live in a separate environment.
- **56 declarations couldn't be named on Tenet's command line.** Their names have dots or commas inside a component, and Tenet now parses `«…»` escapes.

The first two were bugs in the tracing added for this project. Both failed safe: a declaration was rejected, never wrongly accepted.

### Fixtures

On the committed fixtures (`tests/fixtures`), every step is verified and every declaration is concluded or checked:

| Export | Steps | Verified | Declarations concluded | Inductive blocks checked | Quotient constants |
|---|---|---|---|---|---|
| `Nat.add_succ` | 1,778 | 1,778 | 14 | 6 | 0 |
| `Nat.add_succ.v3.0` | 1,759 | 1,759 | 13 | 6 | 0 |
| `eta437` | 1,058 | 1,058 | 8 | 6 | 0 |
| `acc436` | 912 | 912 | 7 | 5 | 0 |
| `quot` | 178 | 178 | 1 | 1 | 4 |
| `syntax` | 48,606 | 48,606 | 228 | 45 (one nested) | 0 |

The tests change recorded results, the results of every kind of step the replayer checks, and require the change to be caught:
- for `Infer`, `DefEq` and `WhnfCore`, the first 25 occurrences of each are changed one at a time;
- a false `Nat.zero ≡ Nat.succ Nat.zero` is caught;
- a wrong but well-formed type is caught;
- a theorem whose trace is emptied is caught.

A replayer that accepted everything would also pass the clean fixtures, so the clean results mean little without these tests.

The replayer is also the template for the emitter: where replay checks a step, emission will print the `set.mm` proof step for it.
