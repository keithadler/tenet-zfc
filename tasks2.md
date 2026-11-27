# tasks2: work for another machine

Tasks for a second machine (or cloud sessions) on `keithadler/tenet-zfc`, after `v0.1.0`. Each task ends in its own pull request against `main`. Start from `main` at `452c1b7` or later.

The heavy runs belong here, not on Keith's Mac: an Init-wide run pushed that machine's load past 100.

## Status (27 November, evening)

Everything from the first round is merged: #16 to #26. No pull request is open. Overall the project is about 65% of the way to its goal; this file assigns **all the work that is left**.

| First-round task | Outcome |
|---|---|
| 1. `theorem` over Init | `theorem-all` and the first blockers' fixes merged (#20). **The measured totals, ranking and forecast are still owed.** |
| 2. Init's definitions | 17,329 of 17,590 (98.5%) with verified equations (#23). Leftovers below. |
| 3. Plain ZFC for `List α` | **Not started.** The largest piece of what is left. |
| 4. More bridges | `Nat.mul` is `x.` (#21). The rest below. |
| 5. Headline map | Done (#24): 114 of the primes cone's 146 theorems proved and checked; gap list in `docs/milestone5.md`. |

**In flight, don't duplicate.** The first machine (Keith's Mac session) has a branch on top of `main` with the pieces the primes lemmas still need, arriving as one PR: `Classical.em` proved in the model directly; a proposition's constructor witnessed by its own arguments, bound variables renamed apart (the `rspcedvd` `$d` trap, gap 2 in `docs/milestone5.md`); `And`/`Iff` recursors into any sort and projections out of them; `False`'s recursor; conversion under a λ; and `examples/Primes.lean` reworked to use the excluded middle alone (8 lemmas, with `not_forall`, `not_imp` and `fact_succ` added). Today both machines built induction on `Nat.le` independently. To avoid that again: **before starting a task, say so in a draft PR or an issue**, and check for one.

## Rules for every task

- **Money:** no paid cloud machines (AWS or any other) without Keith's explicit OK for that run, with an estimate of the cost first. GitHub's runners are free for this repository: use `init-run.yml` and `headline.yml`.
- **Keith's Mac:** no heavy runs there. One low-priority process at a time at most.
- **Merging to `main`:** only Keith merges, or says to. A green CI run on the merged result is the bar; a PR that conflicts gets `main` merged into it first.
- **Branches:** work on your own branch and open a PR against `main`. Never push to `main`, and never create tags or releases.
- **Commits** end with `Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>`. PR bodies end with `🤖 Generated with [Claude Code](https://claude.com/claude-code)`.
- **Merging:** merge `origin/main` into your branch before opening the PR, and again if it conflicts later. Keep both sides' features.
- **Checks:** every output must pass all three:
  - metamath-exe, with no `?Error` line (it prints "All proofs … verified" even after an error);
  - mmverify.py, exit status 0;
  - `scripts/check-definitions`, which runs mmj2's `definitionCheck`.
- **Plain-ZFC claims** must also pass `scripts/check-axioms` (no `ax-groth`, no universe variable left in the statement).
- **Both targets build:** `dotnet build -c Release` for net8.0 and net10.0. CI runs Linux, macOS and Windows.
- **Report honestly:** record refusals and failures with their reasons. A checker rejecting an output is a bug in the model or prover: fix it, or document it with a minimal reproduction.
- **`$d` traps:** see `docs/milestone3.md`. The usual fixes are renaming bound variables (`cbvmptv`, `cbvmpov`, `cbviunv`, `cbvixpv`) and proving under only the hypotheses needed.

## Setup

Copy what `.github/workflows/ci.yml` does in its `emit-and-verify` job. It pins exact commits of everything:

- .NET 10 SDK (and 8, to build both targets); Java 11 (zulu) for mmj2;
- `set.mm`, metamath-exe, mmverify.py and mmj2 at the commits in the workflow's `env`.

Then set these so the verifier-gated tests run:

```
TENET_ZFC_SETMM      folder holding set.mm
TENET_ZFC_METAMATH   path to the metamath-exe binary
TENET_ZFC_MMVERIFY   path to mmverify.py
TENET_ZFC_JAVA       path to Java 11
TENET_ZFC_MMJ2       folder holding mmj2.jar and macros/
```

For exports: build [leanout](https://github.com/keithadler/leanout) with Lean 4.36.0, then `leanout Init -o init.ndjson`. For one constant and its dependencies: `leanout Init -o f.ndjson -- Nat.add_comm`.

Read first: `README.md` (status and roadmap), `docs/milestone3.md`, `docs/milestone4.md`, `docs/bridges.md`, `docs/demo.md`.

---

Tasks are lettered so they don't collide with the first round's numbers. Shares are rough fractions of the remaining 35%.

## Task A: finish theorem coverage on Init (about 10 of the 35)

**Why:** milestone 3's gate is "all of Lean core translates and verifies". Definitions are at 98.5%. Theorems are measured only on a first sample: 27% of 150 before #20's fixes.

**Do:**
1. Finish the every-10th sample of `Init`'s 45,588 theorems on GitHub's runners (`init-run.yml`, `mode=theorems`), with `main` as it is now. Publish in `docs/milestone3.md`: proved and verified, refused by reason, over budget, errors; size and time distributions.
2. **The ranking and the forecast**, which the first round still owes: which few constructs unblock the most theorems, and the work to reach 50% and 80%.
3. Fix the blockers in rank order. Known from the primes cone (`docs/milestone5.md`): conversions between Π-propositions that differ by more than bound variables (10 of 146); theorems over the time budget (4); "can't infer a type: applying something that isn't a function" (3).
4. **Choice in theorems** (8 of 146 in the cone, and common in `Init`): theorems that go through `Classical.choice` as data, `Classical.choose` and `Classical.propDecidable`. The model has choice (a well-ordering of the tower's union); the theorem translator refuses it. Carry the well-ordering `W` and `W We U. ran U` through `theorem` as hypotheses.
5. Re-measure after each fix. Then the full run, not the sample, if the free runners can carry it; if not, say what it would cost and ask.

**Done when:** the measured share of `Init`'s theorems is published with the ranking, and the top blockers are fixed or explained.

## Task B: Init's definitions, the leftovers (about 2 of the 35)

**Do:**
1. The 256 definitions too large for mmj2's definition check: split long steps into lemmas, or document why not.
2. The 11 computation rules refused because a witness's variable occurs in the hypotheses (`LawfulApplicative.mk`, `Equivalence.mk`, `LawfulFunctor.mk`): the renaming the first machine's PR brings for theorems, applied to `Iota`.
3. `Acc.rec`'s and `Acc.below.rec`'s computation rules.
4. The 3 out-of-memory constants (`Lean.Grind.Semiring.mk` and two others).
5. **Re-total the complete run with the fixed `scripts/summarize-all`** (#17), and re-check chunk 31 with mmj2 after #23's fix. The README says these counts were totalled before the fix; replace them and remove that caveat.

**Done when:** every `Init` definition is verified or its refusal explained, and the published counts come from the fixed script.

## Task C: plain ZFC (about 15 of the 35, the largest)

**Why:** almost every output assumes `U e. lean.-tower`. Two theorems are in plain ZFC. To a set theorist, a universe hypothesis on facts about natural numbers is the project's weakest point.

**Do**, in this order (`docs/milestone4.md` has the design):
1. Lowering for recursive types with parameters (`List α`): unions over type families, which need the reflection schema.
2. `lean-ccatlen` with no universe hypothesis and no `ax-groth`, next to set.mm's `ccatlen`, checked by `scripts/check-axioms` (which now accepts only set.mm's ZFC axioms by name).
3. `--lowered` for `theorem` and `theorem-all`, then for `define` and `define-all`.
4. The 28-theorem library and the primes cone in plain ZFC, with the count of what lowers and what doesn't, and why.
5. Lowering as the default, the tower as a reported fallback. Each result reported as plain ZFC, or as ZFC plus universes with the declarations that needed them.
6. Milestone 4's gate: mathlib's `Nat` and `Int` files in plain ZFC. This needs mathlib's export through the model first, which nobody has tried: measure it with `model-survey` before promising anything.

**Done when:** `ccatlen` from Lean's proof is a theorem of plain ZFC (step 2) at the least; the gate (step 6) for the milestone.

## Task D: bridges (about 3 of the 35)

**Why:** a translated theorem convinces when it lands in set.mm's own vocabulary. Addition, multiplication, lists and lengths are bridged.

**Do**, in the style of `NatBridge.cs` and `ListBridge.cs`, each with a cross-checked theorem:
1. `Nat.le` and `Nat.lt` to `<_` and `<` on `NN0`: induction over the stages one way, `B = A + k` the other.
2. `Nat.sub` to truncated subtraction.
3. `∣` (`∃ c, b = a * c`) to set.mm's `||`.
4. `Prime` (as in `examples/Primes.lean`) to the statement in set.mm's `infpn`, with a theorem proving the two statements equivalent.
5. `Int` to `ZZ`, with `+`, `x.`, negation and order.

**Done when:** each is verified, and items 1, 3 and 4 are enough to restate `infinitude_of_primes` as `infpn`.

## Task E: the headline theorem, end to end (about 5 of the 35)

**Needs:** the first machine's PR (above), then Tasks A (its blockers in the cone), D (items 1, 3, 4) and C (for plain ZFC).

**Do:**
1. All 8 lemmas of `examples/Primes.lean` through the model, checked by all three checkers. `headline.yml` reports each one.
2. Restated through the bridges as set.mm's `infpn`, next to set.mm's own proof: two independent proofs of one statement, with sabotage checks, as `scripts/demo` does for `ccatlen`.
3. In plain ZFC, checked by `scripts/check-axioms`.
4. Publish the outputs, sizes, times and the count of what needed universes. Update `docs/demo.md` and the README.

**Done when:** `infinitude_of_primes` from Lean's proof is set.mm's `infpn` in plain ZFC.

## Task F: trust and housekeeping (small, do alongside)

From the code review (#17) and today:
1. The unsound recursor case is refused, not modelled: an inductive proposition with a data field that eliminates into any sort. Model it by reading the field back from the indices.
2. Verifier-gated tests `return` when the tools are absent, so they pass instead of skipping. Make them skip, and run the mmj2 part in CI's test step.
3. `tenet-zfc run` reports a polymorphic declaration "proved" on its all-zero universe instance, which for `Sort u` is the `Prop` one. Report the instance, or prove a representative one.
4. `scripts/demo`'s sabotage checks count a crash as a rejection. Tell them apart.
5. `Classical.em` and `propext` are proved in the model directly, not from Lean's proofs. Document this in `docs/milestone3.md` as a stated list of such constants.
6. A constructor of a recursive proposition with more than one recursive premise, if #20 doesn't already cover it.
7. Commits from each machine carry the co-author line of the model that did the work.

## Task G: the next release

When A and D land and E's step 1 is done: `CHANGELOG.md`, the README, and a `v0.2.0` section. **Keith tags and releases; nobody else does.**

---

## Order and independence

- **Start now, in parallel:** A (steps 1 to 3), B, C (steps 1 and 2), D (items 1 and 2).
- **After the first machine's PR merges:** A step 4 (choice), D items 3 and 4, E step 1.
- **Last:** E steps 2 to 4, then G.
- C is independent of everything else until E step 3, and is the long pole: start it first.
- All of these touch `docs/milestone3.md`, `README.md` and `CHANGELOG.md`. Expect small conflicts, and merge `main` into your branch before asking for a merge.
