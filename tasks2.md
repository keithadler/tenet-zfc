# tasks2: work for another machine

Tasks for a second machine (or cloud sessions) on `keithadler/tenet-zfc`, after `v0.1.0`. Each task ends in its own pull request against `main`. Start from `main` at `452c1b7` or later.

The heavy runs belong here, not on Keith's Mac: an Init-wide run pushed that machine's load past 100.

## Rules for every task

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

## Task 1: run `theorem` over all of Init

**Why:** 28 of 30 hand-picked theorems go through the model. Nobody knows what fraction of Init's 45,588 theorems does. This number decides the project's timeline.

**Starting point:** the branch `claude/init-theorems-5561b3` has 14 commits of work on a batch mode (`theorem-all`). If it has been pushed, start from it and merge `origin/main`. If it isn't on the remote, build the batch mode fresh, modelled on `define-all` (`src/TenetZfc/DefineAll.cs`).

**Do:**
1. A batch mode, `tenet-zfc theorem-all <export> <set.mm> <outdir>`: chunked, resumable, a time budget per theorem, lemmas shared within a chunk, each refusal or error recorded per theorem with its reason. Reuse `scripts/verify-all` and `scripts/summarize-all`.
2. Run it on Init. If the whole run is too slow, run every 10th theorem first and say so.
3. Record in `docs/milestone3.md`: theorems proved and verified; refusals ranked by reason; checker failures and why; size and time distributions.
4. **The deliverable is the ranking:** which few missing constructs unblock the most theorems, with a forecast of the work to reach 50% and 80% of Init.
5. Fix the top one or two blockers if they're cheap, and re-measure.
6. Add a small CI chunk (a few minutes at most) and update the README's status.

**Done when:** the measured numbers and the ranked blockers are in the docs, every emitted chunk passes all three checkers, and the PR is open.

## Task 2: finish Init's definitions

**Why:** PR #15's re-run was cut short. In 34 of 40 chunks, 16,565 of 17,000 constants verify.

**Do:**
1. Run `define-all` and `verify-all` on the chunks that didn't finish (33, 35–39), and re-run the chunks whose refusals were quotients or choice in the tower, which PR #12 fixed.
2. **mmj2's 15,000-symbol limit:** chunk 31 has an error from it, and 57 constants were refused for it. Split long proof steps into lemmas or share more, so they fit, or document why not.
3. **`Acc.rec`'s computation rule.** `Acc` is modelled (`src/TenetZfc/Model.Least.cs`), but its recursor's rule isn't proved.
4. Update the counts in `docs/milestone3.md` and `README.md`.

**Done when:** all 40 chunks are verified or their failures explained, and the final counts are published.

## Task 3: plain ZFC for `List α` and the theorem library

**Why:** `Nat.add_zero` and `Nat.zero_add` are in plain ZFC (PR #14, `--lowered`, `docs/milestone4.md`). The headline theorem `lean-ccatlen` still assumes the universe tower.

**Do:**
1. Lowering for recursive types with parameters (`List α`). The doc lists what's missing: unions over type families, which need the reflection schema.
2. `lean-ccatlen` with no universe hypothesis and no `ax-groth`, next to set.mm's `ccatlen`. Check it with `scripts/check-axioms`.
3. `--lowered` for `theorem`, and for `define`/`define-all` if feasible. Emit the 28-theorem library in plain ZFC and report how many go through.
4. Update `docs/milestone4.md`, `docs/demo.md` and the README.

**Done when:** `ccatlen` from Lean's proof is a theorem of plain ZFC, accepted by all three checkers and `check-axioms`.

## Task 4: more bridges

**Why:** a translated theorem is convincing when it lands in set.mm's own vocabulary, as `ccatlen` does. Only `Nat`/`NN0` and `List`/`Word` are bridged.

**Do**, in the style of `src/TenetZfc/NatBridge.cs` and `ListBridge.cs`:
1. `Nat.mul` to `x.`, `Nat.sub` to truncated subtraction, `Nat.le`/`Nat.lt` to `<_`/`<` on `NN0`.
2. `Int` to `ZZ`, with `+`, `x.`, negation and order.
3. For each, restate one or two library theorems in set.mm's terms and prove them equivalent to set.mm's own theorem where one exists (for example `Nat.add_comm` and `nn0addcom`-style results).

**Done when:** each bridge is verified, with at least one cross-checked theorem per operation.

## Task 5: toward the headline theorem

**Why:** milestone 5 is a famous theorem end to end. The infinitude of primes is the natural pick: set.mm proves it independently (`infpn`), so it gives another `ccatlen`-style cross-check.

**Do:**
1. Pick the Lean statement and proof (core or mathlib's `Nat.exists_infinite_primes`) and export it with its dependencies.
2. Run `model-survey` and `theorem` on that export. Report what translates, what's refused and why.
3. Write the gap list in a new `docs/milestone5.md`: the missing constructs, the bridges needed (`Nat.Prime` to set.mm's `Prime`, divisibility, factorial), and an estimate.
4. Fix what's cheap. This task is mainly the map, not the finished proof.

**Done when:** the gap list is published with measured numbers.

---

## Order and independence

Tasks 1, 2 and 3 are independent and can run in parallel on separate machines. Task 4 is independent too. Task 5 is best after Task 1's ranking is known. All touch `docs/milestone3.md` and `README.md`, so expect small merge conflicts there.
