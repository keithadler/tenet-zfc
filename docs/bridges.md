# Bridge theorems: the model's `Nat` is `NN0`

Milestone 3's model gives every Lean constant a `set.mm` definition computed from Lean's own (see [milestone3.md](milestone3.md)). A theorem translated through the model is about the model's sets: `lean.Nat`, `lean.Nat.succ`, `lean.Nat.add`. A reader wants it in `set.mm`'s own vocabulary: `NN0`, `+`, decimal numerals. Bridge theorems connect the two.

Milestone 2 connected them by assumption: a hand table that read `Nat` as `NN0`, `Nat.add` as `+` and a literal as a numeral ([interpretation.md](interpretation.md), `StatementTranslator`, `Bridge.cs`). This document is about replacing that table with theorems. Everything below is proved from the model's definitions and `set.mm`'s axioms. The outputs are checked by metamath-exe, mmverify.py and mmj2's definition check, and none of them adds an axiom.

`tenet-zfc nat-bridge <export.ndjson> <set.mm> <out.mm> [<n>...]` writes them. The export must contain `Nat.add` (CI uses `tests/fixtures/natadd.ndjson`, exported by leanout from Lean 4.36.0's `Init`). The command adds a theorem `F ( n ) = n` for each numeral `n` it is given.

## The bridge map

The model's `Nat` at a universe `U` is `( lean.Nat ` U )`. It is the union of an ω-chain of stages of tagged tuples:
- zero is `<. (/) , (/) >.`;
- `succ x` is `<. 1o , <. (/) , <. x , (/) >. >. >.`.

The model writes a literal `n` as `( lean.Nat.-lit ` ( lean.Nat.-ofnum ` n ) )`:
- `lean.Nat.-ofnum` inverts `set.mm`'s isomorphism from `ω` onto `NN0`, which is `G = ( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om )` from `om2uzf1oi`;
- `lean.Nat.-lit` sends the ordinal `k` to `succ` applied `k` times to zero.

The bridge runs that backwards:

```
F = ( `' lean.Nat.-ofnum o. `' lean.Nat.-lit )
```

It reads off a model numeral's ordinal, then maps that ordinal into `NN0`. `F` is a term written in `set.mm`'s notation over the model's two literal constants. It isn't a new definition.

## What is proved

| Label | Statement | Meaning |
|---|---|---|
| `lean-nat-f1o` | `( U e. Univ -> F : ( lean.Nat ` U ) -1-1-onto-> NN0 )` | `F` is a bijection from the model's `Nat` onto `NN0` |
| `lean-nat-fzero` | `( U e. Univ -> ( F ` ( lean.Nat.zero ` U ) ) = 0 )` | zero is `0` |
| `lean-nat-fsucc` | `( ( U e. Univ /\ A e. N ) -> ( F ` ( ( lean.Nat.succ ` U ) ` A ) ) = ( ( F ` A ) + 1 ) )` | `succ` is `+ 1` |
| `lean-nat-flitnum` | `( A e. NN0 -> ( F ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` A ) ) ) = A )` | a literal is its numeral |
| `lean-nat-lit-256` (one per numeral asked for) | `( F ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` ; ; 2 5 6 ) ) ) = ; ; 2 5 6` | the same, closed, so `set.mm`'s decimal lemmas apply |
| `lean-nat-eq` | `( ( U e. Univ /\ ( A e. N /\ B e. N ) ) -> ( A = B <-> ( F ` A ) = ( F ` B ) ) )` | equations in the model are equations in `NN0` |
| `lean-nat-add` | `( ( R(G) /\ ( A e. N /\ B e. N ) ) -> ( F ` ( ( G ` A ) ` B ) ) = ( ( F ` A ) + ( F ` B ) ) )` | anything with `Nat.add`'s computation rules is `+` |
| `lean-nat-natadd` | the same, with `G` the model's `( lean.Nat.add ` U )` | `⟦Nat.add⟧` is `+`, given its rules |
| `lean-nat-2p2e4-iff` | `( R(G) -> ( ( ( G ` 2̂ ) ` 2̂ ) = 4̂ <-> ( 2 + 2 ) = 4 ) )` | the cross-check: Lean's `2 + 2 = 4` is `set.mm`'s |
| `lean-nat-2p2e4`, `lean-nat-natadd-2p2e4` | `( R(G) -> ( ( G ` 2̂ ) ` 2̂ ) = 4̂ )` | proved from `set.mm`'s `2p2e4`, through the bridge |

The table abbreviates three things:
- `N` is `( lean.Nat ` U )`.
- `2̂` and `4̂` are the model's literals, `( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 2 ) )` and the same for 4.
- `R(G)` is `Nat.add`'s two computation rules for `G`, as hypotheses:

```
( ( U e. Univ /\ A. a e. N ( ( G ` a ) ` ( lean.Nat.zero ` U ) ) = a )
  /\ A. a e. N A. b e. N ( ( G ` a ) ` ( ( lean.Nat.succ ` U ) ` b ) ) = ( ( lean.Nat.succ ` U ) ` ( ( G ` a ) ` b ) ) )
```

`lean-nat-2p2e4-iff` is the cross-check the plan asked for. It puts Lean's statement `2 + 2 = 4`, read in the model, next to `set.mm`'s `( 2 + 2 ) = 4`, and proves the two equivalent. `set.mm`'s own `2p2e4` then proves the model's version. That is how `ccatlen` was used in milestone 2, except that here the link is a theorem.

## How it is proved

The core is that the literal map is a bijection from `ω` onto the model's `Nat`. It is proved in four parts.

1. **Its values.** It takes 0 to zero and `suc k` to `succ` of its value at `k` (`fr0g`, `frsucmpt2`).
2. **Every literal is in the model's `Nat`.** By induction (`finds`), the literal `k` is in stage `k + 1`. Each stage is `stage ∪ {zero} ∪ succ[stage]` (`rdgsuc` and the step's definition), so its successor is in the next stage.
3. **Every element of the model's `Nat` is a literal.** By induction, each stage lies inside the literal map's range. Zero is the literal 0, and the range is closed under `succ`.
4. **It is injective.** By induction on `k`, for all `m`: if the literals of `k` and `m` are equal, then `k = m`. The proof splits `m` into zero or a successor (`nn0suc`). Zero isn't a successor, because their first components are `(/)` and `1o` (`opth1`, `1n0`). `succ` is injective (`opth`).

The rest follows from these:
- `F` is a bijection, by `f1oco` with `om2uzf1oi`.
- Zero and `succ` go to `0` and `+ 1`, by `om2uz0i` and `om2uzsuci`.
- A literal goes to its numeral, by `f1ocnvfv2` twice.
- Addition is by induction on the second argument's ordinal. The induction carries "is in `N`" along with the equation, because the successor step needs it.

`lean-nat-litinj`'s induction hypothesis binds `m`, so the step proves its `∀` over a fresh `l` and renames it (`cbvralvw`). Instantiating the hypotheses `∀a`, `∀b` uses `rspcv` rather than `rspcdva`, which would need the bound variable absent from a context that binds it. Both verifiers caught the first versions of both.

## Why `Nat.add`'s computation rules are hypotheses

The task was to prove `F ( ⟦Nat.add⟧ a b ) = F a + F b` outright, from `Nat.add`'s computation rules as theorems about the model. **In the current model those rules are false**, so the theorem is stated for any `G` satisfying them, and instantiated at `( lean.Nat.add ` U )`.

The reason is the model's single universe (milestone3.md, step 1, "One universe for every level"):
- Lean compiles `Nat.add` by structural recursion, through `Nat.brecOn` and `Nat.below`.
- `Nat.below` calls `Nat.rec` with the motive `fun _ => Sort (max 1 u)`. The model translates it as `( z e. ( lean.Nat ` U ) |-> U )`, a function whose values are the universe itself.
- `Nat.rec`'s domain is `( U ^m ( lean.Nat ` U ) )`. That motive could only be in it if `U e. U`, which `elirr` rules out.
- So `Nat.rec` at that motive is `(/)` (`ndmfv`), and `Nat.below` is `(/)` everywhere. In Lean, `Nat.below motive 0` is `PUnit`, which is not empty.

Both steps are proved and checked, in every `nat-bridge` output:
- `lean-nat-belowmotive`: `( U e. Univ -> ( ( lean.Nat.rec ` U ) ` ( z e. ( lean.Nat ` U ) |-> U ) ) = (/) )`
- `lean-nat-belowempty`: `( … -> ( ( ( lean.Nat.below ` U ) ` A ) ` B ) = (/) )`

The rest of the chain is not machine-checked. `brecOn`'s motive is `PProd (motive n) (Nat.below motive n)`, which becomes `(/)` because `PProd` with an empty factor is empty. `Nat.rec`'s base case would then need an element of `(/)`, so `⟦Nat.add⟧ a b = ( 1st ` ( 2nd ` (/) ) ) = (/)` for all `a` and `b`, and `a + 0 = a` fails.

The fix is milestone 4's separate universe levels. A motive into `Sort u` needs a universe that contains `U`. Once `Nat.add`'s rules hold in the model (Lean proves them by `rfl`), `lean-nat-natadd` gives `⟦Nat.add⟧ = +` with no hypotheses left. Every structurally recursive definition in `Init` goes through `brecOn`, so this limit affects all of them, not just addition.

## Milestone 2's table, entry by entry

| Milestone 2 assumed | Now |
|---|---|
| `Nat` is `NN0` | `lean-nat-f1o`: a proved bijection, which is what "is" can mean for two different sets |
| `Nat.zero` is `0`, `Nat.succ n` is `n + 1` | `lean-nat-fzero`, `lean-nat-fsucc` |
| a literal `n` is the numeral `n` | `lean-nat-flitnum`, and `lean-nat-lit-n` for each numeral a proof needs |
| `Nat.add` is `+` | `lean-nat-add`, for anything with `Nat.add`'s computation rules; unconditional once the model satisfies them (above) |
| `a = b` on `Nat` is `=` on `NN0` | `lean-nat-eq` |

`StatementTranslator` and `Bridge.cs` stay as they are, because milestone 2's emitter still uses them. A generic emitter (milestone 3, step 4) will state a theorem about `lean.Nat`, then restate it with `lean-nat-eq` and the rows above. `lean-nat-2p2e4-iff` is that restatement done once by hand.

## Not yet

- **`List` and `Word`.** The bijection from `( ( lean.List ` U ) ` A )` onto `Word A`, with `length` as `#` and `append` as `++`. The method carries over: a map defined by recursion, proved bijective by induction over the stages. Lists have a parameter and two fields per `cons`, so the proofs are longer. `List.length` and `List.append` are structurally recursive, so they hit the same `Nat.below` limit as `Nat.add`, and need the same hypotheses for now.
- **Literal arithmetic.** `Nat.add` on two literals would need `set.mm`'s `decadd` toolkit for multi-digit numerals. The bridge reduces the kernel's GMP steps to it: `lean-nat-lit-n` and `lean-nat-add` together turn `lit a + lit b = lit c` into `a + b = c` in `NN0`.

## The proof kit

The bridge's proofs are written in C# with `ProofKit` (`src/TenetZfc/ProofKit.cs`), a small tactic layer over `Prover.Apply`:
- **`Use`** applies a `set.mm` theorem. Its substitution comes from matching the theorem's hypotheses (and, if given, its conclusion) against what is supplied, so a step names only the theorem and its premises.
- **`Imp`** chains through a closed implication in deduction form.
- **`Rw`** rewrites with an equation.
- **`Cong`** proves congruence. It has more constructs than `Deduction.Congruence`: `suc`, `ran`, `dom`, `` `' ``, `o.`, `C_`, `<->`, `-.`, `A.`, `E.`, `X_`, `frecs`, mpo.
- **`Finds`** does induction on ω.

None of it is trusted, since every proof it builds goes through the verifiers.

The `nat-bridge` output is 47 theorems in 89,762 proof steps. That is 455 KB flat and 50 KB compressed.
