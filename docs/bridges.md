# Bridge theorems: the model's `Nat` is `NN0`

Milestone 3's model gives every Lean constant a `set.mm` definition computed from Lean's own (see [milestone3.md](milestone3.md)). A theorem translated through the model is about the model's sets: `lean.Nat`, `lean.Nat.succ`, `lean.Nat.add`. A reader wants it in `set.mm`'s own vocabulary: `NN0`, `+`, decimal numerals. Bridge theorems connect the two.

Milestone 2 connected them by assumption: a hand table that read `Nat` as `NN0`, `Nat.add` as `+` and a literal as a numeral ([interpretation.md](interpretation.md), `StatementTranslator`, `Bridge.cs`). This document is about replacing that table with theorems. Everything below is proved from the model's definitions and `set.mm`'s axioms. The outputs are checked by metamath-exe, mmverify.py and mmj2's definition check, and none of them adds an axiom.

`tenet-zfc nat-bridge <export.ndjson> <set.mm> <out.mm> [<n>|<theorem>...]` writes them. The export must contain `Nat.add` (`tests/fixtures/natadd.ndjson`, or `theorems.ndjson`, both exported by leanout from Lean 4.36.0's `Init`). The command adds a theorem `F ( n ) = n` for each numeral `n` it is given, and proves and restates each theorem it is given (below).

The bridge runs on the model's default, tower mode, where the universe argument `U` is a tower of Grothendieck universes and every theorem has the hypothesis `U e. lean.-tower` ([milestone3.md](milestone3.md#tower-mode-universescs-monomorphcs)). `--single-universe` writes the older bridge over one universe, `U e. Univ`, in which `Nat.add`'s computation rules are hypotheses (see the end of this document).

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
| `lean-nat-f1o` | `( U e. lean.-tower -> F : ( lean.Nat ` U ) -1-1-onto-> NN0 )` | `F` is a bijection from the model's `Nat` onto `NN0` |
| `lean-nat-fzero` | `( U e. lean.-tower -> ( F ` ( lean.Nat.zero ` U ) ) = 0 )` | zero is `0` |
| `lean-nat-fsucc` | `( ( U e. lean.-tower /\ A e. N ) -> ( F ` ( ( lean.Nat.succ ` U ) ` A ) ) = ( ( F ` A ) + 1 ) )` | `succ` is `+ 1` |
| `lean-nat-flitnum` | `( A e. NN0 -> ( F ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` A ) ) ) = A )` | a literal is its numeral |
| `lean-nat-lit-256` (one per numeral asked for) | `( F ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` ; ; 2 5 6 ) ) ) = ; ; 2 5 6` | the same, closed, so `set.mm`'s decimal lemmas apply |
| `lean-nat-eq` | `( ( U e. lean.-tower /\ ( A e. N /\ B e. N ) ) -> ( A = B <-> ( F ` A ) = ( F ` B ) ) )` | equations in the model are equations in `NN0` |
| `lean-nat-add` | `( ( R(G) /\ ( A e. N /\ B e. N ) ) -> ( F ` ( ( G ` A ) ` B ) ) = ( ( F ` A ) + ( F ` B ) ) )` | anything with `Nat.add`'s computation rules is `+` |
| `lean-nat-natadd-zero` | `( ( U e. lean.-tower /\ A e. N ) -> ( ( ( lean.Nat.add ` U ) ` A ) ` ( lean.Nat.zero ` U ) ) = A )` | `Nat.add`'s first computation rule, proved from its definition |
| `lean-nat-natadd-succ` | `( ( ( U e. lean.-tower /\ A e. N ) /\ B e. N ) -> ( ( ( lean.Nat.add ` U ) ` A ) ` ( ( lean.Nat.succ ` U ) ` B ) ) = ( ( lean.Nat.succ ` U ) ` ( ( ( lean.Nat.add ` U ) ` A ) ` B ) ) )` | its second |
| `lean-nat-natadd-rules` | `( U e. lean.-tower -> R(( lean.Nat.add ` U )) )` | so the model's `Nat.add` satisfies `R` |
| `lean-nat-natadd` | `( ( U e. lean.-tower /\ ( A e. N /\ B e. N ) ) -> ( F ` ( ( ( lean.Nat.add ` U ) ` A ) ` B ) ) = ( ( F ` A ) + ( F ` B ) ) )` | **`⟦Nat.add⟧` is `+`**, with no hypotheses but the tower's |
| `lean-nat-2p2e4-iff` | `( R(G) -> ( ( ( G ` 2̂ ) ` 2̂ ) = 4̂ <-> ( 2 + 2 ) = 4 ) )` | the cross-check: Lean's `2 + 2 = 4` is `set.mm`'s |
| `lean-nat-2p2e4` | `( R(G) -> ( ( G ` 2̂ ) ` 2̂ ) = 4̂ )` | proved from `set.mm`'s `2p2e4`, through the bridge |
| `lean-nat-natadd-2p2e4` | `( U e. lean.-tower -> ( ( ( lean.Nat.add ` U ) ` 2̂ ) ` 2̂ ) = 4̂ )` | the same for the model's `Nat.add` |

The table abbreviates three things:
- `N` is `( lean.Nat ` U )`.
- `2̂` and `4̂` are the model's literals, `( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 2 ) )` and the same for 4.
- `R(G)` is `Nat.add`'s two computation rules for `G`:

```
( ( U e. lean.-tower /\ A. a e. N ( ( G ` a ) ` ( lean.Nat.zero ` U ) ) = a )
  /\ A. a e. N A. b e. N ( ( G ` a ) ` ( ( lean.Nat.succ ` U ) ` b ) ) = ( ( lean.Nat.succ ` U ) ` ( ( G ` a ) ` b ) ) )
```

`lean-nat-add` is stated for any `G` with these rules, and `lean-nat-natadd-rules` proves that the model's `Nat.add` has them.

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

## `Nat.add`'s computation rules, proved

`⟦Nat.add⟧ = +` needs `Nat.add`'s two computation rules as facts about the model. Lean proves both by `rfl`: `n + 0` and `n + succ m` reduce, through `Nat.add`'s compiled definition, `Nat.brecOn`, `Nat.below` and `Nat.rec`, to `n` and `succ (n + m)`. In tower mode they hold in the model, and the bridge proves them the same way, by those reductions:

- `Model.ProveDefEq` (`src/TenetZfc/DefEq.cs`) proves `( hypotheses -> ⟦l⟧ = ⟦r⟧ )` for definitionally equal Lean terms `l` and `r` over free variables, with the theorem translator's conversion steps: delta (the definitions), beta (`fvmptd3`), iota (the computation rules `lean-iota-c`), projections and congruence ([milestone3.md](milestone3.md#how-a-theorem-is-proved)).
- `lean-nat-natadd-zero` is `Nat.add a Nat.zero ≡ a`, and `lean-nat-natadd-succ` is `Nat.add a (Nat.succ b) ≡ Nat.succ (Nat.add a b)`. They are 1.6 and 4.5 million flat proof steps, most of them typing `Nat.brecOn`'s arguments, and take about five minutes together.
- `ralrimiva` turns them into `R(( lean.Nat.add ` U ))`, and `lean-nat-add` does the rest.

The output, with the literals 2, 4 and 256, is 509 KB compressed. All three checkers accept it, and its header states the tower assumption.

## Lean's theorems, restated in `set.mm`'s arithmetic

`nat-bridge … Nat.add_zero Nat.zero_add` proves each theorem named through the model from its proof term (as `tenet-zfc theorem` does), then restates it in `NN0`. For `Nat.add_zero` (`∀ n, n + 0 = n`) it writes:

| Label | Statement |
|---|---|
| `lean-thm-Nat.add_zero` | `( ( U e. lean.-tower /\ A e. N ) -> (/) e. ⟦A + 0 = A⟧ )`, through the model ([milestone3.md](milestone3.md#results)) |
| `lean-nat-Nat.add_zero-lhs` | `⟦A + 0⟧ = ( ( ( lean.Nat.add ` U ) ` A ) ` ( lean.Nat.zero ` U ) )`: `HAdd.hAdd`, `instHAdd`, `instAddNat` and the literal `0` unfolded (`ProveDefEq`) |
| `lean-nat-Nat.add_zero` | `( ( U e. lean.-tower /\ A e. N ) -> ( ( F ` A ) + 0 ) = ( F ` A ) )` |
| `lean-nn0-Nat.add_zero` | `( ( U e. lean.-tower /\ A e. NN0 ) -> ( A + 0 ) = A )` |

The steps from the first to the last:
1. `Eq` is `=`: `⟦@Eq α a b⟧` is `if ( b = a , 1o , (/) )` (`lean-Eq.u1-eq`), and `(/)` is in it exactly when `b = a` (`lean-prop`).
2. Each side unfolds to `Nat.add`, `Nat.zero` and `Nat.succ` over the variables.
3. Through `F`, those are `+`, `0` and `+ 1` (`lean-nat-natadd`, `lean-nat-fzero`, `lean-nat-fsucc`), given that each subterm is in the model's `Nat` (`lean-nat-natadd-el`, `lean-nat-succel`, `lean-nat-zeroel`).
4. For `A e. NN0`, `( `' F ` A )` is in the model's `Nat` and `F` takes it back to `A` (`f1ocnv`, `f1ocnvfv2`).

So `( A + 0 ) = A` here comes from Lean's proof of `Nat.add_zero`, through the model and the bridge, not from `set.mm`'s `addrid`. `Nat.zero_add` gives `( 0 + A ) = A` the same way. The restatement takes theorems of the form `∀ (a b … : Nat), l = r` with `l` and `r` built from `+`, literals, `Nat.succ` and the variables. CI proves both theorems and their restatements into one output and runs the three checkers on it.

## In the one-universe model, the rules are false

`--single-universe` builds the bridge over the old model, with one universe `U e. Univ` for every level. There `Nat.add`'s computation rules are false, so `lean-nat-natadd` takes them as hypotheses. The reason:

- Lean compiles `Nat.add` by structural recursion, through `Nat.brecOn` and `Nat.below`.
- `Nat.below` calls `Nat.rec` with the motive `fun _ => Sort (max 1 u)`. The model translates it as `( z e. ( lean.Nat ` U ) |-> U )`, a function whose values are the universe itself.
- `Nat.rec`'s domain is `( U ^m ( lean.Nat ` U ) )`. That motive could only be in it if `U e. U`, which `elirr` rules out.
- So `Nat.rec` at that motive is `(/)` (`ndmfv`), and `Nat.below` is `(/)` everywhere. In Lean, `Nat.below motive 0` is `PUnit`, which is not empty.

Both steps are proved and checked, in every `--single-universe` `nat-bridge` output:
- `lean-nat-belowmotive`: `( U e. Univ -> ( ( lean.Nat.rec ` U ) ` ( z e. ( lean.Nat ` U ) |-> U ) ) = (/) )`
- `lean-nat-belowempty`: `( … -> ( ( ( lean.Nat.below ` U ) ` A ) ` B ) = (/) )`

The rest of the chain is not machine-checked. `brecOn`'s motive is `PProd (motive n) (Nat.below motive n)`, which becomes `(/)` because `PProd` with an empty factor is empty. `Nat.rec`'s base case would then need an element of `(/)`, so `⟦Nat.add⟧ a b = ( 1st ` ( 2nd ` (/) ) ) = (/)` for all `a` and `b`, and `a + 0 = a` fails. Every structurally recursive definition in `Init` goes through `brecOn`, so this affected all of them. In tower mode `Nat.below`'s motive returns `( U ` (/) )`, which is in the recursor's domain, and the rules hold.

## Milestone 2's table, entry by entry

| Milestone 2 assumed | Now |
|---|---|
| `Nat` is `NN0` | `lean-nat-f1o`: a proved bijection, which is what "is" can mean for two different sets |
| `Nat.zero` is `0`, `Nat.succ n` is `n + 1` | `lean-nat-fzero`, `lean-nat-fsucc` |
| a literal `n` is the numeral `n` | `lean-nat-flitnum`, and `lean-nat-lit-n` for each numeral a proof needs |
| `Nat.add` is `+` | `lean-nat-natadd`, with no hypotheses but the tower's (`lean-nat-add` for anything with `Nat.add`'s computation rules) |
| `a = b` on `Nat` is `=` on `NN0` | `lean-nat-eq` |

`StatementTranslator` and `Bridge.cs` stay as they are, because milestone 2's emitter still uses them. The generic route now exists for `Nat` equations: a theorem proved through the model is restated with the rows above (`NatBridge.Restate`, previous section). `lean-nat-2p2e4-iff` is the same restatement done by hand for a closed equation.

## Not yet

- **`List` and `Word`.** The bijection from `( ( lean.List.{0} ` U ) ` A )` onto `Word A`, with `length` as `#` and `append` as `++`, and `List.length_append` restated as `ccatlen`. The method carries over: a map defined by recursion, proved bijective by induction over the stages. Lists have a parameter and two fields per `cons`, so the proofs are longer. In tower mode `List.length` and `List.append` satisfy their computation rules, so, unlike before, nothing blocks it but the work; `ProveDefEq` proves the rules as it does `Nat.add`'s.
- **Literal arithmetic.** `Nat.add` on two literals would need `set.mm`'s `decadd` toolkit for multi-digit numerals. The bridge reduces the kernel's GMP steps to it: `lean-nat-lit-n` and `lean-nat-add` together turn `lit a + lit b = lit c` into `a + b = c` in `NN0`.

## The proof kit

The bridge's proofs are written in C# with `ProofKit` (`src/TenetZfc/ProofKit.cs`), a small tactic layer over `Prover.Apply`:
- **`Use`** applies a `set.mm` theorem. Its substitution comes from matching the theorem's hypotheses (and, if given, its conclusion) against what is supplied, so a step names only the theorem and its premises.
- **`Imp`** chains through a closed implication in deduction form.
- **`Rw`** rewrites with an equation.
- **`Cong`** proves congruence. It has more constructs than `Deduction.Congruence`: `suc`, `ran`, `dom`, `` `' ``, `o.`, `C_`, `<->`, `-.`, `A.`, `E.`, `X_`, `frecs`, mpo.
- **`Finds`** does induction on ω.

None of it is trusted, since every proof it builds goes through the verifiers.

The one-universe `nat-bridge` output is 47 theorems in 89,762 proof steps: 455 KB flat and 50 KB compressed. The tower output adds the two computation rules (6.1 million flat steps, 509 KB compressed with everything else).
