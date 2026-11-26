/-
Lists the declarations a module itself declares, one name per line, sorted, for `tenet-zfc run`.
Run with `lean --run ModuleDecls.lean <Module> [--all]`, with LEAN_PATH reaching the module's .olean.
Without --all, it leaves out what Lean generates around a declaration: internal details (matchers, auxiliary proofs),
auxiliary recursors (casesOn, recOn, brecOn, below), no-confusion principles, and the other helpers below.
-/
import Lean.AuxRecursor
import Lean.Util.Path
open Lean

def generated : List String :=
  ["noConfusionType", "ctorElimType", "ctorElim", "ctorIdx", "toCtorIdx", "sizeOf_spec", "injEq", "inj", "eq_def"]

def main (args : List String) : IO UInt32 := do
  let some m := args.head? | IO.eprintln "usage: lean --run ModuleDecls.lean <Module> [--all]"; return 2
  let all := args.contains "--all"
  let mod := m.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := mod }] {}
  let some idx := env.getModuleIdx? mod | IO.eprintln s!"module {mod} not found"; return 1
  let mut names : Array String := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n != some idx then continue
    let last := match n with | .str _ s => s | _ => ""
    if !all && (n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || generated.contains last) then continue
    names := names.push n.toString
  for n in names.qsort (· < ·) do IO.println n
  return 0
