import BoundariesOfClass.ClassNumberFormula.Main
import BoundariesOfClassNegControls.ClassNumberFormula.Sorry
import BoundariesOfClassNegControls.ClassNumberFormula.DecoyOAI
import BoundariesOfClassNegControls.ClassNumberFormula.DecoyClassSum

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.Checks: controls C-CNF1 (axioms) and C-CNF9 (detector fires)

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. Two in-Lean checks, each of which
**fails the build** (`throwError`) if the control does not behave as pre-registered:

* `#cnf_expect_sorryAx n`: `Lean.collectAxioms n` must contain `sorryAx` (C-CNF1, on the `sorry` copy of (U′)).
* `#cnf_expect_axioms_std n`: `Lean.collectAxioms n` must be exactly `{propext, Classical.choice, Quot.sound}` (the real
  (U′), as the matching negative of C-CNF1).
* `#cnf_closure_forbidden n expect`: walks the constant closure of `n` (`getUsedConstantsAsSet`, transitively) and counts
  the constants whose module of origin has root `OAI`, `PrimeNumberTheoremAnd`, `RellichKondrachov` or `HCN`, or lies in
  `BoundariesOfClass.Assembly`. With `expect := clean` the count must be `0` (the real (U′)); with `expect := fires` it
  must be positive (the two decoys, C-CNF9). This is the detector of the CNF manifest probe; the C-CNF9 lines show that
  it fires.

These are supporting checks. The closure audit is the authoritative test; it must report the same outcomes.
-/

set_option autoImplicit false

open Lean Elab Command

namespace BoundariesOfClassNegControls.ClassNumberFormula

/-- The transitive constant closure of `n`. -/
def closureOf (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[n]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      for d in ci.getUsedConstantsAsSet do
        stack := stack.push d
  return seen

/-- The number of closure constants from forbidden modules (T, HCN, the class-sum assembly). -/
def forbiddenCount (env : Environment) (n : Name) : Nat :=
  let roots : List Name := [`OAI, `PrimeNumberTheoremAnd, `RellichKondrachov, `HCN, `BoundariesOfClass.Assembly]
  (closureOf env n).toList.filter (fun c =>
    match env.getModuleIdxFor? c with
    | some idx => roots.any fun p => p.isPrefixOf (env.header.moduleNames[idx.toNat]!)
    | none => false) |>.length

elab "#cnf_closure_forbidden " n:ident " clean" : command => do
  let k := forbiddenCount (← getEnv) n.getId
  if k ≠ 0 then throwError "{n.getId}: expected no forbidden constants, found {k}"
  logInfo m!"{n.getId}: forbidden constants = 0, as expected"

elab "#cnf_closure_forbidden " n:ident " fires" : command => do
  let k := forbiddenCount (← getEnv) n.getId
  if k = 0 then throwError "{n.getId}: the detector did not fire"
  logInfo m!"{n.getId}: forbidden constants = {k} > 0, the detector fires, as expected"

elab "#cnf_expect_sorryAx " n:ident : command => do
  let axs ← liftCoreM (Lean.collectAxioms n.getId)
  if !axs.contains ``sorryAx then throwError "{n.getId}: expected sorryAx, got {axs.toList}"
  logInfo m!"{n.getId}: axioms {axs.toList} contain sorryAx, as expected"

elab "#cnf_expect_axioms_std " n:ident : command => do
  let axs ← liftCoreM (Lean.collectAxioms n.getId)
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  if !(axs.size == 3 && std.all axs.contains) then throwError "{n.getId}: unexpected axioms {axs.toList}"
  logInfo m!"{n.getId}: axioms are exactly propext, Classical.choice, Quot.sound, as expected"

-- C-CNF1
#cnf_expect_sorryAx BoundariesOfClassNegControls.ClassNumberFormula.classNumber_le_sharp_sorry
#cnf_expect_axioms_std BoundariesOfClass.classNumber_le_sharp

-- the real five: clean
#cnf_closure_forbidden BoundariesOfClass.norm_LFunction_one_le clean
#cnf_closure_forbidden BoundariesOfClass.LFunction_one_eq_general clean
#cnf_closure_forbidden BoundariesOfClass.LFunction_one_eq clean
#cnf_closure_forbidden BoundariesOfClass.exists_LFunction_factorisation clean
#cnf_closure_forbidden BoundariesOfClass.classNumber_le_sharp clean

-- C-CNF9: the detector fires on the decoys of C-CNF2 and C-CNF3
#cnf_closure_forbidden BoundariesOfClassNegControls.ClassNumberFormula.classNumber_le_sharp_oaiDecoy fires
#cnf_closure_forbidden BoundariesOfClassNegControls.ClassNumberFormula.classNumber_le_sharp_classSumDecoy fires

end BoundariesOfClassNegControls.ClassNumberFormula
