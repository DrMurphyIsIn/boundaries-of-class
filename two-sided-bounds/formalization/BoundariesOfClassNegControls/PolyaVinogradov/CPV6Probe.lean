import Lean

/-!
# Control C-PV6: the probe command for the duplicate-import diagnostics

`#cpv6_probe n` prints three views of the constant `n`, which can disagree when two imported modules declare `n` with
the same type:

* `origin`: `Environment.getModuleIdxFor?`, the module recorded for `n` (at this pin, the FIRST import's);
* `collectAxioms`: the axioms Lean's `#print axioms` machinery reports (also the FIRST import's);
* `walk`: whether `sorryAx` is reachable from `n` through `Environment.find?`, that is, through the copy the environment
  actually holds (at this pin, the LAST import's), together with the module of the held copy's value as seen by the walk.

Imports only Lean's core, so that it adds no declaration that could itself be duplicated.
-/

open Lean Elab Command

namespace BoundariesOfClassNegControls.PolyaVinogradov.CPV6

/-- The constants reachable from `n` through the environment's held values and types. -/
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

elab "#cpv6_probe " n:ident : command => do
  let env ← getEnv
  let origin := (env.getModuleIdxFor? n.getId).map fun idx => env.header.moduleNames[idx.toNat]!
  let axs ← liftCoreM (collectAxioms n.getId)
  let cl := closureOf env n.getId
  let walkSorry := cl.contains ``sorryAx
  let challengeLoaded := env.header.moduleNames.filter fun mn => (`BoundariesOfClassChallenges).isPrefixOf mn
  logInfo m!"{n.getId}: origin {origin}; collectAxioms {axs.toList}; walk reaches sorryAx: {walkSorry}; \
    challenge modules loaded: {challengeLoaded.toList}"

end BoundariesOfClassNegControls.PolyaVinogradov.CPV6
