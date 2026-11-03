import BoundariesOfClassNegControls.PolyaVinogradov.CPV2OAIDecoy
import BoundariesOfClassNegControls.PolyaVinogradov.CPV3ModuleDecoy

/-!
# Control C-PV8: the manifest detector run on the decoys

The closure walk run on the decoys of C-PV2 and C-PV3, and on the real Pólya–Vinogradov headline P1. Expected: the C-PV2
decoy reports a count of constants from OAI/PNT+/RK/HCN modules > 0, and OAI modules in its module set; the C-PV3 decoy
reports CN1.Foundations modules in its module set, which P1's frozen set excludes; the real P1 reports 0 and no CN1 or
OAI module. The walk follows `Environment.find?`, so it sees the copy of each constant that the environment holds.
-/

open Lean Elab Command

namespace BoundariesOfClassNegControls.PolyaVinogradov.CPV8

/-- The constants reachable from `n` through the values and types the environment holds. -/
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

elab "#cpv8_detect " n:ident : command => do
  let env ← getEnv
  let cl := closureOf env n.getId
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map fun idx => env.header.moduleNames[idx.toNat]!
  let modBad := cl.toList.filter fun c => match modOf c with
    | some mn => [`OAI, `PrimeNumberTheoremAnd, `RellichKondrachov, `HCN].any fun p => p.isPrefixOf mn
    | none => false
  let base : List Name := [`Init, `Std, `Lean, `Batteries, `Mathlib]
  let mods : NameSet := cl.toList.foldl (fun s c => match modOf c with
    | some mn => if base.any (·.isPrefixOf mn) then s else s.insert mn
    | none => s) {}
  let modList := mods.toList.map toString |>.toArray.qsort (· < ·)
  let cn1 := modList.filter (·.startsWith "CN1.")
  let oai := modList.filter (·.startsWith "OAI")
  logInfo m!"{n.getId}: {cl.size} constants; constants from OAI/PNT+/RK/HCN modules: {modBad.length}; \
    module count {modList.size}; OAI modules: {oai.size}; CN1 modules: {cn1}"

end BoundariesOfClassNegControls.PolyaVinogradov.CPV8

#cpv8_detect BoundariesOfClassNegControls.PolyaVinogradov.decoy_oai_norm_sum_le_of_isPrimitive
#cpv8_detect BoundariesOfClassNegControls.PolyaVinogradov.decoy_cn1_norm_sum_le_of_isPrimitive
#cpv8_detect BoundariesOfClass.norm_sum_le_of_isPrimitive
