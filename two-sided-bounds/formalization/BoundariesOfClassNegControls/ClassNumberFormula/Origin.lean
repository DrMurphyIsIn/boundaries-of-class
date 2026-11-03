import BoundariesOfClass.ClassNumberFormula.Main

/-!
# BoundariesOfClassNegControls.ClassNumberFormula.Origin: control C-CNF6 (origin check), and the C-CNF7 stub

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Never imported by the solution. This module imports the solution's
`ClassNumberFormula.Main` and nothing else, so its environment is the CNF solution environment.

* **C-CNF6.** `#cnf_origin_check` fails the build (`throwError`) unless (i) each of the five CNF roots has module of
  origin `BoundariesOfClass.ClassNumberFormula.Main`, and (ii) no imported module has a `Challenges` or `NegControls`
  component in its name. A duplicate import is silent at this pin (the first declaration wins), so the origin check
  replaces the dupImport control.
* **C-CNF7 (stub).** The superseded draft `BoundariesOfClassChallenges/ClassNumberFormula.lean` (`36ba4d75`) is never
  imported together with `BoundaryV2.lean`. That is a rule about the audit and Comparator environments, checked by the
  audit's origin pass in each of them; it has no Lean content here.
-/

set_option autoImplicit false

open Lean Elab Command

namespace BoundariesOfClassNegControls.ClassNumberFormula

elab "#cnf_origin_check" : command => do
  let env ← getEnv
  let roots : List Name := [``BoundariesOfClass.norm_LFunction_one_le, ``BoundariesOfClass.LFunction_one_eq_general,
    ``BoundariesOfClass.LFunction_one_eq, ``BoundariesOfClass.exists_LFunction_factorisation,
    ``BoundariesOfClass.classNumber_le_sharp]
  for r in roots do
    match env.getModuleIdxFor? r with
    | some idx =>
      let mn := env.header.moduleNames[idx.toNat]!
      if mn != `BoundariesOfClass.ClassNumberFormula.Main then
        throwError "{r}: module of origin {mn}, expected BoundariesOfClass.ClassNumberFormula.Main"
    | none => throwError "{r}: not found in an imported module"
  let bad := env.header.moduleNames.toList.filter fun mn =>
    mn.components.any fun c => (c.toString.splitOn "Challenges").length > 1 || (c.toString.splitOn "NegControls").length > 1
  if !bad.isEmpty then throwError "challenge or control modules loaded: {bad}"
  logInfo m!"origin check passed: 5 roots from BoundariesOfClass.ClassNumberFormula.Main; \
    {env.header.moduleNames.size} modules loaded, none a Challenges or NegControls module"

-- C-CNF6
#cnf_origin_check

end BoundariesOfClassNegControls.ClassNumberFormula
