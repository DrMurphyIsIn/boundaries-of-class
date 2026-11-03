import Lake

open System Lake DSL

/-!
Lean project for explicit two-sided bounds on the class number of an imaginary quadratic field, and the class number
boundary that follows from them. `BoundariesOfClassChallenges/BoundaryV2.lean` states the 28 theorems with `sorry`;
`BoundariesOfClass` proves them.

The one dependency is openai/math at the same pinned commit as the class number one and class number two entries
(`../../formalization/`, `../../hcn/formalization/`). It brings Lean v4.34.1, Mathlib `d13f23b` and OpenAI's zero-free
region `Re s > 7/8` for Dirichlet L-functions, whose Lean proof is inside the closure of the lower-bound theorems. Every
other package in `lake-manifest.json` is a dependency of openai/math at the revision openai/math pins, exactly as in
`../../hcn/formalization/lake-manifest.json`.

openai/math ships Lean-v4.34.1 compatibility patches for its dependencies; its lakefile applies them only when it is the
root project, so here they are applied by `scripts/apply_oai_patches.sh` (the class number one entry's script, byte for
byte), which must run once before the first `lake build`. Do not run `lake update`.

The modules `CN1/`, `HCN/` and `HCNChallenges/` are verbatim copies of the same directories of `../../hcn/formalization/`
(release v1.2.0), so that this project builds on its own.
-/

package BoundariesOfClass where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OAI from git
  "https://github.com/openai/math" @ "adc7f1241b42e322a6451854ab7e4b4c146bf78a" / "lean"

/-- The challenge side: the 28 statements with `sorry`, importing Mathlib only. -/
lean_lib BoundariesOfClassChallenges where
  globs := #[`BoundariesOfClassChallenges.+]

/-- Verbatim copy of `../../hcn/formalization/CN1/`. -/
lean_lib CN1 where
  globs := #[`CN1.+]

/-- Verbatim copy of `../../hcn/formalization/HCNChallenges/`; imported by nothing here. -/
lean_lib HCNChallenges where
  globs := #[`HCNChallenges.+]

/-- Verbatim copy of `../../hcn/formalization/HCN/`. -/
lean_lib HCN where
  globs := #[`HCN.+]

/-- The solution side. Imports no challenge module and no negative control. -/
@[default_target]
lean_lib BoundariesOfClass where
  globs := #[`BoundariesOfClass.+]

/-- Negative controls: tampered statements and kernel-checked refutations. Outside `BoundariesOfClass`, and never
imported by it. Never import a module of this library together with the solution's main module. -/
lean_lib BoundariesOfClassNegControls where
  globs := #[`BoundariesOfClassNegControls.+]
