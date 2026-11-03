import BoundariesOfClassNegControls.PolyaVinogradov.CPV6Probe
import BoundariesOfClassChallenges.BoundaryV2
import BoundariesOfClass.PolyaVinogradov.ClassNumber
import BoundariesOfClass.Primitivity.Field

/-!
# Control C-PV6, diagnostic A: challenge imported FIRST, then the solution

The challenge module and the solution are imported together, challenge first. At this pin a same-type duplicate is
imported silently: the environment holds the LAST copy (the solution's), while `getModuleIdxFor?` and `collectAxioms`
report the FIRST (the challenge's).

Expected, for each of the six roots P1–P6: origin = the challenge module; collectAxioms contains `sorryAx`; the walk
does NOT reach `sorryAx`. So `axioms_consistent` fails, and the origin check flags it. The challenge module is loaded,
so the forbidden-import rule also flags it.

This is the less dangerous order: the origin check alone catches it.
-/

#cpv6_probe BoundariesOfClass.norm_sum_le_of_isPrimitive
#cpv6_probe BoundariesOfClass.norm_LFunction_one_le_of_isPrimitive
#cpv6_probe BoundariesOfClass.norm_LFunction_one_le_loglog
#cpv6_probe BoundariesOfClass.classNumber_le_half_log
#cpv6_probe BoundariesOfClass.classNumber_le_loglog
#cpv6_probe BoundariesOfClass.isPrimitive_of_factorisation
