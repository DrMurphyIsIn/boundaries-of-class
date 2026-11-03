import BoundariesOfClassNegControls.PolyaVinogradov.CPV6Probe
import BoundariesOfClass.PolyaVinogradov.ClassNumber
import BoundariesOfClass.Primitivity.Field
import BoundariesOfClassChallenges.BoundaryV2

/-!
# Control C-PV6, diagnostic B: solution imported FIRST, then the challenge (THE DANGEROUS ORDER)

The solution and the challenge module are imported together, solution first. At this pin a same-type duplicate is
imported silently: the environment holds the LAST copy (the challenge's `sorry` version), while `getModuleIdxFor?` and
`collectAxioms` report the FIRST (the solution's).

Expected, for each of the six roots P1–P6: origin = the solution module; collectAxioms gives the standard three axioms
without `sorryAx`; but the walk DOES reach `sorryAx`. So the origin check and `#print axioms` look clean while the
environment holds the challenge's `sorry` terms. Only the closure walk, the duplicate-declaration scan and the
forbidden-import rule (the challenge module is loaded) catch it.

The origin check alone misses this order.
-/

#cpv6_probe BoundariesOfClass.norm_sum_le_of_isPrimitive
#cpv6_probe BoundariesOfClass.norm_LFunction_one_le_of_isPrimitive
#cpv6_probe BoundariesOfClass.norm_LFunction_one_le_loglog
#cpv6_probe BoundariesOfClass.classNumber_le_half_log
#cpv6_probe BoundariesOfClass.classNumber_le_loglog
#cpv6_probe BoundariesOfClass.isPrimitive_of_factorisation
