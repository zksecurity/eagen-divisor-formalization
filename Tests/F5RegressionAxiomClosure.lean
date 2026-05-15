/-
  Tests/F5RegressionAxiomClosure.lean

  Regression sanity-check for the soundness restoration:
  * The headline theorems no longer depend on the false
    `CoordRingElt.divisor_group_sum_zero` axiom.
  * On the geometric-zero skeleton branch, the MA/IP closures are
    sorry-free and expose the current named geometric/class-group
    obligations directly.

  Run via `lake env lean Tests/F5RegressionAxiomClosure.lean` (the
  `#print axioms` outputs land in the build log).
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness

open Divisor

-- Axiom closure of the headline soundness/completeness theorems.
-- Confirms the soundness restoration: the previous unsound axiom
-- `Divisor.CoordRingElt.divisor_group_sum_zero` is no longer in the
-- closure of the headline theorem.

#print axioms Divisor.ma_extractable

#print axioms Divisor.ip_extractable

#print axioms Divisor.ma_completeness

-- Raw point-count-dependent base forms remain available under `_base`.
#print axioms Divisor.ma_extractable_base

#print axioms Divisor.ip_extractable_base

#print axioms Divisor.ma_completeness_base
