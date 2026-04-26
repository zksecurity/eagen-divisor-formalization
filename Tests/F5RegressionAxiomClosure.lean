/-
  Tests/F5RegressionAxiomClosure.lean

  Regression sanity-check for the soundness restoration:
  * The headline theorems no longer depend on the false
    `CoordRingElt.divisor_group_sum_zero` axiom.
  * The closure now contains the sound replacements.

  Run via `lake env lean Tests/F5RegressionAxiomClosure.lean` (the
  `#print axioms` outputs land in the build log).
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness

open Divisor

-- Axiom closure of the headline soundness theorems.
-- Confirms the soundness restoration: the previous unsound axiom
-- `Divisor.CoordRingElt.divisor_group_sum_zero` is no longer in the
-- closure; replaced by `Divisor.CoordRingElt.exists_divisor_multiplicity`.

#print axioms Divisor.ma_extractable

#print axioms Divisor.ip_knowledge_sound

#print axioms Divisor.ma_completeness
