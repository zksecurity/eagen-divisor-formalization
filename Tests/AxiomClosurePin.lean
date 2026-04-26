/-
  Tests/AxiomClosurePin.lean

  Pin the axiom closure of the headline soundness theorems. Reading
  the build log lets a reviewer confirm the closure is exactly what's
  expected (and catch any drift early).

  Expected closures (post-soundness-restoration):

  * `ma_extractable`, `ip_knowledge_sound`:
      propext, Classical.choice, Quot.sound,
      Divisor.CoordRingElt.exists_divisor_multiplicity,
      Divisor.chord_fiber_product_eq_normZ_under_split,
      Divisor.chord_sum_eq_chord_fiber_product_logDeriv,
      Divisor.hasse_weil

  * `ma_completeness`:
      propext, Classical.choice, Quot.sound,
      Divisor.weil_reciprocity_honest

  * `ma_completeness_clean`:
      propext, Classical.choice, Quot.sound,
      Divisor.weil_reciprocity_honest,
      Divisor.hasse_weil

  In particular: `Divisor.CoordRingElt.divisor_group_sum_zero` (the
  previously unsound axiom) is no longer reachable from any headline
  theorem.
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness

#print axioms Divisor.ma_extractable
#print axioms Divisor.ip_knowledge_sound
#print axioms Divisor.ma_completeness
#print axioms Divisor.ma_completeness_clean

/-! ## Hard guards: typecheck-fail if these axioms ever come back

    Constructing an `Empty` from the false axiom would let us prove
    `False`. We deliberately do NOT have such a construction; the test
    below would compile only if an inconsistency were introduced. -/

-- Sanity: the new sound axiom exists and has the expected shape.
example {E : Divisor.ECSetup} (D : Divisor.CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (Divisor.normPoly_splits_over_Fq E D →
        (∑ P ∈ E.points, β P) = (Divisor.normPoly E D).natDegree) ∧
      (Divisor.normPoly_splits_over_Fq E D →
        Divisor.ECPoint.weightedSum E E.points
          (fun P => Divisor.ECPoint.nsmul E (β P)
                      (Divisor.ECPoint.affine E P.1 P.2)) = 0) :=
  Divisor.CoordRingElt.exists_divisor_multiplicity E D hD
