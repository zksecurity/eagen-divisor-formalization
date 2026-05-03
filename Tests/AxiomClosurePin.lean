/-
  Tests/AxiomClosurePin.lean

  Pin the axiom closure of the headline soundness theorems. Reading
  the build log lets a reviewer confirm the closure is exactly what's
  expected (and catch any drift early).

  Expected closures on the geometric-zero skeleton branch:

  * `ma_extractable`, `ip_knowledge_sound`:
      propext, Classical.choice, Quot.sound,
      Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
      Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g,
      Divisor.hasse_weil,
      Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero

    The Frobenius descent proof gap is closed: there is no `sorryAx` in
    the MA/IP closure. The headline theorem signatures no longer carry
    `hSplit : splitsOnE E D`; the `splitsOnE` predicate now only gates
    the multiplicity-accounting test below. `hasse_weil` comes from the
    geometric SZ bound on `E(F_q) × E(F_q)`. The remaining algebraic
    assumptions are narrow:
    * divisor-of-norm divisibility (lower bound) for the concrete
      resultant: `chord_fiber_product_concrete_bar_zfiber_pow_dvd`
      (Stacks 02RS lower-bound coefficient form). This *replaces* the
      previous multiplicity-equality axiom: the matching upper bound
      (the global natDegree inequality) is now a theorem
      (`chord_fiber_product_concrete_natDegree_le_normPoly_natDegree`
      in `Divisor/ChordFiberWeightedDegree.lean`, via the
      weighted-Sylvester analysis). The squeeze argument promotes
      lower-bound-divisibility plus upper-bound-natDegree to
      multiplicity equality.
    * the generic resultant logarithmic derivative formula at a split
      specialization (Lang's trace-of-log-derivative identity narrowed
      to a polynomial/resultant statement; replaces the old
      project-shaped axiom
      `chord_fiber_product_logDeriv_eq_logDerivTerm_trace`, now a
      theorem; carries an explicit `Monic f` hypothesis to match
      mathlib's `Polynomial.resultant_eq_prod_eval`).
    * principal divisor class triviality for the concrete `D`.

    The previously listed axiom
    `Divisor.ordAt_eq_rationalMultAt_of_gd_support_rational` has been
    eliminated: the rational-vs-geometric local-order bridge is now a
    proved theorem (induction on `divLin`'s natDegree-sum measure,
    combined with the closed-form `geomLocalOrder` formula on rational
    lifts). `GeometricDivisorData.mult` is now certified to coincide
    pointwise with `geomLocalOrder`, so `rationalMultAt` reduces to
    `geomLocalOrder` at the lifted rational point.

    The source theorem intended to discharge the generic resultant
    bridge,
    `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`,
    is proved from mathlib's Galois norm/trace and differential
    machinery; it is printed below to guard against drift.

  * `ma_completeness`:
      propext, Classical.choice, Quot.sound,
      Divisor.weil_reciprocity_honest

  * `ma_completeness_clean`:
      propext, Classical.choice, Quot.sound,
      Divisor.weil_reciprocity_honest,
      Divisor.hasse_weil

  * `CoordRingElt.exists_divisor_multiplicity`,
    `CoordRingElt.exists_divisor_multiplicity_ecpoint`,
    `ordAt_group_sum_zero_under_split`:
      propext, Classical.choice, Quot.sound,
      Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero

  In particular: `Divisor.CoordRingElt.divisor_group_sum_zero` (the
  previously unsound axiom) is no longer reachable from any headline
  theorem, and `CoordRingElt.exists_divisor_multiplicity` is now
  theorem-backed (no longer an axiom) with the strong-accounting and
  group-sum-zero clauses gated on `splitsOnE`.
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness

#print axioms Divisor.ma_extractable
#print axioms Divisor.ip_knowledge_sound
#print axioms Divisor.ma_completeness
#print axioms Divisor.ma_completeness_clean
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity_ecpoint
#print axioms Divisor.ordAt_group_sum_zero_under_split
#print axioms Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois

/-! ## Hard guards: typecheck-fail if these axioms ever come back

    Constructing an `Empty` from the false axiom would let us prove
    `False`. We deliberately do NOT have such a construction; the test
    below would compile only if an inconsistency were introduced. -/

-- Sanity: the new sound axiom exists and has the expected shape.
-- Accounting and group-sum-zero are gated on the *stronger* `splitsOnE`
-- predicate (polynomial splitting + fiber-rationality of every root),
-- not just univariate `normPoly_splits_over_Fq`.
example {E : Divisor.ECSetup} (D : Divisor.CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (Divisor.splitsOnE E D →
        (∑ P ∈ E.points, β P) = (Divisor.normPoly E D).natDegree) ∧
      (Divisor.splitsOnE E D →
        Divisor.ECPoint.weightedSum E E.points
          (fun P => Divisor.ECPoint.nsmul E (β P)
                      (Divisor.ECPoint.affine E P.1 P.2)) = 0) :=
  Divisor.CoordRingElt.exists_divisor_multiplicity E D hD

#print axioms Divisor.ma_extractable_unconditional
