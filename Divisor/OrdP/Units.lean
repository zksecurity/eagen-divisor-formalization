/-
  Divisor/OrdP/Units.lean — exact divisor arithmetic on the coordinate ring.

  * `toCoordinateRing_mul`, `_smul`, `_injective`: the transport
    `CoordRingElt → F_q[E]` is a multiplicative injection compatible
    with scalars.
  * `ordAt_mul`: `ordAt` is additive under products at every rational
    point, with no root-multiplicity side conditions (via the
    point-prime valuation).
  * `isUnit_coordinateRing`: the units of `F_q[E]` are the nonzero
    constants.
  * `eq_smul_of_ordAt_eq`: two nonzero elements that split over `E`
    and have the same order at every rational point differ by a
    nonzero scalar. An honest prover message is therefore unique up
    to scaling.
-/
import Divisor.OrdP.SupportClassification
import Divisor.IncrementalConstruction

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace Divisor

variable (E : ECSetup)

theorem toCoordinateRing_mul (D₁ D₂ : CoordRingElt E.q) :
    (mulCoordRingElt E D₁ D₂).toCoordinateRing E =
      D₁.toCoordinateRing E * D₂.toCoordinateRing E := by
  unfold CoordRingElt.toCoordinateRing CoordRingElt.toBivar mulCoordRingElt
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  refine ⟨-Polynomial.C (D₁.b * D₂.b), ?_⟩
  rw [toW_polynomial]
  simp only [Polynomial.C_add, Polynomial.C_mul]
  ring

theorem mulCoordRingElt_ne_zero (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0)) :
    ¬ ((mulCoordRingElt E D₁ D₂).a = 0 ∧ (mulCoordRingElt E D₁ D₂).b = 0) := by
  intro h
  have h0 : (mulCoordRingElt E D₁ D₂).toCoordinateRing E = 0 := by
    rw [CoordRingElt.toCoordinateRing_eq_smul_basis, h.1, h.2]; simp
  rw [toCoordinateRing_mul] at h0
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact CoordRingElt.toCoordinateRing_ne_zero E D₁ h₁ h0
  · exact CoordRingElt.toCoordinateRing_ne_zero E D₂ h₂ h0

/-- **Unconditional** additivity of `ordAt` under products (no root-multiplicity caps). -/
theorem ordAt_mul (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    ordAt E (mulCoordRingElt E D₁ D₂) P = ordAt E D₁ P + ordAt E D₂ P := by
  have h := pointPrime_intValuation_toCoordinateRing E (mulCoordRingElt E D₁ D₂) hP
    (mulCoordRingElt_ne_zero E D₁ D₂ h₁ h₂)
  rw [toCoordinateRing_mul, map_mul, pointPrime_intValuation_toCoordinateRing E D₁ hP h₁,
    pointPrime_intValuation_toCoordinateRing E D₂ hP h₂, ← WithZero.exp_add,
    WithZero.exp_inj] at h
  omega

/-! ## Uniqueness up to scalar -/

theorem toCoordinateRing_smul (c : ZMod E.q) (D : CoordRingElt E.q) :
    (c • D).toCoordinateRing E =
      algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing (Polynomial.C c) *
        D.toCoordinateRing E := by
  rw [CoordRingElt.toCoordinateRing_eq_smul_basis, CoordRingElt.toCoordinateRing_eq_smul_basis,
    CoordRingElt.smul_a, CoordRingElt.smul_b, mul_add, ← Algebra.smul_def,
    ← Algebra.smul_def, smul_smul, smul_smul, Polynomial.smul_eq_C_mul,
    Polynomial.smul_eq_C_mul, mul_neg]

/-- Units of the coordinate ring are nonzero constants. -/
theorem isUnit_coordinateRing (u : E.toW.toAffine.CoordinateRing) (hu : IsUnit u) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      u = algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing (Polynomial.C c) := by
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq u
  set D : CoordRingElt E.q := ⟨p, -q⟩
  have hD : D.toCoordinateRing E = u := by
    rw [CoordRingElt.toCoordinateRing_eq_smul_basis, ← hpq]; simp [D]
  have hN : IsUnit (normPoly E D) := by
    rw [← norm_toCoordinateRing_eq_normPoly, hD]; exact hu.map _
  have hdeg : D.degE = 0 := by
    rw [← normPoly_natDegree_eq]; exact Polynomial.natDegree_eq_zero_of_isUnit hN
  have ha : D.a.natDegree = 0 := by have := D.two_a_le_degE; omega
  have hb : D.b = 0 := by
    by_contra hb; have := CoordRingElt.three_add_two_b_le_degE hb; omega
  refine ⟨D.a.coeff 0, ?_, ?_⟩
  · intro h0
    have : D.a = 0 := by rw [Polynomial.eq_C_of_natDegree_eq_zero ha, h0, map_zero]
    apply hu.ne_zero
    rw [← hD, CoordRingElt.toCoordinateRing_eq_smul_basis, this, hb]; simp
  · rw [← hD, CoordRingElt.toCoordinateRing_eq_smul_basis, hb, neg_zero, zero_smul, add_zero,
      Algebra.smul_def, mul_one, ← Polynomial.eq_C_of_natDegree_eq_zero ha]

theorem toCoordinateRing_injective {D₁ D₂ : CoordRingElt E.q}
    (h : D₁.toCoordinateRing E = D₂.toCoordinateRing E) : D₁ = D₂ := by
  rw [CoordRingElt.toCoordinateRing_eq_smul_basis,
    CoordRingElt.toCoordinateRing_eq_smul_basis, ← sub_eq_zero] at h
  have h' : (D₁.a - D₂.a) • (1 : E.toW.toAffine.CoordinateRing) +
      (-D₁.b - -D₂.b) • CoordinateRing.mk E.toW.toAffine Polynomial.X = 0 := by
    rw [← h, sub_smul, sub_smul]; abel
  obtain ⟨ha, hb⟩ := CoordinateRing.smul_basis_eq_zero h'
  cases D₁; cases D₂
  simp only [CoordRingElt.mk.injEq]
  exact ⟨sub_eq_zero.mp ha, by linear_combination -hb⟩

/-- **Honest `D` is unique up to a nonzero scalar.** -/
theorem eq_smul_of_ordAt_eq (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hs₁ : splitsOnE E D₁) (hs₂ : splitsOnE E D₂)
    (hord : ∀ P ∈ E.points, ordAt E D₁ P = ordAt E D₂ P) :
    ∃ c : ZMod E.q, c ≠ 0 ∧ D₁ = c • D₂ := by
  have hspan : Ideal.span {D₁.toCoordinateRing E} = Ideal.span {D₂.toCoordinateRing E} := by
    rw [span_toCoordinateRing_eq_prod E D₁ h₁ hs₁, span_toCoordinateRing_eq_prod E D₂ h₂ hs₂]
    exact Finset.prod_congr rfl fun P _ => by rw [hord P.1 P.2]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  obtain ⟨c, hc, hcu⟩ := isUnit_coordinateRing E u u.isUnit
  refine ⟨c⁻¹, inv_ne_zero hc, toCoordinateRing_injective E ?_⟩
  rw [toCoordinateRing_smul, ← hu, hcu, mul_comm, mul_assoc, ← map_mul, ← Polynomial.C_mul,
    mul_inv_cancel₀ hc, Polynomial.C_1, map_one, mul_one]

end Divisor
