/-
  Divisor/OrdP/ValuationBridgeOrd.lean — the `ordAt` valuation
  bridge over `ZMod E.q`.

  Main results:

  * `pointPrime_intValuation_toCoordinateRing`:
    `v_P(D) = exp(−ordAt E D P)` for every `P ∈ E.points` and nonzero
    `D` — the project's recursive/closed-form `ordAt` computes the
    `HeightOneSpectrum.intValuation` at the point prime.
  * `multiplicity_pointPrime_eq_ordAt` and
    `count_pointPrime_eq_ordAt`: the same statement in the
    `multiplicity` and `Associates.count` normal forms (the latter is
    what `Ideal.finprod_heightOneSpectrum_factorization` consumes in
    Phase 2).

  The induction mirrors the fuel recursion of
  `Divisor/OrdP/Uniformizer.lean`: the non-vanishing case is
  valuation-one, the lone case is the norm identity, the twin case
  peels one factor of `X − x₀` (`toCoordinateRing_divLin_of_twin`)
  with the fuel bound maintained by the degree drop of `divLin`.
-/
import Divisor.OrdP.ValuationBridge

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WithZero Multiplicative IsDedekindDomain

namespace Divisor

variable (E : ECSetup)

/-! ## Twin vanishing and `divLin` exactness -/

/-- Vanishing on both sheets at non-2-torsion `x₀` forces both
components to vanish at `x₀` (char ≠ 2). -/
theorem eval_a_b_zero_of_twin {D : CoordRingElt E.q} {x₀ y₀ : ZMod E.q}
    (hy : y₀ ≠ 0) (h1 : D.eval x₀ y₀ = 0) (h2 : D.eval x₀ (-y₀) = 0) :
    D.a.eval x₀ = 0 ∧ D.b.eval x₀ = 0 := by
  unfold CoordRingElt.eval at h1 h2
  have ha : D.a.eval x₀ = 0 := by
    have h2a : (2 : ZMod E.q) * D.a.eval x₀ = 0 := by linear_combination h1 + h2
    exact (mul_eq_zero.mp h2a).resolve_left (two_ne_zero_zmod E)
  refine ⟨ha, ?_⟩
  have hb : D.b.eval x₀ * y₀ = 0 := by linear_combination ha - h1
  exact (mul_eq_zero.mp hb).resolve_right hy

/-- **Twin-case exactness**: if both components vanish at `x₀` then
`D = (X − x₀) · D'` in the coordinate ring, with `D' = D.divLin x₀`. -/
theorem toCoordinateRing_divLin_of_twin (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (ha0 : D.a.eval x₀ = 0) (hb0 : D.b.eval x₀ = 0) :
    D.toCoordinateRing E =
      CoordinateRing.XClass E.toW.toAffine x₀ *
        ((D.divLin x₀).toCoordinateRing E) := by
  have ha : (Polynomial.X - Polynomial.C x₀) *
      (D.a /ₘ (Polynomial.X - Polynomial.C x₀)) = D.a :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha0
  have hb : (Polynomial.X - Polynomial.C x₀) *
      (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) = D.b :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hb0
  unfold CoordRingElt.toCoordinateRing CoordinateRing.XClass
  rw [← map_mul]
  congr 1
  show D.toBivar = _
  have hbiv : D.toBivar =
      Polynomial.C (Polynomial.X - Polynomial.C x₀) * (D.divLin x₀).toBivar := by
    unfold CoordRingElt.toBivar
    rw [CoordRingElt.divLin_a, CoordRingElt.divLin_b]
    conv_lhs => rw [← ha, ← hb]
    simp only [Polynomial.C_mul]
    ring
  exact hbiv

/-- `divLin` of a nonzero twin-vanishing `D` is nonzero. -/
theorem divLin_ne_zero_of_twin {D : CoordRingElt E.q} {x₀ : ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (ha0 : D.a.eval x₀ = 0) (hb0 : D.b.eval x₀ = 0) :
    ¬ ((D.divLin x₀).a = 0 ∧ (D.divLin x₀).b = 0) := by
  rintro ⟨ha', hb'⟩
  apply hD
  rw [CoordRingElt.divLin_a] at ha'
  rw [CoordRingElt.divLin_b] at hb'
  constructor
  · rw [← Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha0, ha', mul_zero]
  · rw [← Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hb0, hb', mul_zero]

/-- A nonzero polynomial vanishing at `x₀` has positive degree. -/
private theorem one_le_natDegree_of_root {p : (ZMod E.q)[X]} {x₀ : ZMod E.q}
    (hp : p ≠ 0) (h0 : p.eval x₀ = 0) : 1 ≤ p.natDegree := by
  have hdvd : (Polynomial.X - Polynomial.C x₀) ∣ p :=
    Polynomial.dvd_iff_isRoot.mpr h0
  calc 1 = (Polynomial.X - Polynomial.C x₀).natDegree :=
        (Polynomial.natDegree_X_sub_C x₀).symm
    _ ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hdvd hp

/-- The degree budget strictly drops under `divLin` in the twin case.
(Private: `Divisor/OrdP/LocalRing.lean` exports the strict-`<` form
under the name `divLin_natDegree_sum_lt`.) -/
private theorem divLin_natDegree_budget {D : CoordRingElt E.q} {x₀ : ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (ha0 : D.a.eval x₀ = 0) (hb0 : D.b.eval x₀ = 0) :
    (D.divLin x₀).a.natDegree + (D.divLin x₀).b.natDegree + 1 ≤
      D.a.natDegree + D.b.natDegree := by
  rw [CoordRingElt.divLin_a, CoordRingElt.divLin_b]
  have hmono : (Polynomial.X - Polynomial.C x₀).Monic :=
    Polynomial.monic_X_sub_C x₀
  by_cases ha : D.a = 0
  · have hb : D.b ≠ 0 := fun h => hD ⟨ha, h⟩
    rw [ha, Polynomial.zero_divByMonic,
      Polynomial.natDegree_divByMonic D.b hmono, Polynomial.natDegree_X_sub_C]
    have := one_le_natDegree_of_root E hb hb0
    simp only [Polynomial.natDegree_zero]
    omega
  · by_cases hb : D.b = 0
    · rw [hb, Polynomial.zero_divByMonic,
        Polynomial.natDegree_divByMonic D.a hmono, Polynomial.natDegree_X_sub_C]
      have := one_le_natDegree_of_root E ha ha0
      simp only [Polynomial.natDegree_zero]
      omega
    · rw [Polynomial.natDegree_divByMonic D.a hmono,
        Polynomial.natDegree_divByMonic D.b hmono, Polynomial.natDegree_X_sub_C]
      have h1 := one_le_natDegree_of_root E ha ha0
      have h2 := one_le_natDegree_of_root E hb hb0
      omega

/-! ## The non-2-torsion bridge, by induction on fuel -/

/-- The recursion of `ordAt_nonTwoTorsion_aux` computes the
`intValuation` at the point prime, given enough fuel. -/
theorem pointPrime_intValuation_nonTwoTorsion_aux (fuel : ℕ)
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hy : P.2 ≠ 0) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hfuel : D.a.natDegree + D.b.natDegree + 1 ≤ fuel) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-(ordAt_nonTwoTorsion_aux E fuel D P : ℤ)) := by
  classical
  induction fuel generalizing D with
  | zero => omega
  | succ n IH =>
    show (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-((if D.a = 0 ∧ D.b = 0 then 0
        else if D.eval P.1 P.2 ≠ 0 then 0
        else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
        else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P : ℕ) : ℤ))
    rw [if_neg hD]
    by_cases hvan : D.eval P.1 P.2 = 0
    · rw [if_neg (not_not.mpr hvan)]
      by_cases hlone : D.eval P.1 (-P.2) ≠ 0
      · rw [if_pos hlone]
        exact pointPrime_intValuation_of_lone E D hP hy hlone
      · rw [if_neg hlone]
        rw [not_not] at hlone
        obtain ⟨ha0, hb0⟩ := eval_a_b_zero_of_twin E hy hvan hlone
        have hD' := divLin_ne_zero_of_twin E hD ha0 hb0
        have hdrop := divLin_natDegree_budget E hD ha0 hb0
        rw [toCoordinateRing_divLin_of_twin E D ha0 hb0, map_mul,
          pointPrime_intValuation_XClass_of_ne_zero E hP hy,
          IH (D.divLin P.1) hD' (by omega), ← exp_add]
        congr 1
        push_cast
        ring
    · rw [if_pos hvan]
      have h1 : (E.pointPrime hP).intValuation (D.toCoordinateRing E) = 1 :=
        (pointPrime_intValuation_eq_one_iff E D hP).mpr hvan
      rw [h1]
      norm_num

/-- **Non-2-torsion bridge**: `v_P(D) = exp(−ordAt_nonTwoTorsion E D P)`. -/
theorem pointPrime_intValuation_nonTwoTorsion (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hy : P.2 ≠ 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-(ordAt_nonTwoTorsion E D P : ℤ)) :=
  pointPrime_intValuation_nonTwoTorsion_aux E _ D hP hy hD le_rfl

/-! ## The headline bridge and its count forms -/

/-- **The valuation bridge** (`ZMod` side): for
`P ∈ E.points` and `D ≠ 0`, the project's recursive `ordAt` computes
the `v_P`-adic valuation: `v_P(D) = exp(−ordAt E D P)`. -/
theorem pointPrime_intValuation_toCoordinateRing (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-(ordAt E D P : ℤ)) := by
  rw [ordAt_eq_dispatch E D hP hD]
  by_cases hy : P.2 = 0
  · rw [if_pos hy]
    exact pointPrime_intValuation_twoTorsion E D hP hy hD
  · rw [if_neg hy]
    exact pointPrime_intValuation_nonTwoTorsion E D hP hy hD

/-- The bridge in `multiplicity` form: `ordAt E D P` is the exact power
of the point prime dividing `span {D}`. -/
theorem multiplicity_pointPrime_eq_ordAt (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    multiplicity (E.pointPrime hP).asIdeal
      (Ideal.span {D.toCoordinateRing E}) = ordAt E D P := by
  have h := pointPrime_intValuation_toCoordinateRing E D hP hD
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _
    (CoordRingElt.toCoordinateRing_ne_zero E D hD)] at h
  rw [exp_inj, neg_inj] at h
  exact_mod_cast h

/-- The bridge in `Associates.count` form — the exponent that
`Ideal.finprod_heightOneSpectrum_factorization` reads off
(`maxPowDividing`), for Phase 2. -/
theorem count_pointPrime_eq_ordAt (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (Associates.mk (E.pointPrime hP).asIdeal).count
      (Associates.mk (Ideal.span {D.toCoordinateRing E})).factors =
      ordAt E D P := by
  have h := pointPrime_intValuation_toCoordinateRing E D hP hD
  rw [HeightOneSpectrum.intValuation_if_neg _
    (CoordRingElt.toCoordinateRing_ne_zero E D hD)] at h
  rw [exp_inj, neg_inj] at h
  exact_mod_cast h

end Divisor
