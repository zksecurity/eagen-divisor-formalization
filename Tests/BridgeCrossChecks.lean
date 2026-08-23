/-
  Tests/BridgeCrossChecks.lean — valuation-bridge sanity tests.

  The two accounting identities

  * `sum_ordAt_eq_natDegree_under_split`
      (`Σ_{P ∈ E.points} ordAt E D P = (normPoly E D).natDegree`
       under `splitsOnE`), and
  * `geomLocalOrder_fiber_accounting`
      (`Σ_{Q.x = α} geomLocalOrder E D Q = rootMult α (normPolyBar E D)`
       for the exact geometric zero set)

  must be derivable from the valuation bridge itself — they serve as
  sanity tests here, not inputs. The production proofs are combinatorial
  (fuel induction on `divLin` / closed-formula case analysis) and
  predate the valuation bridge. This file DERIVES both statements
  again, from the bridge alone:

  * the headline bridge theorems
    `pointPrime_intValuation_toCoordinateRing` (`v_P(D) = exp(−ordAt)`)
    and `geomPointPrime_intValuation_toBar`
    (`v_Q(D̄) = exp(−geomLocalOrder)`);
  * the conjugation-product valuation identities
    (`toCoordinateRing_mul_conjElt` + `pointPrime_intValuation_mk_C`,
    `geomPointPrime_intValuation_mul_conj`);
  * a valuation-transport lemma along the coordinate-ring conjugation
    involution (vendored Tau Ceti `conj`), which maps the point prime
    of `(x, y)` to the point prime of `(x, −y)`.

  The two original theorems are cited NOWHERE in this file (only their
  statements are mirrored); DVR additivity of the valuation under the
  norm factorisation `D·σD = N(D)` does the accounting, which is the
  textbook derivation. Names carry the `_via_bridge` suffix; the
  statements are verbatim copies of the originals.
-/
import Divisor.OrdP.ValuationBridgeOrd
import Divisor.OrdP.GeomValuationBridge
import Divisor.SplitsOnE

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero Classical
open IsDedekindDomain
open TauCeti.WeierstrassCurve.Affine.CoordinateRing (conj conj_mk_C conj_mk_Y)
open scoped Polynomial.Bivariate

namespace Divisor

/-! ## Valuation transport along a ring automorphism -/

/-- If a ring automorphism `e` of a Dedekind domain maps the height-one
prime `w` onto the height-one prime `v`, then `v(e z) = w(z)`. -/
private theorem intValuation_map_ringEquiv {A : Type*} [CommRing A]
    [IsDedekindDomain A] (e : A ≃+* A)
    (v w : HeightOneSpectrum A)
    (h : Ideal.map (e : A →+* A) w.asIdeal = v.asIdeal) (z : A) :
    v.intValuation (e z) = w.intValuation z := by
  by_cases hz : z = 0
  · subst hz
    simp only [map_zero]
  · have hez : e z ≠ 0 := fun h0 => hz (by simpa using congrArg e.symm h0)
    -- membership transfers through the automorphism at every power
    have hmemJ : ∀ (J : Ideal A) (x : A),
        e x ∈ J.map (e : A →+* A) ↔ x ∈ J := by
      intro J x
      constructor
      · intro hx
        have h2 := Ideal.mem_map_of_mem (e.symm : A →+* A) hx
        rw [Ideal.map_map,
          show ((e.symm : A →+* A).comp (e : A →+* A)) = RingHom.id A by
            ext t; simp,
          Ideal.map_id] at h2
        simpa using h2
      · exact fun hx => Ideal.mem_map_of_mem _ hx
    have hmem : ∀ n : ℕ, (e z ∈ v.asIdeal ^ n ↔ z ∈ w.asIdeal ^ n) := by
      intro n
      rw [← h, ← Ideal.map_pow]
      exact hmemJ _ z
    -- both values are `exp` of a nonpositive integer
    have hform : ∀ u : ℤᵐ⁰, u ≠ 0 → u ≤ 1 → ∃ n : ℕ, u = exp (-(n : ℤ)) := by
      intro u hu0 hu1
      refine ⟨(-(log u)).toNat, ?_⟩
      have hlog : log u ≤ 0 := by
        rw [← exp_log hu0, show (1 : ℤᵐ⁰) = exp 0 from exp_zero.symm,
          exp_le_exp] at hu1
        exact hu1
      rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log hu0]
    obtain ⟨m, hm⟩ := hform _ (v.intValuation_ne_zero (e z) hez)
      (v.intValuation_le_one (e z))
    obtain ⟨k, hk⟩ := hform _ (w.intValuation_ne_zero z hz)
      (w.intValuation_le_one z)
    -- the membership grids coincide, so the exponents coincide
    have hiff : ∀ n : ℕ,
        (exp (-(m : ℤ)) : ℤᵐ⁰) ≤ exp (-(n : ℤ)) ↔
        (exp (-(k : ℤ)) : ℤᵐ⁰) ≤ exp (-(n : ℤ)) := by
      intro n
      rw [← hm, ← hk, v.intValuation_le_pow_iff_mem,
        w.intValuation_le_pow_iff_mem]
      exact hmem n
    have h1 := (hiff k).mpr le_rfl
    have h2 := (hiff m).mp le_rfl
    rw [exp_le_exp] at h1 h2
    rw [hm, hk, exp_inj]
    omega

/-! ## The conjugation involution on point data

The vendored Tau Ceti `conj` is the coordinate-ring form of
`(x, y) ↦ (x, −y)` on a short-Weierstrass curve (`a₁ = a₃ = 0`):
it fixes constants, negates `y`, and maps the point ideal of `(x, y)`
to the point ideal of `(x, −y)`. -/

section ConjGeneric

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

private theorem mk_negPolynomial (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    CoordinateRing.mk W W.negPolynomial =
      -(CoordinateRing.mk W Y) := by
  rw [WeierstrassCurve.Affine.negPolynomial, h₁, h₃]
  rw [show (-(Y : R[X][Y]) - Polynomial.C (Polynomial.C 0 * X + Polynomial.C 0))
    = -(Y : R[X][Y]) from by simp]
  rw [map_neg]

private theorem conj_mk_Y' (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    conj W (CoordinateRing.mk W Y) = -(CoordinateRing.mk W Y) := by
  rw [show CoordinateRing.mk W Y = AdjoinRoot.root W.polynomial from
    AdjoinRoot.mk_X, conj_mk_Y, mk_negPolynomial W h₁ h₃]
  exact congrArg Neg.neg AdjoinRoot.mk_X

private theorem conj_mk_CC (p : R[X]) :
    conj W (CoordinateRing.mk W (Polynomial.C p)) =
      CoordinateRing.mk W (Polynomial.C p) :=
  conj_mk_C W p

/-- `conj` on the class of a line `a − b·y`: negate `b`. -/
private theorem conj_mk_line (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0)
    (a b : R[X]) :
    conj W (CoordinateRing.mk W (Polynomial.C a - Polynomial.C b * Y)) =
      CoordinateRing.mk W (Polynomial.C a - Polynomial.C (-b) * Y) := by
  rw [map_sub, map_mul, map_sub, map_mul, conj_mk_CC, conj_mk_CC,
    conj_mk_Y' W h₁ h₃]
  rw [show (Polynomial.C a - Polynomial.C (-b) * Y : R[X][Y]) =
    Polynomial.C a + Polynomial.C b * Y from by
      rw [Polynomial.C_neg]; ring]
  rw [map_add, map_mul]
  ring

private theorem conj_XClass (x : R) :
    conj W (CoordinateRing.XClass W x) = CoordinateRing.XClass W x :=
  conj_mk_CC W (X - Polynomial.C x)

private theorem conj_YClass (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (y : R) :
    conj W (CoordinateRing.YClass W (Polynomial.C y)) =
      -CoordinateRing.YClass W (Polynomial.C (-y)) := by
  rw [CoordinateRing.YClass, CoordinateRing.YClass, map_sub, map_sub,
    conj_mk_Y' W h₁ h₃, conj_mk_CC]
  rw [show (Polynomial.C (Polynomial.C (-y)) : R[X][Y]) =
    -Polynomial.C (Polynomial.C y) from by
      rw [Polynomial.C_neg, Polynomial.C_neg]]
  rw [map_sub, map_neg]
  ring

/-- `conj` maps the point ideal of `(x, y)` onto the point ideal of
`(x, −y)`. -/
private theorem map_conj_XYIdeal (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0)
    (x y : R) :
    (CoordinateRing.XYIdeal W x (Polynomial.C y)).map
        (((conj W).toRingEquiv :
          W.CoordinateRing →+* W.CoordinateRing)) =
      CoordinateRing.XYIdeal W x (Polynomial.C (-y)) := by
  have happ : ∀ z : W.CoordinateRing,
      (((conj W).toRingEquiv : W.CoordinateRing →+* W.CoordinateRing)) z =
        conj W z := fun z => rfl
  rw [CoordinateRing.XYIdeal, CoordinateRing.XYIdeal, Ideal.map_span]
  rw [Set.image_pair]
  rw [happ, happ, conj_XClass W x, conj_YClass W h₁ h₃ y]
  -- span is unchanged by negating a generator
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have := neg_mem (Ideal.subset_span
        (Set.mem_insert_of_mem _ rfl) :
          -CoordinateRing.YClass W (Polynomial.C (-y)) ∈
            Ideal.span ({CoordinateRing.XClass W x,
              -CoordinateRing.YClass W (Polynomial.C (-y))} :
                Set W.CoordinateRing))
      simpa using this

end ConjGeneric

variable (E : ECSetup)

/-! ## Transport instantiated on the two curves -/

/-- Transport at rational points: `v_P(conj z) = v_{σP}(z)`. -/
private theorem pointPrime_intValuation_conj_apply
    {P Pσ : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hPσ : Pσ ∈ E.points)
    (hx : Pσ.1 = P.1) (hy : Pσ.2 = -P.2) (z : E.toW.toAffine.CoordinateRing) :
    (E.pointPrime hP).intValuation (conj E.toW.toAffine z) =
      (E.pointPrime hPσ).intValuation z := by
  refine intValuation_map_ringEquiv
    (conj E.toW.toAffine).toRingEquiv _ _ ?_ z
  rw [ECSetup.pointPrime_asIdeal, ECSetup.pointPrime_asIdeal, hx, hy,
    map_conj_XYIdeal E.toW.toAffine (E.toW_a₁) (E.toW_a₃), neg_neg]

/-- Transport at geometric points: `v_Q(conj z) = v_{σQ}(z)`. -/
private theorem geomPointPrime_intValuation_conj_apply
    (Q Qσ : GeomPoint E) (hx : Qσ.x = Q.x) (hy : Qσ.y = -Q.y)
    (z : E.toWBar.toAffine.CoordinateRing) :
    (geomPointPrime E Q).intValuation (conj E.toWBar.toAffine z) =
      (geomPointPrime E Qσ).intValuation z := by
  refine intValuation_map_ringEquiv
    (conj E.toWBar.toAffine).toRingEquiv _ _ ?_ z
  rw [geomPointPrime_asIdeal, geomPointPrime_asIdeal, hx, hy,
    map_conj_XYIdeal E.toWBar.toAffine (E.toWBar_a₁) (E.toWBar_a₃), neg_neg]

/-- `conj` realizes `conjElt` on the class of a rational `D`. -/
private theorem conj_toCoordinateRing (D : CoordRingElt E.q) :
    conj E.toW.toAffine (D.toCoordinateRing E) =
      D.conjElt.toCoordinateRing E := by
  show conj E.toW.toAffine
      (CoordinateRing.mk E.toW.toAffine
        (Polynomial.C D.a - Polynomial.C D.b * Y)) =
    CoordinateRing.mk E.toW.toAffine
      (Polynomial.C D.conjElt.a - Polynomial.C D.conjElt.b * Y)
  rw [conj_mk_line E.toW.toAffine (E.toW_a₁) (E.toW_a₃)]
  rfl

/-- `conj` negates the second component of `barD`. -/
private theorem conj_barD (a b : Polynomial (Fqbar E)) :
    conj E.toWBar.toAffine (barD E a b) = barD E a (-b) := by
  show conj E.toWBar.toAffine
      (CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C a - Polynomial.C b * Y)) = _
  rw [conj_mk_line E.toWBar.toAffine (E.toWBar_a₁) (E.toWBar_a₃)]
  rfl

/-! ## Per-point identities from the bridge (rational side) -/

/-- Vanishing order is zero where `D` does not vanish (bridge form). -/
private theorem ordAt_eq_zero_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hne : D.eval P.1 P.2 ≠ 0) :
    ordAt E D P = 0 := by
  have h1 : (E.pointPrime hP).intValuation (D.toCoordinateRing E) = 1 :=
    (pointPrime_intValuation_eq_one_iff E D hP).mpr hne
  rw [pointPrime_intValuation_toCoordinateRing E D hP hD,
    show (1 : ℤᵐ⁰) = exp 0 from exp_zero.symm, exp_inj] at h1
  omega

/-- The conjugate-pair sum at a non-2-torsion fiber (bridge form):
`ordAt P + ordAt σP = rootMult x₀ N`. -/
private theorem ordAt_pair_sum_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hσP : (P.1, -P.2) ∈ E.points) (hy : P.2 ≠ 0) :
    ordAt E D P + ordAt E D (P.1, -P.2) =
      rootMultiplicity P.1 (normPoly E D) := by
  classical
  have hσ := pointPrime_intValuation_conj_apply E hP hσP rfl rfl
    (D.toCoordinateRing E)
  rw [conj_toCoordinateRing] at hσ
  have hprod : (E.pointPrime hP).intValuation (D.toCoordinateRing E) *
      (E.pointPrime hP).intValuation (D.conjElt.toCoordinateRing E) =
      exp (-(rootMultiplicity P.1 (normPoly E D) : ℤ)) := by
    rw [← map_mul, toCoordinateRing_mul_conjElt,
      pointPrime_intValuation_mk_C E hP (normPoly_ne_zero E D hD),
      if_neg hy, one_mul]
  have hDσ : ¬ (D.conjElt.a = 0 ∧ D.conjElt.b = 0) := by
    rintro ⟨ha, hb⟩
    exact hD ⟨ha, by simpa using hb⟩
  rw [hσ, pointPrime_intValuation_toCoordinateRing E D hP hD,
    pointPrime_intValuation_toCoordinateRing E D hσP hD,
    ← exp_add, exp_inj] at hprod
  omega

/-- The 2-torsion order (bridge form): `ordAt P = rootMult x₀ N`. -/
private theorem ordAt_twoTorsion_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hy : P.2 = 0) :
    ordAt E D P = rootMultiplicity P.1 (normPoly E D) := by
  classical
  have hσ := pointPrime_intValuation_conj_apply E hP hP rfl
    (by rw [hy, neg_zero]) (D.toCoordinateRing E)
  rw [conj_toCoordinateRing] at hσ
  have hprod : (E.pointPrime hP).intValuation (D.toCoordinateRing E) *
      (E.pointPrime hP).intValuation (D.conjElt.toCoordinateRing E) =
      exp (-((2 * rootMultiplicity P.1 (normPoly E D) : ℕ) : ℤ)) := by
    rw [← map_mul, toCoordinateRing_mul_conjElt,
      pointPrime_intValuation_mk_C E hP (normPoly_ne_zero E D hD),
      if_pos hy]
  rw [hσ, pointPrime_intValuation_toCoordinateRing E D hP hD,
    ← exp_add, exp_inj] at hprod
  push_cast at hprod
  omega

/-! ## Cross-check 2: the split-time degree accounting, via the bridge -/

/-- **`sum_ordAt_eq_natDegree_under_split`, re-derived from the
valuation bridge** (statement verbatim; the production proof is not
cited). -/
theorem sum_ordAt_eq_natDegree_under_split_via_bridge
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D) :
    (∑ P ∈ E.points, ordAt E D P) = (normPoly E D).natDegree := by
  classical
  rw [sum_E_points_eq_sum_fiberwise E]
  have hPer : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P)
        = rootMultiplicity x₀ (normPoly E D) := by
    intro x₀
    by_cases hEx : ∃ P : ZMod E.q × ZMod E.q, P ∈ E.points ∧ P.1 = x₀
    · obtain ⟨P₀, hP₀E, hP₀x⟩ := hEx
      by_cases hy : P₀.2 = 0
      · -- 2-torsion fiber: the single point `P₀`
        have hfib : E.points.filter (fun P => P.1 = x₀) = {P₀} := by
          apply Finset.ext
          intro P'
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hP'E, hP'x⟩
            have h1 : P'.2 ^ 2 = P₀.2 ^ 2 := by
              rw [E.hOnCurve P' hP'E, E.hOnCurve P₀ hP₀E, hP'x, hP₀x]
            rw [hy] at h1
            have h2 : P'.2 = 0 := by simpa using h1
            exact Prod.ext (hP'x.trans hP₀x.symm) (h2.trans hy.symm)
          · rintro rfl
            exact ⟨hP₀E, hP₀x⟩
        rw [hfib, Finset.sum_singleton, ← hP₀x]
        exact ordAt_twoTorsion_via_bridge E D hD hP₀E hy
      · -- twin fiber: `P₀` and its conjugate
        obtain ⟨hσE, hσne⟩ := neg_sheet_on_E E P₀ hP₀E hy
        have hfib : E.points.filter (fun P => P.1 = x₀) =
            {P₀, (P₀.1, -P₀.2)} := by
          apply Finset.ext
          intro P'
          simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hP'E, hP'x⟩
            have h1 : P'.2 ^ 2 = P₀.2 ^ 2 := by
              rw [E.hOnCurve P' hP'E, E.hOnCurve P₀ hP₀E, hP'x, hP₀x]
            have h2 : (P'.2 - P₀.2) * (P'.2 + P₀.2) = 0 := by
              linear_combination h1
            rcases mul_eq_zero.mp h2 with h | h
            · left
              exact Prod.ext (hP'x.trans hP₀x.symm) (sub_eq_zero.mp h)
            · right
              exact Prod.ext (hP'x.trans hP₀x.symm)
                (by linear_combination h)
          · rintro (rfl | rfl)
            · exact ⟨hP₀E, hP₀x⟩
            · exact ⟨hσE, hP₀x⟩
        rw [hfib, Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            exact fun h => hσne h.symm),
          Finset.sum_singleton, ← hP₀x]
        exact ordAt_pair_sum_via_bridge E D hD hP₀E hσE hy
    · -- empty fiber: `x₀` is not a root of the norm, by `splitsOnE`
      push Not at hEx
      have hEmpty : E.points.filter (fun P => P.1 = x₀) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro P hP
        exact hEx P hP
      rw [hEmpty, Finset.sum_empty]
      by_contra hne
      have hroot : x₀ ∈ (normPoly E D).roots := by
        rw [Polynomial.mem_roots (normPoly_ne_zero E D hD)]
        exact (Polynomial.rootMultiplicity_pos
          (normPoly_ne_zero E D hD)).mp
          (Nat.pos_of_ne_zero (fun h => hne h.symm))
      obtain ⟨y, hy⟩ := hSplit.2 x₀ hroot
      exact hEx (x₀, y) hy rfl
  rw [Finset.sum_congr rfl (fun x₀ _ => hPer x₀),
    sum_rootMultiplicity_eq_card_roots]
  exact hSplit.1

/-! ## Per-point identities from the bridge (geometric side) -/

private theorem geomLocalOrder_eq_zero_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (Q : GeomPoint E)
    (hne : D.geomEval E Q ≠ 0) :
    geomLocalOrder E D Q = 0 := by
  have h1 : (geomPointPrime E Q).intValuation
      (barD E (geomAPoly E D) (geomBPoly E D)) = 1 := by
    rw [geomPointPrime_intValuation_eq_one_iff]
    intro h0
    apply hne
    unfold CoordRingElt.geomEval
    unfold barEval at h0
    rw [geomAPoly, geomBPoly] at h0
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map]
    exact h0
  rw [geomPointPrime_intValuation_toBar E D hD Q,
    show (1 : ℤᵐ⁰) = exp 0 from exp_zero.symm, exp_inj] at h1
  omega

private theorem geom_hab (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ¬ (geomAPoly E D = 0 ∧ geomBPoly E D = 0) := by
  rintro ⟨ha, hb⟩
  apply hD
  constructor
  · exact (Polynomial.map_eq_zero_iff
      (algebraMap (ZMod E.q) (Fqbar E)).injective).mp ha
  · exact (Polynomial.map_eq_zero_iff
      (algebraMap (ZMod E.q) (Fqbar E)).injective).mp hb

/-- The conjugate-pair sum at a geometric fiber (bridge form). -/
private theorem geomLocalOrder_pair_sum_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (Q Qσ : GeomPoint E)
    (hx : Qσ.x = Q.x) (hy : Qσ.y = -Q.y) (hyne : Q.y ≠ 0) :
    geomLocalOrder E D Q + geomLocalOrder E D Qσ =
      rootMultiplicity Q.x (normPolyBar E D) := by
  classical
  have hσ := geomPointPrime_intValuation_conj_apply E Q Qσ hx hy
    (barD E (geomAPoly E D) (geomBPoly E D))
  rw [conj_barD] at hσ
  have hprod := geomPointPrime_intValuation_mul_conj E
    (geom_hab E D hD) Q
  rw [if_neg hyne, one_mul, barNormPoly_eq_normPolyBar] at hprod
  rw [hσ, geomPointPrime_intValuation_toBar E D hD Q,
    geomPointPrime_intValuation_toBar E D hD Qσ,
    ← exp_add, exp_inj] at hprod
  omega

/-- The geometric 2-torsion order (bridge form). -/
private theorem geomLocalOrder_twoTorsion_via_bridge (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (Q : GeomPoint E) (hy : Q.y = 0) :
    geomLocalOrder E D Q = rootMultiplicity Q.x (normPolyBar E D) := by
  classical
  have hσ := geomPointPrime_intValuation_conj_apply E Q Q rfl
    (by rw [hy, neg_zero]) (barD E (geomAPoly E D) (geomBPoly E D))
  rw [conj_barD] at hσ
  have hprod := geomPointPrime_intValuation_mul_conj E
    (geom_hab E D hD) Q
  rw [if_pos hy, barNormPoly_eq_normPolyBar] at hprod
  rw [hσ, geomPointPrime_intValuation_toBar E D hD Q,
    ← exp_add, exp_inj] at hprod
  push_cast at hprod
  omega

private theorem GeomPoint.ext' {Q Q' : GeomPoint E}
    (hx : Q.x = Q'.x) (hy : Q.y = Q'.y) : Q = Q' := by
  cases Q
  cases Q'
  simp only at hx hy
  subst hx
  subst hy
  rfl

/-! ## Cross-check 1: the geometric fiber accounting, via the bridge -/

set_option linter.unusedVariables false in
/-- **`geomLocalOrder_fiber_accounting`, re-derived from the valuation
bridge** (statement verbatim; the production proof is not cited).
`hSupportZero` is carried to mirror the original signature; the
bridge derivation needs only the converse inclusion. -/
theorem geomLocalOrder_fiber_accounting_via_bridge
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), geomLocalOrder E D Q)
        = (normPolyBar E D).rootMultiplicity α := by
  classical
  intro α
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_pow_nat_eq
    (α ^ 3 + fqToBar E E.curveA * α + fqToBar E E.curveB) (n := 2)
    (by norm_num)
  set Q₀ : GeomPoint E := ⟨α, y₀, hy₀⟩ with hQ₀def
  have hQ₀x : Q₀.x = α := rfl
  have hQ₀y : Q₀.y = y₀ := rfl
  -- order vanishes off the support
  have hoffsupp : ∀ Q : GeomPoint E, Q ∉ support →
      geomLocalOrder E D Q = 0 := by
    intro Q hQ
    refine geomLocalOrder_eq_zero_via_bridge E D hDnz Q ?_
    intro h0
    exact hQ (hZeroSupport Q h0)
  by_cases hy : y₀ = 0
  · -- 2-torsion fiber `{Q₀}`
    have hsub : support.filter (fun Q => Q.x = α) ⊆ {Q₀} := by
      intro Q hQ
      obtain ⟨-, hQx⟩ := Finset.mem_filter.mp hQ
      have h1 : Q.y ^ 2 = y₀ ^ 2 := by
        rw [Q.onCurve, hy₀, hQx]
      rw [hy] at h1
      have h2 : Q.y = 0 := by simpa using h1
      simp only [Finset.mem_singleton]
      exact GeomPoint.ext' E hQx (h2.trans hy.symm)
    rw [Finset.sum_subset hsub (by
      intro Q hQmem hQnot
      simp only [Finset.mem_singleton] at hQmem
      subst hQmem
      refine hoffsupp Q₀ ?_
      intro hQ₀supp
      exact hQnot (Finset.mem_filter.mpr ⟨hQ₀supp, hQ₀x⟩))]
    rw [Finset.sum_singleton]
    exact geomLocalOrder_twoTorsion_via_bridge E D hDnz Q₀ hy
  · -- twin fiber `{Q₀, σQ₀}`
    set Qσ : GeomPoint E := Q₀.conjugate E with hQσdef
    have hQσx : Qσ.x = α := rfl
    have hQσy : Qσ.y = -y₀ := rfl
    have hne : Q₀ ≠ Qσ := by
      intro h
      apply hy
      have h2 : Q₀.y = Qσ.y := by rw [h]
      rw [hQ₀y, hQσy] at h2
      have h3 : (2 : Fqbar E) * y₀ = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 (two_ne_zero_bar E)
      · exact h4
    have hsub : support.filter (fun Q => Q.x = α) ⊆ {Q₀, Qσ} := by
      intro Q hQ
      obtain ⟨-, hQx⟩ := Finset.mem_filter.mp hQ
      have h1 : Q.y ^ 2 = y₀ ^ 2 := by
        rw [Q.onCurve, hy₀, hQx]
      have h2 : (Q.y - y₀) * (Q.y + y₀) = 0 := by linear_combination h1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases mul_eq_zero.mp h2 with h | h
      · left
        exact GeomPoint.ext' E hQx (sub_eq_zero.mp h)
      · right
        refine GeomPoint.ext' E hQx ?_
        rw [hQσy]
        linear_combination h
    rw [Finset.sum_subset hsub (by
      intro Q hQmem hQnot
      simp only [Finset.mem_insert, Finset.mem_singleton] at hQmem
      have hQx : Q.x = α := by
        rcases hQmem with rfl | rfl
        · exact hQ₀x
        · exact hQσx
      refine hoffsupp Q ?_
      intro hQsupp
      exact hQnot (Finset.mem_filter.mpr ⟨hQsupp, hQx⟩))]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact hne)]
    rw [Finset.sum_singleton]
    rw [show (normPolyBar E D).rootMultiplicity α =
      rootMultiplicity Q₀.x (normPolyBar E D) from rfl]
    exact geomLocalOrder_pair_sum_via_bridge E D hDnz Q₀ Qσ hQσx hQσy hy

end Divisor

/-! The via-bridge derivations are as axiom-clean as the originals. -/

/--
info: 'Divisor.sum_ordAt_eq_natDegree_under_split_via_bridge' depends on axioms: [propext,
 choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.sum_ordAt_eq_natDegree_under_split_via_bridge

/--
info: 'Divisor.geomLocalOrder_fiber_accounting_via_bridge' depends on axioms: [propext,
 choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.geomLocalOrder_fiber_accounting_via_bridge
