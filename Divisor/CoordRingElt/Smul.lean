/-
  Divisor/CoordRingElt/Smul.lean

  Scalar-normalization facts for coordinate-ring elements.  These lemmas
  are deliberately independent of any admissible-set choice: Parker,
  Eagen, hash, and later normalizers can all reuse them.
-/
import Divisor.OrdP.LocalRing
import Divisor.SupportDisjoint

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

namespace Polynomial

theorem rootMultiplicity_smul_nonzero (a : ZMod E.q) (ha : a ≠ 0)
    (p : (ZMod E.q)[X]) (x : ZMod E.q) :
    rootMultiplicity x (a • p) = rootMultiplicity x p := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Polynomial.smul_eq_C_mul]
    rw [Polynomial.rootMultiplicity_mul]
    · simp
    · exact mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hp

theorem smul_divByMonic (c : ZMod E.q) (p q : (ZMod E.q)[X]) :
    (c • p) /ₘ q = c • (p /ₘ q) := by
  by_cases hq : q.Monic
  · exact (Polynomial.div_modByMonic_unique
      (c • (p /ₘ q)) (c • (p %ₘ q)) hq
      ⟨by rw [mul_smul_comm, ← smul_add, Polynomial.modByMonic_add_div p q],
        (Polynomial.degree_smul_le _ _).trans_lt
          (Polynomial.degree_modByMonic_lt _ hq)⟩).1
  · simp_rw [Polynomial.divByMonic_eq_of_not_monic _ hq, smul_zero]

end Polynomial

namespace CoordRingElt

theorem smul_isZero_iff (c : ZMod E.q) (hc : c ≠ 0) (D : CoordRingElt E.q) :
    ((c • D).a = 0 ∧ (c • D).b = 0) ↔ (D.a = 0 ∧ D.b = 0) := by
  constructor
  · intro h
    constructor
    · have ha := h.1
      rw [CoordRingElt.smul_a] at ha
      exact (smul_eq_zero.mp ha).resolve_left hc
    · have hb := h.2
      rw [CoordRingElt.smul_b] at hb
      exact (smul_eq_zero.mp hb).resolve_left hc
  · intro h
    simp [h.1, h.2]

theorem divLin_smul (c : ZMod E.q) (D : CoordRingElt E.q) (x : ZMod E.q) :
    (c • D).divLin x = c • (D.divLin x) := by
  cases D with
  | mk a b =>
    rw [CoordRingElt.mk.injEq]
    exact ⟨Polynomial.smul_divByMonic E c a (X - C x),
      Polynomial.smul_divByMonic E c b (X - C x)⟩

theorem degE_smul (c : ZMod E.q) (hc : c ≠ 0) (D : CoordRingElt E.q) :
    (c • D).degE = D.degE := by
  unfold CoordRingElt.degE
  simp [CoordRingElt.smul_a, CoordRingElt.smul_b,
    Polynomial.natDegree_smul _ hc]

end CoordRingElt

theorem normPoly_smul (c : ZMod E.q) (D : CoordRingElt E.q) :
    normPoly E (c • D) = c ^ 2 • normPoly E D := by
  rw [normPoly_eq, normPoly_eq]
  simp only [CoordRingElt.smul_a, CoordRingElt.smul_b]
  repeat rw [Polynomial.smul_eq_C_mul]
  simp [Polynomial.C_pow]
  ring_nf

theorem splitsOnE_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) :
    splitsOnE E (c • D) ↔ splitsOnE E D := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  constructor
  · intro h
    obtain ⟨hsplit, hfiber⟩ := h
    refine ⟨?_, ?_⟩
    · unfold normPoly_splits_over_Fq at hsplit ⊢
      rw [normPoly_smul E c D, Polynomial.roots_smul_nonzero _ hc2,
        Polynomial.natDegree_smul _ hc2] at hsplit
      exact hsplit
    · intro α hroot
      apply hfiber α
      rwa [normPoly_smul E c D, Polynomial.roots_smul_nonzero _ hc2]
  · intro h
    obtain ⟨hsplit, hfiber⟩ := h
    refine ⟨?_, ?_⟩
    · unfold normPoly_splits_over_Fq at hsplit ⊢
      rw [normPoly_smul E c D, Polynomial.roots_smul_nonzero _ hc2,
        Polynomial.natDegree_smul _ hc2]
      exact hsplit
    · intro α hroot
      exact hfiber α (by
        rwa [normPoly_smul E c D, Polynomial.roots_smul_nonzero _ hc2] at hroot)

theorem ordAt_twoTorsion_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    ordAt_twoTorsion E (c • D) P = ordAt_twoTorsion E D P := by
  unfold ordAt_twoTorsion
  simp [CoordRingElt.smul_a, CoordRingElt.smul_b,
    Polynomial.rootMultiplicity_smul_nonzero E c hc, hc]

theorem ordAt_nonTwoTorsion_aux_smul (c : ZMod E.q) (hc : c ≠ 0) :
    ∀ (fuel : ℕ) (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q),
      ordAt_nonTwoTorsion_aux E fuel (c • D) P =
        ordAt_nonTwoTorsion_aux E fuel D P := by
  intro fuel
  induction fuel with
  | zero =>
      intro D P
      rfl
  | succ n IH =>
      intro D P
      show
        (if (c • D).a = 0 ∧ (c • D).b = 0 then 0
         else if (c • D).eval P.1 P.2 ≠ 0 then 0
         else if (c • D).eval P.1 (-P.2) ≠ 0 then
           rootMultiplicity P.1 (normPoly E (c • D))
         else 1 + ordAt_nonTwoTorsion_aux E n ((c • D).divLin P.1) P)
        =
        (if D.a = 0 ∧ D.b = 0 then 0
         else if D.eval P.1 P.2 ≠ 0 then 0
         else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
         else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P)
      simp only [CoordRingElt.smul_isZero_iff E c hc D]
      by_cases hD : D.a = 0 ∧ D.b = 0
      · rw [if_pos hD, if_pos hD]
      · rw [if_neg hD, if_neg hD]
        have hEval : (c • D).eval P.1 P.2 ≠ 0 ↔
            D.eval P.1 P.2 ≠ 0 := by
          simp [CoordRingElt.eval_smul, hc]
        have hEvalNeg : (c • D).eval P.1 (-P.2) ≠ 0 ↔
            D.eval P.1 (-P.2) ≠ 0 := by
          simp [CoordRingElt.eval_smul, hc]
        simp only [hEval]
        by_cases h1 : D.eval P.1 P.2 ≠ 0
        · rw [if_pos h1, if_pos h1]
        · rw [if_neg h1, if_neg h1]
          simp only [hEvalNeg]
          by_cases h2 : D.eval P.1 (-P.2) ≠ 0
          · rw [if_pos h2, if_pos h2]
            rw [normPoly_smul E c D]
            exact Polynomial.rootMultiplicity_smul_nonzero E (c ^ 2)
              (pow_ne_zero 2 hc) (normPoly E D) P.1
          · rw [if_neg h2, if_neg h2]
            rw [CoordRingElt.divLin_smul E c D P.1]
            rw [IH (D.divLin P.1) P]

theorem ordAt_nonTwoTorsion_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    ordAt_nonTwoTorsion E (c • D) P = ordAt_nonTwoTorsion E D P := by
  unfold ordAt_nonTwoTorsion
  simp [CoordRingElt.smul_a, CoordRingElt.smul_b,
    Polynomial.natDegree_smul _ hc,
    ordAt_nonTwoTorsion_aux_smul E c hc]

theorem ordAt_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    ordAt E (c • D) P = ordAt E D P := by
  classical
  by_cases hP : P ∈ E.points
  · by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
    · have hD_scaled : ¬ ((c • D).a = 0 ∧ (c • D).b = 0) := by
        intro h
        exact hD ((CoordRingElt.smul_isZero_iff E c hc D).mp h)
      rw [ordAt_eq_dispatch E (c • D) hP hD_scaled,
        ordAt_eq_dispatch E D hP hD]
      by_cases hY : P.2 = 0
      · simp [hY, ordAt_twoTorsion_smul E c hc D P]
      · simp [hY, ordAt_nonTwoTorsion_smul E c hc D P]
    · have hDz : D.a = 0 ∧ D.b = 0 := Classical.not_not.mp hD
      have hScaledZ : (c • D).a = 0 ∧ (c • D).b = 0 :=
        (CoordRingElt.smul_isZero_iff E c hc D).mpr hDz
      rw [ordAt_eq_zero_of_offE_or_zero E D P
          (by intro h; exact h.2 hDz),
        ordAt_eq_zero_of_offE_or_zero E (c • D) P
          (by intro h; exact h.2 hScaledZ)]
  · rw [ordAt_eq_zero_of_offE_or_zero E D P
        (by intro h; exact hP h.1),
      ordAt_eq_zero_of_offE_or_zero E (c • D) P
        (by intro h; exact hP h.1)]

theorem divisorOfD_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) (R : ECPoint E) :
    divisorOfD E (c • D) R = divisorOfD E D R := by
  classical
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
      show -((normPoly E (c • D)).natDegree : ℤ) =
        -((normPoly E D).natDegree : ℤ)
      rw [normPoly_smul E c D,
        Polynomial.natDegree_smul _ (pow_ne_zero 2 hc)]
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
      show (ordAt E (c • D) (x, y) : ℤ) = (ordAt E D (x, y) : ℤ)
      rw [ordAt_smul E c hc D (x, y)]

theorem numZeros_smul (c : ZMod E.q) (hc : c ≠ 0)
    (D : CoordRingElt E.q) :
    numZeros E (c • D) = numZeros E D := by
  unfold numZeros zeros
  congr 1
  ext P
  simp [CoordRingElt.eval_smul, hc]

end Divisor
