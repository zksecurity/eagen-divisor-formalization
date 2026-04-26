/-
  Divisor/ChordLogDerivProof.lean

  Proof of `chordLogDerivMatchesNormZ` under splitting and norm-accounting
  hypotheses, parameterised over an arbitrary multiplicity function β_fun.

  ## Proof structure

  The target `chordLogDerivMatchesNormZ E D β_fun A₀ A₁` unfolds to:

      (LT₀ + LT₁ + LT₂) · normZ(μ) = normZ'(μ)

  where LTᵢ = logDerivTerm(Aᵢ, λ), μ = zLambda λ A₀, and normZ uses β_fun.

  **Step 1.** Show `normZ(μ) ≠ 0` from `hQline`.
  **Step 2.** Reduce to ratio form via `chordLogDerivMatchesNormZ_of_ratio_eq`.
  **Step 3.** Prove the ratio identity via two axioms:
    AXIOM 1 (`chord_fiber_product_eq_normZ_under_split`): chord_fiber_product = c·normZ.
    AXIOM 2 (`chord_sum_eq_chord_fiber_product_logDeriv`): chord-sum = log-deriv of chord_fiber_product.
-/
import Divisor.ChordSumResidue
import Divisor.NormZDecomp
import Divisor.BivariateLogDeriv
import Divisor.ChordCubicSymmetric
import Divisor.PartialFractionHelper
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomChordSumEqChordFiberProductLogDeriv
import Mathlib

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Step 1: normZ(μ) ≠ 0 from hQline -/

/-- When no zero of D lies on the chord line (`hQline`), the norm
polynomial `normZ` is nonzero at the chord intercept μ = zLambda λ A₀. -/
theorem normZ_eval_ne_zero_of_hQline
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0 := by
  apply normZ_eval_ne_zero_at_nonroot E _ D hD β_fun
  intro Q hQ
  have hL := hQline Q hQ
  have hLsub := L_eval_eq_zLambda_sub E A₀ A₁ Q
  intro heq
  apply hL
  rw [hLsub, heq, sub_self]

/-! ## Helper: log-derivative of a constant multiple -/

theorem logDeriv_const_mul {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (g : K[X]) (μ : K) (hg : g.eval μ ≠ 0) :
    eval μ (derivative (C c * g)) / (C c * g).eval μ =
    eval μ (derivative g) / g.eval μ := by
  rw [derivative_C_mul, eval_C_mul, eval_C_mul]
  field_simp

/-! ## Step 3: chord_sum_eq_residue_sum -/

/-- **Theorem (scalar trace-of-log-derivative identity on the chord fiber).**
Parameterised over an arbitrary multiplicity function β_fun. The
support / coverage / accounting hypotheses on β_fun ensure the
chord-fiber-product axiom applies. -/
theorem chord_sum_eq_residue_sum
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) = (normPoly E D).natDegree)
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = -∑ Q ∈ zerosFinset E D,
        (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  have hNormZne : (normZ E lam D β_fun).eval μ ≠ 0 := by
    rw [hMu, hLam]
    exact normZ_eval_ne_zero_of_hQline E D β_fun A₀ A₁ hD hQline
  obtain ⟨c, hc_ne, hcfp_eq⟩ :=
    chord_fiber_product_eq_normZ_under_split E D lam hD hSplit β_fun hβsup hβcov hAccount
  have hcfp_ne : (chord_fiber_product E lam D).eval μ ≠ 0 := by
    rw [hcfp_eq, eval_mul, eval_C]
    exact mul_ne_zero hc_ne hNormZne
  have hAxiom2 : logDerivTerm E D E.curveA lam A₀
        + logDerivTerm E D E.curveA lam A₁
        + logDerivTerm E D E.curveA lam
            (lam ^ 2 - A₀.1 - A₁.1,
             lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      = eval μ (derivative (chord_fiber_product E lam D))
        / (chord_fiber_product E lam D).eval μ := by
    rw [hLam, hMu]
    exact chord_sum_eq_chord_fiber_product_logDeriv E D A₀ A₁
      hA₀ hA₁ hNV hD hA₀def hA₁def hA₂def hDen (by rw [← hLam, ← hMu]; exact hcfp_ne)
  have hLogDeriv : eval μ (derivative (chord_fiber_product E lam D))
      / (chord_fiber_product E lam D).eval μ =
      eval μ (derivative (normZ E lam D β_fun)) / (normZ E lam D β_fun).eval μ := by
    rw [hcfp_eq]
    exact logDeriv_const_mul c hc_ne (normZ E lam D β_fun) μ hNormZne
  have hPFE := normZ_logDeriv_at_chord_intercept E D β_fun A₀ A₁ hQline
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    with hLT
  set N : ZMod E.q := (normZ E lam D β_fun).eval μ with hN
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D β_fun)) with hNd
  set S : ZMod E.q :=
    ∑ Q ∈ zerosFinset E D,
      (β_fun Q : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ with hS
  change Nd = -(N * S) at hPFE
  have hLT_eq : LT = Nd / N := by
    rw [hAxiom2, hLogDeriv]
  have hNd_div : Nd / N = -S := by
    rw [hPFE]
    field_simp
  show LT = -S
  rw [hLT_eq, hNd_div]

/-- **Trace-of-log-derivative identity.** -/
theorem trace_logDeriv_eq_normZ_logDeriv
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) = (normPoly E D).natDegree)
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = eval (zLambda E lam A₀)
        (derivative (normZ E lam D β_fun))
      / (normZ E lam D β_fun).eval (zLambda E lam A₀) := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  have hScalar := chord_sum_eq_residue_sum E D β_fun A₀ A₁
    hA₀ hA₁ hNV hD hSplit hβsup hβcov hAccount hA₀def hA₁def hA₂def hQline hDen
  have hPFE := normZ_logDeriv_at_chord_intercept E D β_fun A₀ A₁ hQline
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    with hLT
  set N : ZMod E.q := (normZ E lam D β_fun).eval μ with hN
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D β_fun)) with hNd
  set S : ZMod E.q :=
    ∑ Q ∈ zerosFinset E D,
      (β_fun Q : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ with hS
  change LT = -S at hScalar
  change Nd = -(N * S) at hPFE
  show LT = Nd / N
  rw [hPFE, hScalar]
  field_simp

/-! ## Step 2 + Assembly: Main theorem -/

/-- **Main theorem: `chordLogDerivMatchesNormZ` under splitting and
accounting hypotheses, parameterised over β_fun.** -/
theorem chordLogDerivMatchesNormZ_holds
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) = (normPoly E D).natDegree)
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0) :
    chordLogDerivMatchesNormZ E D β_fun A₀ A₁ := by
  have hNormZne := normZ_eval_ne_zero_of_hQline E D β_fun A₀ A₁ hD hQline
  apply chordLogDerivMatchesNormZ_of_ratio_eq E D β_fun A₀ A₁ hNormZne
  exact trace_logDeriv_eq_normZ_logDeriv E D β_fun A₀ A₁
    hA₀ hA₁ hNV hD hSplit hβsup hβcov hAccount hA₀def hA₁def hA₂def hQline hDen hNormZne

end Divisor
