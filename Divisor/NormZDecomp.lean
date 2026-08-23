/-
  Divisor/NormZDecomp.lean

  Derivative and partial-fraction-expansion identities for
  `normZ E λ D β_fun`, the chord-coordinate norm polynomial.

  `normZ E λ D β_fun` is defined directly as the explicit product form

    `normZ E λ D β_fun = C lc * ∏_{Q ∈ zerosFinset} (X - C (zLambda λ Q))^(β_fun Q)`

  with `lc = (normPoly E D).leadingCoeff`. The β_fun argument is the
  multiplicity function used; downstream consumers instantiate it with
  the *true* divisor multiplicity from
  `CoordRingElt.exists_divisor_multiplicity` (consumed via
  `CoordRingElt.has_principal_divisor`). All theorems here are
  parameterised over an arbitrary β_fun.

  This module provides:

  * `normZ_derivative`: explicit formula for `(normZ E λ D β_fun).derivative`
    as a Finset sum.
  * `normZ_derivative_eval`: evaluation of the derivative at any μ.
  * `normZ_eval_ne_zero_at_nonroot`: `normZ(μ) ≠ 0` when μ differs from
    every `z(Q)` for `Q ∈ zerosFinset`.
  * `normZ_logDeriv_at_nonroot`: divided log-derivative identity
    `(normZ)'(μ) / normZ(μ) = Σ_Q β_fun(Q) / (μ - z(Q))`.
  * `normZ_logDeriv_at_chord_intercept`: chord-intercept form via
    `L_eval_eq_zLambda_sub`.

  No new axioms, no `sorry` / `admit`.
-/
import Divisor.FunctionFieldZ
import Divisor.ResidueIdentity

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Derivative of `normZ` via the product rule -/

/-- **Derivative of `normZ`, explicit sum form.** Under the product-form
definition of `normZ E λ D β_fun`, the derivative is the sum

  `C lc * Σ_{Q ∈ zerosFinset} C (β_fun Q) *
       (X - C (zLambda λ Q))^(β_fun Q - 1) *
       ∏_{Q' ∈ zerosFinset.erase Q} (X - C (zLambda λ Q'))^(β_fun Q')`

where `lc = (normPoly E D).leadingCoeff`. -/
theorem normZ_derivative (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    derivative (normZ E lam D β_fun) =
      C ((normPoly E D).leadingCoeff) *
        ∑ Q ∈ zerosFinset E D,
          (C ((β_fun Q : ZMod E.q)) *
            (X - C (zLambda E lam Q)) ^ ((β_fun Q) - 1) *
            ∏ Q' ∈ (zerosFinset E D).erase Q,
              (X - C (zLambda E lam Q')) ^ (β_fun Q')) := by
  classical
  unfold normZ
  exact derivative_C_mul_prod_X_sub_C_pow_indexed
    (K := ZMod E.q) (normPoly E D).leadingCoeff (zerosFinset E D)
    (fun Q => zLambda E lam Q) (fun Q => β_fun Q)

/-- **Evaluation of `(normZ)'` at an arbitrary μ.** -/
theorem normZ_derivative_eval
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (μ : ZMod E.q) :
    eval μ (derivative (normZ E lam D β_fun)) =
      (normPoly E D).leadingCoeff *
        ∑ Q ∈ zerosFinset E D,
          ((β_fun Q : ZMod E.q) *
            (μ - zLambda E lam Q) ^ ((β_fun Q) - 1) *
            ∏ Q' ∈ (zerosFinset E D).erase Q,
              (μ - zLambda E lam Q') ^ (β_fun Q')) := by
  classical
  rw [normZ_derivative, eval_mul, eval_C, eval_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro Q _
  rw [eval_mul, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C,
      eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro Q' _
  rw [eval_pow, eval_sub, eval_X, eval_C]

/-! ## Non-vanishing of `normZ(μ)` away from projected zeros -/

/-- **`normZ(μ) ≠ 0` at a non-root μ.** When μ is not in the image of
`zLambda λ` on `zerosFinset E D`, every factor of the product is
nonzero. -/
theorem normZ_eval_ne_zero_at_nonroot
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (μ : ZMod E.q)
    (hNonRoot : ∀ Q ∈ zerosFinset E D, μ ≠ zLambda E lam Q) :
    (normZ E lam D β_fun).eval μ ≠ 0 := by
  classical
  rw [normZ_eval]
  apply mul_ne_zero
  · exact normPoly_leadingCoeff_ne_zero E D hD
  · apply Finset.prod_ne_zero_iff.mpr
    intro Q hQ
    apply pow_ne_zero
    exact sub_ne_zero.mpr (hNonRoot Q hQ)

/-! ## Log-derivative identity in divided form -/

/-- **Algebraic identity for a single summand.** Under the non-root
hypothesis `(μ - z(Q)) ≠ 0`, the Q-th summand of `normZ_derivative_eval`
equals `β_fun(Q) · [∏_{Q' ∈ zerosFinset} (μ - z(Q'))^(β_fun Q')] / (μ - z(Q))`.
-/
private theorem summand_eq_full_prod_div
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (μ : ZMod E.q)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ zerosFinset E D)
    (hDiffQ : μ - zLambda E lam Q ≠ 0) :
    (β_fun Q : ZMod E.q) *
        (μ - zLambda E lam Q) ^ ((β_fun Q) - 1) *
        ∏ Q' ∈ (zerosFinset E D).erase Q,
          (μ - zLambda E lam Q') ^ (β_fun Q') =
      (β_fun Q : ZMod E.q) *
        (∏ Q' ∈ zerosFinset E D,
          (μ - zLambda E lam Q') ^ (β_fun Q'))
        * (μ - zLambda E lam Q)⁻¹ := by
  classical
  set y := μ - zLambda E lam Q with hy_def
  set m := β_fun Q with hm_def
  set P := ∏ Q' ∈ (zerosFinset E D).erase Q,
      (μ - zLambda E lam Q') ^ (β_fun Q') with hP_def
  have hFull :
      (∏ Q' ∈ zerosFinset E D,
        (μ - zLambda E lam Q') ^ (β_fun Q'))
        = y ^ m * P := by
    rw [hy_def, hm_def, hP_def]
    exact (Finset.mul_prod_erase (zerosFinset E D)
          (fun Q' => (μ - zLambda E lam Q') ^ (β_fun Q')) hQ).symm
  rw [hFull]
  by_cases hM : m = 0
  · rw [hM]
    simp
  · have hMpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hM
    have hPow : y ^ (m - 1) = y ^ m * y⁻¹ := by
      have hy : y ≠ 0 := hDiffQ
      have := pow_succ y (m - 1)
      rw [Nat.sub_add_cancel hMpos] at this
      field_simp
      rw [this]
    calc (m : ZMod E.q) * y ^ (m - 1) * P
        = (m : ZMod E.q) * (y ^ m * y⁻¹) * P := by rw [hPow]
      _ = (m : ZMod E.q) * (y ^ m * P) * y⁻¹ := by ring

/-- **Denominator-cleared log-derivative PFE (final form).** -/
theorem normZ_logDeriv_at_nonroot
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (μ : ZMod E.q)
    (hNonRoot : ∀ Q ∈ zerosFinset E D, μ - zLambda E lam Q ≠ 0) :
    eval μ (derivative (normZ E lam D β_fun)) =
      (normZ E lam D β_fun).eval μ *
        ∑ Q ∈ zerosFinset E D,
          (β_fun Q : ZMod E.q) * (μ - zLambda E lam Q)⁻¹ := by
  classical
  rw [normZ_derivative_eval, normZ_eval, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hDiffQ : μ - zLambda E lam Q ≠ 0 := hNonRoot Q hQ
  have hSum := summand_eq_full_prod_div E lam D β_fun μ hQ hDiffQ
  rw [hSum]
  ring

/-! ## Bridge to `L_Q` via `L_eval_eq_zLambda_sub` -/

/-- At μ = `zLambda λ A₀`, the difference `μ - zLambda λ Q` equals
`-L_Q(Q)` where `L_Q = lineThrough A₀ A₁` and λ = slopeOf A₀ A₁. -/
theorem zLambda_intercept_sub_eq_neg_lineEval
    (A₀ A₁ Q : ZMod E.q × ZMod E.q) :
    zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ -
        zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q =
      -(lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 := by
  have hL := L_eval_eq_zLambda_sub E A₀ A₁ Q
  linear_combination hL

/-- **Chord-intercept log-derivative identity.** -/
theorem normZ_logDeriv_at_chord_intercept
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun)) =
      -((normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
          (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) *
        ∑ Q ∈ zerosFinset E D,
          (β_fun Q : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹) := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam_def
  set μ := zLambda E lam A₀ with hMu_def
  have hNonRoot : ∀ Q ∈ zerosFinset E D, μ - zLambda E lam Q ≠ 0 := by
    intro Q hQ
    rw [hMu_def, hLam_def, zLambda_intercept_sub_eq_neg_lineEval]
    intro hZero
    apply hQline Q hQ
    linear_combination -hZero
  rw [normZ_logDeriv_at_nonroot E lam D β_fun μ hNonRoot]
  have hRw :
      ∑ Q ∈ zerosFinset E D,
        (β_fun Q : ZMod E.q) * (μ - zLambda E lam Q)⁻¹ =
      -∑ Q ∈ zerosFinset E D,
        (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    rw [hMu_def, hLam_def, zLambda_intercept_sub_eq_neg_lineEval]
    rw [inv_neg]
    ring
  rw [hRw]
  ring

end Divisor
