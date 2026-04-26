/-
  Divisor/NormZDecomp.lean

  Queue-3 step . Derivative and
  partial-fraction-expansion identities for `normZ E λ D`, the
  chord-coordinate norm polynomial 

  Because chose to DEFINE `normZ E λ D` as the explicit
  product form

    `normZ E λ D = C lc * ∏_{Q ∈ zerosFinset} (X - C (zLambda λ Q))^(β Q)`

  with `lc = (normPoly E D).leadingCoeff` and `β = betaConstructive E D`,
  the "norm decomposition" (nominal target) is already
  definitional. What downstream phases actually consume is the
  derivative / log-derivative data. This module provides:

  * `normZ_derivative`: explicit formula for `(normZ E λ D).derivative`
    as a Finset sum, via `derivative_C_mul_prod_X_sub_C_pow` from
    `PartialFractionExpansion`.
  * `normZ_derivative_eval`: evaluation of the derivative at any μ.
  * `normZ_eval_ne_zero_at_nonroot`: `normZ(μ) ≠ 0` when μ differs from
    every `z(Q)` (for `Q ∈ zerosFinset`).
  * `normZ_logDeriv_at_nonroot`: the divided log-derivative identity
    `(normZ)'(μ) / normZ(μ) = Σ_Q β(Q) / (μ - z(Q))` at a non-root μ.
  * `normZ_logDeriv_at_nonroot_L`: same identity with `μ - z(Q)`
    rewritten as `-L_Q(Q)` via `L_eval_eq_zLambda_sub`, specialised to
    μ = `zLambda λ A₀` (the chord intercept).

  consumes `normZ_logDeriv_at_nonroot_L` (the chord-intercept
  form) directly; no further abstract PFE machinery is needed.

  No new axioms, no `sorry` / `admit`. This file only needs the Phase
  1a `normZ` definition and the generic derivative tools in
  `PartialFractionExpansion.lean`.
-/
import Divisor.FunctionFieldZ
import Divisor.PartialFractionExpansion
import Divisor.ResidueIdentity

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Derivative of `normZ` via the product rule

    The explicit product form of `normZ` () makes
    the derivative fall out of the generic
    `derivative_C_mul_prod_X_sub_C_pow` lemma. -/

/-- **Derivative of `normZ`, explicit sum form.** Under the product-form
definition of `normZ E λ D`, the derivative is the sum

  `C lc * Σ_{Q ∈ zerosFinset} C (β Q) *
       (X - C (zLambda λ Q))^(β Q - 1) *
       ∏_{Q' ∈ zerosFinset.erase Q} (X - C (zLambda λ Q'))^(β Q')`

where `lc = (normPoly E D).leadingCoeff` and `β = betaConstructive E D`. -/
theorem normZ_derivative (lam : ZMod E.q) (D : CoordRingElt E.q) :
    derivative (normZ E lam D) =
      C ((normPoly E D).leadingCoeff) *
        ∑ Q ∈ zerosFinset E D,
          (C ((betaConstructive E D Q : ZMod E.q)) *
            (X - C (zLambda E lam Q)) ^ ((betaConstructive E D Q) - 1) *
            ∏ Q' ∈ (zerosFinset E D).erase Q,
              (X - C (zLambda E lam Q')) ^ (betaConstructive E D Q')) := by
  classical
  unfold normZ
  exact derivative_C_mul_prod_X_sub_C_pow_indexed
    (K := ZMod E.q) (normPoly E D).leadingCoeff (zerosFinset E D)
    (fun Q => zLambda E lam Q) (fun Q => betaConstructive E D Q)

/-- **Evaluation of `(normZ)'` at an arbitrary μ.** -/
theorem normZ_derivative_eval
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : ZMod E.q) :
    eval μ (derivative (normZ E lam D)) =
      (normPoly E D).leadingCoeff *
        ∑ Q ∈ zerosFinset E D,
          ((betaConstructive E D Q : ZMod E.q) *
            (μ - zLambda E lam Q) ^ ((betaConstructive E D Q) - 1) *
            ∏ Q' ∈ (zerosFinset E D).erase Q,
              (μ - zLambda E lam Q') ^ (betaConstructive E D Q')) := by
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
nonzero. Combined with `normPoly_leadingCoeff_ne_zero`, this gives
non-vanishing of `normZ(μ)`. -/
theorem normZ_eval_ne_zero_at_nonroot
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (μ : ZMod E.q)
    (hNonRoot : ∀ Q ∈ zerosFinset E D, μ ≠ zLambda E lam Q) :
    (normZ E lam D).eval μ ≠ 0 := by
  classical
  rw [normZ_eval]
  apply mul_ne_zero
  · exact normPoly_leadingCoeff_ne_zero E D hD
  · apply Finset.prod_ne_zero_iff.mpr
    intro Q hQ
    apply pow_ne_zero
    exact sub_ne_zero.mpr (hNonRoot Q hQ)

/-! ## Log-derivative identity in divided form

    At μ where every `(μ - z(Q))` is nonzero, we can divide and obtain
    the clean rational identity

      `(normZ)'(μ) / normZ(μ) = Σ_Q β(Q) / (μ - z(Q))`.

    This is the "partial-fraction expansion of the logarithmic
    derivative" consumes at the chord intercept. -/

/-- **Algebraic identity for a single summand.** Under the non-root
hypothesis `(μ - z(Q)) ≠ 0`, the Q-th summand of `normZ_derivative_eval`
equals `β(Q) · [∏_{Q' ∈ zerosFinset} (μ - z(Q'))^(β Q')] / (μ - z(Q))`.

The proof is the elementary power-rule manipulation
`y^{m-1} = y^m / y` when `y ≠ 0` and `m ≥ 0`. -/
private theorem summand_eq_full_prod_div
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : ZMod E.q)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ zerosFinset E D)
    (hDiffQ : μ - zLambda E lam Q ≠ 0) :
    (betaConstructive E D Q : ZMod E.q) *
        (μ - zLambda E lam Q) ^ ((betaConstructive E D Q) - 1) *
        ∏ Q' ∈ (zerosFinset E D).erase Q,
          (μ - zLambda E lam Q') ^ (betaConstructive E D Q') =
      (betaConstructive E D Q : ZMod E.q) *
        (∏ Q' ∈ zerosFinset E D,
          (μ - zLambda E lam Q') ^ (betaConstructive E D Q'))
        * (μ - zLambda E lam Q)⁻¹ := by
  classical
  set y := μ - zLambda E lam Q with hy_def
  set m := betaConstructive E D Q with hm_def
  set P := ∏ Q' ∈ (zerosFinset E D).erase Q,
      (μ - zLambda E lam Q') ^ (betaConstructive E D Q') with hP_def
  -- Split out the Q-factor from the full product.
  have hFull :
      (∏ Q' ∈ zerosFinset E D,
        (μ - zLambda E lam Q') ^ (betaConstructive E D Q'))
        = y ^ m * P := by
    rw [hy_def, hm_def, hP_def]
    exact (Finset.mul_prod_erase (zerosFinset E D)
          (fun Q' => (μ - zLambda E lam Q') ^ (betaConstructive E D Q')) hQ).symm
  rw [hFull]
  -- Goal: (m : ZMod E.q) * y^(m-1) * P = (m : ZMod E.q) * (y^m * P) * y⁻¹.
  by_cases hM : m = 0
  · -- β = 0 case: both sides are 0.
    rw [hM]
    simp
  · have hMpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hM
    -- y^(m-1) · y = y^m, and y ≠ 0.
    have hPow : y ^ (m - 1) = y ^ m * y⁻¹ := by
      have hy : y ≠ 0 := hDiffQ
      have := pow_succ y (m - 1)
      rw [Nat.sub_add_cancel hMpos] at this
      field_simp
      rw [this]
    calc (m : ZMod E.q) * y ^ (m - 1) * P
        = (m : ZMod E.q) * (y ^ m * y⁻¹) * P := by rw [hPow]
      _ = (m : ZMod E.q) * (y ^ m * P) * y⁻¹ := by ring

/-- **Denominator-cleared log-derivative PFE (final form).** When μ is
not in the image of `zLambda λ` on `zerosFinset E D`, the pointwise
evaluation of `(normZ)'(μ)` equals `normZ(μ)` times a sum of
`β(Q) / (μ - z(Q))` terms:

  `(normZ)'(μ) = normZ(μ) · Σ_{Q ∈ zerosFinset} β(Q) / (μ - z(Q))`.

This is the partial-fraction expansion of the logarithmic derivative
at a non-root μ. -/
theorem normZ_logDeriv_at_nonroot
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : ZMod E.q)
    (hNonRoot : ∀ Q ∈ zerosFinset E D, μ - zLambda E lam Q ≠ 0) :
    eval μ (derivative (normZ E lam D)) =
      (normZ E lam D).eval μ *
        ∑ Q ∈ zerosFinset E D,
          (betaConstructive E D Q : ZMod E.q) * (μ - zLambda E lam Q)⁻¹ := by
  classical
  rw [normZ_derivative_eval, normZ_eval, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hDiffQ : μ - zLambda E lam Q ≠ 0 := hNonRoot Q hQ
  -- RHS single term:
  --   lc · (∏ Q', (μ - z(Q'))^β(Q')) · β(Q) · (μ - z(Q))⁻¹
  -- = lc · β(Q) · (∏ Q', ...) · (μ - z(Q))⁻¹
  -- We match this against the LHS single term via summand_eq_full_prod_div.
  have hSum := summand_eq_full_prod_div E lam D μ hQ hDiffQ
  -- LHS single term: lc · (β(Q) · (μ - z(Q))^(β(Q)-1) · ∏_{erase Q} ...)
  -- = lc · [hSum RHS] = lc · β(Q) · (∏ Q', ...) · (μ - z(Q))⁻¹.
  rw [hSum]
  ring

/-! ## Bridge to `L_Q` via `L_eval_eq_zLambda_sub`

    The chord line `L_Q = lineThrough A₀ A₁` evaluated at an arbitrary
    point `P` equals `zLambda λ P - zLambda λ A₀` by
    `L_eval_eq_zLambda_sub` (from `ResidueIdentity.lean:54`). So at
    μ = `zLambda λ A₀` we have `L_Q(Q) = zLambda λ Q - μ = -(μ - z(Q))`,
    hence `μ - z(Q) = -L_Q(Q)` and `(μ - z(Q))⁻¹ = -(L_Q(Q))⁻¹`.

    This section packages the bridge so we can invoke the PFE
    identity directly with `L_Q(Q)` on the RHS. -/

/-- At μ = `zLambda λ A₀`, the difference `μ - zLambda λ Q` equals
`-L_Q(Q)` where `L_Q = lineThrough A₀ A₁` and λ = slopeOf A₀ A₁. -/
theorem zLambda_intercept_sub_eq_neg_lineEval
    (A₀ A₁ Q : ZMod E.q × ZMod E.q) :
    zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ -
        zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q =
      -(lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 := by
  have hL := L_eval_eq_zLambda_sub E A₀ A₁ Q
  linear_combination hL

/-- **Chord-intercept log-derivative identity.** Specialising
`normZ_logDeriv_at_nonroot` to the chord intercept μ = `zLambda λ A₀`
and rewriting `μ - z(Q)` as `-L_Q(Q)`:

  `(normZ)'(μ) = normZ(μ) · Σ_Q β(Q) · (-L_Q(Q))⁻¹`
             ` = -normZ(μ) · Σ_Q β(Q) · L_Q(Q)⁻¹`.

Hypothesis: `L_Q(Q) ≠ 0` for every `Q ∈ zerosFinset E D`. This is the
exact form `\ref{lem:log-derivative}` RHS consumes. -/
theorem normZ_logDeriv_at_chord_intercept
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D)) =
      -((normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
          (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) *
        ∑ Q ∈ zerosFinset E D,
          (betaConstructive E D Q : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹) := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam_def
  set μ := zLambda E lam A₀ with hMu_def
  -- Non-root hypothesis: μ - z(Q) = -L_Q(Q) ≠ 0 since L_Q(Q) ≠ 0.
  have hNonRoot : ∀ Q ∈ zerosFinset E D, μ - zLambda E lam Q ≠ 0 := by
    intro Q hQ
    rw [hMu_def, hLam_def, zLambda_intercept_sub_eq_neg_lineEval]
    intro hZero
    apply hQline Q hQ
    linear_combination -hZero
  -- Apply the divided-form PFE.
  rw [normZ_logDeriv_at_nonroot E lam D μ hNonRoot]
  -- Now rewrite each (μ - z(Q))⁻¹ as -(L_Q(Q))⁻¹.
  have hRw :
      ∑ Q ∈ zerosFinset E D,
        (betaConstructive E D Q : ZMod E.q) * (μ - zLambda E lam Q)⁻¹ =
      -∑ Q ∈ zerosFinset E D,
        (betaConstructive E D Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    rw [hMu_def, hLam_def, zLambda_intercept_sub_eq_neg_lineEval]
    -- (-(L_Q Q))⁻¹ = -(L_Q Q)⁻¹
    rw [inv_neg]
    ring
  rw [hRw]
  ring

end Divisor
