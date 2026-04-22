/-
  Divisor/ChordLogDerivHelper.lean
  Pure algebraic helpers for chord_sum_eq_residue_sum.
  No project imports — avoids axiom issues with subagent.
-/
import Mathlib

open Polynomial Finset

/-- If LT * N = Nd and Nd = -(N * S) and N ≠ 0, then LT = -S. -/
theorem chord_sum_from_product_form {q : ℕ} [Fact (Nat.Prime q)]
    (LT S N Nd : ZMod q)
    (hNne : N ≠ 0)
    (hPFE : Nd = -(N * S))
    (hProd : LT * N = Nd) :
    LT = -S :=
  mul_left_cancel₀ hNne <| by linear_combination' hProd + hPFE

/-
4-point partial fraction identity with linear numerator.
-/
theorem pf_four_point_linear {K : Type*} [Field K]
    (x₀ x₁ x₂ α c d : K)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (h0α : x₀ ≠ α) (h1α : x₁ ≠ α) (h2α : x₂ ≠ α) :
    (c * x₀ + d) / ((x₀ - α) * ((x₀ - x₁) * (x₀ - x₂))) +
    (c * x₁ + d) / ((x₁ - α) * ((x₁ - x₀) * (x₁ - x₂))) +
    (c * x₂ + d) / ((x₂ - α) * ((x₂ - x₀) * (x₂ - x₁))) =
    -(c * α + d) / ((α - x₀) * ((α - x₁) * (α - x₂))) := by
  rw [ div_add_div, div_add_div, div_eq_div_iff ];
  grind +ring;
  grind +ring;
  · grind +revert;
  · grind;
  · grind;
  · exact mul_ne_zero ( sub_ne_zero_of_ne h0α ) ( mul_ne_zero ( sub_ne_zero_of_ne h01 ) ( sub_ne_zero_of_ne h02 ) );
  · exact mul_ne_zero ( sub_ne_zero_of_ne h1α ) ( mul_ne_zero ( sub_ne_zero_of_ne ( Ne.symm h01 ) ) ( sub_ne_zero_of_ne h12 ) )

/-- The logDerivTerm numerator decomposes as `2y·D_chord'(x) - b(x)·f'(x)`. -/
theorem logDerivTerm_numerator_decomp {K : Type*} [Field K]
    (a' b' b lam mu x curveA : K) :
    let y := lam * x + mu
    let fp := 3 * x ^ 2 + curveA - 2 * lam * y
    let dchord' := a' - b' * y - b * lam
    (a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + curveA) =
    2 * y * dchord' - b * fp := by
  ring

/-- Splitting `(A - B*C) / (D*C) = A/(D*C) - B/D` for nonzero D, C. -/
theorem div_split_sub {K : Type*} [Field K]
    (A B C D : K) (_hD : D ≠ 0) (hC : C ≠ 0) :
    (A - B * C) / (D * C) = A / (D * C) - B / D := by
  rw [sub_div, mul_div_mul_right _ _ hC]