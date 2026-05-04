/-
  Divisor/LogDerivEagenLength4.lean

  Length-4-specific application of `logDerivCheckFn_zero_of_explicit_divisor_data`
  using `eagenBuild_length4_explicit` as the divisor witness.

  This wires together:
  * The constructive D = `eagenBuild_length4_explicit P_0 P_1 P_2 P_3`.
  * Static prerequisites (D ≠ 0, splitsOnE, zerosFinset = {P_0..P_3},
    sum of ordAt = natDegree, β_fun = ordAt = betaTrue) — all proved.
  * Per-pair side conditions (hQline, hDen, hResidueMatch) as explicit
    hypotheses.

  Output: `logDerivCheckFn E D P_target k B m A_0 A_1 = 0` for any "good"
  (`¬ badChallengesCompleteness`) pair (A_0, A_1).

  This is the length-4 specialization of the (currently axiomatic)
  `weil_reciprocity_honest`, with the formerly-unsound axiom statement
  replaced by a constructive theorem about `eagenBuild_length4_explicit`.
-/

import Divisor.IncrementalConstruction
import Divisor.WeilReciprocityDescent

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-- Length-4-specific `logDerivCheckFn = 0`: for `D = eagenBuild_length4`
    with all the genericity hypotheses required, and any "good"
    `(A_0, A_1)` pair, the log-derivative check vanishes — modulo the
    per-pair side conditions `hQline`, `hDen`, and the protocol-level
    residue match `hResidueMatch`. -/
theorem logDerivCheckFn_zero_for_eagenBuild_length4
    (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q)
    (hP₀ : P₀ ∈ E.points) (hP₁ : P₁ ∈ E.points)
    (hP₂ : P₂ ∈ E.points) (hP₃ : P₃ ∈ E.points)
    (h_xx_01 : P₀.1 ≠ P₁.1) (h_xx_23 : P₂.1 ≠ P₃.1)
    (h_P₀_ne_A2_01 : P₀.1 ≠ slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
    (h_P₁_ne_A2_01 : P₁.1 ≠ slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
    (h_P₂_ne_A2_23 : P₂.1 ≠ slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1)
    (h_P₃_ne_A2_23 : P₃.1 ≠ slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1)
    (h_P₀_off_L₂ : P₀ ≠ P₂ ∧ P₀ ≠ P₃ ∧ P₀ ≠ (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1,
                    slopeOf P₂.1 P₂.2 P₃.1 P₃.2
                      * (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1)
                      + (P₂.2 - slopeOf P₂.1 P₂.2 P₃.1 P₃.2 * P₂.1)))
    (h_P₁_off_L₂ : P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₁ ≠ (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1,
                    slopeOf P₂.1 P₂.2 P₃.1 P₃.2
                      * (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1)
                      + (P₂.2 - slopeOf P₂.1 P₂.2 P₃.1 P₃.2 * P₂.1)))
    (h_P₂_off_L₁ : P₂ ≠ P₀ ∧ P₂ ≠ P₁ ∧ P₂ ≠ (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1,
                    slopeOf P₀.1 P₀.2 P₁.1 P₁.2
                      * (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
                      + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)))
    (h_P₃_off_L₁ : P₃ ≠ P₀ ∧ P₃ ≠ P₁ ∧ P₃ ≠ (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1,
                    slopeOf P₀.1 P₀.2 P₁.1 P₁.2
                      * (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
                      + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)))
    (h_third_match :
      slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1
        = slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
    (h_y_match :
      slopeOf P₂.1 P₂.2 P₃.1 P₃.2
        * (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1)
        + (P₂.2 - slopeOf P₂.1 P₂.2 P₃.1 P₃.2 * P₂.1)
          = -(slopeOf P₀.1 P₀.2 P₁.1 P₁.2
              * (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
              + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)))
    (h_Q₀_nontorsion : slopeOf P₀.1 P₀.2 P₁.1 P₁.2
                        * (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
                        + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1) ≠ 0)
    (h_Q₀_off_L₂_inputs :
      let Q₀x := slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1
      let Q₀y := slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * Q₀x + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)
      (Q₀x, Q₀y) ≠ P₂ ∧ (Q₀x, Q₀y) ≠ P₃ ∧ (Q₀x, Q₀y) ≠ (Q₀x, -Q₀y))
    (h_negQ₀_off_L₁_inputs :
      let Q₀x := slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1
      let Q₀y := slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * Q₀x + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)
      (Q₀x, -Q₀y) ≠ P₀ ∧ (Q₀x, -Q₀y) ≠ P₁ ∧ (Q₀x, -Q₀y) ≠ (Q₀x, Q₀y))
    (h_inputs_distinct : P₀ ≠ P₁ ∧ P₀ ≠ P₂ ∧ P₀ ≠ P₃ ∧ P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃)
    (P_target : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E
              (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃))
    (hQline : ∀ Q ∈ zerosFinset E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hResidueMatch :
      (∑ Q ∈ zerosFinset E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃),
          (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P_target.1 (-P_target.2))⁻¹
          + (Finset.univ : Finset (Fin k)).sum
              (fun j => (m j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)) :
    logDerivCheckFn E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
        P_target k B m A₀ A₁ = 0 := by
  classical
  set D := eagenBuild_length4_explicit E P₀ P₁ P₂ P₃ with hD_def
  -- Discharge static prerequisites.
  have hNZ : ¬ (D.a = 0 ∧ D.b = 0) := eagenBuild_length4_explicit_ne_zero E P₀ P₁ P₂ P₃
    hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_third_match h_y_match h_Q₀_nontorsion
  have hSplit : splitsOnE E D := splitsOnE_eagenBuild_length4 E P₀ P₁ P₂ P₃
    hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
    h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
    h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
    h_inputs_distinct
  have hAccount : (∑ Q ∈ E.points, ordAt E D Q) = (normPoly E D).natDegree := by
    rw [ordAt_sum_eagenBuild_length4_eq_four E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
      h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
      h_inputs_distinct]
    rw [eagenBuild_length4_normPoly_natDegree_eq_four E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₂_ne_A2_23 h_P₃_ne_A2_23
      h_third_match h_y_match h_Q₀_nontorsion]
  -- β_fun = ordAt = betaTrue.
  have hβsup : ∀ Q, ordAt E D Q ≠ 0 → Q ∈ E.points ∧ D.eval Q.1 Q.2 = 0 :=
    betaTrue_support E D hNZ
  have hβcov : ∀ Q ∈ E.points, D.eval Q.1 Q.2 = 0 → ordAt E D Q ≠ 0 := by
    intro Q hQE hQeval
    have h_pos : 0 < ordAt E D Q := (ordAt_pos_iff_zero E D hNZ Q hQE).mpr hQeval
    omega
  have hβtrue : ∀ Q, ordAt E D Q = betaTrue E D hNZ Q := fun _ => rfl
  -- Apply logDerivCheckFn_zero_of_explicit_divisor_data.
  exact logDerivCheckFn_zero_of_explicit_divisor_data E D P_target B m
    (ordAt E D) hNZ hSplit hβsup hβcov hAccount hβtrue
    A₀ A₁ hA₀ hA₁ hNV hGood hQline hDen hResidueMatch

end Divisor
