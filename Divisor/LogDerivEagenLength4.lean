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

  ## Axiom closure

  `#print axioms logDerivCheckFn_zero_for_eagenBuild_length4` shows:
    propext, Classical.choice, Quot.sound,
    Divisor.chord_fiber_product_eq_normZ_under_split,
    Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g

  Both Divisor-specific axioms are already in `ma_extractable`'s closure
  (soundness side). NO `weil_reciprocity_honest` dependency.

  ## Discharged side conditions (May 2026 update)

  Both `hQline` and `hDen` are now derived internally from `hGood`:
  * `hQline_of_hGood_eagenBuild_length4` — Bezout argument.
  * `hDen_of_hGood` — chord-derivative-denominator factorization
    `3·pt.x² + A − 2λ·pt.y = (pt.x − A_i.x)(pt.x − A_j.x)` for various
    indices. Combined with strengthened bad set excluding the relevant
    tangent collisions.

  The main theorem `logDerivCheckFn_zero_for_eagenBuild_length4` only
  takes `hResidueMatch` as the user-supplied per-pair hypothesis.

  ## Remaining gaps to fully discharge `weil_reciprocity_honest`

  1. `hResidueMatch` (protocol-level identification of the four eagenBuild
     inputs `{P_0..P_3}` with the honest message structure
     `{(-P), B_j with multiplicities}`) — genuinely application-specific.
     For length-4 with k=3 distinct bases at scalars 1, this is the
     identification `[P_0, P_1, P_2, P_3] = [(-P), B_1, B_2, B_3]`
     after a permutation determined by `wit.scalars`.

  2. General-N `eagenBuild` — currently only length-4. Honest divisors
     for general k bases + scalars require the recursive driver from
     Eagen §3.1.1 (paper p. 4). Length-4 only handles the special case
     where the input list has exactly 4 elements with all distinct
     x-coordinates (so no doublings, no repeats).
-/

import Divisor.IncrementalConstruction
import Divisor.WeilReciprocityDescent

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## hDen identity: chord-derivative-denominator factorization

Key algebraic identity for deriving `hDen` from `¬badPairCompletenessPred`:

  `3·A_0.x² + curveA − 2λ·A_0.y = (A_0.x − A_1.x)(A_0.x − A_2.x)`

where `A_2.x = λ² − A_0.x − A_1.x`. So the chord-derivative-denominator
at A_0 vanishes iff A_0.x = A_1.x (excluded by hNV) or A_2.x = A_0.x
(chord-tangent at A_0, equivalent to A_2 = A_0 modulo chord-y formula,
excluded by `¬tangentCollisionAtA_0` in the strengthened B4 bad set).

This identity uses `chord_x_pairwise_sum` (Vieta `e_2 = A − 2λμ`) plus
the trivial `lam² = A_0.x + A_1.x + A_2.x` (`e_1`) substitution.

Derivation pending — once landed, hDen at all three points (A_0, A_1, A_2)
follows by symmetric/trivial application. -/

theorem chord_deriv_denom_factor_at_A₀
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let A₂x := lam ^ 2 - A₀.1 - A₁.1
    3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2
      = (A₀.1 - A₁.1) * (A₀.1 - A₂x) := by
  intro lam A₂x
  -- Vieta `e_2 = A - 2λμ`: A_0.x · A_1.x + A_0.x · A_2.x + A_1.x · A_2.x = A - 2λμ.
  -- where μ = A_0.y - λ · A_0.x.
  have hVieta := chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  simp only [show (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 : ZMod E.q) = lam from rfl] at hVieta
  -- Unfold lets in hVieta:
  have hVieta' : A₀.1 * A₁.1 + A₀.1 * A₂x + A₁.1 * A₂x
      = E.curveA - 2 * lam * (A₀.2 - lam * A₀.1) := hVieta
  -- Now ring:
  have h_A2x : A₂x = lam ^ 2 - A₀.1 - A₁.1 := rfl
  linear_combination -hVieta'

theorem chord_deriv_denom_factor_at_A₁
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let A₂x := lam ^ 2 - A₀.1 - A₁.1
    3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2
      = (A₁.1 - A₀.1) * (A₁.1 - A₂x) := by
  intro lam A₂x
  have hVieta := chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  simp only [show (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 : ZMod E.q) = lam from rfl] at hVieta
  have hVieta' : A₀.1 * A₁.1 + A₀.1 * A₂x + A₁.1 * A₂x
      = E.curveA - 2 * lam * (A₀.2 - lam * A₀.1) := hVieta
  have h_A2x : A₂x = lam ^ 2 - A₀.1 - A₁.1 := rfl
  -- Slope: lam · (A_1.x - A_0.x) = A_1.y - A_0.y.
  have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    show slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2
    unfold slopeOf
    have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
    field_simp
  linear_combination -hVieta' + 2 * lam * hSlope

theorem chord_deriv_denom_factor_at_A₂
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let A₂x := lam ^ 2 - A₀.1 - A₁.1
    let A₂y := lam * A₂x + (A₀.2 - lam * A₀.1)
    3 * A₂x ^ 2 + E.curveA - 2 * lam * A₂y
      = (A₂x - A₀.1) * (A₂x - A₁.1) := by
  intro lam A₂x A₂y
  have hVieta := chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  simp only [show (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 : ZMod E.q) = lam from rfl] at hVieta
  have hVieta' : A₀.1 * A₁.1 + A₀.1 * A₂x + A₁.1 * A₂x
      = E.curveA - 2 * lam * (A₀.2 - lam * A₀.1) := hVieta
  have h_A2x : A₂x = lam ^ 2 - A₀.1 - A₁.1 := rfl
  have h_A2y : A₂y = lam * A₂x + (A₀.2 - lam * A₀.1) := rfl
  linear_combination -hVieta'

/-! ## hDen derivation from hGood (strengthened bad set)

Combine the chord-derivative-denominator factorization identities with
the B4-strengthened `¬badPairCompletenessPred` to discharge `hDen`. -/

theorem hDen_of_hGood
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E D) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    ∀ pt : ZMod E.q × ZMod E.q,
      pt = A₀ ∨ pt = A₁ ∨
      pt = (lam ^ 2 - A₀.1 - A₁.1,
            lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0 := by
  classical
  intro lam
  set A₂x : ZMod E.q := lam ^ 2 - A₀.1 - A₁.1 with hA₂x_def
  set A₂y : ZMod E.q := lam * A₂x + (A₀.2 - lam * A₀.1) with hA₂y_def
  have hMem : (A₀, A₁) ∈ E.points ×ˢ E.points := Finset.mk_mem_product hA₀ hA₁
  have h_unbad : ¬ badPairCompletenessPred E D (A₀, A₁) := fun hbad =>
    hGood (Finset.mem_filter.mpr ⟨hMem, hbad⟩)
  -- thirdPoint formula.
  have hThirdEq : thirdPoint E A₀ A₁ = some (A₂x, A₂y) := by
    unfold thirdPoint
    rw [if_neg hNV]
    rfl
  have hNotDiag : A₀ ≠ A₁ := fun h => h_unbad (by
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    show (A₀, A₁).1 = (A₀, A₁).2
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    exact h)
  -- ¬tangentCollisionAtA_0: thirdPoint ≠ some A_0.
  have hNotTangent_A₀ : (A₂x, A₂y) ≠ A₀ := fun h => h_unbad (by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    show thirdPoint E (A₀, A₁).1 (A₀, A₁).2 = some (A₀, A₁).1
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq, h])
  -- ¬tangentCollisionAtA_1: thirdPoint ≠ some A_1.
  have hNotTangent_A₁ : (A₂x, A₂y) ≠ A₁ := fun h => h_unbad (by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    show thirdPoint E (A₀, A₁).1 (A₀, A₁).2 = some (A₀, A₁).2
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq, h])
  -- A_2.x ≠ A_0.x.
  have hA₂x_ne_A₀x : A₂x ≠ A₀.1 := by
    intro h
    apply hNotTangent_A₀
    -- From A_2.x = A_0.x and chord-line, A_2.y = A_0.y, so A_2 = A_0.
    have hA₂y : A₂y = A₀.2 := by
      rw [hA₂y_def, h]; ring
    exact Prod.ext h hA₂y
  -- A_2.x ≠ A_1.x.
  have hA₂x_ne_A₁x : A₂x ≠ A₁.1 := by
    intro h
    apply hNotTangent_A₁
    -- From A_2.x = A_1.x, A_2.y = lam·A_1.x + μ = lam·A_1.x + A_0.y - lam·A_0.x
    --                          = A_0.y + lam·(A_1.x - A_0.x) = A_1.y (by slope identity).
    have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
      show slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2
      unfold slopeOf
      have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
      field_simp
    have hA₂y : A₂y = A₁.2 := by
      rw [hA₂y_def, h]
      linear_combination hSlope
    exact Prod.ext h hA₂y
  intro pt hpt
  rcases hpt with h | h | h
  · -- pt = A_0.
    rw [h, chord_deriv_denom_factor_at_A₀ E A₀ A₁ hA₀ hA₁ hNV]
    intro hMul
    rcases mul_eq_zero.mp hMul with h₁ | h₂
    · exact (sub_ne_zero.mpr hNV) h₁
    · exact (sub_ne_zero.mpr (Ne.symm hA₂x_ne_A₀x)) h₂
  · -- pt = A_1.
    rw [h, chord_deriv_denom_factor_at_A₁ E A₀ A₁ hA₀ hA₁ hNV]
    intro hMul
    rcases mul_eq_zero.mp hMul with h₁ | h₂
    · exact (sub_ne_zero.mpr (Ne.symm hNV)) h₁
    · exact (sub_ne_zero.mpr (Ne.symm hA₂x_ne_A₁x)) h₂
  · -- pt = A_2.
    rw [h]
    show 3 * A₂x ^ 2 + E.curveA - 2 * lam * A₂y ≠ 0
    rw [chord_deriv_denom_factor_at_A₂ E A₀ A₁ hA₀ hA₁ hNV]
    intro hMul
    rcases mul_eq_zero.mp hMul with h₁ | h₂
    · exact (sub_ne_zero.mpr hA₂x_ne_A₀x) h₁
    · exact (sub_ne_zero.mpr hA₂x_ne_A₁x) h₂

/-! ## Residue sum expansion: closed-form RHS for hResidueMatch

The chord-residue sum on the LHS of `hResidueMatch` expands explicitly to
the sum of L-evaluation-reciprocals at each input point P_i (since
zerosFinset = {P_0..P_3} and ordAt = 1 at each). -/

theorem eagenBuild_length4_residue_sum_eq
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
    (L : Line E.q) :
    (∑ Q ∈ zerosFinset E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃),
        (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) Q : ZMod E.q) *
        (L.eval Q.1 Q.2)⁻¹)
      = (L.eval P₀.1 P₀.2)⁻¹ + (L.eval P₁.1 P₁.2)⁻¹
        + (L.eval P₂.1 P₂.2)⁻¹ + (L.eval P₃.1 P₃.2)⁻¹ := by
  classical
  -- ordAt = 1 at each input.
  have ord_P₀ : ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₀ = 1 := by
    have hDiv := eagenBuild_length4_div_at_P₀ E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_third_match h_y_match h_Q₀_nontorsion
    have h_eq : divisorOfD E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
                  (ECPoint.affine E P₀.1 P₀.2)
          = (ordAtPoint E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
              (ECPoint.affine E P₀.1 P₀.2) : ℤ) := by
      rw [ECPoint.affine_of_nonsingular E
            (E.equation_iff_nonsingular.mp ((E.equation_iff P₀.1 P₀.2).mpr (E.hOnCurve _ hP₀)))]
      rfl
    rw [h_eq, ordAtPoint_affine E _ hP₀] at hDiv
    have : (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₀ : ℤ) = 1 := hDiv
    omega
  have ord_P₁ : ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₁ = 1 := by
    have hDiv := eagenBuild_length4_div_at_P₁ E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₁_off_L₂ h_third_match h_y_match h_Q₀_nontorsion
    have h_eq : divisorOfD E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
                  (ECPoint.affine E P₁.1 P₁.2)
          = (ordAtPoint E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
              (ECPoint.affine E P₁.1 P₁.2) : ℤ) := by
      rw [ECPoint.affine_of_nonsingular E
            (E.equation_iff_nonsingular.mp ((E.equation_iff P₁.1 P₁.2).mpr (E.hOnCurve _ hP₁)))]
      rfl
    rw [h_eq, ordAtPoint_affine E _ hP₁] at hDiv
    have : (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₁ : ℤ) = 1 := hDiv
    omega
  have ord_P₂ : ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₂ = 1 := by
    have hDiv := eagenBuild_length4_div_at_P₂ E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₂_off_L₁ h_third_match h_y_match h_Q₀_nontorsion
    have h_eq : divisorOfD E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
                  (ECPoint.affine E P₂.1 P₂.2)
          = (ordAtPoint E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
              (ECPoint.affine E P₂.1 P₂.2) : ℤ) := by
      rw [ECPoint.affine_of_nonsingular E
            (E.equation_iff_nonsingular.mp ((E.equation_iff P₂.1 P₂.2).mpr (E.hOnCurve _ hP₂)))]
      rfl
    rw [h_eq, ordAtPoint_affine E _ hP₂] at hDiv
    have : (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₂ : ℤ) = 1 := hDiv
    omega
  have ord_P₃ : ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₃ = 1 := by
    have hDiv := eagenBuild_length4_div_at_P₃ E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₃_off_L₁ h_third_match h_y_match h_Q₀_nontorsion
    have h_eq : divisorOfD E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
                  (ECPoint.affine E P₃.1 P₃.2)
          = (ordAtPoint E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)
              (ECPoint.affine E P₃.1 P₃.2) : ℤ) := by
      rw [ECPoint.affine_of_nonsingular E
            (E.equation_iff_nonsingular.mp ((E.equation_iff P₃.1 P₃.2).mpr (E.hOnCurve _ hP₃)))]
      rfl
    rw [h_eq, ordAtPoint_affine E _ hP₃] at hDiv
    have : (ordAt E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) P₃ : ℤ) = 1 := hDiv
    omega
  -- zerosFinset = {P_0, P_1, P_2, P_3}.
  rw [zerosFinset_eagenBuild_length4_eq E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
      h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs]
  -- Expand the sum.
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := h_inputs_distinct
  have h_P_0_notin_123 : P₀ ∉ ({P₁, P₂, P₃} : Finset (ZMod E.q × ZMod E.q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨h01, h02, h03⟩
  have h_P_1_notin_23 : P₁ ∉ ({P₂, P₃} : Finset (ZMod E.q × ZMod E.q)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨h12, h13⟩
  have h_P_2_notin_3 : P₂ ∉ ({P₃} : Finset (ZMod E.q × ZMod E.q)) := by
    simp only [Finset.mem_singleton]; exact h23
  rw [show ({P₀, P₁, P₂, P₃} : Finset (ZMod E.q × ZMod E.q))
      = insert P₀ (insert P₁ (insert P₂ ({P₃} : Finset _))) from rfl]
  rw [Finset.sum_insert h_P_0_notin_123,
      Finset.sum_insert h_P_1_notin_23,
      Finset.sum_insert h_P_2_notin_3,
      Finset.sum_singleton]
  rw [ord_P₀, ord_P₁, ord_P₂, ord_P₃]
  push_cast
  ring

/-! ## hQline derivation: chord doesn't pass through any zero

For length-4 `D = eagenBuild_length4`, `zerosFinset = {P_0..P_3}`. A
chord through `(A_0, A_1)` (non-vertical) intersects `E` in
`{A_0, A_1, A_2}`. The pair being "good" (`¬badPairCompletenessPred`)
excludes `D` vanishing at any of `{A_0, A_1, A_2}`. Hence no zero of
`D` lies on the chord. -/

theorem hQline_of_hGood_eagenBuild_length4
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
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E
              (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃)) :
    ∀ Q ∈ zerosFinset E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 := by
  classical
  intro Q hQzeros
  -- Q ∈ zerosFinset implies Q.1, Q.2 are coords of some P_i.
  have hQfin := zerosFinset_eagenBuild_length4_eq E P₀ P₁ P₂ P₃
    hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
    h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
    h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
  rw [hQfin] at hQzeros
  -- Q is in E.points (since zerosFinset ⊆ E.points).
  have hQE : Q ∈ E.points := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQzeros
    rcases hQzeros with h | h | h | h
    · rw [h]; exact hP₀
    · rw [h]; exact hP₁
    · rw [h]; exact hP₂
    · rw [h]; exact hP₃
  -- Suppose chord(Q) = 0. Then Q ∈ {A_0, A_1, A_2}.
  intro hZero
  have hQ_in_chord : Q = A₀ ∨ Q = A₁ ∨
      Q = (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
           slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
           (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) :=
    chord_line_support_in_E E A₀ A₁ hA₀ hA₁ hNV Q hQE hZero
  -- ¬bad: D doesn't vanish at A_0, A_1, A_2.
  have hMem : (A₀, A₁) ∈ E.points ×ˢ E.points := Finset.mk_mem_product hA₀ hA₁
  have h_unbad : ¬ badPairCompletenessPred E
      (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) (A₀, A₁) := fun hbad =>
    hGood (Finset.mem_filter.mpr ⟨hMem, hbad⟩)
  -- Q ∈ zerosFinset means D.eval Q = 0.
  have hQzero : (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃).eval Q.1 Q.2 = 0 := by
    -- zerosFinset = E.points.filter (D.eval = 0) — extract the filter.
    have h_back := zerosFinset_eagenBuild_length4_eq E P₀ P₁ P₂ P₃
      hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
      h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
      h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
    have : Q ∈ zerosFinset E (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃) := by
      rw [h_back]; exact hQzeros
    unfold zerosFinset zeros at this
    exact (Finset.mem_filter.mp this).2
  -- thirdPoint formula matches.
  have hThirdEq : thirdPoint E A₀ A₁ =
      some (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
            slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
            (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) := by
    unfold thirdPoint slopeOf
    rw [if_neg hNV]
  rcases hQ_in_chord with hQA₀ | hQA₁ | hQA₂
  · -- Q = A_0: D.eval A_0 = 0 contradicts ¬bad.
    apply h_unbad
    exact Or.inl (by rw [← hQA₀]; exact hQzero)
  · -- Q = A_1: similar.
    apply h_unbad
    exact Or.inr (Or.inl (by rw [← hQA₁]; exact hQzero))
  · -- Q = A_2: D.eval A_2 = 0 contradicts ¬bad.
    apply h_unbad
    refine Or.inr (Or.inr (Or.inl ?_))
    show (match thirdPoint E (A₀, A₁).1 (A₀, A₁).2 with
      | none => True
      | some (x, y) => (eagenBuild_length4_explicit E P₀ P₁ P₂ P₃).eval x y = 0)
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq]
    rw [← hQA₂]; exact hQzero

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
  -- hQline: derived from hGood via Bezout.
  have hQline := hQline_of_hGood_eagenBuild_length4 E P₀ P₁ P₂ P₃
    hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
    h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
    h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
    A₀ A₁ hA₀ hA₁ hNV hGood
  -- hDen: derived from hGood via chord-derivative-denominator factorization.
  have hDen := hDen_of_hGood E D A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply logDerivCheckFn_zero_of_explicit_divisor_data.
  exact logDerivCheckFn_zero_of_explicit_divisor_data E D P_target B m
    (ordAt E D) hNZ hSplit hβsup hβcov hAccount hβtrue
    A₀ A₁ hA₀ hA₁ hNV hGood hQline hDen hResidueMatch

end Divisor
