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

  ## Remaining gaps to fully discharge `weil_reciprocity_honest`

  1. `hDen` (denominator non-vanishing for chord-derivative formula at
     A_0, A_1, A_2) — currently explicit. Mathematically follows from
     B4-strengthened `¬badPairCompletenessPred` via:
       3·pt.x² + A − 2λ·pt.y = 0 ⟺ pt.x is a double root of the chord
       cubic ⟺ A_2.x = A_0.x or A_2.x = A_1.x ⟺ A_2 = A_0 or A_2 = A_1
       (chord determines y from x) ⟺ tangentCollisionAtA_i — excluded
       by B4. Lean derivation pending (~100 LOC algebraic chain via
       `chord_x_pairwise_sum`, `chord_x_triple_product`).

  2. `hResidueMatch` (protocol-level identification of the four eagenBuild
     inputs `{P_0..P_3}` with the honest message structure
     `{(-P), B_j with multiplicities}`) — genuinely application-specific.
     For length-4 with k=3 distinct bases at scalars 1, this is the
     identification `[P_0, P_1, P_2, P_3] = [(-P), B_1, B_2, B_3]`
     after a permutation determined by `wit.scalars`.

  3. General-N `eagenBuild` — currently only length-4. Honest divisors
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
  -- hQline: derived from hGood via Bezout.
  have hQline := hQline_of_hGood_eagenBuild_length4 E P₀ P₁ P₂ P₃
    hP₀ hP₁ hP₂ hP₃ h_xx_01 h_xx_23 h_P₀_ne_A2_01 h_P₁_ne_A2_01
    h_P₂_ne_A2_23 h_P₃_ne_A2_23 h_P₀_off_L₂ h_P₁_off_L₂ h_P₂_off_L₁ h_P₃_off_L₁
    h_third_match h_y_match h_Q₀_nontorsion h_Q₀_off_L₂_inputs h_negQ₀_off_L₁_inputs
    A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply logDerivCheckFn_zero_of_explicit_divisor_data.
  exact logDerivCheckFn_zero_of_explicit_divisor_data E D P_target B m
    (ordAt E D) hNZ hSplit hβsup hβcov hAccount hβtrue
    A₀ A₁ hA₀ hA₁ hNV hGood hQline hDen hResidueMatch

end Divisor
