/-
  Divisor/LogDerivEagenLength4.lean

  Chord side conditions derived from a good challenge pair
  (`(A_0, A_1) ∉ badChallengesCompleteness E D`):

  * `hNV_of_hGood` — the chord is non-vertical, `A_0.x ≠ A_1.x`.
  * `hDen_of_hGood` — the chord-derivative denominator
    `3·pt.x² + A − 2λ·pt.y` is nonzero at `A_0`, `A_1` and the third
    intersection `A_2`, via the factorization
    `3·pt.x² + A − 2λ·pt.y = (pt.x − A_i.x)(pt.x − A_j.x)`
    (`chord_deriv_denom_factor_at_A₀/₁/₂`); the bad set excludes the
    relevant tangent collisions.
-/

import Divisor.IncrementalConstruction
import Divisor.WeilReciprocityDescent
import Divisor.MACompletenessCore

open Polynomial Finset Classical

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

hDen at all three points (A_0, A_1, A_2) follows by symmetric/trivial
application. -/

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
    -- = A_0.y + lam·(A_1.x - A_0.x) = A_1.y (by slope identity).
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

/-! ## hNV derivation from ¬bad set

For any `(A_0, A_1) ∉ badChallengesCompleteness E D`, we have
`A_0.1 ≠ A_1.1`. The strengthened bad set excludes:
* diagonal A_0 = A_1 (covers A_0.1 = A_1.1 ∧ A_0.2 = A_1.2 ∧ y ≠ 0);
* thirdPoint = none cases (A_0.1 = A_1.1 ∧ A_0.2 ≠ A_1.2 vertical chord;
  A_0 = A_1 = (x, 0) 2-torsion doubling).
Hence A_0.1 = A_1.1 cannot hold for a "good" pair. -/

theorem hNV_of_hGood {D : CoordRingElt E.q}
    {A₀ A₁ : ZMod E.q × ZMod E.q}
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E D) :
    A₀.1 ≠ A₁.1 := by
  classical
  intro hVert
  apply hGood
  refine Finset.mem_filter.mpr ⟨Finset.mk_mem_product hA₀ hA₁, ?_⟩
  -- A_0.1 = A_1.1. Two subcases: A_0 = A_1 (diagonal) or thirdPoint = none.
  by_cases hY : A₀.2 = A₁.2
  · -- Diagonal: A_0 = A_1.
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    show (A₀, A₁).1 = (A₀, A₁).2
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    exact Prod.ext hVert hY
  · -- A_0.1 = A_1.1, A_0.2 ≠ A_1.2 → vertical chord, thirdPoint = none.
    refine Or.inr (Or.inr (Or.inl ?_))
    show (match thirdPoint E (A₀, A₁).1 (A₀, A₁).2 with
      | none => True
      | some (x, y) => D.eval x y = 0)
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    have hThirdNone : thirdPoint E A₀ A₁ = none := by
      unfold thirdPoint
      rw [if_pos hVert]
      rw [if_neg hY]
    rw [hThirdNone]
    trivial

end Divisor
