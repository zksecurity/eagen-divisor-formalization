/-
  Divisor/ChordCubicSymmetric.lean

  Elementary symmetric polynomial identities for the **chord cubic**

      x³ − λ² x² + (A − 2 λ μ) x + (B − μ²)

  whose roots are the three x-coordinates `x₀, x₁, x₂` of the chord
  intersections of the line `y = λ x + μ` with the elliptic curve
  `y² = x³ + A x + B` over `F_q`.

  These identities are the algebraic levers for the chord-residue and
  log-derivative identities:

  * `e₁ = x₀ + x₁ + x₂ = λ²`
  * `e₂ = x₀ x₁ + x₀ x₂ + x₁ x₂ = A − 2 λ μ`
  * `e₃ = x₀ x₁ x₂ = μ² − B`

  They are consumed downstream (notably by `Divisor/ChordSumBZero.lean`
  and any proof of `chord_sum_eq_residue_sum`) to clear denominators
  and reduce the chord-sum log-derivative identity to a polynomial
  identity in `(ZMod E.q)[x₀, x₁, x₂, A, B, λ, μ]`.

  The goal is to express the three symmetric sums in terms of the
  chord-cubic coefficients `λ²`, `A − 2λμ`, `μ² − B`, derived directly
  from the chord construction: each `A_i = (x_i, y_i)` lies on `E`
  with `y_i = λ x_i + μ`, which gives `(λ x_i + μ)² = x_i³ + A x_i + B`,
  a cubic in `x_i` whose three roots are the `x_i`.
-/
import Divisor.PolyGSlopeProjection
import Mathlib

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The chord cubic coefficients

When `A₀ = (x₀, y₀), A₁ = (x₁, y₁) ∈ E` satisfy `x₀ ≠ x₁`, set
`λ = slopeOf x₀ y₀ x₁ y₁ = (y₁ − y₀) · (x₁ − x₀)⁻¹` and
`μ = y₀ − λ x₀`. Define `A₂ = (x₂, y₂)` with
`x₂ = λ² − x₀ − x₁` and `y₂ = λ x₂ + μ`.

Then `x₀, x₁, x₂` are the three roots of the chord cubic and
`A₂ ∈ E`. This is the "chord-and-tangent" construction.
-/

/-- **Elementary symmetric sum `e₁`:** the three chord x-coordinates
sum to `λ²`. Immediate from `x₂ := λ² − x₀ − x₁`. -/
theorem chord_x_sum_eq_lam_sq
    (x₀ y₀ x₁ y₁ : ZMod E.q) :
    let lam := slopeOf x₀ y₀ x₁ y₁
    x₀ + x₁ + (lam ^ 2 - x₀ - x₁) = lam ^ 2 := by
  intro lam
  ring

/-- **Elementary symmetric sum `e₂`:** pairwise products of the three
chord x-coordinates equal `A − 2λμ`, where `A = E.curveA` and
`μ = y₀ − λ x₀`.

PROVIDED SOLUTION
Algebraic derivation from the chord construction: both `A₀` and `A₁`
lie on the elliptic curve `y² = x³ + A x + B` AND on the line
`y = λ x + μ`. Eliminating `y` yields the cubic equation
`x³ − λ² x² + (A − 2 λ μ) x + (B − μ²) = 0` whose roots are
`x₀, x₁, x₂`. Vieta for a monic cubic gives `e₂ = A − 2λμ`.

In Lean:
1. Hypotheses: `A₀, A₁ ∈ E.points` (from `hA₀`, `hA₁`) give
   `y₀² = x₀³ + A x₀ + B` and `y₁² = x₁³ + A x₁ + B`.
2. `x₀ ≠ x₁` (from `hNV`) lets us extract `λ` with
   `y₁ − y₀ = λ · (x₁ − x₀)`.
3. `linear_combination` the curve equations against the slope
   relation to produce `x₀·x₁ + x₀·x₂ + x₁·x₂ − (A − 2λμ) = 0`
   where `x₂ = λ² − x₀ − x₁`, `μ = y₀ − λ x₀`.
4. The key algebraic identity:
     `(y₁ − y₀) / (x₁ − x₀) = λ`
     ⟹ `(y₁ − y₀)² = λ² (x₁ − x₀)²` (multiply through)
     ⟹ expand `y_i² = x_i³ + A x_i + B` on both sides.
   This gives a polynomial equation from which `e₂ = A − 2λμ` falls out.
5. Alternative: prove via `field_simp` on slopeOf definition plus
   curve equations, then `linear_combination` or `polyrith`. -/
theorem chord_x_pairwise_sum
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let mu  := A₀.2 - lam * A₀.1
    let x₂  := lam ^ 2 - A₀.1 - A₁.1
    A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂ = E.curveA - 2 * lam * mu := by
  simp only [slopeOf]
  have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have h₀ := E.hOnCurve A₀ hA₀
  have h₁ := E.hOnCurve A₁ hA₁
  field_simp
  linear_combination (A₁.1 - A₀.1) * h₁ - (A₁.1 - A₀.1) * h₀

/-- **Elementary symmetric sum `e₃`:** product of the three chord
x-coordinates equals `μ² − B`, where `μ = y₀ − λ x₀` and
`B = E.curveB`.

PROVIDED SOLUTION
Same chord-cubic Vieta as `chord_x_pairwise_sum`. The monic cubic
    `x³ − λ² x² + (A − 2 λ μ) x + (B − μ²)`
has constant term `B − μ²`, so `e₃ = −(constant term) = μ² − B`.

In Lean:
1. Extract `λ (x₁ − x₀) = y₁ − y₀` from `slopeOf` and `hNV`.
2. Use `hA₀`, `hA₁` (curve equations).
3. `linear_combination` against these relations to discharge
   `x₀ · x₁ · (λ² − x₀ − x₁) − (μ² − B) = 0` where `μ = y₀ − λ x₀`. -/
theorem chord_x_triple_product
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let mu  := A₀.2 - lam * A₀.1
    let x₂  := lam ^ 2 - A₀.1 - A₁.1
    A₀.1 * A₁.1 * x₂ = mu ^ 2 - E.curveB := by
  simp only [slopeOf]
  have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have h₀ := E.hOnCurve A₀ hA₀
  have h₁ := E.hOnCurve A₁ hA₁
  field_simp
  linear_combination -(A₁.1 - A₀.1) * A₁.1 * h₀ + A₀.1 * (A₁.1 - A₀.1) * h₁

/-- **Chord third point lies on E.** Given `A₀, A₁ ∈ E.points` with
`A₀.1 ≠ A₁.1`, the constructed `A₂ = (λ² − x₀ − x₁, λ·x₂ + μ)` lies
on the curve `y² = x³ + A x + B`.

PROVIDED SOLUTION
Direct computation: `y₂² − (x₂³ + A x₂ + B) = 0` is a polynomial
identity modulo the slope relation and the two curve equations at
`A₀, A₁`. `linear_combination` should close it.

Alternative: use `E.hComplete` to deduce `A₂ ∈ E.points` from the
curve equation at `A₂`. -/
theorem chord_third_point_on_E
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let x₂  := lam ^ 2 - A₀.1 - A₁.1
    let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
    y₂ ^ 2 = x₂ ^ 3 + E.curveA * x₂ + E.curveB := by
  intro lam x₂ y₂
  have he₂ := chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  have he₃ := chord_x_triple_product E A₀ A₁ hA₀ hA₁ hNV
  simp only [] at he₂ he₃
  linear_combination x₂ * he₂ - he₃

/-- **Chord-line Bezout helper.** For `A₀, A₁ ∈ E.points` with
`A₀.1 ≠ A₁.1`, any point `Q ∈ E.points` lying on the chord line
`y = λ·x + μ` (where `λ = slopeOf A₀ A₁`, `μ = A₀.2 − λ·A₀.1`) is
exactly one of the three chord-fiber points: `A₀`, `A₁`, or
`A₂ = (λ² − A₀.1 − A₁.1, λ·A₂.1 + μ)`.

Proof: the curve equation `Q.2² = Q.1³ + A·Q.1 + B` together with
`Q.2 = λ·Q.1 + μ` (from the chord) yield the cubic
`Q.1³ − λ²·Q.1² + (A − 2λμ)·Q.1 − (μ² − B) = 0`. By Vieta
(`chord_x_pairwise_sum`, `chord_x_triple_product`) this cubic factors
as `(Q.1 − A₀.1)(Q.1 − A₁.1)(Q.1 − x₂) = 0`, so `Q.1 ∈
{A₀.1, A₁.1, x₂}`; pairing with `Q.2 = λ·Q.1 + μ` and the analogous
equations at `A₀, A₁, A₂` identifies `Q` with the corresponding
chord point. -/
theorem chord_line_support_in_E
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (Q : ZMod E.q × ZMod E.q)
    (hQ : Q ∈ E.points)
    (hLine : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0) :
    Q = A₀ ∨ Q = A₁ ∨
      Q = (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
           slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
           (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) := by
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLamDef
  set mu := A₀.2 - lam * A₀.1 with hMuDef
  set x₂ := lam ^ 2 - A₀.1 - A₁.1 with hx₂Def
  -- Step 1: Q lies on the chord line, so `Q.2 = λ·Q.1 + μ`.
  have hQy : Q.2 = lam * Q.1 + mu := by
    have hL : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2
            = Q.2 - lam * Q.1 - mu := by
      simp [Line.eval, lineThrough, hLamDef, hMuDef]
    have h := hLine
    rw [hL] at h
    linear_combination h
  -- Step 2: curve equation for Q.
  have hQc : Q.2 ^ 2 = Q.1 ^ 3 + E.curveA * Q.1 + E.curveB := E.hOnCurve Q hQ
  -- Step 3: substitute `Q.2 = λ·Q.1 + μ` into the curve equation.
  have hY2 : (lam * Q.1 + mu) ^ 2 = Q.1 ^ 3 + E.curveA * Q.1 + E.curveB := by
    rw [← hQy]; exact hQc
  -- Step 4: Vieta for the chord cubic.
  have he₁ : A₀.1 + A₁.1 + x₂ = lam ^ 2 := by
    show A₀.1 + A₁.1 + (lam ^ 2 - A₀.1 - A₁.1) = lam ^ 2; ring
  have he₂ : A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂ = E.curveA - 2 * lam * mu :=
    chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  have he₃ : A₀.1 * A₁.1 * x₂ = mu ^ 2 - E.curveB :=
    chord_x_triple_product E A₀ A₁ hA₀ hA₁ hNV
  -- Step 5: cubic factors at `Q.1`.
  have hCubic : (Q.1 - A₀.1) * (Q.1 - A₁.1) * (Q.1 - x₂) = 0 := by
    linear_combination
      -Q.1 ^ 2 * he₁ + Q.1 * he₂ - he₃ - hY2
  -- Step 6: case-split on which factor vanishes.
  rcases mul_eq_zero.mp hCubic with h | h
  · rcases mul_eq_zero.mp h with h | h
    · -- Q.1 = A₀.1
      have hx : Q.1 = A₀.1 := sub_eq_zero.mp h
      have hy : Q.2 = A₀.2 := by
        rw [hQy, hx]
        show lam * A₀.1 + (A₀.2 - lam * A₀.1) = A₀.2
        ring
      left
      exact Prod.ext hx hy
    · -- Q.1 = A₁.1
      have hx : Q.1 = A₁.1 := sub_eq_zero.mp h
      -- Slope identity: λ·(A₁.1 − A₀.1) = A₁.2 − A₀.2.
      have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
        show slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2
        have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
        rw [slopeOf]
        field_simp
      have hy : Q.2 = A₁.2 := by
        rw [hQy, hx]
        show lam * A₁.1 + (A₀.2 - lam * A₀.1) = A₁.2
        linear_combination hSlope
      right; left
      exact Prod.ext hx hy
  · -- Q.1 = x₂
    have hx : Q.1 = x₂ := sub_eq_zero.mp h
    have hy : Q.2 = lam * x₂ + mu := by rw [hQy, hx]
    refine Or.inr (Or.inr ?_)
    rw [show Q = (Q.1, Q.2) from Prod.mk.eta.symm, hx, hy]

end Divisor
