/-
  Divisor/ChordCubicSymmetric.lean

  Elementary symmetric polynomial identities for the **chord cubic**

      x³ − λ² x² + (A − 2 λ μ) x + (B − μ²)

  whose roots are the three x-coordinates `x₀, x₁, x₂` of the chord
  intersections of the line `y = λ x + μ` with the elliptic curve
  `y² = x³ + A x + B` over `F_q`.

  These identities are the algebraic levers of §5 of `docs/goal.md`:

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
import Divisor.Defs
import Divisor.PolyFibK
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
  sorry

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
  sorry

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
  sorry

end Divisor
