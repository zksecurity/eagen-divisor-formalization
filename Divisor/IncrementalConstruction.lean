/-
  Divisor/IncrementalConstruction.lean

  Building blocks for the principal-divisor witness
  `D = a(x) − b(x)·y` on the elliptic curve `E`. The underlying
  construction is Miller's (full citation in `Divisor/LineBuild.lean`);
  the scheduling follows Liam Eagen,
  "Zero Knowledge Proofs of Elliptic Curve Inner Products from Principal
  Divisors and Weil Reciprocity" (eprint 2022/596), §3.1.1.

  * `chordCoordRingElt P Q` — the chord / tangent / vertical line
    through `P` and `Q` as a `CoordRingElt`.
  * `mulCoordRingElt` — multiplication in `F_q[E]`, with the norm
    multiplicativity `normPoly_mul_eq`.
  * `ECPoints_same_x_y_eq_or_neg` — two curve points over the same
    x-coordinate have equal or opposite y-coordinates.

  The recursive line build on these blocks lives in
  `Divisor/LineBuild.lean`.
-/
import Divisor.ChordCubicSymmetric
import Divisor.DivisorPrincipal
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Chord / tangent / vertical line as a `CoordRingElt`

Given two affine points `P, Q` on `E`, the line through them (in the
sense of the cubic intersection on `E`) takes one of three shapes:

* **Chord** (`P.1 ≠ Q.1`): slope `λ = (Q.2 − P.2)/(Q.1 − P.1)`, line
  `y − λ·x − μ` with `μ = P.2 − λ·P.1`. Encoded as
  `a = −λ·X − μ`, `b = −1`.

* **Tangent at non-2-torsion** (`P = Q`, `P.2 ≠ 0`): slope
  `λ = (3·P.1² + A)/(2·P.2)`, same line shape as the chord.

* **Vertical** (`P.1 = Q.1` and `P ≠ Q`, *or* `P = Q` with `P.2 = 0`):
  line `x − P.1`. Encoded as `a = X − C P.1`, `b = 0`.

The dispatch matches `thirdPoint` (`Divisor/DefsPre.lean:283`), so the
two are consistent on which branch fires for a given pair. -/

/-- Encoding the line through `P` and `Q` as a `CoordRingElt`. Three
    branches: chord, tangent at non-2-torsion, vertical. -/
noncomputable def chordCoordRingElt
    (P Q : ZMod E.q × ZMod E.q) : CoordRingElt E.q :=
  if _hxx : P.1 = Q.1 then
    if _hyy : P.2 = Q.2 then
      -- coincident point: tangent or vertical (2-torsion).
      if P.2 = 0 then
        -- vertical (2-torsion doubling).
        { a := X - C P.1, b := 0 }
      else
        -- tangent at non-2-torsion.
        let lam : ZMod E.q := (3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹
        let mu : ZMod E.q := P.2 - lam * P.1
        { a := -(C lam) * X - C mu, b := -1 }
    else
      -- same x, different y ⇒ Q = -P: vertical line.
      { a := X - C P.1, b := 0 }
  else
    -- chord through distinct x-coordinates.
    let lam : ZMod E.q := (Q.2 - P.2) * (Q.1 - P.1)⁻¹
    let mu : ZMod E.q := P.2 - lam * P.1
    { a := -(C lam) * X - C mu, b := -1 }


/-! ## Multiplication of `CoordRingElt`s in `F_q[E]`

`F_q[E] = F_q[X,Y]/(Y² - X³ - AX - B)` admits multiplication by reducing
`Y²` to `X³ + AX + B`. For `D₁ = a₁ − b₁·Y` and `D₂ = a₂ − b₂·Y`:

  D₁ · D₂ = (a₁·a₂ + b₁·b₂·(X³+AX+B)) − (a₁·b₂ + a₂·b₁)·Y

So `(D₁ · D₂).a = a₁·a₂ + b₁·b₂·curveX` and
`(D₁ · D₂).b = a₁·b₂ + a₂·b₁`. -/

/-- Multiplication of `CoordRingElt`s in `F_q[E]`. -/
noncomputable def mulCoordRingElt
    (D₁ D₂ : CoordRingElt E.q) : CoordRingElt E.q :=
  { a := D₁.a * D₂.a + D₁.b * D₂.b * curveX E,
    b := D₁.a * D₂.b + D₂.a * D₁.b }

/-- **Key algebraic identity.** The norm polynomial is multiplicative:
    `N(D₁ · D₂) = N(D₁) · N(D₂)`. Direct ring identity — no curve
    machinery needed.

    This is the polynomial-side multiplicativity that drives the
    `natDegree`-additivity used by `divisorOfD` at infinity. -/
theorem normPoly_mul_eq
    (D₁ D₂ : CoordRingElt E.q) :
    normPoly E (mulCoordRingElt E D₁ D₂) = normPoly E D₁ * normPoly E D₂ := by
  rw [normPoly_eq, normPoly_eq, normPoly_eq]
  show (D₁.a * D₂.a + D₁.b * D₂.b * curveX E) ^ 2
        - (D₁.a * D₂.b + D₂.a * D₁.b) ^ 2 * curveX E
      = (D₁.a ^ 2 - D₁.b ^ 2 * curveX E)
        * (D₂.a ^ 2 - D₂.b ^ 2 * curveX E)
  ring


/-- For two points on E with the same x-coordinate, their y-coordinates
    are equal or negatives. Follows from the curve equation
    `y² = x³ + Ax + B`. -/
theorem ECPoints_same_x_y_eq_or_neg
    {x y₁ y₂ : ZMod E.q}
    (h₁ : (x, y₁) ∈ E.points) (h₂ : (x, y₂) ∈ E.points) :
    y₁ = y₂ ∨ y₁ = -y₂ := by
  have he₁ : y₁ ^ 2 = x ^ 3 + E.curveA * x + E.curveB := E.hOnCurve _ h₁
  have he₂ : y₂ ^ 2 = x ^ 3 + E.curveA * x + E.curveB := E.hOnCurve _ h₂
  have h_eq_sq : y₁ ^ 2 = y₂ ^ 2 := he₁.trans he₂.symm
  have h_diff : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination h_eq_sq
  rcases mul_eq_zero.mp h_diff with h | h
  · left; linear_combination h
  · right; linear_combination h


end Divisor
