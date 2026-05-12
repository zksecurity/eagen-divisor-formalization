/-
  Divisor/CoordRingEltC.lean

  Computable analog of `CoordRingElt` built on `CoeffPoly`.  Mirrors
  the construction layer in `Divisor/IncrementalConstruction.lean`:
  `chordCoordRingElt`, `mulCoordRingElt`, and `divLin` — all as plain
  `def`s.

  Bridges to the existing `Polynomial`-valued `CoordRingElt` live in
  a separate file.
-/
import Divisor.CoeffPoly
import Divisor.DefsPre

namespace Divisor

/-- Computable analog of `CoordRingElt q`: a pair of `CoeffPoly q`. -/
structure CoordRingEltC (q : ℕ) where
  a : CoeffPoly q
  b : CoeffPoly q
  deriving Repr, DecidableEq

namespace CoordRingEltC

variable {q : ℕ}

/-- Evaluation `D(x, y) = a(x) - b(x) · y`. -/
def eval (D : CoordRingEltC q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y

/-- Componentwise division by `X - C x₀`. -/
def divLin (D : CoordRingEltC q) (x₀ : ZMod q) : CoordRingEltC q :=
  { a := D.a.divXSubC x₀
    b := D.b.divXSubC x₀ }

/-- Multiplication in `F_q[E] = F_q[X, Y] / (Y² − X³ − A·X − B)`.

    `(a₁ − b₁·Y) · (a₂ − b₂·Y)
        = (a₁·a₂ + b₁·b₂·(X³ + A·X + B)) − (a₁·b₂ + a₂·b₁) · Y`. -/
def mul (curveA curveB : ZMod q) (D₁ D₂ : CoordRingEltC q) :
    CoordRingEltC q :=
  let curveXP : CoeffPoly q :=
    -- X^3 + curveA · X + curveB, coeffs [B, A, 0, 1]
    ⟨[curveB, curveA, 0, 1]⟩
  { a := D₁.a * D₂.a + (D₁.b * D₂.b) * curveXP
    b := D₁.a * D₂.b + D₂.a * D₁.b }

/-! ## Chord-line constructor

Three branches matching `chordCoordRingElt` in
`Divisor/IncrementalConstruction.lean`:

* P = Q with P.2 = 0 (2-torsion): vertical line, `a = X − C P.1`, `b = 0`.
* P = Q with P.2 ≠ 0 (tangent at non-2-torsion): slope from curve.
* P.1 = Q.1 with P.2 ≠ Q.2 (P = −Q): vertical line `X − C P.1`.
* P.1 ≠ Q.1 (distinct chord): standard slope.
-/

/-- Computable analog of `chordCoordRingElt` over `ZMod q`.

    `curveA` is needed for the tangent branch. -/
def chord (curveA : ZMod q) (P Q : ZMod q × ZMod q) : CoordRingEltC q :=
  if P.1 = Q.1 then
    if P.2 = Q.2 then
      if P.2 = 0 then
        -- vertical (2-torsion doubling): a = X - C P.1, b = 0
        { a := CoeffPoly.X - CoeffPoly.C P.1, b := 0 }
      else
        -- tangent at non-2-torsion
        let lam : ZMod q := (3 * P.1 ^ 2 + curveA) * (2 * P.2)⁻¹
        let mu : ZMod q := P.2 - lam * P.1
        { a := -(CoeffPoly.C lam) * CoeffPoly.X - CoeffPoly.C mu
          b := -1 }
    else
      -- same x, different y ⇒ Q = -P: vertical
      { a := CoeffPoly.X - CoeffPoly.C P.1, b := 0 }
  else
    -- distinct chord
    let lam : ZMod q := (Q.2 - P.2) * (Q.1 - P.1)⁻¹
    let mu : ZMod q := P.2 - lam * P.1
    { a := -(CoeffPoly.C lam) * CoeffPoly.X - CoeffPoly.C mu
      b := -1 }

end CoordRingEltC

end Divisor
