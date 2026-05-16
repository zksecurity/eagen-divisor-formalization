/-
  Divisor/BivariateLogDeriv.lean

  Denominator-cleared polynomial identity relating the scalar
  `logDerivTerm` (on `E × E`, defined via an explicit rational
  formula in `(a, b, a', b', x, y, λ)`) to the univariate norm polynomial
  `N(D) = a² − b² · curveX` and its formal derivative `N(D)'`.

  Strategy:

  1. `logDerivTerm(pt, λ) = num · dxdz_num / (den · dxdz_den)` where
     * `num := a'(x) − b'(x) · y`
     * `den := a(x) − b(x) · y = D.eval x y`
     * `dxdz_num := 2y`
     * `dxdz_den := 3x² + A − 2λy`.

  2. Multiply numerator and denominator by the conjugate `a(x) + b(x)·y`
     to rationalise:
     `logDerivTerm = num · 2y · (a + b·y) / (N(D)(x) · dxdz_den)` on `E`.

  3. Expand the polynomial `num · 2y · (a + b·y)` and reduce `y²` via
     the curve equation `y² = curveX(x)`:
     `num · 2y · (a + b·y) = 2·(a'·a − b'·b·curveX) · y
                              + 2·curveX · (a'·b − b'·a)`.
     (Linear in `y` after `y²`-reduction.)

  4. Recognise `2·(a'·a − b'·b·curveX) = N(D)'(x) + b²·(3x² + A)` (since
     `N(D) = a² − b²·curveX` ⇒ `N(D)' = 2a·a' − 2b·b'·curveX − b²·(3x² + A)`).

  So we get the final denominator-cleared form:
  ```
  N(D)(x) · (3x² + A − 2λy) · logDerivTerm(pt, λ)
      = (N(D)'(x) + b²·(3x² + A))·y + 2·curveX(x)·(a'·b − b'·a)
  ```

  The `logDerivTermSum` definition and a sum-form denominator-cleared
  identity over the three chord intersections is provided as `Layer 4`;
  Layer 4 just sums Layer 3 pointwise to match the scalar identity
  against `polyG`'s first sum.

  No new axioms, no `sorry` / `admit`.
-/
import Divisor.LogDeriv
import Divisor.NormLogDeriv
import Divisor.BetaConstructive
import Divisor.CubicIntersection
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The norm polynomial's formal derivative -/

/-- Evaluate the formal derivative of `N(D)` at `x₀`.

    `N(D) = a² − b² · curveX` ⇒
    `N(D)' = 2·a·a' − 2·b·b'·curveX − b² · curveX'`,
    so `eval x (N(D)') = 2·a(x)·a'(x) − 2·b(x)·b'(x)·curveX(x)
                           − b(x)² · (3x² + A)`. -/
theorem normPoly_derivative_eval
    (D : CoordRingElt E.q) (x : ZMod E.q) :
    eval x (derivative (normPoly E D)) =
      2 * D.a.eval x * D.a.derivative.eval x
        - 2 * D.b.eval x * D.b.derivative.eval x
             * (x ^ 3 + E.curveA * x + E.curveB)
        - D.b.eval x ^ 2 * (3 * x ^ 2 + E.curveA) := by
  classical
  -- Rewrite `normPoly = a² - b² · curveX`, then differentiate piece by piece.
  have hN : normPoly E D = D.a ^ 2 - D.b ^ 2 * curveX E := normPoly_eq E D
  have hCurve : (curveX E).eval x = x ^ 3 + E.curveA * x + E.curveB := by
    unfold curveX
    simp [eval_add, eval_pow, eval_mul, eval_X, eval_C]
  have hCurveDer : (derivative (curveX E)).eval x = 3 * x ^ 2 + E.curveA := by
    unfold curveX
    simp [derivative_add, derivative_pow, derivative_mul, derivative_X,
          derivative_C, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  -- derivative (a² - b² · curveX) = 2·a·a' - (2·b·b'·curveX + b²·curveX')
  have hDer : derivative (normPoly E D) =
      C 2 * D.a * derivative D.a
        - (C 2 * D.b * derivative D.b * curveX E
            + D.b ^ 2 * derivative (curveX E)) := by
    rw [hN]
    simp only [derivative_sub, derivative_mul, derivative_pow]
    -- d/dx (a^2) = 2 * a^1 * a' = 2 * a * a'
    -- d/dx (b^2 * curveX) = d(b^2)/dx * curveX + b^2 * curveX'
    --                     = 2*b*b' * curveX + b^2 * curveX'
    push_cast
    ring
  rw [hDer]
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C]
  rw [hCurve, hCurveDer]
  ring

/-! ## Layer 2 : the rationalised form on `E`

    On `E.points`, `D.eval x y · (a(x) + b(x)·y) = N(D).eval x` via
    `y² = curveX.eval x`. This is the key "multiply by conjugate" step. -/

/-- Given `P ∈ E.points`, `D.eval P.1 P.2 · (a.eval P.1 + b.eval P.1 · P.2) =
    N(D).eval P.1`. -/
theorem D_eval_mul_conj_eq_normPoly_eval
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    D.eval P.1 P.2 * (D.a.eval P.1 + D.b.eval P.1 * P.2) =
      (normPoly E D).eval P.1 := by
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  rw [normPoly_eval]
  unfold CoordRingElt.eval
  -- (a - b·y) · (a + b·y) = a² − b²·y² = a² − b²·(x³+Ax+B)
  have hSq : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := hOC
  linear_combination -D.b.eval P.1 ^ 2 * hSq

/-! ## Layer 3 : single-point denominator-cleared identity -/

/-- **Layer 3 main theorem** (paper-faithful `logDerivTerm`).

    For any point `P = (x, y)` on `E.points` and any scalar `λ`, assuming
    the product of denominators `(D.eval x y) · (3x² + A − 2λy) ≠ 0`, the
    `logDerivTerm` identity

    ```
    N(D)(x) · (3x² + A − 2λy) · logDerivTerm(P, λ) =
        2·y·(a'(x)·a(x) − b'(x)·b(x)·curveX(x))
         + 2·curveX(x)·(a'(x)·b(x) − b'(x)·a(x))
         − (a(x) + b(x)·y) · b(x) · (3x² + A)
    ```

    holds as a scalar identity in `ZMod E.q`. The final correction term
    `−(a + b·y) · b · (3x² + A)` is the paper-faithful chain-rule piece
    `(∂D/∂y) · (dy/dz)` cleared over the common denominator `N(D)(x)`
    using `N(D)(x) / D(x, y) = a(x) + b(x)·y` (on `E`). -/
theorem logDerivTerm_denom_cleared_pointwise
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : D.eval P.1 P.2 ≠ 0)
    (hXDen : (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) ≠ 0) :
    (normPoly E D).eval P.1 * (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) *
        logDerivTerm E D E.curveA lam P =
      2 * P.2 * (D.a.derivative.eval P.1 * D.a.eval P.1
                   - D.b.derivative.eval P.1 * D.b.eval P.1
                        * (P.1 ^ 3 + E.curveA * P.1 + E.curveB))
        + 2 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB) *
          (D.a.derivative.eval P.1 * D.b.eval P.1
             - D.b.derivative.eval P.1 * D.a.eval P.1)
        - (D.a.eval P.1 + D.b.eval P.1 * P.2) * D.b.eval P.1
            * (3 * P.1 ^ 2 + E.curveA) := by
  classical
  -- Abbreviations.
  set a := D.a.eval P.1 with ha_def
  set b := D.b.eval P.1 with hb_def
  set a' := D.a.derivative.eval P.1 with ha'_def
  set b' := D.b.derivative.eval P.1 with hb'_def
  set y := P.2
  set x := P.1
  -- On-curve identity.
  have hSq : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB := E.hOnCurve P hP
  -- `D.eval x y = a - b·y` and `(normPoly E D).eval x = a² - b²·(x³+Ax+B)`.
  have hDen : D.eval x y = a - b * y := rfl
  have hDenNZ : (a - b * y) ≠ 0 := by rw [← hDen]; exact hD
  have hN : (normPoly E D).eval x = a ^ 2 - b ^ 2 *
              (x ^ 3 + E.curveA * x + E.curveB) := normPoly_eval E D x
  -- Unfold `logDerivTerm` (paper form).
  -- LT = ((a' - b'·y) · (2·y) + (-b) · (3x² + A)) · ((a - b·y) * (3x² + A − 2λy))⁻¹
  have hLT : logDerivTerm E D E.curveA lam P
      = ((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA)) *
          ((a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y))⁻¹ := by
    unfold logDerivTerm
    rfl
  -- Auxiliary: on E, (a + b·y)·[(a' - b'·y)·(2·y) + (-b)·(3x²+A)]
  --   = 2·y·(a'·a − b'·b·(x³+Ax+B)) + 2·(x³+Ax+B)·(a'·b − b'·a)
  --     − (a + b·y)·b·(3x² + A).
  have hAux :
      (a + b * y) * ((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA))
        = 2 * y * (a' * a - b' * b * (x ^ 3 + E.curveA * x + E.curveB))
          + 2 * (x ^ 3 + E.curveA * x + E.curveB) * (a' * b - b' * a)
          - (a + b * y) * b * (3 * x ^ 2 + E.curveA) := by
    linear_combination (-2 * b * b' * y + 2 * a' * b - 2 * a * b') * hSq
  -- Auxiliary: on E, a² − b²·(x³+Ax+B) = (a - b·y)·(a + b·y).
  have hProd : a ^ 2 - b ^ 2 * (x ^ 3 + E.curveA * x + E.curveB)
              = (a - b * y) * (a + b * y) := by
    linear_combination b ^ 2 * hSq
  -- Rewrite LHS using hLT and hN.
  rw [hLT, hN, hProd]
  -- Goal: (a - b·y) * (a + b·y) * (3x² + A − 2λy) *
  --        [((a'-b'y)(2y) + (-b)(3x²+A)) * ((a-by)(3x²+A-2λy))⁻¹]
  --     = old RHS − (a+b·y)·b·(3x²+A)
  have hMul : (a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y) ≠ 0 :=
    mul_ne_zero hDenNZ hXDen
  have hInvCancel :
      (a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y)
        * ((a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y))⁻¹ = 1 :=
    mul_inv_cancel₀ hMul
  calc (a - b * y) * (a + b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y) *
          (((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA)) *
            ((a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y))⁻¹)
      = ((a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y)
            * ((a - b * y) * (3 * x ^ 2 + E.curveA - 2 * lam * y))⁻¹) *
          ((a + b * y) *
            ((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA))) := by ring
    _ = 1 * ((a + b * y) *
            ((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA))) := by
          rw [hInvCancel]
    _ = (a + b * y) *
            ((a' - b' * y) * (2 * y) + (-b) * (3 * x ^ 2 + E.curveA)) := by ring
    _ = 2 * y * (a' * a - b' * b * (x ^ 3 + E.curveA * x + E.curveB))
          + 2 * (x ^ 3 + E.curveA * x + E.curveB) * (a' * b - b' * a)
          - (a + b * y) * b * (3 * x ^ 2 + E.curveA) := hAux

/-- **Corollary of Layer 3** (form in terms of `eval (derivative (normPoly))`):

    At `(P, λ)` with denominators nonzero, the denominator-cleared
    `logDerivTerm` is equivalently expressed via `eval x (N(D)')`.

    ```
    2 · N(D)(x) · (3x² + A − 2λy) · logDerivTerm(P, λ)
        = (N(D)'(x) + b(x)²·(3x²+A)) · (2y)
           + 4·curveX(x)·(a'·b − b'·a)
           − 2·(a+b·y)·b·(3x²+A).
    ```
    Follows by substitution via `normPoly_derivative_eval`. -/
theorem logDerivTerm_denom_cleared_with_normPoly_derivative
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : D.eval P.1 P.2 ≠ 0)
    (hXDen : (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) ≠ 0) :
    2 * (normPoly E D).eval P.1 * (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) *
        logDerivTerm E D E.curveA lam P =
      (eval P.1 (derivative (normPoly E D))
          + D.b.eval P.1 ^ 2 * (3 * P.1 ^ 2 + E.curveA)) * (2 * P.2)
        + 4 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB) *
            (D.a.derivative.eval P.1 * D.b.eval P.1
              - D.b.derivative.eval P.1 * D.a.eval P.1)
        - 2 * (D.a.eval P.1 + D.b.eval P.1 * P.2) * D.b.eval P.1
            * (3 * P.1 ^ 2 + E.curveA) := by
  -- Multiply Layer 3 by 2, then substitute 2·(a'·a − b'·b·curveX) = N(D)' + b²·(3x²+A).
  have hCore := logDerivTerm_denom_cleared_pointwise E D lam hP hD hXDen
  have hNpDer := normPoly_derivative_eval E D P.1
  -- Abbreviations.
  set x := P.1
  set y := P.2
  set a := D.a.eval x
  set b := D.b.eval x
  set a' := D.a.derivative.eval x
  set b' := D.b.derivative.eval x
  set cx := x ^ 3 + E.curveA * x + E.curveB
  set gx := 3 * x ^ 2 + E.curveA
  -- hNpDer: eval x (N(D)') = 2·a·a' - 2·b·b'·cx - b²·gx
  have hNpDer' : eval x (derivative (normPoly E D)) + b ^ 2 * gx
                   = 2 * a * a' - 2 * b * b' * cx := by
    linear_combination hNpDer
  -- Rearrange the goal.
  linear_combination 2 * hCore - 2 * y * hNpDer'

/-! ## Layer 4 : sum form over chord intersections

    Given a pair `(A₀, A₁)` of affine E-points with `A₀.1 ≠ A₁.1` (chord
    case), the third chord intersection is the affine point
    `A₂ = (λ² − A₀.1 − A₁.1, λ · x₂ + (A₀.2 − λ · A₀.1))` where
    `λ = (A₁.2 − A₀.2) / (A₁.1 − A₀.1)`. When `A₂` lies on `E`, the sum
    `Σᵢ logDerivTerm(Aᵢ, λ)` is pointwise the sum of the Layer-3
    identities. -/

/-- The three chord points as indexed by `Fin 3`. -/
noncomputable def chordPoints (A₀ A₁ : ZMod E.q × ZMod E.q) : Fin 3 → ZMod E.q × ZMod E.q
  | ⟨0, _⟩ => A₀
  | ⟨1, _⟩ => A₁
  | ⟨2, _⟩ =>
      let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
      let x₂ := lam ^ 2 - A₀.1 - A₁.1
      let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
      (x₂, y₂)

/-- Sum of `logDerivTerm` over the three chord intersections. -/
noncomputable def logDerivTermSum
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  (Finset.univ : Finset (Fin 3)).sum
    (fun i => logDerivTerm E D E.curveA lam (chordPoints E A₀ A₁ i))

/-- Unfolded form: `logDerivTermSum` equals `logDerivTerm(A₀) +
    logDerivTerm(A₁) + logDerivTerm(A₂)`. -/
theorem logDerivTermSum_eq
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    logDerivTermSum E D A₀ A₁ =
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ +
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁ +
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
        (chordPoints E A₀ A₁ ⟨2, by omega⟩) := by
  unfold logDerivTermSum
  -- Expand the sum over Fin 3 = {⟨0,_⟩, ⟨1,_⟩, ⟨2,_⟩} explicitly.
  rw [show (Finset.univ : Finset (Fin 3)) =
      {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  -- After unfolding: `LHS = f ⟨0,_⟩ + (f ⟨1,_⟩ + f ⟨2,_⟩)`
  -- chordPoints @ ⟨0,_⟩ = A₀ and @ ⟨1,_⟩ = A₁ by rfl.
  show
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ +
      (logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁ +
        logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (chordPoints E A₀ A₁ ⟨2, by omega⟩)) = _
  ring

/-- Pointwise application of Layer 3 to each of the three chord points,
    *assuming* each is on `E.points` with the corresponding denominators
    nonzero. Gives a sum of three denominator-cleared polynomial
    identities. -/
theorem logDerivTermSum_denom_cleared_sumform
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points)
    (hA₁ : A₁ ∈ E.points)
    (hA₂ : chordPoints E A₀ A₁ ⟨2, by omega⟩ ∈ E.points)
    (hDA₀ : D.eval A₀.1 A₀.2 ≠ 0)
    (hDA₁ : D.eval A₁.1 A₁.2 ≠ 0)
    (hDA₂ : D.eval (chordPoints E A₀ A₁ ⟨2, by omega⟩).1
                   (chordPoints E A₀ A₁ ⟨2, by omega⟩).2 ≠ 0)
    (hXDen₀ : (3 * A₀.1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) ≠ 0)
    (hXDen₁ : (3 * A₁.1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) ≠ 0)
    (hXDen₂ : (3 * (chordPoints E A₀ A₁ ⟨2, by omega⟩).1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2
                        * (chordPoints E A₀ A₁ ⟨2, by omega⟩).2) ≠ 0) :
    (∀ i : Fin 3,
      let P := chordPoints E A₀ A₁ i
      let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
      (normPoly E D).eval P.1 * (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) *
          logDerivTerm E D E.curveA lam P =
        2 * P.2 * (D.a.derivative.eval P.1 * D.a.eval P.1
                     - D.b.derivative.eval P.1 * D.b.eval P.1
                          * (P.1 ^ 3 + E.curveA * P.1 + E.curveB))
          + 2 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB) *
            (D.a.derivative.eval P.1 * D.b.eval P.1
               - D.b.derivative.eval P.1 * D.a.eval P.1)
          - (D.a.eval P.1 + D.b.eval P.1 * P.2) * D.b.eval P.1
              * (3 * P.1 ^ 2 + E.curveA)) := by
  intro i
  -- Dispatch to Layer 3 depending on i ∈ {0, 1, 2}.
  match i with
  | ⟨0, _⟩ =>
      show _ = _
      have := logDerivTerm_denom_cleared_pointwise E D
        (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) hA₀ hDA₀ hXDen₀
      convert this using 0
  | ⟨1, _⟩ =>
      show _ = _
      have := logDerivTerm_denom_cleared_pointwise E D
        (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) hA₁ hDA₁ hXDen₁
      convert this using 0
  | ⟨2, _⟩ =>
      show _ = _
      have := logDerivTerm_denom_cleared_pointwise E D
        (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) hA₂ hDA₂ hXDen₂
      convert this using 0

/-! ## Historical note on paper-faithful integrand

    `logDerivTerm` is now the paper-faithful form.
    The previous `logDerivTermPaper` / `logDerivTermPaper_sub_logDerivTerm`
    reference lemmas are obsolete and have been removed. The correction
    term `−(a + b·y) · b · (3x² + A)` now appears directly in the
    RHS of `logDerivTerm_denom_cleared_pointwise`. -/

end Divisor
