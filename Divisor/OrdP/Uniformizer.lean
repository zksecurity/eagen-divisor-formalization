/-
  Divisor/OrdP/Uniformizer.lean

  Order of vanishing at affine F_q-rational points of `E`, computed
  by Taylor expansion in a local uniformizer.

  Background (Silverman AEC, II §1): for a smooth affine point `P` on
  `E : y² = x³ + Ax + B` (char ≠ 2), uniformizer choice depends on
  whether `P.2 = 0`:

  * Non-2-torsion (`P.2 ≠ 0`): `x − P.1` is a uniformizer.
  * 2-torsion (`P.2 = 0`): `y` is a uniformizer; `x − P.1` has order 2.

  We define `ordAt E D P : ℕ` as the order of vanishing of `D = a − b·y`
  at `P`, computed by iterated Taylor coefficient extraction in the
  uniformizer.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Non-2-torsion uniformizer order

    For `P = (x₀, y₀)` with `y₀ ≠ 0`, `x − x₀` is a uniformizer.
    The Taylor expansion of `D = a − b·y` along `x` uses
    `y(x) = y₀ + λ_y · (x − x₀) + …` with
    `λ_y = (3x₀² + A) / (2 y₀)`.

    The order of vanishing is the smallest `n` such that the
    `(x − x₀)^n`-coefficient of `D` is nonzero.  We encode this via
    iterated derivatives:

      `ord_P(D) = inf { n : (d/dx)^n D evaluated at P ≠ 0 }`.

    The (d/dx) operation on `CoordRingElt` is

      `(d/dx)(a − b·y) = (a' − b·λ_y) − (b' − 0)·y`           (when y₀ ≠ 0)

    where the curve's `dy/dx = λ_y` is treated as a *constant* at `P`
    (since we're expanding in `x − P.1`, evaluating at `P` after each
    derivative step).  More precisely the formal recipe is:

      D₀ := D
      D_{n+1} := derivCRE_x D_n     -- (d/dx) at P, threading curve eq

    with `D_n.eval P.1 P.2 = (n!)⁻¹ · ∂ⁿ D` evaluated at P. -/

/-- One step of formal x-derivative on a `CoordRingElt`, evaluated
    along the curve at a non-2-torsion point.

    Concretely: `(d/dx)(a − b·y) = (a' − b · (3x² + A)/(2y)) − b' · y`,
    *as a formal CoordRingElt*. Encoded by clearing the `1/(2y)`
    factor — we keep the leading-x form intact for non-evaluative
    use, and evaluate at `P` only when needed. -/
noncomputable def stepX (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) : CoordRingElt E.q :=
  { a := D.a.derivative -
         D.b * Polynomial.C ((3 * P.1 ^ 2 + E.curveA) / (2 * P.2))
    b := D.b.derivative }

/-- Order of vanishing of `D` at a non-2-torsion `P`.  Returns the
    smallest `n` such that `(stepX^n D).eval P.1 P.2 ≠ 0`, bounded
    by `D.degE + 1`. Returns 0 if D is identically zero or P is off-curve. -/
noncomputable def ordAt_nonTwoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if hP : P ∈ E.points ∧ P.2 ≠ 0 ∧ ¬ (D.a = 0 ∧ D.b = 0) then
      Nat.find (p := fun n =>
        ((Nat.iterate (stepX E · P) n D).eval P.1 P.2 ≠ 0
        ∨ n ≥ D.degE + 1))
        ⟨D.degE + 1, Or.inr (by omega)⟩
    else 0

/-! ## 2-torsion uniformizer order

    For `P = (x₀, 0)`, `y` is a uniformizer; `x − x₀` has order 2.
    Order of `D = a − b·y` at `P`:
    * Constant: `a(x₀)`. If nonzero, ord = 0.
    * `y` term: `−b(x₀)`. If nonzero, ord = 1.
    * Higher: `a` contributes only even powers (via `x − x₀ = y² · q⁻¹`),
      `b · y` contributes only odd powers. So:
      - `y²` coeff comes from `a'(x₀) · q(x₀)⁻¹` where `q(x) = x² + x·x₀ + x₀² + A`.
      - `y³` coeff from `−b'(x₀) · q(x₀)⁻¹`.
      - And so on, with derivatives of `a, b` and powers of `q⁻¹`.
-/

/-- Compactified value `q(P) = 3 x₀² + A = curve's tangent denominator at P`.
    For 2-torsion P, `q(P)` is nonzero (by smoothness of E). -/
noncomputable def qAtTwoTorsion (P : ZMod E.q × ZMod E.q) : ZMod E.q :=
  3 * P.1 ^ 2 + E.curveA

/-- Order of vanishing of `D` at a 2-torsion `P`. Computes the order
    by alternating derivatives of `a, b` weighted by `q(P)⁻¹` powers.
    The y-term contributes odd orders; the a-term contributes even
    orders. -/
noncomputable def ordAt_twoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  -- Skeleton: real recursion in LocalRing.lean.
  exact 0

/-! ## Combined `ordAt` -/

/-- Order of vanishing of `D` at the affine F_q-rational point `P`.

    Currently defined as a *minimal* placeholder that satisfies the
    support / coverage / total-degree-bound shape but NOT the
    accounting or group-sum identities (those require the full
    Taylor expansion in the uniformizer, deferred to a future
    iteration).

    Phase-1 status: the placeholder gives `ordAt = 1` at every
    F_q-rational affine zero of `D` (when `D` is nonzero) and `0`
    elsewhere. Lemmas `ordAt_pos_iff_zero`, `ordAt_eq_zero_offE`,
    and `sum_ordAt_le_degE` are dischargeable from this placeholder;
    `sum_ordAt_eq_natDegree_under_split` and
    `ordAt_group_sum_zero_under_split` require the real
    Taylor-expansion definition (sorry'd in `LocalRing.lean`). -/
noncomputable def ordAt (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if P ∈ E.points ∧ D.eval P.1 P.2 = 0 ∧ ¬ (D.a = 0 ∧ D.b = 0) then
      1
    else
      0

end Divisor
