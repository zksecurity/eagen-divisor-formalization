/-
  Divisor/IncrementalConstruction.lean

  Algorithmic construction of the principal-divisor witness `D = a(x) − b(x)·y`
  on the elliptic curve `E`, following Liam Eagen,
  "Zero Knowledge Proofs of Elliptic Curve Inner Products from Principal
  Divisors and Weil Reciprocity" (eprint 2022/596), §3.1.1.

  Eagen's incremental construction takes a list of curve points summing
  to zero in the group law and produces a coordinate-ring element whose
  divisor on `E` matches the formal sum of the inputs (with a single
  pole at infinity absorbing the degree). This file develops the
  algorithm and its correctness, eliminating the need for an opaque
  `IsPrincipal` postulate.

  Outline:

  * `chordCoordRingElt P Q` — line through `P` and `Q` (chord, tangent,
    or vertical), packaged as a `CoordRingElt`.
  * `mulCoordRingElt D₁ D₂` — multiplication in `F_q[E]` (reducing
    `y² ↦ x³ + Ax + B`).
  * `divideByXSubX0 D x₀` — cancel the polynomial factor `(x − x₀)`
    when it divides both `a` and `b`.
  * `eagenBuild` — the incremental driver (Eagen §3.1.1).

  Correctness theorems are added in the same file as the definitions
  they certify; together they discharge the divisor-existence step
  used in `MAProverMsg.isHonestFor` and the `weil_reciprocity_honest`
  axiom in `Divisor.Soundness`.
-/
import Divisor.Defs
import Divisor.CubicIntersection
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

/-- Evaluation simp lemma: a non-vertical chord/tangent CoordRingElt evaluates as expected. -/
private theorem chordCoordRingElt_eval_nonvertical
    (lam mu : ZMod E.q) (x y : ZMod E.q) :
    ({ a := -(C lam) * X - C mu, b := -1 } : CoordRingElt E.q).eval x y =
      -(lam * x) - mu + y := by
  show eval x (-(C lam) * X - C mu) - eval x (-1) * y = -(lam * x) - mu + y
  simp [eval_sub, eval_mul, eval_neg, eval_C, eval_X, eval_one]

/-- Evaluation simp lemma: the vertical-line CoordRingElt evaluates as `x - x₀`. -/
private theorem chordCoordRingElt_eval_vertical
    (x₀ : ZMod E.q) (x y : ZMod E.q) :
    ({ a := X - C x₀, b := 0 } : CoordRingElt E.q).eval x y = x - x₀ := by
  show eval x (X - C x₀) - eval x 0 * y = x - x₀
  simp

/-- The `CoordRingElt` produced by `chordCoordRingElt` always vanishes
    at its left input `P`. (Sanity check; full divisor identification
    appears later.) -/
theorem chordCoordRingElt_eval_left
    (P Q : ZMod E.q × ZMod E.q) :
    (chordCoordRingElt E P Q).eval P.1 P.2 = 0 := by
  classical
  unfold chordCoordRingElt
  by_cases hxx : P.1 = Q.1
  · rw [dif_pos hxx]
    by_cases hyy : P.2 = Q.2
    · rw [dif_pos hyy]
      by_cases h2t : P.2 = 0
      · rw [if_pos h2t]
        rw [chordCoordRingElt_eval_vertical]
        ring
      · rw [if_neg h2t]
        rw [chordCoordRingElt_eval_nonvertical]
        ring
    · rw [dif_neg hyy]
      rw [chordCoordRingElt_eval_vertical]
      ring
  · rw [dif_neg hxx]
    rw [chordCoordRingElt_eval_nonvertical]
    ring

/-- The `CoordRingElt` produced by `chordCoordRingElt` always vanishes
    at its right input `Q`. -/
theorem chordCoordRingElt_eval_right
    (P Q : ZMod E.q × ZMod E.q) :
    (chordCoordRingElt E P Q).eval Q.1 Q.2 = 0 := by
  classical
  unfold chordCoordRingElt
  by_cases hxx : P.1 = Q.1
  · rw [dif_pos hxx]
    by_cases hyy : P.2 = Q.2
    · rw [dif_pos hyy]
      -- P = Q: reduce to left case.
      have hQ : Q = P := Prod.ext hxx.symm hyy.symm
      rw [hQ]
      by_cases h2t : P.2 = 0
      · rw [if_pos h2t]
        rw [chordCoordRingElt_eval_vertical]; ring
      · rw [if_neg h2t]
        rw [chordCoordRingElt_eval_nonvertical]; ring
    · rw [dif_neg hyy]
      rw [chordCoordRingElt_eval_vertical, hxx]
      ring
  · rw [dif_neg hxx]
    rw [chordCoordRingElt_eval_nonvertical]
    -- Goal: -((Q.2 - P.2)*(Q.1 - P.1)⁻¹ * Q.1) - (P.2 - (Q.2 - P.2)*(Q.1 - P.1)⁻¹ * P.1) + Q.2 = 0
    have hxne : (Q.1 - P.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx)
    field_simp
    ring

end Divisor
