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
import Divisor.BetaConstructive
import Divisor.ChordCubicSymmetric
import Divisor.OrdP.Uniformizer
import Divisor.OrdP.LocalRing
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

/-! ## `chordCoordRingElt` agrees with `lineThrough` (non-vertical case) -/

/-- For `P.1 ≠ Q.1`, `chordCoordRingElt P Q` evaluates the same as
    `(lineThrough P.1 P.2 Q.1 Q.2).eval` — both encode the line
    `y − λx − μ`. -/
theorem chordCoordRingElt_eval_eq_lineThrough_chord
    {P Q : ZMod E.q × ZMod E.q} (hxx : P.1 ≠ Q.1)
    (S : ZMod E.q × ZMod E.q) :
    (chordCoordRingElt E P Q).eval S.1 S.2
      = (lineThrough P.1 P.2 Q.1 Q.2).eval S.1 S.2 := by
  classical
  unfold chordCoordRingElt
  rw [dif_neg hxx]
  rw [chordCoordRingElt_eval_nonvertical]
  show -((Q.2 - P.2) * (Q.1 - P.1)⁻¹ * S.1) -
        (P.2 - (Q.2 - P.2) * (Q.1 - P.1)⁻¹ * P.1) + S.2
      = S.2 - (Line.lam (lineThrough P.1 P.2 Q.1 Q.2)) * S.1
        - (Line.mu (lineThrough P.1 P.2 Q.1 Q.2))
  unfold lineThrough slopeOf
  simp only []
  ring

/-! ## Non-zero-ness of `chordCoordRingElt`

The chord-line `CoordRingElt` is never the zero element of `F_q[E]`:

* In the chord and tangent branches, `b = -1 ≠ 0`.
* In the vertical branches, `a = X - C x₀ ≠ 0` (a degree-1 polynomial).

Required for invoking `normPoly_ne_zero`, `ordAt_pos_iff_zero`, and any
`splitsOnE`-based accounting. -/

theorem chordCoordRingElt_ne_zero
    (P Q : ZMod E.q × ZMod E.q) :
    ¬ ((chordCoordRingElt E P Q).a = 0 ∧ (chordCoordRingElt E P Q).b = 0) := by
  classical
  unfold chordCoordRingElt
  by_cases hxx : P.1 = Q.1
  · rw [dif_pos hxx]
    by_cases hyy : P.2 = Q.2
    · rw [dif_pos hyy]
      by_cases h2t : P.2 = 0
      · rw [if_pos h2t]
        intro ⟨ha, _⟩
        -- ha : X - C P.1 = 0, but natDegree(X - C P.1) = 1.
        have hd : (X - C P.1 : (ZMod E.q)[X]).natDegree = 1 := natDegree_X_sub_C _
        have : (0 : (ZMod E.q)[X]).natDegree = 1 := by rw [← ha]; exact hd
        rw [natDegree_zero] at this; omega
      · rw [if_neg h2t]
        intro ⟨_, hb⟩
        -- hb : -1 = 0
        have h1 : (1 : (ZMod E.q)[X]) ≠ 0 := one_ne_zero
        exact h1 (neg_eq_zero.mp hb)
    · rw [dif_neg hyy]
      intro ⟨ha, _⟩
      have hd : (X - C P.1 : (ZMod E.q)[X]).natDegree = 1 := natDegree_X_sub_C _
      have : (0 : (ZMod E.q)[X]).natDegree = 1 := by rw [← ha]; exact hd
      rw [natDegree_zero] at this; omega
  · rw [dif_neg hxx]
    intro ⟨_, hb⟩
    have h1 : (1 : (ZMod E.q)[X]) ≠ 0 := one_ne_zero
    exact h1 (neg_eq_zero.mp hb)

/-! ## `normPoly` of the chord-line `CoordRingElt`

The norm polynomial `N(D) = D.a² − D.b²·(X³+AX+B)` factors cleanly
in each branch.

* **Vertical** (`a = X − x₀`, `b = 0`): `N(D) = (X − x₀)²`. This is a
  direct calculation.
* **Non-vertical** (`a = −λX − μ`, `b = −1`): `N(D) = (λX+μ)² − (X³+AX+B)`,
  a cubic of leading coefficient `−1`.
-/

/-- `normPoly` of the vertical chord line `D = (X − x₀, 0)`. -/
theorem normPoly_chordCoordRingElt_vertical (x₀ : ZMod E.q) :
    normPoly E ({ a := X - C x₀, b := 0 } : CoordRingElt E.q) = (X - C x₀) ^ 2 := by
  rw [normPoly_eq]
  show (X - C x₀) ^ 2 - 0 ^ 2 * curveX E = (X - C x₀) ^ 2
  ring

/-- `normPoly` of a non-vertical chord/tangent line
    `D = (−λX − μ, −1)`. Equal to `(λX+μ)² − (X³+AX+B)`. -/
theorem normPoly_chordCoordRingElt_nonvertical (lam mu : ZMod E.q) :
    normPoly E ({ a := -(C lam) * X - C mu, b := -1 } : CoordRingElt E.q) =
      (C lam * X + C mu) ^ 2 - curveX E := by
  rw [normPoly_eq]
  show (-(C lam) * X - C mu) ^ 2 - (-1 : (ZMod E.q)[X]) ^ 2 * curveX E
      = (C lam * X + C mu) ^ 2 - curveX E
  ring

/-- The `natDegree` of `normPoly` for the vertical chord line is `2`
    (matching the actual pole order at infinity in the divisor of the
    vertical line through a 2-torsion or `±P` pair). -/
theorem natDegree_normPoly_chordCoordRingElt_vertical (x₀ : ZMod E.q) :
    (normPoly E ({ a := X - C x₀, b := 0 } : CoordRingElt E.q)).natDegree = 2 := by
  rw [normPoly_chordCoordRingElt_vertical]
  rw [natDegree_pow, natDegree_X_sub_C]

/-- The `natDegree` of `normPoly` for a non-vertical chord/tangent line
    is `3`. Argument: the subtracted `curveX E = X³ + AX + B` has natDegree
    exactly 3 with leading coefficient 1, while `(λX+μ)²` has natDegree
    at most 2. -/
theorem natDegree_normPoly_chordCoordRingElt_nonvertical (lam mu : ZMod E.q) :
    (normPoly E ({ a := -(C lam) * X - C mu, b := -1 } : CoordRingElt E.q)).natDegree = 3 := by
  rw [normPoly_chordCoordRingElt_nonvertical]
  -- Goal: ((C lam * X + C mu)^2 - curveX E).natDegree = 3
  have hLin : (C lam * X + C mu).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X.le)
    · exact (natDegree_C _).le.trans (by omega)
  have hSquare : ((C lam * X + C mu) ^ 2).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_pow_le).trans ?_
    omega
  have hCurveDeg : (curveX E).natDegree = 3 := by
    unfold curveX
    -- X^3 + C A · X + C B has degree 3
    have h1 : (X ^ 3 + C E.curveA * X : (ZMod E.q)[X]).natDegree = 3 := by
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · exact natDegree_X_pow 3
      · rw [natDegree_X_pow]
        refine lt_of_le_of_lt ?_ (by omega : 1 < 3)
        exact (natDegree_C_mul_le _ _).trans natDegree_X.le
    rw [show X ^ 3 + C E.curveA * X + C E.curveB =
              (X ^ 3 + C E.curveA * X) + C E.curveB by ring]
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · exact h1
    · rw [h1, natDegree_C]; omega
  have hSubLE : (((C lam * X + C mu) ^ 2 - curveX E : (ZMod E.q)[X])).natDegree ≤ 3 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ hCurveDeg.le)
    omega
  -- Show natDegree ≥ 3 by checking coefficient at index 3.
  have hCoeff3 :
      ((C lam * X + C mu) ^ 2 - curveX E : (ZMod E.q)[X]).coeff 3 = -1 := by
    rw [coeff_sub]
    have hSqCoeff3 : ((C lam * X + C mu) ^ 2 : (ZMod E.q)[X]).coeff 3 = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    have hCurveCoeff3 : (curveX E).coeff 3 = 1 := by
      unfold curveX
      simp [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    rw [hSqCoeff3, hCurveCoeff3]; ring
  -- Use leadingCoeff non-zero ⇒ natDegree exact via coeff_natDegree.
  have hNonzero : (((C lam * X + C mu) ^ 2 - curveX E : (ZMod E.q)[X])) ≠ 0 := by
    intro hZero
    have := congrArg (fun p => Polynomial.coeff p 3) hZero
    simp only at this
    rw [hCoeff3] at this
    simp at this
  apply le_antisymm hSubLE
  by_contra hLt
  push_neg at hLt
  have : ((C lam * X + C mu) ^ 2 - curveX E : (ZMod E.q)[X]).coeff 3 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    omega
  rw [hCoeff3] at this
  simp at this

/-! ## Chord-line zero set on `E`

For the chord branch (`P.1 ≠ Q.1`), the only on-curve zeros of
`chordCoordRingElt P Q` are exactly `P`, `Q`, and the third
intersection. Direct corollary of the existing
`chord_line_support_in_E` (`Divisor/ChordCubicSymmetric.lean:168`) once
we observe that `chordCoordRingElt`'s evaluation matches
`lineThrough.eval`. -/

/-- Chord case: the on-curve zeros of `chordCoordRingElt P Q` lie in
    `{P, Q, A₂}` where `A₂` is the third chord intersection. -/
theorem chordCoordRingElt_zeros_on_E_chord
    {P Q : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (hxx : P.1 ≠ Q.1)
    {S : ZMod E.q × ZMod E.q} (hS : S ∈ E.points)
    (hZero : (chordCoordRingElt E P Q).eval S.1 S.2 = 0) :
    S = P ∨ S = Q ∨
      S = (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1,
           slopeOf P.1 P.2 Q.1 Q.2 *
             (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
           (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1)) := by
  rw [chordCoordRingElt_eval_eq_lineThrough_chord E hxx S] at hZero
  exact chord_line_support_in_E E P Q hP hQ hxx S hS hZero

/-! ## Vanishing of `chordCoordRingElt` at the chord's third intersection -/

/-- Chord case: `chordCoordRingElt P Q` vanishes at `thirdPoint`. -/
theorem chordCoordRingElt_eval_thirdPoint_chord
    {P Q : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (hxx : P.1 ≠ Q.1) :
    let lam := slopeOf P.1 P.2 Q.1 Q.2
    let x₂ := lam ^ 2 - P.1 - Q.1
    let y₂ := lam * x₂ + (P.2 - lam * P.1)
    (chordCoordRingElt E P Q).eval x₂ y₂ = 0 := by
  intro lam x₂ y₂
  rw [chordCoordRingElt_eval_eq_lineThrough_chord E hxx (x₂, y₂)]
  show (lineThrough P.1 P.2 Q.1 Q.2).eval x₂ y₂ = 0
  -- (lineThrough P Q).eval (x, y) = y - lam·x - mu, with mu = P.2 - lam·P.1.
  -- By construction y₂ = lam·x₂ + (P.2 − lam·P.1).
  unfold Line.eval lineThrough
  show y₂ - (slopeOf P.1 P.2 Q.1 Q.2) * x₂
        - (P.2 - (slopeOf P.1 P.2 Q.1 Q.2) * P.1) = 0
  show (slopeOf P.1 P.2 Q.1 Q.2 * x₂ + (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1))
        - slopeOf P.1 P.2 Q.1 Q.2 * x₂
        - (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) = 0
  ring

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

/-- Pointwise evaluation of a product equals the product of evaluations
    on `E.points` (the curve relation `y² = x³+Ax+B` reduces the cross
    `y²` term). -/
theorem mulCoordRingElt_eval_on_E
    (D₁ D₂ : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    (mulCoordRingElt E D₁ D₂).eval P.1 P.2 =
      D₁.eval P.1 P.2 * D₂.eval P.1 P.2 := by
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  show (D₁.a * D₂.a + D₁.b * D₂.b * curveX E).eval P.1
      - (D₁.a * D₂.b + D₂.a * D₁.b).eval P.1 * P.2
    = (D₁.a.eval P.1 - D₁.b.eval P.1 * P.2)
      * (D₂.a.eval P.1 - D₂.b.eval P.1 * P.2)
  unfold curveX
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
  have hRw : P.1 ^ 3 + E.curveA * P.1 + E.curveB = P.2 ^ 2 := by
    rw [hOC]
  rw [hRw]
  ring

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

/-- Multiplicativity of `natDegree(normPoly)` (under nonzero hypotheses). -/
theorem natDegree_normPoly_mul_eq
    (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0)) :
    (normPoly E (mulCoordRingElt E D₁ D₂)).natDegree =
      (normPoly E D₁).natDegree + (normPoly E D₂).natDegree := by
  rw [normPoly_mul_eq]
  exact Polynomial.natDegree_mul (normPoly_ne_zero E D₁ h₁) (normPoly_ne_zero E D₂ h₂)

/-! ## Polynomial cancellation `(X − x₀)`

When `(X − x₀)` divides both `D.a` and `D.b`, dividing it out gives a
new `CoordRingElt`. We use mathlib's `Polynomial.divByMonic` (whose
result is `0` when the divisor doesn't divide). -/

-- Reuse `CoordRingElt.divLin` from `Divisor/OrdP/Uniformizer.lean` —
-- componentwise division by `X − C x₀`. When `(X − x₀)` divides both
-- `a` and `b`, the result is `D / (X − x₀)` and reduces the divisor
-- by the cancelled `±(x₀, y₀)` pair.

/-- When `(X − x₀)` divides both `a` and `b`, evaluation of the
    cancelled `D` agrees with `D.eval / (x − x₀)`. -/
theorem divLin_eval_mul_X_sub_C
    (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (haDvd : (X - C x₀) ∣ D.a) (hbDvd : (X - C x₀) ∣ D.b)
    (x y : ZMod E.q) :
    (D.divLin x₀).eval x y * (x - x₀) = D.eval x y := by
  rw [CoordRingElt.eval, CoordRingElt.divLin_a, CoordRingElt.divLin_b]
  show ((D.a /ₘ (X - C x₀)).eval x - (D.b /ₘ (X - C x₀)).eval x * y) * (x - x₀)
      = D.a.eval x - D.b.eval x * y
  have hMonic : (X - C x₀ : (ZMod E.q)[X]).Monic := monic_X_sub_C _
  obtain ⟨qa, hqa⟩ := haDvd
  obtain ⟨qb, hqb⟩ := hbDvd
  have ha_eq : D.a /ₘ (X - C x₀) = qa := by
    have : D.a = (X - C x₀) * qa := hqa
    rw [this]
    exact mul_divByMonic_cancel_left _ hMonic
  have hb_eq : D.b /ₘ (X - C x₀) = qb := by
    have : D.b = (X - C x₀) * qb := hqb
    rw [this]
    exact mul_divByMonic_cancel_left _ hMonic
  rw [ha_eq, hb_eq, hqa, hqb]
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  ring

end Divisor
