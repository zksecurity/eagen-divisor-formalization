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

/-! ## `splitsOnE` for the vertical chord-line case

For `D = (X − C x₀, 0)` with `x₀` the x-coordinate of some F_q-point
on `E`, the norm polynomial `(X − x₀)²` splits over `F_q` (the only
root is `x₀`, with multiplicity 2) and the root lifts. -/

theorem splitsOnE_chordCoordRingElt_vertical
    (P Q : ZMod E.q × ZMod E.q) (hP : P ∈ E.points)
    (hxx : P.1 = Q.1)
    (hCase : P.2 ≠ Q.2 ∨ (P.2 = Q.2 ∧ P.2 = 0)) :
    splitsOnE E (chordCoordRingElt E P Q) := by
  classical
  -- D = (X - C P.1, 0) in both vertical sub-branches.
  have hD : chordCoordRingElt E P Q
      = ({ a := X - C P.1, b := 0 } : CoordRingElt E.q) := by
    unfold chordCoordRingElt
    rw [dif_pos hxx]
    rcases hCase with hyy | ⟨hyy, h2t⟩
    · rw [dif_neg hyy]
    · rw [dif_pos hyy, if_pos h2t]
  rw [hD]
  refine ⟨?_, ?_⟩
  · -- normPoly_splits_over_Fq: card roots = natDegree
    show Multiset.card (normPoly E _).roots = (normPoly E _).natDegree
    rw [normPoly_chordCoordRingElt_vertical, natDegree_pow, natDegree_X_sub_C]
    rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]
    simp
  · -- Every root of normPoly is the x-coord of an F_q-point
    intro α hα
    rw [normPoly_chordCoordRingElt_vertical] at hα
    rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C] at hα
    -- hα : α ∈ 2 • ({P.1} : Multiset _)
    have : α = P.1 := by
      have h_eq : (2 • ({P.1} : Multiset (ZMod E.q))) = {P.1, P.1} := by
        rfl
      rw [h_eq] at hα
      rcases Multiset.mem_cons.mp hα with h | h
      · exact h
      · simpa using h
    rw [this]
    exact ⟨P.2, hP⟩

/-! ## `splitsOnE` for the chord case

Vieta's formulas on the chord-line cubic `(λX+μ)² − (X³+AX+B)` give

  `(λX+μ)² − (X³+AX+B) = −(X − P.1)(X − Q.1)(X − x₂)`

where `x₂ = λ² − P.1 − Q.1`. Hence the roots multiset is
`{P.1, Q.1, x₂}`, splitting over `F_q`. Each root has an `F_q`-point
above it (`P`, `Q`, `chord_third_point_on_E`). -/

private theorem normPoly_chord_factor_chord
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points) (hxx : P.1 ≠ Q.1) :
    let lam := slopeOf P.1 P.2 Q.1 Q.2
    let x₂ := lam ^ 2 - P.1 - Q.1
    normPoly E (chordCoordRingElt E P Q)
      = -((X - C P.1) * (X - C Q.1) * (X - C x₂)) := by
  classical
  intro lam x₂
  set mu := P.2 - lam * P.1 with hmuDef
  -- chordCoordRingElt P Q in chord branch = { a := -(C lam) X - C mu, b := -1 }
  have hD : (chordCoordRingElt E P Q).a = -(C lam) * X - C mu ∧
            (chordCoordRingElt E P Q).b = -1 := by
    unfold chordCoordRingElt
    rw [dif_neg hxx]
    refine ⟨rfl, rfl⟩
  -- normPoly = a² - b² · curveX = (lam X + mu)² - curveX
  have hNorm : normPoly E (chordCoordRingElt E P Q) =
      (C lam * X + C mu) ^ 2 - curveX E := by
    rw [normPoly_eq, hD.1, hD.2]
    ring
  rw [hNorm]
  unfold curveX
  -- Vieta hypotheses.
  have he₁ : P.1 + Q.1 + x₂ = lam ^ 2 := by
    show P.1 + Q.1 + (lam ^ 2 - P.1 - Q.1) = lam ^ 2; ring
  have he₂ : P.1 * Q.1 + P.1 * x₂ + Q.1 * x₂ = E.curveA - 2 * lam * mu := by
    have := chord_x_pairwise_sum E P Q hP hQ hxx
    -- this uses lam (slopeOf), mu (= P.2 - lam · P.1), x₂ as in the theorem.
    -- Match my x₂ and mu definitions.
    show P.1 * Q.1 + P.1 * x₂ + Q.1 * x₂ = E.curveA - 2 * lam * mu
    convert this using 2 <;> rfl
  have he₃ : P.1 * Q.1 * x₂ = mu ^ 2 - E.curveB := by
    have := chord_x_triple_product E P Q hP hQ hxx
    show P.1 * Q.1 * x₂ = mu ^ 2 - E.curveB
    convert this using 2 <;> rfl
  -- Now: (C lam · X + C mu)² − (X³ + C A · X + C B)
  --   = -((X - C P.1)(X - C Q.1)(X - C x₂))
  -- Expand the RHS first, in terms of e₁, e₂, e₃.
  have hRHS_expand :
      -((X - C P.1) * (X - C Q.1) * (X - C x₂)) =
        -X ^ 3 + (C P.1 + C Q.1 + C x₂) * X ^ 2
          - (C P.1 * C Q.1 + C P.1 * C x₂ + C Q.1 * C x₂) * X
          + C P.1 * C Q.1 * C x₂ := by ring
  rw [hRHS_expand]
  -- Convert C-products to single C of products.
  have hPQs : C P.1 + C Q.1 + C x₂ = C (P.1 + Q.1 + x₂) := by
    rw [Polynomial.C_add, Polynomial.C_add]
  have hPQp : C P.1 * C Q.1 + C P.1 * C x₂ + C Q.1 * C x₂
      = C (P.1 * Q.1 + P.1 * x₂ + Q.1 * x₂) := by
    rw [Polynomial.C_add, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_mul,
        Polynomial.C_mul]
  have hPQt : C P.1 * C Q.1 * C x₂ = C (P.1 * Q.1 * x₂) := by
    rw [Polynomial.C_mul, Polynomial.C_mul]
  rw [hPQs, hPQp, hPQt, he₁, he₂, he₃]
  -- Now both sides are C-applied polynomial identities.
  -- LHS: (C lam · X + C mu)² - (X³ + C A · X + C B)
  -- RHS: -X³ + C(λ²) X² - C(A - 2λμ) X + C(μ² - B)
  -- expand using Polynomial.C and ring.
  rw [show C (lam ^ 2) = C lam * C lam from by rw [pow_two, Polynomial.C_mul]]
  rw [show C (E.curveA - 2 * lam * mu) = C E.curveA - 2 * C lam * C mu from by
        have h2 : (C (2 : ZMod E.q) : (ZMod E.q)[X]) = 2 := by
          rw [show (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) from by norm_cast,
              Polynomial.C_eq_natCast]
          norm_cast
        rw [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_mul, h2]]
  rw [show C (mu ^ 2 - E.curveB) = C mu * C mu - C E.curveB from by
        rw [Polynomial.C_sub, pow_two, Polynomial.C_mul]]
  ring

theorem splitsOnE_chordCoordRingElt_chord
    (P Q : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (hxx : P.1 ≠ Q.1) :
    splitsOnE E (chordCoordRingElt E P Q) := by
  classical
  set lam := slopeOf P.1 P.2 Q.1 Q.2 with hlam
  set mu := P.2 - lam * P.1 with hmu
  set x₂ := lam ^ 2 - P.1 - Q.1 with hx₂
  -- Use the factored form for the roots multiset.
  have hFactor := normPoly_chord_factor_chord E P Q hP hQ hxx
  simp only [← hlam, ← hmu, ← hx₂] at hFactor
  refine ⟨?_, ?_⟩
  · -- splits: card roots = natDegree
    show Multiset.card (normPoly E _).roots = (normPoly E _).natDegree
    rw [hFactor]
    rw [natDegree_neg]
    have hMul1 : (X - C P.1 : (ZMod E.q)[X]) * (X - C Q.1) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have hX2 : (X - C x₂ : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    rw [Polynomial.roots_neg]
    rw [Polynomial.roots_mul (mul_ne_zero hMul1 hX2)]
    rw [Polynomial.roots_mul hMul1]
    rw [Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    rw [show ((X - C P.1) * (X - C Q.1) * (X - C x₂) : (ZMod E.q)[X]).natDegree = 3 from ?_]
    · simp [Multiset.card_add]
    · rw [natDegree_mul hMul1 hX2, natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
          natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]
  · -- Every root lifts to an F_q-point
    intro α hα
    rw [hFactor] at hα
    rw [Polynomial.roots_neg] at hα
    have hMul1 : (X - C P.1 : (ZMod E.q)[X]) * (X - C Q.1) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have hX2 : (X - C x₂ : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    rw [Polynomial.roots_mul (mul_ne_zero hMul1 hX2)] at hα
    rw [Polynomial.roots_mul hMul1] at hα
    rw [Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C] at hα
    -- hα : α ∈ {P.1} + {Q.1} + {x₂}
    rcases Multiset.mem_add.mp hα with h12 | h3
    · rcases Multiset.mem_add.mp h12 with h1 | h2
      · exact ⟨P.2, by rw [Multiset.mem_singleton.mp h1]; exact hP⟩
      · exact ⟨Q.2, by rw [Multiset.mem_singleton.mp h2]; exact hQ⟩
    · -- α = x₂; lift via chord_third_point_on_E
      rw [Multiset.mem_singleton.mp h3]
      have hOC : (lam * x₂ + mu) ^ 2 = x₂ ^ 3 + E.curveA * x₂ + E.curveB := by
        have := chord_third_point_on_E E P Q hP hQ hxx
        simp only [← hlam, ← hx₂] at this
        convert this using 2
      exact ⟨lam * x₂ + mu, E.hComplete _ _ hOC⟩

/-! ## `splitsOnE` for the tangent (non-2-torsion doubling) case

When `P = Q` and `P.2 ≠ 0`, `chordCoordRingElt P P` is the tangent line
through `P` with slope `λ = (3·P.1²+A)/(2·P.2)`. The cubic `(λX+μ)² −
(X³+AX+B)` has `P.1` as a double root and `x₂ = λ²−2·P.1` as the third.

Two field-level Vieta identities (derived from the curve equation and
the slope definition) drive the polynomial factorisation. -/

private theorem tangent_vieta_pairwise
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (h2t : P.2 ≠ 0) :
    let lam := (3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹
    let mu := P.2 - lam * P.1
    let x₂ := lam ^ 2 - 2 * P.1
    P.1 ^ 2 + 2 * P.1 * x₂ = E.curveA - 2 * lam * mu := by
  intro lam mu x₂
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  have h2NZ : (2 : ZMod E.q) ≠ 0 := by
    have hq5 : E.q ≥ 5 := E.hq_ge
    have hcast : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
    rw [hcast, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
    intro hdvd
    have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h2yNZ : (2 * P.2 : ZMod E.q) ≠ 0 := mul_ne_zero h2NZ h2t
  -- 2λ · P.2 = 3·P.1² + A
  have hSlope : 2 * lam * P.2 = 3 * P.1 ^ 2 + E.curveA := by
    show 2 * ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹) * P.2 = 3 * P.1 ^ 2 + E.curveA
    field_simp
  -- Derive: 2λμ = 3P.1² + A − 2λ²·P.1 (via μ = P.2 − λ·P.1)
  -- Hence: A − 2λμ = -3P.1² + 2λ²·P.1.
  -- Want: P.1² + 2 P.1 (λ² − 2 P.1) = -3P.1² + 2λ²·P.1.
  -- LHS = P.1² + 2 λ²·P.1 − 4 P.1² = -3 P.1² + 2 λ²·P.1. ✓
  have hMu : mu = P.2 - lam * P.1 := rfl
  have h2lm : 2 * lam * mu = 3 * P.1 ^ 2 + E.curveA - 2 * lam ^ 2 * P.1 := by
    show 2 * lam * (P.2 - lam * P.1) = 3 * P.1 ^ 2 + E.curveA - 2 * lam ^ 2 * P.1
    linear_combination hSlope
  show P.1 ^ 2 + 2 * P.1 * (lam ^ 2 - 2 * P.1)
      = E.curveA - 2 * lam * mu
  rw [h2lm]; ring

private theorem tangent_vieta_triple
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (h2t : P.2 ≠ 0) :
    let lam := (3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹
    let mu := P.2 - lam * P.1
    let x₂ := lam ^ 2 - 2 * P.1
    P.1 ^ 2 * x₂ = mu ^ 2 - E.curveB := by
  intro lam mu x₂
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  have h2NZ : (2 : ZMod E.q) ≠ 0 := by
    have hq5 : E.q ≥ 5 := E.hq_ge
    have hcast : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
    rw [hcast, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
    intro hdvd
    have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h2yNZ : (2 * P.2 : ZMod E.q) ≠ 0 := mul_ne_zero h2NZ h2t
  have hSlope : 2 * lam * P.2 = 3 * P.1 ^ 2 + E.curveA := by
    show 2 * ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹) * P.2 = 3 * P.1 ^ 2 + E.curveA
    field_simp
  -- μ² = (P.2 − λ·P.1)² = P.2² − 2λ·P.1·P.2 + λ²·P.1²
  -- 2λ·P.1·P.2 = (3P.1² + A)·P.1 = 3P.1³ + A·P.1
  -- P.2² = P.1³ + A·P.1 + B
  -- μ² = P.1³ + A·P.1 + B − 3P.1³ − A·P.1 + λ²·P.1²
  --    = −2P.1³ + B + λ²·P.1²
  -- μ² − B = −2P.1³ + λ²·P.1² = P.1² (λ² − 2 P.1) = P.1² · x₂. ✓
  have h2lp1p2 : 2 * lam * P.1 * P.2 = 3 * P.1 ^ 3 + E.curveA * P.1 := by
    linear_combination P.1 * hSlope
  have hMu2 : mu ^ 2 = P.2 ^ 2 - 2 * lam * P.1 * P.2 + lam ^ 2 * P.1 ^ 2 := by
    show (P.2 - lam * P.1) ^ 2 = P.2 ^ 2 - 2 * lam * P.1 * P.2 + lam ^ 2 * P.1 ^ 2
    ring
  show P.1 ^ 2 * (lam ^ 2 - 2 * P.1) = mu ^ 2 - E.curveB
  rw [hMu2, hOC, h2lp1p2]; ring

private theorem normPoly_chord_factor_tangent
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (h2t : P.2 ≠ 0) :
    let lam := (3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹
    let mu := P.2 - lam * P.1
    let x₂ := lam ^ 2 - 2 * P.1
    normPoly E (chordCoordRingElt E P P)
      = -((X - C P.1) ^ 2 * (X - C x₂)) := by
  classical
  intro lam mu x₂
  have hD : (chordCoordRingElt E P P).a = -(C lam) * X - C mu ∧
            (chordCoordRingElt E P P).b = -1 := by
    unfold chordCoordRingElt
    rw [dif_pos rfl, dif_pos rfl, if_neg h2t]
    refine ⟨rfl, rfl⟩
  have hNorm : normPoly E (chordCoordRingElt E P P) =
      (C lam * X + C mu) ^ 2 - curveX E := by
    rw [normPoly_eq, hD.1, hD.2]
    ring
  rw [hNorm]
  unfold curveX
  have hP2 : P.1 ^ 2 + 2 * P.1 * x₂ = E.curveA - 2 * lam * mu :=
    tangent_vieta_pairwise E hP h2t
  have hP3 : P.1 ^ 2 * x₂ = mu ^ 2 - E.curveB :=
    tangent_vieta_triple E hP h2t
  have hP1 : 2 * P.1 + x₂ = lam ^ 2 := by
    show 2 * P.1 + (lam ^ 2 - 2 * P.1) = lam ^ 2; ring
  -- Expand both sides as polynomials and use the field-level Vieta identities.
  -- LHS = (C lam · X + C mu)² − (X³ + C A · X + C B)
  --     = C(λ²) X² + C(2λμ) X + C(μ²) − X³ − C A · X − C B
  -- RHS = -(X − C P.1)²(X − C x₂)
  --     = −X³ + C(2P.1+x₂) X² − C(P.1² + 2 P.1 x₂) X + C(P.1² · x₂)
  -- These match coefficient-by-coefficient via Vieta.
  have h2C : (C (2 : ZMod E.q) : (ZMod E.q)[X]) = 2 := by
    rw [show (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) from by norm_cast,
        Polynomial.C_eq_natCast]
    norm_cast
  have hLHS_expand :
      (C lam * X + C mu) ^ 2 - (X ^ 3 + C E.curveA * X + C E.curveB) =
        C (lam ^ 2) * X ^ 2 + C (2 * lam * mu) * X + C (mu ^ 2)
          - X ^ 3 - C E.curveA * X - C E.curveB := by
    have hl2C : ((C lam : (ZMod E.q)[X]) ^ 2) = C (lam ^ 2) := by
      rw [pow_two, ← Polynomial.C_mul, ← pow_two]
    have hm2C : ((C mu : (ZMod E.q)[X]) ^ 2) = C (mu ^ 2) := by
      rw [pow_two, ← Polynomial.C_mul, ← pow_two]
    have h2lmC : (2 * C lam * C mu : (ZMod E.q)[X]) = C (2 * lam * mu) := by
      rw [show (2 * lam * mu : ZMod E.q) = (2 : ZMod E.q) * lam * mu from rfl,
          show C ((2 : ZMod E.q) * lam * mu) = C 2 * C lam * C mu from by
            rw [Polynomial.C_mul, Polynomial.C_mul]]
      rw [h2C]
    rw [← hl2C, ← h2lmC, ← hm2C]; ring
  have hRHS_expand :
      -((X - C P.1) ^ 2 * (X - C x₂)) =
        -X ^ 3 + (2 * C P.1 + C x₂) * X ^ 2
          - (C P.1 ^ 2 + 2 * C P.1 * C x₂) * X
          + C P.1 ^ 2 * C x₂ := by ring
  rw [hLHS_expand, hRHS_expand]
  -- Convert C-products on RHS to single C-applications:
  have hP1sqC : (C P.1 ^ 2 : (ZMod E.q)[X]) = C (P.1 ^ 2) := by
    rw [pow_two, ← Polynomial.C_mul, ← pow_two]
  have h2P1Cx2C : (2 * C P.1 * C x₂ : (ZMod E.q)[X]) = C (2 * P.1 * x₂) := by
    rw [Polynomial.C_mul, Polynomial.C_mul, h2C]
  have hP1sqx2C : (C P.1 ^ 2 * C x₂ : (ZMod E.q)[X]) = C (P.1 ^ 2 * x₂) := by
    rw [hP1sqC, ← Polynomial.C_mul]
  have h2P1plusx2C : (2 * C P.1 + C x₂ : (ZMod E.q)[X]) = C (2 * P.1 + x₂) := by
    rw [Polynomial.C_add, Polynomial.C_mul, h2C]
  have hSumC :
      (C P.1 ^ 2 + 2 * C P.1 * C x₂ : (ZMod E.q)[X])
        = C (P.1 ^ 2 + 2 * P.1 * x₂) := by
    rw [Polynomial.C_add, hP1sqC, h2P1Cx2C]
  rw [h2P1plusx2C, hSumC, hP1sqx2C]
  -- Apply the three Vieta identities (under C):
  rw [show C (2 * P.1 + x₂ : ZMod E.q) = C (lam ^ 2) from by rw [hP1]]
  rw [show C (P.1 ^ 2 + 2 * P.1 * x₂ : ZMod E.q)
        = C (E.curveA - 2 * lam * mu) from by rw [hP2]]
  rw [show C (P.1 ^ 2 * x₂ : ZMod E.q)
        = C (mu ^ 2 - E.curveB) from by rw [hP3]]
  -- Now everything is in the same form; close with C-distribution + ring.
  rw [show C (E.curveA - 2 * lam * mu : ZMod E.q)
        = C E.curveA - C (2 * lam * mu) from by rw [Polynomial.C_sub]]
  rw [show C (mu ^ 2 - E.curveB : ZMod E.q) = C (mu ^ 2) - C E.curveB from by
        rw [Polynomial.C_sub]]
  ring

theorem splitsOnE_chordCoordRingElt_tangent
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (h2t : P.2 ≠ 0) :
    splitsOnE E (chordCoordRingElt E P P) := by
  classical
  set lam := (3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹ with hlam
  set x₂ := lam ^ 2 - 2 * P.1 with hx₂
  have hFactor := normPoly_chord_factor_tangent E hP h2t
  simp only [← hlam, ← hx₂] at hFactor
  refine ⟨?_, ?_⟩
  · show Multiset.card (normPoly E _).roots = (normPoly E _).natDegree
    rw [hFactor, natDegree_neg]
    have hSq : (X - C P.1 : (ZMod E.q)[X]) ^ 2 ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
    have hX2 : (X - C x₂ : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    rw [Polynomial.roots_neg, Polynomial.roots_mul (mul_ne_zero hSq hX2),
        Polynomial.roots_pow, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    have hND : ((X - C P.1) ^ 2 * (X - C x₂) : (ZMod E.q)[X]).natDegree = 3 := by
      rw [natDegree_mul hSq hX2, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C]
    rw [hND]
    simp
  · intro α hα
    rw [hFactor] at hα
    have hSq : (X - C P.1 : (ZMod E.q)[X]) ^ 2 ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
    have hX2 : (X - C x₂ : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    rw [Polynomial.roots_neg, Polynomial.roots_mul (mul_ne_zero hSq hX2),
        Polynomial.roots_pow, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C] at hα
    rcases Multiset.mem_add.mp hα with h12 | h3
    · have h_eq : (2 • ({P.1} : Multiset (ZMod E.q))) = {P.1, P.1} := rfl
      rw [h_eq] at h12
      rcases Multiset.mem_cons.mp h12 with h | h
      · exact ⟨P.2, by rw [h]; exact hP⟩
      · exact ⟨P.2, by rw [Multiset.mem_singleton.mp h]; exact hP⟩
    · -- α = x₂; the third intersection is on E.
      rw [Multiset.mem_singleton.mp h3]
      -- Use the doubling-third-intersection-on-E claim.
      -- y₂ = λ·x₂ + μ where μ = P.2 - λ·P.1.
      set mu := P.2 - lam * P.1 with hmu
      have hOC : (lam * x₂ + mu) ^ 2 = x₂ ^ 3 + E.curveA * x₂ + E.curveB := by
        -- Use Vieta's: from `tangent_vieta_pairwise` and `tangent_vieta_triple`,
        -- (λ·x₂ + μ)² simplifies. Actually easier: just verify (λx + μ)² − (x³+Ax+B) = 0 at x=x₂.
        -- Since normPoly = -(X-P.1)²(X-x₂), normPoly evaluated at x₂ is 0.
        -- normPoly = (C λ X + C μ)² - curveX, so eval x₂ gives (λx₂+μ)² − (x₂³+Ax₂+B) = 0.
        have hRoot :
            ((C lam * X + C mu) ^ 2 - curveX E).eval x₂ = 0 := by
          have hRefactor : (C lam * X + C mu) ^ 2 - curveX E
              = normPoly E (chordCoordRingElt E P P) := by
            rw [normPoly_eq]
            unfold chordCoordRingElt
            rw [dif_pos rfl, dif_pos rfl, if_neg h2t]
            ring
          rw [hRefactor, hFactor]
          simp [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
                Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
        unfold curveX at hRoot
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
                   Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hRoot
        linear_combination hRoot
      exact ⟨lam * x₂ + mu, E.hComplete _ _ hOC⟩

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
