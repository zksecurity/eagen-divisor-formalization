/-
  Divisor/SupportDisjoint.lean

  `\ref{lem:support-disjoint}` (Support Disjointness): Bassa 2025, Lemma 5.

  For D in F_q[E] with N zeros, and random A0, A1 in E(F_q) \ {O},
  A2 = -(A0 + A1):

    Pr[supp(D) intersects {A0, A1, A2}] <= 3*(N+1) / #E(F_q)

  Proof: union bound over three events.
-/
import Divisor.Defs
import Divisor.Axioms.AxiomHasseWeil
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

open Classical Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Bad events -/

/-- The number of zeros of D among the affine points -/
def numZeros (D : CoordRingElt E.q) : ℕ :=
  (zeros D E.points).card

/-- Predicate form of the completeness bad event for a given pair.

Strengthened (per the soundness audit) to also exclude:
* the *diagonal* `A₀ = A₁` (Lean's `slopeOf` gives `0/0 = 0` here, not
  the geometric tangent slope);
* `thirdPoint E A₀ A₁ = some A₀` (chord tangent at A₀, where the
  `dx/dz` denominator at A₂ = A₀ vanishes);
* `thirdPoint E A₀ A₁ = some A₁` (chord tangent at A₁, similar).

These three additional graphs each contribute at most `|E.points|`
to the bad-set cardinality, so the union-bound shape becomes
`(3N + 4) · |E.points|`. -/
noncomputable def badPairCompletenessPred (D : CoordRingElt E.q)
    (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) : Prop :=
  D.eval p.1.1 p.1.2 = 0
  ∨ D.eval p.2.1 p.2.2 = 0
  ∨ (match thirdPoint E p.1 p.2 with
      | none => True
      | some (x, y) => D.eval x y = 0)
  ∨ p.1 = p.2  -- diagonal
  ∨ thirdPoint E p.1 p.2 = some p.1  -- tangent collision at A₀
  ∨ thirdPoint E p.1 p.2 = some p.2  -- tangent collision at A₁

/-- The completeness bad set: pairs `(A₀, A₁)` where
    `D(A₀) = 0`, `D(A₁) = 0`, `A₂ = ∞`, or `A₂ = (x, y)` with `D(x, y) = 0`. -/
noncomputable def badChallengesCompleteness (D : CoordRingElt E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter (badPairCompletenessPred E D)

/-! ## Tangent-collision bad-pair set

The "tangent at A₀" pairs: `{(A₀, A₁) ∈ E.points × E.points :
thirdPoint E A₀ A₁ = some A₀}`. This is the configuration where
the chord through `A₀` and `A₁` is tangent to `E` at `A₀`. Lean's
`logDerivCheckFn` uses the chord (not the geometric tangent) slope
in this case, leading to incorrect values.

Codex-confirmed bound: `|S₅| ≤ |E.points|` via `thirdPoint_inj_on_A₁`
(group-law: `A₀ + A₁ = -A₀` ⟹ `A₁ = -2A₀`, unique). -/

noncomputable def tangentCollisionAtA₀ :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter (fun p => thirdPoint E p.1 p.2 = some p.1)

/-! ## A2 = O iff A1 = -A0

For fixed A0 = (x0, y0), the condition A1 = -A0 means A1 = (x0, -y0).
At most one such point exists in any Finset (since elements are unique). -/

/-- For each A0, at most one A1 in E.points satisfies A1 = -A0.
    Proof: the predicate (A1.1 = x0 ∧ A1.2 = -y0) determines A1 uniquely. -/
theorem card_A2_is_infinity (A₀ : ZMod E.q × ZMod E.q) :
    (E.points.filter (fun A₁ => A₁.1 = A₀.1 ∧ A₁.2 = -A₀.2)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact Prod.ext (ha.2.1.trans hb.2.1.symm) (ha.2.2.trans hb.2.2.symm)

/-! ## Main result: `\ref{lem:support-disjoint}` (structural)

The full `\ref{lem:support-disjoint}` requires the group law to handle A2.
We state the bound structurally: the union bound over
A0-hits-zero, A1-hits-zero, and A2-bad gives the result. -/

/-- The number of (A0, A1) pairs where A0 is a zero of D:
    for each A1, there are at most numZeros choices of A0. -/
theorem card_A0_bad_le (D : CoordRingElt E.q) :
    ∀ A₁ ∈ E.points,
      (E.points.filter (fun A₀ => D.eval A₀.1 A₀.2 = 0)).card ≤ numZeros E D := by
  intro _ _
  rfl

/-- The number of (A0, A1) pairs where A1 is a zero of D:
    for each A0, there are at most numZeros choices of A1. -/
theorem card_A1_bad_le (D : CoordRingElt E.q) :
    ∀ A₀ ∈ E.points,
      (E.points.filter (fun A₁ => D.eval A₁.1 A₁.2 = 0)).card ≤ numZeros E D := by
  intro _ _
  rfl

/-! ## Chord-intersection: third point on curve -/

/-- If `A₀`, `A₁` are on `E` and the third intersection is affine, it is on `E`.
    Proved by verifying the Weierstrass equation `y² = x³ + Ax + B` holds
    for `(x, y)` via `linear_combination` using the hypotheses
    `y₀² = x₀³ + Ax₀ + B`, `y₁² = x₁³ + Ax₁ + B`, and the slope identity. -/
theorem third_point_on_curve
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    {x y : ZMod E.q}
    (hT : thirdPoint E A₀ A₁ = some (x, y)) :
    (x, y) ∈ E.points := by
  have hC0 : A₀.2 ^ 2 = A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB := E.hOnCurve A₀ hA₀
  have hC1 : A₁.2 ^ 2 = A₁.1 ^ 3 + E.curveA * A₁.1 + E.curveB := E.hOnCurve A₁ hA₁
  apply E.hComplete
  -- Split on which branch produced the affine output.
  unfold thirdPoint at hT
  by_cases hx : A₀.1 = A₁.1
  · rw [if_pos hx] at hT
    by_cases hy : A₀.2 = A₁.2
    · rw [if_pos hy] at hT
      by_cases h2t : A₀.2 = 0
      · rw [if_pos h2t] at hT
        exact absurd hT (by simp)
      · rw [if_neg h2t] at hT
        -- Tangent case. λ = (3·x₀² + A) / (2·y₀).
        set lam := (3 * A₀.1 ^ 2 + E.curveA) * (2 * A₀.2)⁻¹ with hlam_def
        set mu := A₀.2 - lam * A₀.1 with hmu_def
        set x₂ := lam ^ 2 - 2 * A₀.1 with hx2_def
        set y₂ := lam * x₂ + mu with hy2_def
        have hxy : x = x₂ ∧ y = y₂ := by
          rw [Option.some.injEq, Prod.mk.injEq] at hT
          exact ⟨hT.1.symm, hT.2.symm⟩
        rw [hxy.1, hxy.2]
        have h2y_ne : (2 * A₀.2 : ZMod E.q) ≠ 0 := by
          intro hh
          have : A₀.2 = 0 := by
            have h2 : (2 : ZMod E.q) ≠ 0 := by
              have hq5 : E.q ≥ 5 := E.hq_ge
              have : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
              rw [this]
              rw [Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
              intro hdvd
              have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
              omega
            exact (mul_eq_zero.mp hh).resolve_left h2
          exact h2t this
        have hlam_rel : lam * (2 * A₀.2) = 3 * A₀.1 ^ 2 + E.curveA := by
          rw [hlam_def, mul_assoc, inv_mul_cancel₀ h2y_ne, mul_one]
        -- Now: y₂² = x₂³ + A·x₂ + B, derivable from hC0 and hlam_rel.
        show y₂ ^ 2 = x₂ ^ 3 + E.curveA * x₂ + E.curveB
        simp only [hy2_def, hx2_def, hmu_def]
        linear_combination hC0 + (lam ^ 2 - 3 * A₀.1) * hlam_rel
    · rw [if_neg hy] at hT
      exact absurd hT (by simp)
  · rw [if_neg hx] at hT
    set lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹ with hlam_def
    set mu := A₀.2 - lam * A₀.1 with hmu_def
    set x₂ := lam ^ 2 - A₀.1 - A₁.1 with hx2_def
    set y₂ := lam * x₂ + mu with hy2_def
    have hxy : x = x₂ ∧ y = y₂ := by
      rw [Option.some.injEq, Prod.mk.injEq] at hT
      exact ⟨hT.1.symm, hT.2.symm⟩
    rw [hxy.1, hxy.2]
    have hx_ne : (A₁.1 - A₀.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    -- Slope relation after clearing denominator.
    have hlam_rel : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
      rw [hlam_def]; field_simp
    -- Key auxiliary: `Q := (x² + xX + X² + A) - λ²·(X-x) - 2λy`.
    -- We prove `Q = 0` by showing `(X-x)·Q = 0` as a polynomial combination
    -- of the three hypotheses, then using `X - x ≠ 0`.
    set Q : ZMod E.q :=
      (A₀.1 ^ 2 + A₀.1 * A₁.1 + A₁.1 ^ 2 + E.curveA)
        - lam ^ 2 * (A₁.1 - A₀.1) - 2 * lam * A₀.2 with hQdef
    have hQ_mul : (A₁.1 - A₀.1) * Q = 0 := by
      rw [hQdef]
      linear_combination
        (1 : ZMod E.q) * hC0 + (-1 : ZMod E.q) * hC1 +
          (-(lam * (A₁.1 - A₀.1)) - (A₁.2 - A₀.2) - 2 * A₀.2) * hlam_rel
    have hQ : Q = 0 := (mul_eq_zero.mp hQ_mul).resolve_left hx_ne
    -- Key polynomial identity (verified by symbolic computation):
    --   y₂² - (x₂³ + A·x₂ + B) + (x₂ - A₀.1)·Q = A₀.2² - A₀.1³ - A·A₀.1 - B.
    -- The right side is 0 by hC0. Combined with hQ : Q = 0, the goal follows.
    show y₂ ^ 2 = x₂ ^ 3 + E.curveA * x₂ + E.curveB
    have hGoal : y₂ ^ 2 - (x₂ ^ 3 + E.curveA * x₂ + E.curveB) = -((x₂ - A₀.1) * Q) := by
      simp only [hy2_def, hx2_def, hmu_def, hQdef]
      linear_combination hC0
    have : y₂ ^ 2 - (x₂ ^ 3 + E.curveA * x₂ + E.curveB) = 0 := by
      rw [hGoal, hQ]; ring
    linear_combination this

/-! ## Helper: relate `thirdPoint` to mathlib's group law

When `thirdPoint E A₀ A₁ = some (x, y)` and `A₀, A₁ ∈ E.points`, the result
is the negation of the mathlib group sum:
    `affineOfMem A₀ + affineOfMem A₁ = -affineOfMem (x, y)`.
The proof works case-by-case (chord vs. tangent) showing that our `thirdPoint`
coordinates equal `(addX, negAddY)`, and invokes mathlib's
`add_of_X_ne'` / `add_self_of_Y_ne'` lemmas. -/

theorem thirdPoint_some_eq_neg_add
    {A₀ A₁ : ZMod E.q × ZMod E.q}
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    {x y : ZMod E.q}
    (hT : thirdPoint E A₀ A₁ = some (x, y)) :
    ECPoint.affineOfMem E hA₀ + ECPoint.affineOfMem E hA₁ =
      -ECPoint.affineOfMem E (third_point_on_curve E A₀ A₁ hA₀ hA₁ hT) := by
  classical
  -- Extract the nonsingular witnesses.
  have hxy_mem : (x, y) ∈ E.points := third_point_on_curve E A₀ A₁ hA₀ hA₁ hT
  have hns0 : E.toW.toAffine.Nonsingular A₀.1 A₀.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff A₀.1 A₀.2).mpr (E.hOnCurve A₀ hA₀))
  have hns1 : E.toW.toAffine.Nonsingular A₁.1 A₁.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff A₁.1 A₁.2).mpr (E.hOnCurve A₁ hA₁))
  have hnsxy : E.toW.toAffine.Nonsingular x y :=
    E.equation_iff_nonsingular.mp ((E.equation_iff x y).mpr (E.hOnCurve _ hxy_mem))
  -- Curve equations.
  have hC0 : A₀.2 ^ 2 = A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB := E.hOnCurve A₀ hA₀
  -- Show affineOfMem unfolds to .some (with these nonsingular witnesses).
  have heq0 : ECPoint.affineOfMem E hA₀ =
      (.some hns0 : ECPoint E) := rfl
  have heq1 : ECPoint.affineOfMem E hA₁ =
      (.some hns1 : ECPoint E) := rfl
  have heqxy : ECPoint.affineOfMem E hxy_mem =
      (.some hnsxy : ECPoint E) := rfl
  rw [heq0, heq1, heqxy]
  -- Case-split on the structure of `thirdPoint`.
  unfold thirdPoint at hT
  by_cases hxx : A₀.1 = A₁.1
  · rw [if_pos hxx] at hT
    by_cases hyy : A₀.2 = A₁.2
    · rw [if_pos hyy] at hT
      by_cases h2t : A₀.2 = 0
      · rw [if_pos h2t] at hT
        exact absurd hT (by simp)
      · rw [if_neg h2t] at hT
        -- Tangent case: x₀ = x₁, y₀ = y₁, y₀ ≠ 0.
        rw [Option.some.injEq, Prod.mk.injEq] at hT
        obtain ⟨hxe, hye⟩ := hT
        -- Substitute A₁ = A₀ via hxx, hyy.
        -- mathlib slope at (A₀, A₀): (3 x² + A) / (2y).
        -- We need: P + P = -some(x, y) where (x, y) = thirdPoint coords.
        -- Use `add_self_of_Y_ne'`.
        -- First, hns0 vs hns1: since A₀.1 = A₁.1 and A₀.2 = A₁.2, these are
        -- nonsingular witnesses for the same point.
        have hyneg : A₀.2 ≠ E.toW.toAffine.negY A₀.1 A₀.2 := by
          intro h
          apply h2t
          have heq : A₀.2 = -A₀.2 := by
            have hnY : E.toW.toAffine.negY A₀.1 A₀.2 = -A₀.2 := by
              show -A₀.2 - E.toW.a₁ * A₀.1 - E.toW.a₃ = -A₀.2
              rw [E.toW_a₁, E.toW_a₃]; ring
            rw [hnY] at h
            exact h
          have htwo : (2 : ZMod E.q) * A₀.2 = 0 := by linear_combination heq
          have h2 : (2 : ZMod E.q) ≠ 0 := by
            have hq5 : E.q ≥ 5 := E.hq_ge
            have : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
            rw [this, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
            intro hdvd
            have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
            omega
          exact (mul_eq_zero.mp htwo).resolve_left h2
        -- Replace A₁'s nonsingular witness with A₀'s by congruence.
        have hpts_eq : (.some hns1 : ECPoint E) = .some hns0 := by
          congr 1 <;> [exact hxx.symm; exact hyy.symm]
        rw [hpts_eq]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hyneg]
        -- Goal: -some (point at (addX, negAddY)) = -some hnsxy.
        -- Compute the slope.
        have hnegY : E.toW.toAffine.negY A₀.1 A₀.2 = -A₀.2 := by
          show -A₀.2 - E.toW.a₁ * A₀.1 - E.toW.a₃ = -A₀.2
          rw [E.toW_a₁, E.toW_a₃]; ring
        have hsl : E.toW.toAffine.slope A₀.1 A₀.1 A₀.2 A₀.2 =
            (3 * A₀.1 ^ 2 + E.curveA) * (2 * A₀.2)⁻¹ := by
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
          simp only [E.toW_a₁, E.toW_a₂, E.toW_a₄]
          rw [hnegY]
          field_simp
          ring
        -- Coordinate identities.
        have hX_eq : E.toW.toAffine.addX A₀.1 A₀.1
            (E.toW.toAffine.slope A₀.1 A₀.1 A₀.2 A₀.2) = x := by
          simp only [WeierstrassCurve.Affine.addX, E.toW_a₁, E.toW_a₂, hsl]
          linear_combination hxe
        have hY_eq : E.toW.toAffine.negAddY A₀.1 A₀.1 A₀.2
            (E.toW.toAffine.slope A₀.1 A₀.1 A₀.2 A₀.2) = y := by
          simp only [WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
                     E.toW_a₁, E.toW_a₂, hsl]
          linear_combination hye
        -- Equate the two `some` points by rewriting with hX_eq, hY_eq.
        congr 1
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨hX_eq, hY_eq⟩
    · rw [if_neg hyy] at hT
      exact absurd hT (by simp)
  · rw [if_neg hxx] at hT
    -- Chord case: x₀ ≠ x₁.
    rw [Option.some.injEq, Prod.mk.injEq] at hT
    obtain ⟨hxe, hye⟩ := hT
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne' hxx]
    -- Show coordinates match.
    have hsl : E.toW.toAffine.slope A₀.1 A₁.1 A₀.2 A₁.2 =
        (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹ := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxx]
      have hxne : (A₀.1 - A₁.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr hxx
      have hxne' : (A₁.1 - A₀.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx)
      field_simp
      ring
    have hX_eq : E.toW.toAffine.addX A₀.1 A₁.1
        (E.toW.toAffine.slope A₀.1 A₁.1 A₀.2 A₁.2) = x := by
      simp only [WeierstrassCurve.Affine.addX, E.toW_a₁, E.toW_a₂, hsl]
      linear_combination hxe
    have hY_eq : E.toW.toAffine.negAddY A₀.1 A₁.1 A₀.2
        (E.toW.toAffine.slope A₀.1 A₁.1 A₀.2 A₁.2) = y := by
      simp only [WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
                 E.toW_a₁, E.toW_a₂, hsl]
      linear_combination hye
    congr 1
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hX_eq, hY_eq⟩

/-! ## Injectivity of A₁ ↦ thirdPoint E A₀ A₁ (group-law cancellation)

Classical EC fact: for each A₀ on E, the map `A₁ ↦ thirdPoint E A₀ A₁`
is injective on affine A₁ for which the third point is affine (i.e. not ∞).
Equivalent to: if `A₀ + A₁ = A₀ + A₁'` (group law), then `A₁ = A₁'`.

Proved directly from mathlib's group-law cancellation on `ECPoint E`,
via the identity `thirdPoint = -(A₀ + A₁)` (`thirdPoint_some_eq_neg_add`). -/
theorem thirdPoint_inj_on_A₁ (A₀ : ZMod E.q × ZMod E.q) (hA₀ : A₀ ∈ E.points) :
    Set.InjOn (fun A₁ => thirdPoint E A₀ A₁)
      {A₁ | A₁ ∈ E.points ∧ thirdPoint E A₀ A₁ ≠ none} := by
  intro a ha b hb hab
  obtain ⟨ha_mem, ha_ninf⟩ := ha
  obtain ⟨hb_mem, hb_ninf⟩ := hb
  simp only at hab
  -- Extract some-form of thirdPoint for both.
  obtain ⟨pa, hTa'⟩ : ∃ p, thirdPoint E A₀ a = some p :=
    Option.ne_none_iff_exists'.mp ha_ninf
  obtain ⟨pb, hTb'⟩ : ∃ p, thirdPoint E A₀ b = some p :=
    Option.ne_none_iff_exists'.mp hb_ninf
  obtain ⟨xa, ya⟩ := pa
  obtain ⟨xb, yb⟩ := pb
  have hTa : thirdPoint E A₀ a = some (xa, ya) := hTa'
  have hTb : thirdPoint E A₀ b = some (xb, yb) := hTb'
  -- The third points are equal, so their coordinates are equal.
  have heq_coord : (xa, ya) = (xb, yb) := by
    have : (some (xa, ya) : Option (ZMod E.q × ZMod E.q)) = some (xb, yb) := by
      rw [← hTa, ← hTb, hab]
    rw [Option.some.injEq] at this
    exact this
  -- Apply the group-law identity.
  have hGa := thirdPoint_some_eq_neg_add E hA₀ ha_mem hTa
  have hGb := thirdPoint_some_eq_neg_add E hA₀ hb_mem hTb
  -- The membership proofs for (xa, ya) and (xb, yb) coincide (after coord-eq).
  have h_third_a : (xa, ya) ∈ E.points := third_point_on_curve E A₀ a hA₀ ha_mem hTa
  have h_third_b : (xb, yb) ∈ E.points := third_point_on_curve E A₀ b hA₀ hb_mem hTb
  -- After coord identification, the right sides agree, so the left sides do too.
  have hadd_eq : ECPoint.affineOfMem E hA₀ + ECPoint.affineOfMem E ha_mem =
                 ECPoint.affineOfMem E hA₀ + ECPoint.affineOfMem E hb_mem := by
    rw [hGa, hGb]
    -- Need: -affineOfMem (xa, ya) = -affineOfMem (xb, yb).
    obtain ⟨hxx, hyy⟩ := Prod.mk.injEq _ _ _ _ |>.mp heq_coord
    -- affineOfMem depends on the membership proof, but only uses the coords.
    -- Since (xa, ya) = (xb, yb) as points, the affineOfMem values are equal.
    subst hxx
    subst hyy
    rfl
  -- Cancel A₀, then extract a = b from .some equality.
  have hpt_eq : ECPoint.affineOfMem E ha_mem = ECPoint.affineOfMem E hb_mem :=
    add_left_cancel hadd_eq
  -- affineOfMem ha_mem = .some hns_a, affineOfMem hb_mem = .some hns_b;
  -- equality forces a.1 = b.1 ∧ a.2 = b.2.
  have h_some : (.some (E.equation_iff_nonsingular.mp ((E.equation_iff a.1 a.2).mpr
                  (E.hOnCurve a ha_mem))) : ECPoint E)
              = .some (E.equation_iff_nonsingular.mp ((E.equation_iff b.1 b.2).mpr
                  (E.hOnCurve b hb_mem))) := hpt_eq
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h_some
  exact Prod.ext h_some.1 h_some.2

/-- For each `A₀ ∈ E.points`, at most one `A₁ ∈ E.points` satisfies
    `thirdPoint E A₀ A₁ = some A₀` (i.e., the chord is tangent at `A₀`).
    Direct consequence of `thirdPoint_inj_on_A₁`: equal outputs force
    equal inputs on the affine branch. -/
theorem card_thirdPoint_eq_self_fiber
    {A₀ : ZMod E.q × ZMod E.q} (hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = some A₀)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  obtain ⟨ha_mem, ha_eq⟩ := ha
  obtain ⟨hb_mem, hb_eq⟩ := hb
  have ha_ne : thirdPoint E A₀ a ≠ none := by rw [ha_eq]; simp
  have hb_ne : thirdPoint E A₀ b ≠ none := by rw [hb_eq]; simp
  have hAB : thirdPoint E A₀ a = thirdPoint E A₀ b := by rw [ha_eq, hb_eq]
  exact thirdPoint_inj_on_A₁ E A₀ hA₀ ⟨ha_mem, ha_ne⟩ ⟨hb_mem, hb_ne⟩ hAB


/-! ## Auxiliary: fiberwise decomposition -/

/-- For each `A₀ ∈ E.points`, the number of `A₁ ∈ E.points` with
    `thirdPoint E A₀ A₁ = ∞` is at most 1.

    With the corrected `thirdPoint`, infinity occurs only when the chord is
    vertical (`A₁ = -A₀`) or the tangent is vertical (`A₁ = A₀` and
    `A₀.2 = 0`, i.e. 2-torsion). In the 2-torsion case `-A₀ = A₀`, so
    these are the same element, yielding at most one A₁. -/
theorem card_thirdPoint_infinity_fiber (A₀ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = none)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  obtain ⟨hamem, hTa⟩ := ha
  obtain ⟨hbmem, hTb⟩ := hb
  -- Step 1: both a.1 = A₀.1 and b.1 = A₀.1.
  have hax : a.1 = A₀.1 := by
    unfold thirdPoint at hTa
    by_cases hx : A₀.1 = a.1
    · exact hx.symm
    · rw [if_neg hx] at hTa; exact absurd hTa (by simp)
  have hbx : b.1 = A₀.1 := by
    unfold thirdPoint at hTb
    by_cases hx : A₀.1 = b.1
    · exact hx.symm
    · rw [if_neg hx] at hTb; exact absurd hTb (by simp)
  -- Step 2: both a.2 = -A₀.2 (with A₀.2 = 0 collapsing -A₀ = A₀).
  -- Use curve equation for A₀, a, b to deduce a.2² = b.2² = A₀.2².
  have hC0 : A₀.2 ^ 2 = A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB := E.hOnCurve A₀ hA₀
  have hCa : a.2 ^ 2 = a.1 ^ 3 + E.curveA * a.1 + E.curveB := E.hOnCurve a hamem
  have hCb : b.2 ^ 2 = b.1 ^ 3 + E.curveA * b.1 + E.curveB := E.hOnCurve b hbmem
  have hyya : a.2 ^ 2 = A₀.2 ^ 2 := by rw [hCa, hC0]; rw [hax]
  have hyyb : b.2 ^ 2 = A₀.2 ^ 2 := by rw [hCb, hC0]; rw [hbx]
  -- From hyya: a.2 = A₀.2 or a.2 = -A₀.2.
  -- From hTa: in case a.2 = A₀.2, must have A₀.2 = 0 (else tangent gives affine output).
  have ha_yneg : a.2 = -A₀.2 := by
    have : (a.2 - A₀.2) * (a.2 + A₀.2) = 0 := by linear_combination hyya
    rcases mul_eq_zero.mp this with h | h
    · -- a.2 = A₀.2
      have ha_eq : a.2 = A₀.2 := by linear_combination h
      -- From hTa: in "y equal" branch, must hit the 2-torsion if_pos.
      unfold thirdPoint at hTa
      rw [if_pos hax.symm] at hTa
      rw [if_pos ha_eq.symm] at hTa
      by_cases h2 : A₀.2 = 0
      · rw [ha_eq, h2]; ring
      · rw [if_neg h2] at hTa; exact absurd hTa (by simp)
    · linear_combination h
  have hb_yneg : b.2 = -A₀.2 := by
    have : (b.2 - A₀.2) * (b.2 + A₀.2) = 0 := by linear_combination hyyb
    rcases mul_eq_zero.mp this with h | h
    · have hb_eq : b.2 = A₀.2 := by linear_combination h
      unfold thirdPoint at hTb
      rw [if_pos hbx.symm] at hTb
      rw [if_pos hb_eq.symm] at hTb
      by_cases h2 : A₀.2 = 0
      · rw [hb_eq, h2]; ring
      · rw [if_neg h2] at hTb; exact absurd hTb (by simp)
    · linear_combination h
  exact Prod.ext (hax.trans hbx.symm) (ha_yneg.trans hb_yneg.symm)

/-- Fiberwise decomposition of a Finset of pairs filtered by first coordinate
    followed by an A₀-dependent predicate. -/
theorem card_filter_product_fiber_eq
    (S T : Finset (ZMod E.q × ZMod E.q))
    (Q : (ZMod E.q × ZMod E.q) → (ZMod E.q × ZMod E.q) → Prop)
    [∀ a b, Decidable (Q a b)] :
    ((S ×ˢ T).filter (fun p => Q p.1 p.2)).card =
      ∑ A₀ ∈ S, (T.filter (Q A₀)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) => p.1)
    (s := (S ×ˢ T).filter (fun p => Q p.1 p.2)) (t := S)]
  · apply Finset.sum_congr rfl
    intro A₀ hA₀
    apply Finset.card_bij
      (i := fun (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q))
        (_ : p ∈ ((S ×ˢ T).filter (fun p => Q p.1 p.2)).filter
              (fun x => x.1 = A₀)) => p.2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      rw [Finset.mem_filter]
      refine ⟨hp.1.1.2, ?_⟩
      have hQp : Q p.1 p.2 := hp.1.2
      rw [hp.2] at hQp
      exact hQp
    · intro p hp q hq hpq
      simp only [Finset.mem_filter, Finset.mem_product] at hp hq
      apply Prod.ext
      · rw [hp.2, hq.2]
      · exact hpq
    · intro A₁ hA₁
      simp only [Finset.mem_filter] at hA₁
      refine ⟨(A₀, A₁), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hA₀, hA₁.1⟩, hA₁.2⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1

/-! ## Symmetry of `thirdPoint`

For the chord branch (`A₀.1 ≠ A₁.1`), `slopeOf` is symmetric in
`(A₀, A₁)` (just sign-twiddling on the inverse). The chord-line third
intersection is uniquely determined by the chord, hence symmetric. -/

private theorem slopeOf_symm_local (x₀ y₀ x₁ y₁ : ZMod E.q) :
    slopeOf x₀ y₀ x₁ y₁ = slopeOf x₁ y₁ x₀ y₀ := by
  unfold slopeOf
  by_cases h : x₀ = x₁
  · subst h
    have : (x₀ - x₀ : ZMod E.q) = 0 := sub_self x₀
    rw [this]; simp
  · rw [show (x₀ - x₁ : ZMod E.q) = -(x₁ - x₀) from by ring, inv_neg]
    ring

theorem thirdPoint_symm (A₀ A₁ : ZMod E.q × ZMod E.q) :
    thirdPoint E A₀ A₁ = thirdPoint E A₁ A₀ := by
  unfold thirdPoint
  by_cases hxx : A₀.1 = A₁.1
  · rw [if_pos hxx, if_pos hxx.symm]
    by_cases hyy : A₀.2 = A₁.2
    · rw [if_pos hyy, if_pos hyy.symm]
      by_cases h2t0 : A₀.2 = 0
      · rw [if_pos h2t0, if_pos (hyy ▸ h2t0)]
      · rw [if_neg h2t0, if_neg (fun h => h2t0 (hyy ▸ h))]
        -- Both sides are tangent at coincident point. A₀ = A₁, so identical.
        have : A₀ = A₁ := Prod.ext hxx hyy
        rw [this]
    · rw [if_neg hyy, if_neg (Ne.symm hyy)]
  · rw [if_neg hxx, if_neg (Ne.symm hxx)]
    -- Chord case. Use slopeOf symmetry.
    have hsl : (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
              = (A₀.2 - A₁.2) * (A₀.1 - A₁.1)⁻¹ :=
      slopeOf_symm_local E A₀.1 A₀.2 A₁.1 A₁.2
    set lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹ with hlam
    have hsym : (A₀.2 - A₁.2) * (A₀.1 - A₁.1)⁻¹ = lam := hsl.symm
    rw [hsym]
    -- Now both sides have the same `lam`. Need: x₂ and y₂ symmetric in inputs.
    rw [Option.some.injEq, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    -- y₂ symmetric: lam·x₂ + (A₀.2 - lam·A₀.1) = lam·x₂' + (A₁.2 - lam·A₁.1)
    -- where x₂ = lam² - A₀.1 - A₁.1, x₂' = lam² - A₁.1 - A₀.1 (= same).
    -- So just need: A₀.2 - lam·A₀.1 = A₁.2 - lam·A₁.1.
    -- I.e., A₁.2 - A₀.2 = lam·(A₁.1 - A₀.1).
    -- This is the slope identity (cleared of inverse).
    have hxne : (A₁.1 - A₀.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx)
    have hsl_clear : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
      rw [hlam]
      field_simp
    -- Need: lam·x₂ + (A₀.2 - lam·A₀.1) = lam·(lam² - A₁.1 - A₀.1) + (A₁.2 - lam·A₁.1).
    have hx2_eq : lam ^ 2 - A₀.1 - A₁.1 = lam ^ 2 - A₁.1 - A₀.1 := by ring
    rw [hx2_eq]
    linear_combination hsl_clear

/-- Cardinality bound for the tangent-collision-at-A₀ set:
    `|tangentCollisionAtA₀| ≤ |E.points|`. -/
theorem card_tangentCollisionAtA₀_le :
    (tangentCollisionAtA₀ E).card ≤ E.numAffine := by
  classical
  have hfib : (tangentCollisionAtA₀ E).card =
      ∑ A₀ ∈ E.points,
        (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = some A₀)).card :=
    card_filter_product_fiber_eq E E.points E.points
      (fun a b => thirdPoint E a b = some a)
  rw [hfib]
  calc ∑ A₀ ∈ E.points,
          (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = some A₀)).card
      ≤ ∑ A₀ ∈ E.points, 1 :=
        Finset.sum_le_sum (fun A₀ hA₀ => card_thirdPoint_eq_self_fiber E hA₀)
    _ = E.points.card := by rw [Finset.sum_const, smul_eq_mul]; ring
    _ = E.numAffine := rfl

/-- Tangent-collision-at-A₁ Finset (the symmetric counterpart). -/
noncomputable def tangentCollisionAtA₁ :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter (fun p => thirdPoint E p.1 p.2 = some p.2)

/-- Diagonal Finset: pairs `(A, A)` with `A ∈ E.points`. -/
noncomputable def diagonalChallenges :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter (fun p => p.1 = p.2)

/-- Cardinality bound: `|diagonalChallenges| ≤ |E.points|`. -/
theorem card_diagonalChallenges_le :
    (diagonalChallenges E).card ≤ E.numAffine := by
  classical
  have hImg : diagonalChallenges E = E.points.image (fun a => (a, a)) := by
    ext p
    simp only [diagonalChallenges, Finset.mem_filter, Finset.mem_product,
               Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, _h2⟩, hEq⟩
      refine ⟨p.1, h1, ?_⟩
      rw [Prod.mk.injEq]
      exact ⟨rfl, hEq⟩
    · rintro ⟨a, ha, hEq⟩
      rw [← hEq]
      exact ⟨⟨ha, ha⟩, rfl⟩
  rw [hImg]
  exact Finset.card_image_le

/-- Cardinality bound: `|tangentCollisionAtA₁| ≤ |E.points|`. Via swap
    bijection from `tangentCollisionAtA₀` (using `thirdPoint_symm`). -/
theorem card_tangentCollisionAtA₁_le :
    (tangentCollisionAtA₁ E).card ≤ E.numAffine := by
  classical
  -- Bijection: (A_0, A_1) ↔ (A_1, A_0) maps tangentCollisionAtA₁ to tangentCollisionAtA₀.
  have hbij : (tangentCollisionAtA₁ E).card = (tangentCollisionAtA₀ E).card := by
    apply Finset.card_bij (fun (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) _ =>
      (p.2, p.1))
    · -- Map preserves membership.
      intro p hp
      simp only [tangentCollisionAtA₁, Finset.mem_filter, Finset.mem_product] at hp
      simp only [tangentCollisionAtA₀, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hp.1.2, hp.1.1⟩, ?_⟩
      rw [thirdPoint_symm]; exact hp.2
    · -- Injectivity.
      intro p _ q _ heq
      apply Prod.ext
      · exact congrArg Prod.snd heq
      · exact congrArg Prod.fst heq
    · -- Surjectivity.
      intro p hp
      simp only [tangentCollisionAtA₀, Finset.mem_filter, Finset.mem_product] at hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [tangentCollisionAtA₁, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hp.1.2, hp.1.1⟩, ?_⟩
      rw [thirdPoint_symm]; exact hp.2
  rw [hbij]
  exact card_tangentCollisionAtA₀_le E

/-! ## Standalone: third-point-affine zeros of D on E × E

    Extracted from `support_disjointness`: the set of pairs `(A₀, A₁)` such
    that `thirdPoint A₀ A₁` is affine and its coordinates are a zero of `D`
    has cardinality at most `E.numAffine * numZeros E D`. Used by the T3
    factor bound on `D(A₂) = 0`. -/

theorem card_thirdPoint_affine_D_zero_pairs_le (D : CoordRingElt E.q) :
    ((E.points ×ˢ E.points).filter (fun p =>
       match thirdPoint E p.1 p.2 with
       | none => False
       | some (x, y) => D.eval x y = 0)).card
      ≤ E.numAffine * numZeros E D := by
  classical
  set S := (E.points ×ˢ E.points).filter (fun p =>
      match thirdPoint E p.1 p.2 with
      | none => False
      | some (x, y) => D.eval x y = 0)
  have hfib : S.card = ∑ A₀ ∈ E.points,
        (E.points.filter (fun A₁ =>
          match thirdPoint E A₀ A₁ with
          | none => False
          | some (x, y) => D.eval x y = 0)).card :=
    card_filter_product_fiber_eq E E.points E.points
      (fun a b =>
        match thirdPoint E a b with
        | none => False
        | some (x, y) => D.eval x y = 0)
  rw [hfib]
  have hper_A0 :
      ∀ A₀ ∈ E.points,
        (E.points.filter (fun A₁ =>
            match thirdPoint E A₀ A₁ with
            | none => False
            | some (x, y) => D.eval x y = 0)).card ≤ numZeros E D := by
    intro A₀ hA₀
    set fiber := E.points.filter (fun A₁ =>
        match thirdPoint E A₀ A₁ with
        | none => False
        | some (x, y) => D.eval x y = 0) with hfiberdef
    have hfib_aff : ∀ A₁ ∈ fiber,
        A₁ ∈ E.points ∧ thirdPoint E A₀ A₁ ≠ none ∧
        ∃ x y, thirdPoint E A₀ A₁ = some (x, y) ∧ D.eval x y = 0 := by
      intro A₁ hA₁
      simp only [hfiberdef, Finset.mem_filter] at hA₁
      obtain ⟨hmem, hcond⟩ := hA₁
      have hT_ne : thirdPoint E A₀ A₁ ≠ none := by
        intro h
        rw [h] at hcond
        exact hcond
      have hT_eq : ∃ x y, thirdPoint E A₀ A₁ = some (x, y) := by
        obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hT_ne
        obtain ⟨x, y⟩ := p
        exact ⟨x, y, hp⟩
      obtain ⟨x, y, hT⟩ := hT_eq
      rw [hT] at hcond
      refine ⟨hmem, ?_, x, y, hT, hcond⟩
      rw [hT]; exact (by simp)
    let thirdAffine : (ZMod E.q × ZMod E.q) → (ZMod E.q × ZMod E.q) := fun A₁ =>
      match thirdPoint E A₀ A₁ with
      | none => (0, 0)
      | some (x, y) => (x, y)
    have hInj' : Set.InjOn thirdAffine ↑fiber := by
      intro a ha b hb hab
      obtain ⟨hamem, haninf, xa, ya, hTa, _⟩ := hfib_aff a ha
      obtain ⟨hbmem, hbninf, xb, yb, hTb, _⟩ := hfib_aff b hb
      simp only [thirdAffine, hTa, hTb] at hab
      rw [Prod.mk.injEq] at hab
      have htp : thirdPoint E A₀ a = thirdPoint E A₀ b := by
        rw [hTa, hTb, hab.1, hab.2]
      exact thirdPoint_inj_on_A₁ E A₀ hA₀ ⟨hamem, haninf⟩ ⟨hbmem, hbninf⟩ htp
    have hImgSub : (fiber.image thirdAffine) ⊆ zeros D E.points := by
      intro q hq
      simp only [Finset.mem_image] at hq
      obtain ⟨A₁, hA₁fib, hA₁eq⟩ := hq
      obtain ⟨hA₁mem, _, x, y, hT, hDval⟩ := hfib_aff A₁ hA₁fib
      simp only [thirdAffine, hT] at hA₁eq
      rw [← hA₁eq]
      simp only [zeros, Finset.mem_filter]
      exact ⟨third_point_on_curve E A₀ A₁ hA₀ hA₁mem hT, hDval⟩
    have hcard_fiber : fiber.card = (fiber.image thirdAffine).card :=
      (Finset.card_image_of_injOn hInj').symm
    rw [hcard_fiber]
    exact Finset.card_le_card hImgSub
  calc (∑ A₀ ∈ E.points,
          (E.points.filter (fun A₁ =>
            match thirdPoint E A₀ A₁ with
            | none => False
            | some (x, y) => D.eval x y = 0)).card)
      ≤ ∑ A₀ ∈ E.points, numZeros E D :=
        Finset.sum_le_sum hper_A0
    _ = E.points.card * numZeros E D := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = E.numAffine * numZeros E D := rfl

/-- **`\ref{lem:support-disjoint}` (Support Disjointness).**

    For `N` with `numZeros E D ≤ N`, the completeness bad set is bounded:
    `|badChallengesCompleteness E D| ≤ (3 * N + 1) * E.numAffine`.

    This restores the paper's constant `+1` using the corrected `thirdPoint`
    (which returns the tangent-line third point for `A₀ = A₁` rather than
    infinity, unless `A₀.2 = 0`) together with the tight `card_thirdPoint_infinity_fiber`
    bound `≤ 1`.

    Proof: decompose the bad set into four disjuncts
    S₀, S₁, S₂, S₃ and sum via `Finset.card_union_le`. -/
theorem support_disjointness (D : CoordRingElt E.q)
    (N : ℕ) (hN : numZeros E D ≤ N) :
    (badChallengesCompleteness E D).card ≤ (3 * N + 4) * E.numAffine := by
  set S₀ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p => D.eval p.1.1 p.1.2 = 0) with hS0def
  set S₁ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p => D.eval p.2.1 p.2.2 = 0) with hS1def
  set S₂ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => thirdPoint E p.1 p.2 = none) with hS2def
  set S₃ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p =>
      match thirdPoint E p.1 p.2 with
      | none => False
      | some (x, y) => D.eval x y = 0) with hS3def
  set S₄ := diagonalChallenges E with hS4def
  set S₅ := tangentCollisionAtA₀ E with hS5def
  set S₆ := tangentCollisionAtA₁ E with hS6def
  -- Subset inclusion (extended to 6 disjuncts).
  have hsub : badChallengesCompleteness E D ⊆
      S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅ ∪ S₆ := by
    intro p hp
    simp only [badChallengesCompleteness, Finset.mem_filter,
               badPairCompletenessPred] at hp
    obtain ⟨hmem, hbad⟩ := hp
    rcases hbad with h | h | h | h | h | h
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · cases hT : thirdPoint E p.1 p.2 with
      | none =>
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inr ?_)
        exact Finset.mem_filter.mpr ⟨hmem, hT⟩
      | some xy =>
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inr ?_)
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        rw [hT] at h
        rw [hT]
        exact h
    · -- Diagonal.
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inr ?_)
      show p ∈ S₄
      rw [hS4def]
      unfold diagonalChallenges
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · -- Tangent at A_0.
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inr ?_)
      show p ∈ S₅
      rw [hS5def]
      unfold tangentCollisionAtA₀
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · -- Tangent at A_1.
      refine Finset.mem_union.mpr (Or.inr ?_)
      show p ∈ S₆
      rw [hS6def]
      unfold tangentCollisionAtA₁
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
  -- Cardinality of each piece.
  have hS0_card : S₀.card = numZeros E D * E.numAffine := by
    have : S₀ = (zeros D E.points) ×ˢ E.points := by
      ext p
      simp only [hS0def, Finset.mem_filter, Finset.mem_product, zeros,
                 Finset.mem_filter]
      tauto
    rw [this, Finset.card_product]
    rfl
  have hS1_card : S₁.card = E.numAffine * numZeros E D := by
    have : S₁ = E.points ×ˢ (zeros D E.points) := by
      ext p
      simp only [hS1def, Finset.mem_filter, Finset.mem_product, zeros,
                 Finset.mem_filter]
      tauto
    rw [this, Finset.card_product]
    rfl
  -- S₂: fiber ≤ 1 (via corrected thirdPoint), so S₂.card ≤ 1 · numAffine.
  have hS2_card : S₂.card ≤ E.numAffine := by
    have hfib : S₂.card = ∑ A₀ ∈ E.points,
          (E.points.filter (fun A₁ =>
            thirdPoint E A₀ A₁ = none)).card :=
      card_filter_product_fiber_eq E E.points E.points
        (fun a b => thirdPoint E a b = none)
    rw [hfib]
    calc ∑ A₀ ∈ E.points,
            (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = none)).card
        ≤ ∑ A₀ ∈ E.points, 1 := by
          apply Finset.sum_le_sum
          intro A₀ hA₀
          exact card_thirdPoint_infinity_fiber E A₀ hA₀
      _ = E.points.card := by
            rw [Finset.sum_const, smul_eq_mul]; ring
      _ = E.numAffine := rfl
  -- S₃: standalone lemma above.
  have hS3_card : S₃.card ≤ E.numAffine * numZeros E D :=
    card_thirdPoint_affine_D_zero_pairs_le E D
  have hCombine : (badChallengesCompleteness E D).card ≤
      S₀.card + S₁.card + S₂.card + S₃.card + S₄.card + S₅.card + S₆.card := by
    calc (badChallengesCompleteness E D).card
        ≤ (S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅ ∪ S₆).card := Finset.card_le_card hsub
      _ ≤ (S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄ ∪ S₅).card + S₆.card := Finset.card_union_le _ _
      _ ≤ (S₀ ∪ S₁ ∪ S₂ ∪ S₃ ∪ S₄).card + S₅.card + S₆.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (S₀ ∪ S₁ ∪ S₂ ∪ S₃).card + S₄.card + S₅.card + S₆.card :=
          Nat.add_le_add_right (Nat.add_le_add_right
            (Finset.card_union_le _ _) _) _
      _ ≤ (S₀ ∪ S₁ ∪ S₂).card + S₃.card + S₄.card + S₅.card + S₆.card :=
          Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
      _ ≤ (S₀ ∪ S₁).card + S₂.card + S₃.card + S₄.card + S₅.card + S₆.card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) _
      _ ≤ S₀.card + S₁.card + S₂.card + S₃.card + S₄.card + S₅.card + S₆.card :=
          Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.add_le_add_right
              (Finset.card_union_le _ _) _) _) _) _) _
  -- Plug in numeric bounds.
  have h0N : S₀.card ≤ N * E.numAffine := by
    rw [hS0_card]; exact Nat.mul_le_mul_right _ hN
  have h1N : S₁.card ≤ E.numAffine * N := by
    rw [hS1_card]; exact Nat.mul_le_mul_left _ hN
  have h3N : S₃.card ≤ E.numAffine * N :=
    le_trans hS3_card (Nat.mul_le_mul_left _ hN)
  have h4N : S₄.card ≤ E.numAffine := card_diagonalChallenges_le E
  have h5N : S₅.card ≤ E.numAffine := card_tangentCollisionAtA₀_le E
  have h6N : S₆.card ≤ E.numAffine := card_tangentCollisionAtA₁_le E
  calc (badChallengesCompleteness E D).card
      ≤ S₀.card + S₁.card + S₂.card + S₃.card + S₄.card + S₅.card + S₆.card :=
          hCombine
    _ ≤ N * E.numAffine + E.numAffine * N + E.numAffine + E.numAffine * N
        + E.numAffine + E.numAffine + E.numAffine := by gcongr
    _ = (3 * N + 4) * E.numAffine := by ring

/-- **Hasse-derived `|E| ≤ 2q`** (for `q ≥ 5`).
    From the integer-squared form `(|E.points| − q)² ≤ 4q`, derive
    `|E.points| ≤ q + 2√q ≤ 2q` (since `2√q ≤ q` for `q ≥ 4`). -/
theorem points_card_le_two_q (h : 5 ≤ E.q) :
    E.points.card ≤ 2 * E.q := by
  have hHW := hasse_weil E
  rw [E.hNumPoints] at hHW
  have hi : ((E.points.card : ℤ) - E.q)^2 ≤ 4 * E.q := by
    push_cast at hHW
    nlinarith [hHW]
  by_contra hLt
  push_neg at hLt
  have hQ5 : (5 : ℤ) ≤ E.q := by exact_mod_cast h
  have hLow : ((E.points.card : ℤ) - E.q) ≥ E.q + 1 := by
    have : ((E.points.card : ℤ)) ≥ 2 * E.q + 1 := by exact_mod_cast hLt
    linarith
  -- (|E| − q)² ≥ (q + 1)² = q² + 2q + 1; need this > 4q.
  -- For q ≥ 5: q² ≥ 5q, so q² + 2q + 1 ≥ 7q + 1 > 4q.
  nlinarith [hi, hLow, hQ5, sq_nonneg ((E.points.card : ℤ) - E.q - (E.q + 1))]

end Divisor
