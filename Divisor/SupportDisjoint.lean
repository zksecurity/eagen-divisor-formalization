/-
  Divisor/SupportDisjoint.lean

  Lemma 2 (Support Disjointness): Bassa 2025, Lemma 5.

  For D in F_q[E] with N zeros, and random A0, A1 in E(F_q) \ {O},
  A2 = -(A0 + A1):

    Pr[supp(D) intersects {A0, A1, A2}] <= 3*(N+1) / #E(F_q)

  Proof: union bound over three events.
-/
import Divisor.Defs
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

/-- Predicate form of the completeness bad event for a given pair. -/
noncomputable def badPairCompletenessPred (D : CoordRingElt E.q)
    (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) : Prop :=
  D.eval p.1.1 p.1.2 = 0
  ∨ D.eval p.2.1 p.2.2 = 0
  ∨ (match thirdPoint E p.1 p.2 with
      | ECPoint.infinity => True
      | ECPoint.affine x y => D.eval x y = 0)

/-- The completeness bad set: pairs `(A₀, A₁)` where
    `D(A₀) = 0`, `D(A₁) = 0`, `A₂ = ∞`, or `A₂ = (x, y)` with `D(x, y) = 0`. -/
noncomputable def badChallengesCompleteness (D : CoordRingElt E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter (badPairCompletenessPred E D)

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

/-! ## Main result: Lemma 2 (structural)

The full Lemma 2 requires the group law to handle A2.
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
    (hT : thirdPoint E A₀ A₁ = ECPoint.affine x y) :
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
          injection hT with hx_eq hy_eq
          exact ⟨hx_eq.symm, hy_eq.symm⟩
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
      injection hT with hx_eq hy_eq
      exact ⟨hx_eq.symm, hy_eq.symm⟩
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

/-! ## Injectivity of A₁ ↦ thirdPoint E A₀ A₁ (group-law cancellation)

Classical EC fact: for each A₀ on E, the map `A₁ ↦ thirdPoint E A₀ A₁`
is injective on affine A₁ for which the third point is affine (i.e. not ∞).
Equivalent to: if `A₀ + A₁ = A₀ + A₁'` (group law), then `A₁ = A₁'`.

Proved directly from the axiomatized group-law cancellation on `ECPoint`,
via the identity `thirdPoint = -(A₀ + A₁)` (`thirdPoint_eq_neg_add`). -/
theorem thirdPoint_inj_on_A₁ (A₀ : ZMod E.q × ZMod E.q) (hA₀ : A₀ ∈ E.points) :
    Set.InjOn (fun A₁ => thirdPoint E A₀ A₁)
      {A₁ | A₁ ∈ E.points ∧ thirdPoint E A₀ A₁ ≠ ECPoint.infinity} := by
  intro a ha b hb hab
  obtain ⟨_, ha_inf⟩ := ha
  obtain ⟨_, hb_inf⟩ := hb
  -- Beta-reduce and transport to the group law.
  simp only at hab
  rw [thirdPoint_eq_neg_add E A₀ a ha_inf,
      thirdPoint_eq_neg_add E A₀ b hb_inf] at hab
  have hadd : ECPoint.add E (.affine A₀.1 A₀.2) (.affine a.1 a.2)
            = ECPoint.add E (.affine A₀.1 A₀.2) (.affine b.1 b.2) :=
    ECPoint.neg_inj hab
  have hpt : (.affine a.1 a.2 : ECPoint E.q) = .affine b.1 b.2 :=
    ECPoint.add_left_cancel E hadd
  have h12 : a.1 = b.1 ∧ a.2 = b.2 := by
    rw [ECPoint.affine.injEq] at hpt
    exact hpt
  exact Prod.ext h12.1 h12.2

/-! ## Auxiliary: fiberwise decomposition -/

/-- For each `A₀ ∈ E.points`, the number of `A₁ ∈ E.points` with
    `thirdPoint E A₀ A₁ = ∞` is at most 1.

    With the corrected `thirdPoint`, infinity occurs only when the chord is
    vertical (`A₁ = -A₀`) or the tangent is vertical (`A₁ = A₀` and
    `A₀.2 = 0`, i.e. 2-torsion). In the 2-torsion case `-A₀ = A₀`, so
    these are the same element, yielding at most one A₁. -/
theorem card_thirdPoint_infinity_fiber (A₀ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = ECPoint.infinity)).card ≤ 1 := by
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

/-! ## Standalone: third-point-affine zeros of D on E × E

    Extracted from `support_disjointness`: the set of pairs `(A₀, A₁)` such
    that `thirdPoint A₀ A₁` is affine and its coordinates are a zero of `D`
    has cardinality at most `E.numAffine * numZeros E D`. Used by the T3
    factor bound on `D(A₂) = 0`. -/

theorem card_thirdPoint_affine_D_zero_pairs_le (D : CoordRingElt E.q) :
    ((E.points ×ˢ E.points).filter (fun p =>
       match thirdPoint E p.1 p.2 with
       | ECPoint.infinity => False
       | ECPoint.affine x y => D.eval x y = 0)).card
      ≤ E.numAffine * numZeros E D := by
  classical
  set S := (E.points ×ˢ E.points).filter (fun p =>
      match thirdPoint E p.1 p.2 with
      | ECPoint.infinity => False
      | ECPoint.affine x y => D.eval x y = 0)
  have hfib : S.card = ∑ A₀ ∈ E.points,
        (E.points.filter (fun A₁ =>
          match thirdPoint E A₀ A₁ with
          | ECPoint.infinity => False
          | ECPoint.affine x y => D.eval x y = 0)).card :=
    card_filter_product_fiber_eq E E.points E.points
      (fun a b =>
        match thirdPoint E a b with
        | ECPoint.infinity => False
        | ECPoint.affine x y => D.eval x y = 0)
  rw [hfib]
  have hper_A0 :
      ∀ A₀ ∈ E.points,
        (E.points.filter (fun A₁ =>
            match thirdPoint E A₀ A₁ with
            | ECPoint.infinity => False
            | ECPoint.affine x y => D.eval x y = 0)).card ≤ numZeros E D := by
    intro A₀ hA₀
    set fiber := E.points.filter (fun A₁ =>
        match thirdPoint E A₀ A₁ with
        | ECPoint.infinity => False
        | ECPoint.affine x y => D.eval x y = 0) with hfiberdef
    have hfib_aff : ∀ A₁ ∈ fiber,
        A₁ ∈ E.points ∧ thirdPoint E A₀ A₁ ≠ ECPoint.infinity ∧
        ∃ x y, thirdPoint E A₀ A₁ = ECPoint.affine x y ∧ D.eval x y = 0 := by
      intro A₁ hA₁
      simp only [hfiberdef, Finset.mem_filter] at hA₁
      obtain ⟨hmem, hcond⟩ := hA₁
      have hT_eq : ∃ x y, thirdPoint E A₀ A₁ = ECPoint.affine x y := by
        cases hT : thirdPoint E A₀ A₁ with
        | infinity =>
          rw [hT] at hcond
          exact absurd hcond (by simp)
        | affine x y => exact ⟨x, y, rfl⟩
      obtain ⟨x, y, hT⟩ := hT_eq
      rw [hT] at hcond
      refine ⟨hmem, ?_, x, y, hT, hcond⟩
      rw [hT]; exact (by simp)
    let thirdAffine : (ZMod E.q × ZMod E.q) → (ZMod E.q × ZMod E.q) := fun A₁ =>
      match thirdPoint E A₀ A₁ with
      | ECPoint.infinity => (0, 0)
      | ECPoint.affine x y => (x, y)
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
            | ECPoint.infinity => False
            | ECPoint.affine x y => D.eval x y = 0)).card)
      ≤ ∑ A₀ ∈ E.points, numZeros E D :=
        Finset.sum_le_sum hper_A0
    _ = E.points.card * numZeros E D := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = E.numAffine * numZeros E D := rfl

/-- **Lemma 2 (Support Disjointness).**

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
    (badChallengesCompleteness E D).card ≤ (3 * N + 1) * E.numAffine := by
  set S₀ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p => D.eval p.1.1 p.1.2 = 0) with hS0def
  set S₁ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p => D.eval p.2.1 p.2.2 = 0) with hS1def
  set S₂ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => thirdPoint E p.1 p.2 = ECPoint.infinity) with hS2def
  set S₃ : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter (fun p =>
      match thirdPoint E p.1 p.2 with
      | ECPoint.infinity => False
      | ECPoint.affine x y => D.eval x y = 0) with hS3def
  -- Subset inclusion.
  have hsub : badChallengesCompleteness E D ⊆ S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
    intro p hp
    simp only [badChallengesCompleteness, Finset.mem_filter,
               badPairCompletenessPred] at hp
    obtain ⟨hmem, hbad⟩ := hp
    rcases hbad with h | h | h
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_filter.mpr ⟨hmem, h⟩
    · cases hT : thirdPoint E p.1 p.2 with
      | infinity =>
        refine Finset.mem_union.mpr (Or.inl ?_)
        refine Finset.mem_union.mpr (Or.inr ?_)
        exact Finset.mem_filter.mpr ⟨hmem, hT⟩
      | affine x y =>
        refine Finset.mem_union.mpr (Or.inr ?_)
        refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        rw [hT] at h
        rw [hT]
        exact h
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
            thirdPoint E A₀ A₁ = ECPoint.infinity)).card :=
      card_filter_product_fiber_eq E E.points E.points
        (fun a b => thirdPoint E a b = ECPoint.infinity)
    rw [hfib]
    calc ∑ A₀ ∈ E.points,
            (E.points.filter (fun A₁ => thirdPoint E A₀ A₁ = ECPoint.infinity)).card
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
      S₀.card + S₁.card + S₂.card + S₃.card := by
    calc (badChallengesCompleteness E D).card
        ≤ (S₀ ∪ S₁ ∪ S₂ ∪ S₃).card := Finset.card_le_card hsub
      _ ≤ (S₀ ∪ S₁ ∪ S₂).card + S₃.card := Finset.card_union_le _ _
      _ ≤ (S₀ ∪ S₁).card + S₂.card + S₃.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ S₀.card + S₁.card + S₂.card + S₃.card :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  -- Plug in numeric bounds.
  have h0N : S₀.card ≤ N * E.numAffine := by
    rw [hS0_card]; exact Nat.mul_le_mul_right _ hN
  have h1N : S₁.card ≤ E.numAffine * N := by
    rw [hS1_card]; exact Nat.mul_le_mul_left _ hN
  have h3N : S₃.card ≤ E.numAffine * N :=
    le_trans hS3_card (Nat.mul_le_mul_left _ hN)
  calc (badChallengesCompleteness E D).card
      ≤ S₀.card + S₁.card + S₂.card + S₃.card := hCombine
    _ ≤ N * E.numAffine + E.numAffine * N + E.numAffine + E.numAffine * N := by
        gcongr
    _ = (3 * N + 1) * E.numAffine := by ring

end Divisor
