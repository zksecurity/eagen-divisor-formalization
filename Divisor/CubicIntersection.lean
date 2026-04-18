/-
  Divisor/CubicIntersection.lean

  Step 9' of the Lean remediation plan: bound the number of zeros of a
  bivariate polynomial on the F_q-rational points of an elliptic curve.
-/
import Divisor.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The curve polynomial `X³ + A·X + B` -/

noncomputable def curveX : (ZMod E.q)[X] :=
  X ^ 3 + C E.curveA * X + C E.curveB

theorem curveX_natDegree_le_three : (curveX E).natDegree ≤ 3 := by
  unfold curveX
  refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C _).le.trans (by omega)))
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_X_pow 3).le
  · refine (natDegree_C_mul_le _ _).trans ?_
    exact natDegree_X_le.trans (by omega)

/-! ## The curve equation as a polynomial in Y over F_q[X] -/

/-- `Y² - (X³ + A·X + B)` viewed as an element of `(ZMod E.q)[X][Y]`. -/
noncomputable def curveEqPoly : (ZMod E.q)[X][X] :=
  X ^ 2 - C (curveX E)

theorem curveEqPoly_natDegree_eq : (curveEqPoly E).natDegree = 2 := by
  unfold curveEqPoly
  rw [show (X ^ 2 - C (curveX E) : (ZMod E.q)[X][X]) =
         X ^ 2 + (- C (curveX E)) by ring]
  refine natDegree_add_eq_left_of_natDegree_lt ?_ |>.trans (natDegree_X_pow 2)
  rw [natDegree_X_pow, natDegree_neg, natDegree_C]
  omega

theorem curveEqPoly_leadingCoeff : (curveEqPoly E).leadingCoeff = 1 := by
  rw [leadingCoeff, curveEqPoly_natDegree_eq]
  unfold curveEqPoly
  simp [coeff_sub, coeff_X_pow, coeff_C]

theorem curveEqPoly_monic : (curveEqPoly E).Monic :=
  curveEqPoly_leadingCoeff E

theorem curveEqPoly_ne_one : curveEqPoly E ≠ 1 := by
  intro h
  have := curveEqPoly_natDegree_eq E
  rw [h, natDegree_one] at this
  omega

/-! ## Evaluation at a curve point -/

/-- Evaluate `f : R[X][Y]` at `(x, y) : R × R`. -/
noncomputable def bivEval {R : Type*} [CommRing R]
    (f : R[X][X]) (p : R × R) : R :=
  (f.eval (C p.2)).eval p.1

theorem curveEqPoly_eval_zero_on_E {p : ZMod E.q × ZMod E.q} (hp : p ∈ E.points) :
    bivEval (curveEqPoly E) p = 0 := by
  unfold bivEval curveEqPoly curveX
  have hcurve := E.hOnCurve p hp
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_add, eval_mul]
  linear_combination hcurve

/-- Reduction-mod-curve identity: on E, `f` evaluates to the same value
    as its remainder mod the curve equation. -/
theorem bivEval_eq_modByMonic_on_E (f : (ZMod E.q)[X][X])
    {p : ZMod E.q × ZMod E.q} (hp : p ∈ E.points) :
    bivEval f p = bivEval (f %ₘ curveEqPoly E) p := by
  have hrem := modByMonic_add_div f (curveEqPoly_monic E)
  -- f = (f %ₘ curveEqPoly E) + (curveEqPoly E) * (f /ₘ curveEqPoly E)
  have hdecomp : f = f %ₘ curveEqPoly E + curveEqPoly E * (f /ₘ curveEqPoly E) :=
    hrem.symm
  have hcurve : ((curveEqPoly E).eval (C p.2)).eval p.1 = 0 :=
    curveEqPoly_eval_zero_on_E E hp
  unfold bivEval
  conv_lhs => rw [hdecomp]
  simp only [eval_add, eval_mul]
  rw [hcurve, zero_mul, add_zero]

theorem modByMonic_curveEqPoly_natDegree_lt (f : (ZMod E.q)[X][X]) :
    (f %ₘ curveEqPoly E).natDegree < 2 := by
  have := natDegree_modByMonic_lt f (curveEqPoly_monic E) (curveEqPoly_ne_one E)
  rw [curveEqPoly_natDegree_eq] at this
  exact this

/-! ## Canonical form: `a(X) + b(X)·Y` -/

/-- The `X`-part of `f : R[X][Y]` (coefficient of `Y^0`). -/
noncomputable def xPart (f : (ZMod E.q)[X][X]) : (ZMod E.q)[X] := f.coeff 0

/-- The `Y`-part of `f : R[X][Y]` (coefficient of `Y^1`). -/
noncomputable def yPart (f : (ZMod E.q)[X][X]) : (ZMod E.q)[X] := f.coeff 1

/-- If `f.natDegree < 2`, then `f = C (xPart E f) + C (yPart E f) * X`
    as a polynomial in Y (the outer variable). -/
theorem eq_xPart_add_yPart_mul_X (f : (ZMod E.q)[X][X]) (hf : f.natDegree < 2) :
    f = C (xPart E f) + C (yPart E f) * X := by
  unfold xPart yPart
  ext n
  match n with
  | 0 => simp [coeff_add, coeff_C, coeff_mul_X]
  | 1 => simp [coeff_add, coeff_C, coeff_mul_X]
  | k + 2 =>
      have h1 : f.coeff (k + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : (C (f.coeff 0) + C (f.coeff 1) * X).coeff (k + 2) = 0 := by
        simp [coeff_add, coeff_C, coeff_mul_X]
      rw [h1, h2]

theorem bivEval_canonical_form
    (f : (ZMod E.q)[X][X]) (hf : f.natDegree < 2) (p : ZMod E.q × ZMod E.q) :
    bivEval f p = (xPart E f).eval p.1 + (yPart E f).eval p.1 * p.2 := by
  unfold bivEval
  conv_lhs => rw [eq_xPart_add_yPart_mul_X E f hf]
  simp [eval_add, eval_mul, eval_C, eval_X]

/-! ## The resultant R(X) = a² - b²·curveX -/

/-- Univariate polynomial capturing the zero set projection. -/
noncomputable def resultantX (f : (ZMod E.q)[X][X]) : (ZMod E.q)[X] :=
  (xPart E (f %ₘ curveEqPoly E)) ^ 2 -
  (yPart E (f %ₘ curveEqPoly E)) ^ 2 * curveX E

theorem resultantX_eval_zero
    (f : (ZMod E.q)[X][X])
    {p : ZMod E.q × ZMod E.q} (hp : p ∈ E.points) (hf : bivEval f p = 0) :
    (resultantX E f).eval p.1 = 0 := by
  set g := f %ₘ curveEqPoly E with hgDef
  have hgDeg : g.natDegree < 2 := modByMonic_curveEqPoly_natDegree_lt E f
  have hRed : bivEval g p = 0 := by
    rw [← bivEval_eq_modByMonic_on_E E f hp]; exact hf
  rw [bivEval_canonical_form E g hgDeg] at hRed
  have hCurve : p.2 ^ 2 = p.1 ^ 3 + E.curveA * p.1 + E.curveB :=
    E.hOnCurve p hp
  unfold resultantX curveX
  simp only [eval_sub, eval_pow, eval_mul, eval_add, eval_X, eval_C]
  -- From hRed: xe + ye·y = 0, so xe = -ye·y. Goal: xe² - ye²·(x³+Ax+B) = 0.
  set xe := (xPart E g).eval p.1
  set ye := (yPart E g).eval p.1
  -- hRed: xe + ye * p.2 = 0
  -- hCurve: p.2^2 = p.1^3 + E.curveA * p.1 + E.curveB
  -- Goal: xe^2 - ye^2 * (p.1^3 + E.curveA * p.1 + E.curveB) = 0
  have h1 : xe = -(ye * p.2) := by linear_combination hRed
  have h2 : xe ^ 2 = ye ^ 2 * p.2 ^ 2 := by rw [h1]; ring
  calc xe ^ 2 - ye ^ 2 * (p.1 ^ 3 + E.curveA * p.1 + E.curveB)
      = ye ^ 2 * p.2 ^ 2 - ye ^ 2 * (p.1 ^ 3 + E.curveA * p.1 + E.curveB) := by rw [h2]
    _ = ye ^ 2 * (p.2 ^ 2 - (p.1 ^ 3 + E.curveA * p.1 + E.curveB)) := by ring
    _ = ye ^ 2 * 0 := by rw [sub_eq_zero.mpr hCurve]
    _ = 0 := by ring

/-! ## R is nonzero when the canonical form is nonzero -/

theorem natDegree_curveX_eq : (curveX E).natDegree = 3 := by
  unfold curveX
  rw [show (X ^ 3 + C E.curveA * X + C E.curveB : (ZMod E.q)[X]) =
         X ^ 3 + (C E.curveA * X + C E.curveB) by ring]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 3
  · rw [natDegree_X_pow]
    refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
      exact lt_of_le_of_lt natDegree_X_le (by omega)
    · exact lt_of_le_of_lt (natDegree_C _).le (by omega)

theorem curveX_ne_zero : curveX E ≠ 0 := by
  intro h
  have := natDegree_curveX_eq E
  rw [h, natDegree_zero] at this
  omega

/-- `a² - b²·curveX ≠ 0` when (a, b) is nonzero. Proof by parity: if both
    a, b nonzero, `deg(a²) = 2·deg a` is even while `deg(b²·curve) =
    2·deg b + 3` is odd, so no cancellation. -/
theorem resultantX_aux_ne_zero
    {a b : (ZMod E.q)[X]} (hab : ¬(a = 0 ∧ b = 0)) :
    a ^ 2 - b ^ 2 * curveX E ≠ 0 := by
  intro hR
  have hEq : a ^ 2 = b ^ 2 * curveX E := by
    have := hR; linear_combination this
  by_cases hb : b = 0
  · subst hb
    -- hEq : a^2 = 0^2 * curveX E
    have hEq' : a ^ 2 = 0 := by
      rw [hEq]; ring
    have ha : a = 0 := by
      rcases pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp hEq' with rfl
      rfl
    exact hab ⟨ha, rfl⟩
  · by_cases ha : a = 0
    · rw [ha, pow_two, zero_mul] at hEq
      have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
      exact (mul_ne_zero hb2 (curveX_ne_zero E)) hEq.symm
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    have hb2c : b ^ 2 * curveX E ≠ 0 := mul_ne_zero hb2 (curveX_ne_zero E)
    have hDegA : (a ^ 2).natDegree = 2 * a.natDegree := Polynomial.natDegree_pow a 2
    have hDegBC : (b ^ 2 * curveX E).natDegree = 2 * b.natDegree + 3 := by
      rw [Polynomial.natDegree_mul hb2 (curveX_ne_zero E),
          Polynomial.natDegree_pow, natDegree_curveX_eq]
    have hDegEq : (a ^ 2).natDegree = (b ^ 2 * curveX E).natDegree := by
      rw [hEq]
    rw [hDegA, hDegBC] at hDegEq
    omega

theorem resultantX_ne_zero (f : (ZMod E.q)[X][X])
    (hNonzero : f %ₘ curveEqPoly E ≠ 0) :
    resultantX E f ≠ 0 := by
  unfold resultantX
  apply resultantX_aux_ne_zero E
  intro ⟨ha, hb⟩
  apply hNonzero
  have hg := eq_xPart_add_yPart_mul_X E (f %ₘ curveEqPoly E)
                (modByMonic_curveEqPoly_natDegree_lt E f)
  rw [hg, ha, hb]
  simp

/-! ## The final bound -/

/-- Each `x : ZMod E.q` has at most 2 `y`-values with `(x, y) ∈ E.points`
    (since E is a cubic, `y² = x³+Ax+B` has at most 2 roots in `ZMod E.q`). -/
theorem card_points_with_fst_eq_le (x : ZMod E.q) :
    (E.points.filter (fun p => p.1 = x)).card ≤ 2 := by
  classical
  set c₀ := x ^ 3 + E.curveA * x + E.curveB
  set g : (ZMod E.q)[X] := Polynomial.X ^ 2 - C c₀
  have hg_ne : g ≠ 0 := by
    intro h
    have h2 : g.coeff 2 = 0 := by rw [h]; simp
    simp only [g, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C] at h2
    simp at h2
  have hg_deg : g.natDegree ≤ 2 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp [Polynomial.natDegree_X_pow])
              ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)))
  calc (E.points.filter (fun p => p.1 = x)).card
      ≤ g.roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro P hP
          simp only [Finset.mem_filter] at hP
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hg_ne]
          simp only [Polynomial.IsRoot, g, Polynomial.eval_sub,
                     Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          have := E.hOnCurve P hP.1
          rw [hP.2] at this
          linear_combination this
        · intro ⟨_, _⟩ h1 ⟨_, _⟩ h2 hy
          have hx1 := (Finset.mem_filter.mp h1).2
          have hx2 := (Finset.mem_filter.mp h2).2
          exact Prod.ext (hx1.trans hx2.symm) hy
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ 2 := hg_deg

/-- **Step 9' main theorem (polynomial_zeros_on_cubic)**.

    For a bivariate polynomial `f : (ZMod E.q)[X][Y]` whose remainder
    `f %ₘ curveEqPoly E` is nonzero (i.e., `f` is not a multiple of the
    curve equation), the number of zeros of `f` on `E.points` is at
    most `2 · (resultantX E f).natDegree`. -/
theorem card_zeros_on_E_le
    (f : (ZMod E.q)[X][X])
    (hNonzero : f %ₘ curveEqPoly E ≠ 0) :
    (E.points.filter (fun p => bivEval f p = 0)).card ≤
    2 * (resultantX E f).natDegree := by
  classical
  set R := resultantX E f
  have hRNZ : R ≠ 0 := resultantX_ne_zero E f hNonzero
  set zSet := E.points.filter (fun p => bivEval f p = 0)
  set xProj := zSet.image Prod.fst
  -- x-projection of zSet is contained in roots of R.
  have hxProjSub : xProj ⊆ R.roots.toFinset := by
    intro x hx
    simp only [xProj, zSet, Finset.mem_image, Finset.mem_filter] at hx
    obtain ⟨p, ⟨hp, hfp⟩, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hRNZ]
    exact resultantX_eval_zero E f hp hfp
  -- |xProj| ≤ |roots R| ≤ R.natDegree.
  have hxProj_card : xProj.card ≤ R.natDegree := by
    calc xProj.card
        ≤ R.roots.toFinset.card := Finset.card_le_card hxProjSub
      _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
      _ ≤ R.natDegree := Polynomial.card_roots' R
  -- For each x in xProj, fiber has ≤ 2 elements.
  have hFiber : ∀ x ∈ xProj,
      (zSet.filter (fun p => p.1 = x)).card ≤ 2 := by
    intro x _
    have hSub : zSet.filter (fun p => p.1 = x) ⊆
                E.points.filter (fun p => p.1 = x) := by
      intro p hp
      simp only [zSet, Finset.mem_filter] at hp
      simp only [Finset.mem_filter]
      exact ⟨hp.1.1, hp.2⟩
    calc (zSet.filter (fun p => p.1 = x)).card
        ≤ (E.points.filter (fun p => p.1 = x)).card := Finset.card_le_card hSub
      _ ≤ 2 := card_points_with_fst_eq_le E x
  -- Combine: zSet.card ≤ 2 * xProj.card ≤ 2 * R.natDegree.
  calc zSet.card
      ≤ 2 * xProj.card := Finset.card_le_mul_card_image _ _ hFiber
    _ ≤ 2 * R.natDegree := Nat.mul_le_mul_left 2 hxProj_card

/-! ## Fiber argument (Step 10' infrastructure)

Generic lemma: if a binary function `f : (ZMod E.q × ZMod E.q) →
(ZMod E.q × ZMod E.q) → ZMod E.q` has, for each fixed `A₀`, bounded
zeros on `E.points` (either few zeros OR the fiber is identically
zero), and the "bad" `A₀`'s (where fiber is identically zero) are
also few, then the total zero count on `E.points × E.points` is
bounded. This is the combinatorial skeleton of `logDerivCheckFn_zero_set_bound`. -/

theorem fiber_argument
    (f : (ZMod E.q × ZMod E.q) → (ZMod E.q × ZMod E.q) → ZMod E.q)
    (K : ℕ)
    (hFiber : ∀ A₀ ∈ E.points,
      (E.points.filter (fun A₁ => f A₀ A₁ = 0)).card ≤ K
      ∨ (∀ A₁ ∈ E.points, f A₀ A₁ = 0))
    (hBadA₀ :
      (E.points.filter
        (fun A₀ => ∀ A₁ ∈ E.points, f A₀ A₁ = 0)).card ≤ K) :
    ((E.points ×ˢ E.points).filter (fun p => f p.1 p.2 = 0)).card
      ≤ 2 * K * E.points.card := by
  classical
  set zSet := (E.points ×ˢ E.points).filter (fun p => f p.1 p.2 = 0)
  set badA₀ := E.points.filter (fun A₀ => ∀ A₁ ∈ E.points, f A₀ A₁ = 0)
  -- Split zSet by whether A₀ is in badA₀.
  set zBad := zSet.filter (fun p => p.1 ∈ badA₀)
  set zGood := zSet.filter (fun p => p.1 ∉ badA₀)
  have hSplit : zSet = zBad ∪ zGood := by
    ext p
    simp only [zBad, zGood, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      by_cases hb : p.1 ∈ badA₀
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨h, hb⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hDisjoint : Disjoint zBad zGood := by
    rw [Finset.disjoint_filter]
    intros p _ hmem hnmem
    exact hnmem hmem
  -- Bound |zBad|: zBad ⊆ badA₀ × E.points.
  have hBadCard : zBad.card ≤ K * E.points.card := by
    have hSub : zBad ⊆ badA₀ ×ˢ E.points := by
      intro p hp
      simp only [zBad, zSet, Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_product]
      exact ⟨hp.2, hp.1.1.2⟩
    calc zBad.card
        ≤ (badA₀ ×ˢ E.points).card := Finset.card_le_card hSub
      _ = badA₀.card * E.points.card := Finset.card_product _ _
      _ ≤ K * E.points.card := Nat.mul_le_mul_right _ hBadA₀
  -- Bound |zGood|: fiber over each A₀ ∉ badA₀ has ≤ K zeros.
  have hGoodCard : zGood.card ≤ E.points.card * K := by
    -- Each fiber (fixing p.1 = A₀ ∉ badA₀) has ≤ K elements.
    have hFiberGood : ∀ A₀ ∈ E.points,
        (zGood.filter (fun p => p.1 = A₀)).card ≤ K := by
      intro A₀ hA₀
      by_cases hAbad : A₀ ∈ badA₀
      · -- A₀ ∈ badA₀ but we filter p.1 ∉ badA₀ ⟹ the filter is empty.
        have : (zGood.filter (fun p => p.1 = A₀)) = ∅ := by
          apply Finset.eq_empty_of_forall_not_mem
          intro p hp
          simp only [Finset.mem_filter, zGood, zSet] at hp
          exact hp.1.2 (hp.2 ▸ hAbad)
        rw [this]
        simp
      · -- A₀ ∉ badA₀. Use hFiber.
        have := hFiber A₀ hA₀
        rcases this with hle | hall
        · calc (zGood.filter (fun p => p.1 = A₀)).card
              ≤ (E.points.filter (fun A₁ => f A₀ A₁ = 0)).card := by
                apply Finset.card_le_card_of_injOn Prod.snd
                · intro p hp
                  simp only [Finset.mem_filter, zGood, zSet, Finset.mem_product] at hp
                  simp only [Finset.mem_filter]
                  obtain ⟨⟨⟨⟨_, hp2⟩, hpf⟩, _⟩, hpeq⟩ := hp
                  exact ⟨hp2, hpeq ▸ hpf⟩
                · intro p hp q hq heq
                  have hp' : p ∈ zGood.filter (fun r => r.1 = A₀) := hp
                  have hq' : q ∈ zGood.filter (fun r => r.1 = A₀) := hq
                  have hpe : p.1 = A₀ := (Finset.mem_filter.mp hp').2
                  have hqe : q.1 = A₀ := (Finset.mem_filter.mp hq').2
                  exact Prod.ext (hpe.trans hqe.symm) heq
            _ ≤ K := hle
        · -- A₀ ∉ badA₀ but fiber ≡ 0 on E.points: contradicts hAbad.
          exfalso
          apply hAbad
          simp only [badA₀, Finset.mem_filter]
          exact ⟨hA₀, hall⟩
    -- Sum over A₀ via card_le_mul_card_image.
    have hImgSub : zGood.image Prod.fst ⊆ E.points := by
      intro A₀ hA₀
      rw [Finset.mem_image] at hA₀
      obtain ⟨p, hp, rfl⟩ := hA₀
      simp only [zGood, zSet, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1.1
    calc zGood.card
        ≤ K * (zGood.image Prod.fst).card := by
          exact Finset.card_le_mul_card_image _ _
            (fun A₀ hA₀ => hFiberGood A₀ (hImgSub hA₀))
      _ ≤ K * E.points.card := Nat.mul_le_mul_left _ (Finset.card_le_card hImgSub)
      _ = E.points.card * K := Nat.mul_comm _ _
  -- Combine.
  calc zSet.card
      = zBad.card + zGood.card := by
        rw [hSplit, Finset.card_union_of_disjoint hDisjoint]
    _ ≤ K * E.points.card + E.points.card * K := by
        exact Nat.add_le_add hBadCard hGoodCard
    _ = 2 * K * E.points.card := by ring

end Divisor
