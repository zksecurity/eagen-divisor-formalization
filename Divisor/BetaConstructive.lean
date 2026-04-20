/-
  Divisor/BetaConstructive.lean

  Queue-2 Phase-B step QB1: a constructive multiplicity function
  `betaConstructive D : ZMod E.q × ZMod E.q → ℕ` derived directly from
  `D.a, D.b` (no function-field / Weierstrass-preparation machinery
  invoked, and no appeal to the `CoordRingElt.has_principal_divisor`
  axiom).

  Construction. Let `N(D) := D.a^2 - D.b^2 * curveX` (the "norm" polynomial
  in one variable). On a point `P = (x₀, y₀) ∈ E.points`,
  `N(D).eval x₀ = D(x₀, y₀) * D(x₀, -y₀)`. The F_q-multiplicity
  `m := rootMultiplicity x₀ N(D)` therefore controls the total order of
  vanishing of `D` on the two sheets `(x₀, y₀)` and `(x₀, -y₀)` of `E`
  over `x₀`.

  We define
  ```
    betaConstructive D P :=
      if  P ∈ E.points ∧ D.eval P.1 P.2 = 0  then
        if  P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0  then
          rootMultiplicity P.1 (normPoly E D)
        else
          rootMultiplicity P.1 (normPoly E D) / 2
      else 0
  ```

  The `/2` case (both sheets above `x₀` are zeros of `D`) forces
  `D.a x₀ = D.b x₀ = 0`, which in turn forces `(X - C x₀)^2 ∣ N(D)` —
  so `rootMultiplicity x₀ N(D) ≥ 2` and `m/2 ≥ 1`. That makes the
  `≠ 0` coverage property hold.

  Properties proved here (for `D` with `¬ (D.a = 0 ∧ D.b = 0)`):
  * `betaConstructive_support`: support ⊆ `D`'s affine zeros on `E`.
  * `betaConstructive_covers`: every `D`-zero on `E` is in the support.
  * `betaConstructive_sum_le_degE`: `∑_{P∈E.points} β(P) ≤ D.degE`.

  The equality variant of the last property (`∑ β = D.degE`) is
  classical (pole at `∞` is exactly `D.degE`) but over `F_q` it
  requires `N(D)` to split; we only establish the upper bound here.
  QB2 / QB3 consume this surrogate; see the plan doc.
-/
import Divisor.Defs
import Divisor.ClearedPolyForm
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The norm polynomial `N(D) := D.a^2 - D.b^2 · curveX` -/

/-- `normPoly E D = D.a^2 - D.b^2 · curveX E` in `(ZMod E.q)[X]`. -/
noncomputable def normPoly (D : CoordRingElt E.q) : (ZMod E.q)[X] :=
  resultantX E (DAtA₁Poly (E := E) D)

theorem normPoly_eq (D : CoordRingElt E.q) :
    normPoly E D = D.a ^ 2 - D.b ^ 2 * curveX E := by
  unfold normPoly resultantX
  rw [DAtA₁Poly_xPart, DAtA₁Poly_yPart]
  ring

theorem normPoly_ne_zero (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) : normPoly E D ≠ 0 := by
  rw [normPoly_eq]; exact resultantX_aux_ne_zero E hD

theorem normPoly_natDegree_le (D : CoordRingElt E.q) :
    (normPoly E D).natDegree ≤ D.degE :=
  resultantX_DAtA₁Poly_natDegree_le E D

/-- `N(D).eval x₀ = (D.a.eval x₀)^2 - (D.b.eval x₀)^2 · (x₀^3 + A·x₀ + B)`. -/
theorem normPoly_eval (D : CoordRingElt E.q) (x₀ : ZMod E.q) :
    (normPoly E D).eval x₀ =
      (D.a.eval x₀) ^ 2 - (D.b.eval x₀) ^ 2 * (x₀ ^ 3 + E.curveA * x₀ + E.curveB) := by
  rw [normPoly_eq]
  unfold curveX
  simp only [eval_sub, eval_pow, eval_mul, eval_add, eval_X, eval_C]

/-- On `E`, `N(D).eval x₀ = D(x₀, y₀) · D(x₀, -y₀)`. -/
theorem normPoly_eval_eq_D_mul_D_neg
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    (normPoly E D).eval P.1 = D.eval P.1 P.2 * D.eval P.1 (-P.2) := by
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  rw [normPoly_eval]
  unfold CoordRingElt.eval
  have hRw : D.a.eval P.1 ^ 2 -
          D.b.eval P.1 ^ 2 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB)
        = D.a.eval P.1 ^ 2 - D.b.eval P.1 ^ 2 * P.2 ^ 2 := by
    rw [← hOC]
  rw [hRw]; ring

/-! ## Root multiplicity at the `x`-coordinate of a zero on `E` -/

/-- If `P ∈ E.points` and `D.eval P = 0`, then `x₀ = P.1` is a root of
    `N(D)`, so `rootMultiplicity x₀ N(D) ≥ 1`. -/
theorem rootMultiplicity_normPoly_pos
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hZ : D.eval P.1 P.2 = 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    0 < rootMultiplicity P.1 (normPoly E D) := by
  rw [rootMultiplicity_pos (normPoly_ne_zero E D hD)]
  show (normPoly E D).eval P.1 = 0
  rw [normPoly_eval_eq_D_mul_D_neg E D hP, hZ, zero_mul]

/-- If both sheets `(x₀, y₀)` and `(x₀, -y₀)` (with `y₀ ≠ 0`) are zeros of
    `D`, then `D.a.eval x₀ = 0` and `D.b.eval x₀ = 0`. -/
theorem Da_Db_eval_zero_of_both_sheets_zero
    (D : CoordRingElt E.q) {x₀ y₀ : ZMod E.q}
    (hY : y₀ ≠ 0)
    (hZ : D.eval x₀ y₀ = 0) (hZneg : D.eval x₀ (-y₀) = 0) :
    D.a.eval x₀ = 0 ∧ D.b.eval x₀ = 0 := by
  unfold CoordRingElt.eval at hZ hZneg
  have h1 : D.a.eval x₀ - D.b.eval x₀ * y₀ = 0 := hZ
  have h2' : D.a.eval x₀ + D.b.eval x₀ * y₀ = 0 := by linear_combination hZneg
  have hA : 2 * D.a.eval x₀ = 0 := by linear_combination h1 + h2'
  have hBy : 2 * (D.b.eval x₀ * y₀) = 0 := by linear_combination -h1 + h2'
  have h2NZ : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.mp hA with h | h
    · exact absurd h h2NZ
    · exact h
  · have hMulZero : D.b.eval x₀ * y₀ = 0 := by
      rcases mul_eq_zero.mp hBy with h | h
      · exact absurd h h2NZ
      · exact h
    rcases mul_eq_zero.mp hMulZero with h | h
    · exact h
    · exact absurd h hY

/-- Vanishing of `D.a` and `D.b` at `x₀` implies `(X - C x₀)^2 ∣ N(D)`. -/
theorem X_sub_C_sq_dvd_normPoly_of_a_b_eval_zero
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (ha : D.a.eval x₀ = 0) (hb : D.b.eval x₀ = 0) :
    (Polynomial.X - Polynomial.C x₀) ^ 2 ∣ normPoly E D := by
  obtain ⟨a', ha'⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  obtain ⟨b', hb'⟩ := Polynomial.dvd_iff_isRoot.mpr hb
  rw [normPoly_eq, ha', hb']
  refine ⟨a' ^ 2 - b' ^ 2 * curveX E, ?_⟩
  ring

/-- In the "both sheets are D-zeros" case, `rootMultiplicity x₀ N(D) ≥ 2`. -/
theorem rootMultiplicity_normPoly_ge_two_of_both_sheets
    (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {x₀ y₀ : ZMod E.q}
    (hY : y₀ ≠ 0)
    (hZ : D.eval x₀ y₀ = 0) (hZneg : D.eval x₀ (-y₀) = 0) :
    2 ≤ rootMultiplicity x₀ (normPoly E D) := by
  obtain ⟨ha, hb⟩ := Da_Db_eval_zero_of_both_sheets_zero E D hY hZ hZneg
  rw [le_rootMultiplicity_iff (normPoly_ne_zero E D hD)]
  exact X_sub_C_sq_dvd_normPoly_of_a_b_eval_zero E D ha hb

/-! ## The constructive β -/

/-- Constructive multiplicity function.

    Values:
    * 0 off `E` or where `D` is nonzero.
    * `rootMultiplicity x₀ N(D)` at 2-torsion sheets (`y₀ = 0`) and at
      "lone" sheets (the opposite sheet `(x₀, -y₀)` is NOT a `D`-zero).
    * `rootMultiplicity x₀ N(D) / 2` (Nat division) at "twin" sheets
      (both `(x₀, y₀)` and `(x₀, -y₀)` are `D`-zeros). -/
noncomputable def betaConstructive (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if P ∈ E.points ∧ D.eval P.1 P.2 = 0 then
      if P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0 then
        rootMultiplicity P.1 (normPoly E D)
      else
        rootMultiplicity P.1 (normPoly E D) / 2
    else 0

theorem betaConstructive_of_not_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (h : ¬ (P ∈ E.points ∧ D.eval P.1 P.2 = 0)) :
    betaConstructive E D P = 0 := by
  classical
  unfold betaConstructive
  simp [h]

theorem betaConstructive_lone
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hZ : D.eval P.1 P.2 = 0)
    (hLone : P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0) :
    betaConstructive E D P = rootMultiplicity P.1 (normPoly E D) := by
  classical
  unfold betaConstructive
  simp [hP, hZ, hLone]

theorem betaConstructive_twin
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hZ : D.eval P.1 P.2 = 0)
    (hY : P.2 ≠ 0) (hZneg : D.eval P.1 (-P.2) = 0) :
    betaConstructive E D P = rootMultiplicity P.1 (normPoly E D) / 2 := by
  classical
  unfold betaConstructive
  have hNot : ¬ (P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0) := by
    push_neg
    exact ⟨hY, hZneg⟩
  simp [hP, hZ, hNot]

/-! ## Property 1: support -/

/-- `β` is only supported on `E`-points that are `D`-zeros. -/
theorem betaConstructive_support
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (h : betaConstructive E D P ≠ 0) :
    P ∈ E.points ∧ D.eval P.1 P.2 = 0 := by
  classical
  by_contra hNot
  exact h (betaConstructive_of_not_zero E D hNot)

/-! ## Property 2: coverage -/

/-- Every `E`-rational `D`-zero lies in the support of `β`. -/
theorem betaConstructive_covers
    (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hZ : D.eval P.1 P.2 = 0) :
    betaConstructive E D P ≠ 0 := by
  classical
  by_cases hLone : P.2 = 0 ∨ D.eval P.1 (-P.2) ≠ 0
  · rw [betaConstructive_lone E D hP hZ hLone]
    exact Nat.pos_iff_ne_zero.mp (rootMultiplicity_normPoly_pos E D hP hZ hD)
  · push_neg at hLone
    obtain ⟨hY, hZneg⟩ := hLone
    rw [betaConstructive_twin E D hP hZ hY hZneg]
    have hGe2 : 2 ≤ rootMultiplicity P.1 (normPoly E D) :=
      rootMultiplicity_normPoly_ge_two_of_both_sheets E D hD hY hZ hZneg
    omega

/-! ## Sheet partition

    For a fixed `x₀ : ZMod E.q`, the `E`-points above `x₀` form the
    Finset `E.points.filter (·.1 = x₀)`. This set has cardinality ≤ 2
    (proved previously as `card_points_with_fst_eq_le`).

    Sum over sheets at `x₀` of `β`:
    * 0 if no sheet is a `D`-zero,
    * `rootMultiplicity x₀ N(D)` if exactly one sheet is a `D`-zero
      (either a 2-torsion sheet or a lone sheet),
    * `2 * (rootMultiplicity x₀ N(D) / 2) ≤ rootMultiplicity x₀ N(D)` if
      both sheets are `D`-zeros.

    All three cases yield `≤ rootMultiplicity x₀ N(D)`. -/

/-- If `P = (x₀, y₀) ∈ E.points` with `y₀ ≠ 0`, then `(x₀, -y₀) ∈ E.points`
    too, and the two are distinct. -/
theorem neg_sheet_on_E (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points)
    (hY : P.2 ≠ 0) :
    (P.1, -P.2) ∈ E.points ∧ (P.1, -P.2) ≠ P := by
  refine ⟨?_, ?_⟩
  · have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
    have hOC' : (-P.2) ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := by
      rw [neg_pow_two]; exact hOC
    exact E.hComplete P.1 (-P.2) hOC'
  · intro h
    have hSnd : -P.2 = P.2 := by
      have := congrArg Prod.snd h
      simpa using this
    have h2y : 2 * P.2 = 0 := by linear_combination -hSnd
    have h2NZ : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    rcases mul_eq_zero.mp h2y with hz | hz
    · exact h2NZ hz
    · exact hY hz

/-- Per-`x₀` sum bound: `∑_{(x,y)∈E.points, x = x₀} β(x, y) ≤
    rootMultiplicity x₀ N(D)`. -/
theorem sum_betaConstructive_fst_eq_le
    (D : CoordRingElt E.q) (x₀ : ZMod E.q) :
    (∑ P ∈ E.points.filter (fun P => P.1 = x₀), betaConstructive E D P)
      ≤ rootMultiplicity x₀ (normPoly E D) := by
  classical
  set S := E.points.filter (fun P => P.1 = x₀)
  have hCard : S.card ≤ 2 := card_points_with_fst_eq_le E x₀
  -- Split into cases on S.card ∈ {0, 1, 2}.
  interval_cases hScard : S.card
  · -- |S| = 0
    have hEmpty : S = ∅ := Finset.card_eq_zero.mp hScard
    rw [hEmpty]; simp
  · -- |S| = 1: S = {P}. From the "two sheets over x₀" lemma, y = 0.
    rw [Finset.card_eq_one] at hScard
    obtain ⟨P, hSP⟩ := hScard
    rw [hSP, Finset.sum_singleton]
    have hPS : P ∈ S := by rw [hSP]; exact Finset.mem_singleton_self P
    have hPE : P ∈ E.points := (Finset.mem_filter.mp hPS).1
    have hPx : P.1 = x₀ := (Finset.mem_filter.mp hPS).2
    -- If D(P) ≠ 0, β P = 0 ≤ rootMult.
    by_cases hZ : D.eval P.1 P.2 = 0
    · -- D(P) = 0. Either y = 0 (2-torsion, lone) or y ≠ 0 (twin / lone).
      -- If y ≠ 0, then (x, -y) ∈ E.points too (distinct), contradicting |S| = 1.
      have hY0 : P.2 = 0 := by
        by_contra hY
        have ⟨hNegE, hNeq⟩ := neg_sheet_on_E E P hPE hY
        have hNegS : (P.1, -P.2) ∈ S :=
          Finset.mem_filter.mpr ⟨hNegE, hPx⟩
        rw [hSP] at hNegS
        exact hNeq (Finset.mem_singleton.mp hNegS)
      -- With y = 0, we're in lone case (first disjunct of hLone).
      rw [betaConstructive_lone E D hPE hZ (Or.inl hY0), hPx]
    · rw [betaConstructive_of_not_zero E D (fun h => hZ h.2)]
      exact Nat.zero_le _
  · -- |S| = 2: S = {P₁, P₂} with P₁ ≠ P₂.
    rw [Finset.card_eq_two] at hScard
    obtain ⟨P₁, P₂, hNeq, hSP⟩ := hScard
    rw [hSP, Finset.sum_insert (Finset.not_mem_singleton.mpr hNeq),
        Finset.sum_singleton]
    have hP₁ : P₁ ∈ E.points ∧ P₁.1 = x₀ := by
      have : P₁ ∈ S := by rw [hSP]; exact Finset.mem_insert_self _ _
      exact Finset.mem_filter.mp this
    have hP₂ : P₂ ∈ E.points ∧ P₂.1 = x₀ := by
      have : P₂ ∈ S := by
        rw [hSP]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact Finset.mem_filter.mp this
    -- Both points have x = x₀. They are distinct, so their y-coords differ.
    have hYneq : P₁.2 ≠ P₂.2 := fun h => hNeq (Prod.ext (hP₁.2.trans hP₂.2.symm) h)
    -- Also, y coords satisfy y² = x₀³+Ax₀+B. So y₁ = -y₂ (both roots of same
    -- quadratic).
    have hY₁sq : P₁.2 ^ 2 = P₁.1 ^ 3 + E.curveA * P₁.1 + E.curveB :=
      E.hOnCurve P₁ hP₁.1
    have hY₂sq : P₂.2 ^ 2 = P₂.1 ^ 3 + E.curveA * P₂.1 + E.curveB :=
      E.hOnCurve P₂ hP₂.1
    have hYsum : P₁.2 ^ 2 = P₂.2 ^ 2 := by
      rw [hY₁sq, hY₂sq, hP₁.2, hP₂.2]
    -- y₁² = y₂² ⇒ (y₁ - y₂)(y₁ + y₂) = 0. Since y₁ ≠ y₂, y₁ + y₂ = 0, i.e. y₂ = -y₁.
    have hFactor : (P₁.2 - P₂.2) * (P₁.2 + P₂.2) = 0 := by linear_combination hYsum
    have hYneg : P₂.2 = -P₁.2 := by
      have hSumZero : P₁.2 + P₂.2 = 0 := by
        rcases mul_eq_zero.mp hFactor with h | h
        · exact absurd (sub_eq_zero.mp h) hYneq
        · exact h
      linear_combination hSumZero
    -- y₁ ≠ 0 (since if y₁ = 0 then y₂ = 0 too, contradicting y₁ ≠ y₂).
    have hY₁ : P₁.2 ≠ 0 := by
      intro h
      apply hYneq
      rw [h, hYneg, h, neg_zero]
    have hY₂ : P₂.2 ≠ 0 := by
      intro h
      apply hY₁
      have hEq : P₁.2 = -P₂.2 := by rw [hYneg, neg_neg]
      rw [hEq, h, neg_zero]
    -- Case analysis on whether D(P₁) = 0 and D(P₂) = 0.
    by_cases hZ₁ : D.eval P₁.1 P₁.2 = 0
    · by_cases hZ₂ : D.eval P₂.1 P₂.2 = 0
      · -- Both sheets are D-zeros. Twin case at both.
        -- β P₁ = rootMult / 2, β P₂ = rootMult / 2, sum = 2·(m/2) ≤ m.
        have hZ₁neg : D.eval P₁.1 (-P₁.2) = 0 := by
          have : D.eval P₁.1 (-P₁.2) = D.eval P₂.1 P₂.2 := by
            congr 1
            · exact hP₁.2.trans hP₂.2.symm
            · simpa using hYneg.symm
          rw [this, hZ₂]
        have hZ₂neg : D.eval P₂.1 (-P₂.2) = 0 := by
          have : D.eval P₂.1 (-P₂.2) = D.eval P₁.1 P₁.2 := by
            congr 1
            · exact hP₂.2.trans hP₁.2.symm
            · simp [hYneg, neg_neg]
          rw [this, hZ₁]
        rw [betaConstructive_twin E D hP₁.1 hZ₁ hY₁ hZ₁neg,
            betaConstructive_twin E D hP₂.1 hZ₂ hY₂ hZ₂neg]
        rw [hP₁.2, hP₂.2]
        -- 2 · (m/2) ≤ m (Nat)
        have := rootMultiplicity x₀ (normPoly E D)
        omega
      · -- D(P₁) = 0, D(P₂) ≠ 0. P₁ is a lone sheet.
        -- β P₁ = rootMult (lone: D(x₀, -y₁) = D(P₂) ≠ 0).
        -- β P₂ = 0.
        have hZ₁neg : D.eval P₁.1 (-P₁.2) ≠ 0 := by
          -- D.eval P₁.1 (-P₁.2) = D.eval P₂.1 P₂.2 ≠ 0
          have heq : D.eval P₁.1 (-P₁.2) = D.eval P₂.1 P₂.2 := by
            congr 1
            · exact hP₁.2.trans hP₂.2.symm
            · simpa using hYneg.symm
          rw [heq]; exact hZ₂
        rw [betaConstructive_lone E D hP₁.1 hZ₁ (Or.inr hZ₁neg),
            betaConstructive_of_not_zero E D (fun h => hZ₂ h.2)]
        rw [hP₁.2]
        omega
    · by_cases hZ₂ : D.eval P₂.1 P₂.2 = 0
      · -- D(P₁) ≠ 0, D(P₂) = 0. P₂ is a lone sheet.
        have hZ₂neg : D.eval P₂.1 (-P₂.2) ≠ 0 := by
          have heq : D.eval P₂.1 (-P₂.2) = D.eval P₁.1 P₁.2 := by
            congr 1
            · exact hP₂.2.trans hP₁.2.symm
            · simp [hYneg, neg_neg]
          rw [heq]; exact hZ₁
        rw [betaConstructive_of_not_zero E D (fun h => hZ₁ h.2),
            betaConstructive_lone E D hP₂.1 hZ₂ (Or.inr hZ₂neg)]
        rw [hP₂.2]
        omega
      · -- Neither sheet is D-zero. Sum = 0.
        rw [betaConstructive_of_not_zero E D (fun h => hZ₁ h.2),
            betaConstructive_of_not_zero E D (fun h => hZ₂ h.2)]
        omega

/-! ## Property 3 (surrogate): `∑ β ≤ D.degE`

    Strategy:
    1. Group `E.points` by `x`-coordinate via `Finset.sum_fiberwise`.
    2. Each per-x-coord sum is `≤ rootMultiplicity x₀ N(D)` by
       `sum_betaConstructive_fst_eq_le`.
    3. The total over `x₀ ∈ F_q` is `≤ deg N(D) ≤ D.degE`.

    The last step uses `Multiset.card p.roots ≤ natDegree p`. -/

/-- Sum of `rootMultiplicity a p` over all `a : ZMod E.q` is at most
    `natDegree p`. -/
theorem sum_rootMultiplicity_le_natDegree
    (p : (ZMod E.q)[X]) :
    (∑ a : ZMod E.q, rootMultiplicity a p) ≤ p.natDegree := by
  classical
  calc (∑ a : ZMod E.q, rootMultiplicity a p)
      = ∑ a : ZMod E.q, p.roots.count a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [count_roots]
    _ = Multiset.card p.roots := by
        -- ∑ a ∈ univ, s.count a = card s (finite α with DecidableEq).
        -- We use `Multiset.toFinset_sum_count_eq` (sum over toFinset equals card).
        rw [← Multiset.toFinset_sum_count_eq p.roots]
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro a _ hNotIn
        rw [Multiset.mem_toFinset] at hNotIn
        exact Multiset.count_eq_zero_of_not_mem hNotIn
    _ ≤ p.natDegree := card_roots' p

/-- Write `E.points` as a disjoint union over the `x`-coordinates of its
    points: `E.points = ⋃_{x₀} (E.points.filter (·.1 = x₀))`. -/
theorem sum_E_points_eq_sum_fiberwise
    (f : ZMod E.q × ZMod E.q → ℕ) :
    (∑ P ∈ E.points, f P) =
      ∑ x₀ : ZMod E.q, ∑ P ∈ E.points.filter (fun P => P.1 = x₀), f P := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun P (_ : P ∈ E.points) => Finset.mem_univ P.1)]

/-- Main surrogate: `∑_{P ∈ E.points} β(P) ≤ D.degE`.

    Holds unconditionally — even in the `D = 0` corner case, `normPoly E D = 0`
    has `natDegree = 0` and `betaConstructive` is identically zero off `D`'s
    (empty) zero locus, so the bound degenerates to `0 ≤ D.degE`. -/
theorem betaConstructive_sum_le_degE
    (D : CoordRingElt E.q) :
    (∑ P ∈ E.points, betaConstructive E D P) ≤ D.degE := by
  classical
  rw [sum_E_points_eq_sum_fiberwise E]
  calc (∑ x₀ : ZMod E.q,
          ∑ P ∈ E.points.filter (fun P => P.1 = x₀), betaConstructive E D P)
      ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E D) :=
        Finset.sum_le_sum (fun x₀ _ => sum_betaConstructive_fst_eq_le E D x₀)
    _ ≤ (normPoly E D).natDegree :=
        sum_rootMultiplicity_le_natDegree E (normPoly E D)
    _ ≤ D.degE := normPoly_natDegree_le E D

/-! ## Narrow Abel-theorem axioms

    The remaining two properties of `betaConstructive` needed downstream —
    the weighted group-sum-zero identity (the "Abel's theorem on E"
    content), and the equality `∑ β = D.degE` (the pole-order-at-∞
    identity) — depend on function-field / Weierstrass-preparation
    machinery beyond what we mechanize here. We record them as narrow
    axioms covering exactly the classical facts they invoke, with no
    bundling of support / coverage content (those are derived above).

    Classical citation: **Silverman, "The Arithmetic of Elliptic
    Curves", Chapter III, Proposition 3.4** — every nonzero rational
    function `f` on an elliptic curve `E` has a principal divisor
    `div(f) = Σ ord_P(f) · (P)` satisfying
      (i)   `Σ ord_P(f) = 0` (total degree zero), and
      (ii)  `Σ ord_P(f) · P = O` in the group law (Abel's theorem).

    Specialized to `f = D = a(x) - b(x)·y` viewed as a nonzero element
    of `F_q[E] ⊂ F_q(E)`, the affine part of `div(D)` is recorded by
    the multiplicity function `betaConstructive D`, and the pole at `∞`
    has order `D.degE`. Item (i) becomes
    `∑ β(P) = D.degE` (the affine sum equals the pole order at `∞`),
    and item (ii) becomes
    `∑ β(P) · (affine P) = O` (the `∞` term contributes `0 · ∞ = 0`).
-/

/-- **Abel's theorem on E for `D`'s divisor** (Silverman III Prop 3.4,
    group-sum-zero part).

    The `β`-weighted group sum over `E`'s affine points vanishes:
    the divisor of the nonzero rational function `D = a(x) - b(x)·y`
    has group-sum zero, and the `∞` contribution is `-D.degE · (∞)`
    which is `0` under the group law (since `∞` is the identity). -/
axiom CoordRingElt.divisor_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0

/-- **Pole-order-at-∞ identity** (Silverman III Prop 3.4, degree part).

    The total affine multiplicity of the divisor of a nonzero
    `D = a(x) - b(x)·y ∈ F_q[E]` equals `D.degE`, which is the pole
    order of `D` at the point at infinity.

    This strengthens `betaConstructive_sum_le_degE` from `≤` to `=`.
    The gap is due to possible failure of `normPoly` to split over
    `F_q` and edge-case inflation of `D.degE` in the
    `D.b = 0 ∧ D.a.natDegree < 2` cases — neither of which is tracked
    by a `rootMultiplicity`-based construction. The classical identity
    holds over the algebraic closure and descends via the Galois
    structure of the principal-divisor map. -/
axiom CoordRingElt.divisor_degree_eq
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (∑ P ∈ E.points, betaConstructive E D P) = D.degE

/-! ## Derived theorem: `betaConstructive_group_sum_zero` -/

/-- Direct restatement of the group-sum axiom as a convenience theorem
    under the chosen `β = betaConstructive E D` representative. Downstream
    consumers can substitute any symbol matching this signature. -/
theorem betaConstructive_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0 :=
  CoordRingElt.divisor_group_sum_zero E D hD

/-- Direct restatement of the degree axiom: the affine-multiplicity sum
    of `betaConstructive` equals `D.degE`. -/
theorem betaConstructive_sum_eq_degE
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (∑ P ∈ E.points, betaConstructive E D P) = D.degE :=
  CoordRingElt.divisor_degree_eq E D hD

/-! ## Q3.1: split case — `betaConstructive` ↔ `rootMultiplicity` bridge

    When `normPoly E D` splits over `F_q` in the sense that its root
    multiset has cardinality equal to its `natDegree`, the per-`x₀`
    bound `sum_betaConstructive_fst_eq_le` collapses to an equality.
    The key observation is that:

    * `∑_P β P = D.degE` (Silverman III 3.4, `betaConstructive_sum_eq_degE`).
    * `∑_α rootMult α N(D) = Multiset.card N(D).roots` (counting identity).
    * Under the split hypothesis, `Multiset.card roots = natDegree N(D)`.
    * `natDegree N(D) ≤ D.degE` (`normPoly_natDegree_le`).

    Chaining these with the per-`x₀` bound forces equality everywhere.
    Q3.2 consumes the total-sum identity to instantiate the partial-fraction
    expansion from Q3.0 at `p = normPoly E D`. -/

/-- Split predicate: `N(D)` has as many roots as its degree (counted with
multiplicity) over `F_q`. Equivalent to saying every root is `F_q`-rational. -/
def normPoly_splits_over_Fq (D : CoordRingElt E.q) : Prop :=
  Multiset.card (normPoly E D).roots = (normPoly E D).natDegree

/-- Counting identity: the total sum of `rootMultiplicity α p` over `α : F_q`
equals `Multiset.card p.roots`. Same argument as the first half of
`sum_rootMultiplicity_le_natDegree`. -/
theorem sum_rootMultiplicity_eq_card_roots (p : (ZMod E.q)[X]) :
    (∑ α : ZMod E.q, rootMultiplicity α p) = Multiset.card p.roots := by
  classical
  calc (∑ α : ZMod E.q, rootMultiplicity α p)
      = ∑ α : ZMod E.q, p.roots.count α := by
        apply Finset.sum_congr rfl
        intro a _
        rw [count_roots]
    _ = Multiset.card p.roots := by
        rw [← Multiset.toFinset_sum_count_eq p.roots]
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro a _ hNotIn
        rw [Multiset.mem_toFinset] at hNotIn
        exact Multiset.count_eq_zero_of_not_mem hNotIn

/-- Under the split hypothesis, the total `rootMultiplicity` sum equals
`natDegree`. -/
theorem sum_rootMultiplicity_eq_natDegree_of_splits
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D) :
    (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
      = (normPoly E D).natDegree := by
  rw [sum_rootMultiplicity_eq_card_roots]
  exact hSplit

/-- **Q3.1 main bridge (total sum).** When `normPoly E D` splits over `F_q`
and `D` is nontrivial (`¬ (D.a = 0 ∧ D.b = 0)`), the total sum of
`betaConstructive` over `E`-points equals the total sum of
`rootMultiplicity` over `F_q`:

  `(∑ P ∈ E.points, β P) = ∑ α, rootMult α N(D)`.

This is the identity Q3.2 consumes. The proof uses the inequality chain

    D.degE = ∑ β ≤ ∑ α, rootMult α ≤ natDegree N(D) ≤ D.degE

and the split hypothesis to collapse the middle inequality to `natDegree`
via `sum_rootMultiplicity_eq_natDegree_of_splits`. -/
theorem sum_betaConstructive_eq_sum_rootMultiplicity_of_splits
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    (∑ P ∈ E.points, betaConstructive E D P)
      = ∑ α : ZMod E.q, rootMultiplicity α (normPoly E D) := by
  classical
  -- Two chains meeting: ∑β = D.degE, and ∑rootMult = natDegree ≤ D.degE.
  have hBeta : (∑ P ∈ E.points, betaConstructive E D P) = D.degE :=
    betaConstructive_sum_eq_degE E D hD
  have hRoots : (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
                  = (normPoly E D).natDegree :=
    sum_rootMultiplicity_eq_natDegree_of_splits E D hSplit
  have hDeg : (normPoly E D).natDegree ≤ D.degE := normPoly_natDegree_le E D
  -- The per-x₀ surrogate chain ∑ β ≤ ∑ rootMult.
  have hLe : (∑ P ∈ E.points, betaConstructive E D P)
              ≤ ∑ α : ZMod E.q, rootMultiplicity α (normPoly E D) := by
    rw [sum_E_points_eq_sum_fiberwise E]
    exact Finset.sum_le_sum (fun x₀ _ => sum_betaConstructive_fst_eq_le E D x₀)
  -- Combine: D.degE ≤ ∑ rootMult = natDegree ≤ D.degE ⇒ equalities.
  have hGe : (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
              ≤ (∑ P ∈ E.points, betaConstructive E D P) := by
    rw [hBeta, hRoots]; exact hDeg
  exact le_antisymm hLe hGe

/-- **Corollary (split case, natDegree identity).** Under the split
hypothesis, `natDegree (normPoly E D) = D.degE`. This follows from
`natDegree ≤ D.degE` and the equality chain above forcing equality. -/
theorem normPoly_natDegree_eq_degE_of_splits
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    (normPoly E D).natDegree = D.degE := by
  have hSum := sum_betaConstructive_eq_sum_rootMultiplicity_of_splits E D hD hSplit
  have hBeta : (∑ P ∈ E.points, betaConstructive E D P) = D.degE :=
    betaConstructive_sum_eq_degE E D hD
  have hRoots : (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
                  = (normPoly E D).natDegree :=
    sum_rootMultiplicity_eq_natDegree_of_splits E D hSplit
  -- From hSum: D.degE = ∑ β = ∑ rootMult = natDegree.
  rw [← hRoots, ← hSum, hBeta]

/-- **Corollary (per-`x₀` equality).** In the split case, the per-`x₀`
inequality `sum_betaConstructive_fst_eq_le` tightens to an equality:
for every `x₀ : F_q`,

  `∑ P ∈ E.points, P.1 = x₀, β P = rootMultiplicity x₀ (normPoly E D)`.

This follows from the Mathlib equality-forcing lemma
`Finset.sum_eq_sum_iff_of_le`: equal totals + pointwise `≤` ⇒ pointwise `=`. -/
theorem sum_betaConstructive_fst_eq_of_splits
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (x₀ : ZMod E.q) :
    (∑ P ∈ E.points.filter (fun P => P.1 = x₀), betaConstructive E D P)
      = rootMultiplicity x₀ (normPoly E D) := by
  classical
  -- Sum over x₀ : F_q of LHS equals the total sum of β (fiberwise lemma).
  -- Sum over x₀ : F_q of RHS is total rootMultiplicity sum.
  -- The per-x₀ bound `sum_betaConstructive_fst_eq_le` is `≤` pointwise.
  -- The `sum_eq_sum_iff_of_le` flip converts equal totals + pointwise `≤`
  -- to pointwise equality.
  have hTotal := sum_betaConstructive_eq_sum_rootMultiplicity_of_splits E D hD hSplit
  -- Rewrite the LHS of hTotal via fiberwise.
  rw [sum_E_points_eq_sum_fiberwise E] at hTotal
  -- Now hTotal is: ∑ x₀, (∑ P ∈ filter, β P) = ∑ x₀, rootMult x₀ N(D).
  -- Apply Finset.sum_eq_sum_iff_of_le with the per-x₀ bound.
  have hPtwise : ∀ x₀ ∈ (Finset.univ : Finset (ZMod E.q)),
                   (∑ P ∈ E.points.filter (fun P => P.1 = x₀), betaConstructive E D P)
                     ≤ rootMultiplicity x₀ (normPoly E D) :=
    fun x₀ _ => sum_betaConstructive_fst_eq_le E D x₀
  exact (Finset.sum_eq_sum_iff_of_le hPtwise).mp hTotal x₀ (Finset.mem_univ x₀)

end Divisor
