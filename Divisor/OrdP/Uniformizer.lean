/-
  Divisor/OrdP/Uniformizer.lean

  Order of vanishing at affine F_q-rational points of `E`, computed
  by a sound local-ring recipe.

  Background (Silverman AEC, II §1): for a smooth affine point `P` on
  `E : y² = x³ + Ax + B` (char ≠ 2), the local ring `O_{E,P}` is a DVR
  and the choice of uniformizer depends on whether `P.2 = 0`:

  * Non-2-torsion (`P.2 ≠ 0`): `t = x − P.1` is a uniformizer; `y` is a
    unit at `P`.
  * 2-torsion (`P.2 = 0`): `t = y` is a uniformizer; `x − P.1` has
    order 2 (since `y² = (x − P.1) · q(x)` with `q(P.1) ≠ 0`).

  ## Sound `ordAt` design (replaces the previous 0/1 placeholder)

  We compute `ord_P(D)` for `D = a(x) − b(x)·y` ∈ F_q[E] without
  appealing to formal Taylor expansion of `y(x)`.  Two case-specific
  recipes:

  ### 2-torsion (closed form)

    For `P = (x₀, 0)`:
    * `a(x)` contributes only EVEN powers of the uniformizer `t = y`,
      with order `2 · rootMult x₀ a` (since `x − x₀` has order `2`).
    * `b(x) · y` contributes only ODD powers, with order
      `2 · rootMult x₀ b + 1`.
    * Different parities, so the two pieces never cancel:
      `ord_P(D) = min(2·rootMult x₀ a, 2·rootMult x₀ b + 1)`.

  ### Non-2-torsion (recursive twin/lone trichotomy)

    For `P = (x₀, y₀)` with `y₀ ≠ 0`:
    * `D(P) ≠ 0` ⇒ `ord_P(D) = 0`.
    * `D(P) = 0`, `D(P^σ) ≠ 0` (lone): the only mass at `x₀` is on
      the `P` sheet, so by the norm identity
      `ord_P(D) + ord_{P^σ}(D) = rootMult x₀ N(D)`
      we get `ord_P(D) = rootMult x₀ (normPoly E D)`.
    * `D(P) = 0`, `D(P^σ) = 0` (twin): `(X − x₀)` divides both `a`
      and `b`, hence `D = (X − x₀) · D'` on `E` with
      `D' = D /ₘ (X − C x₀)` (componentwise).  Since
      `ord_P(X − x₀) = 1`, we recurse: `ord_P(D) = 1 + ord_P(D')`.
      Termination: `(D'.a.natDegree, D'.b.natDegree)` strictly drops.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Helper: divide both `a` and `b` by `(X − C x₀)` -/

/-- Componentwise division of `D = (a, b)` by the linear polynomial
    `X − C x₀`.  When `(X − C x₀)` divides both `a` and `b`, the
    result `D'` satisfies `D = (X − x₀) · D'` as elements of the
    coordinate ring of `E`. -/
noncomputable def CoordRingElt.divLin {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (x₀ : ZMod q) : CoordRingElt q :=
  { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
    b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }

theorem CoordRingElt.divLin_a {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (x₀ : ZMod q) :
    (D.divLin x₀).a = D.a /ₘ (Polynomial.X - Polynomial.C x₀) := rfl

theorem CoordRingElt.divLin_b {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (x₀ : ZMod q) :
    (D.divLin x₀).b = D.b /ₘ (Polynomial.X - Polynomial.C x₀) := rfl

/-! ## 2-torsion: closed-form local order -/

/-- Order of vanishing of `D = a − b·y` at a 2-torsion point
    `P = (x₀, 0)`.

    Closed form `min(2·rootMult x₀ a, 2·rootMult x₀ b + 1)`:
    `a(x)` contributes only even orders (via `x − x₀ = y²·u(x)` with
    `u(x₀) = 1/(3x₀² + A) ≠ 0`); `b(x)·y` contributes only odd orders.
    The two parities are disjoint so the min is exact.

    Conventions: when `a = 0` we omit the `2·rootMult x₀ a` slot
    (treat as `+∞`); similarly when `b = 0` we omit
    `2·rootMult x₀ b + 1`; if both are zero, we return `0` (the
    "ord of the zero divisor" placeholder used uniformly across the
    file). -/
noncomputable def ordAt_twoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if D.a = 0 ∧ D.b = 0 then 0
    else if D.a = 0 then 2 * rootMultiplicity P.1 D.b + 1
    else if D.b = 0 then 2 * rootMultiplicity P.1 D.a
    else min (2 * rootMultiplicity P.1 D.a) (2 * rootMultiplicity P.1 D.b + 1)

/-! ## Non-2-torsion: recursive lone/twin local order -/

/-- Auxiliary recursion with explicit fuel, used to define
    `ordAt_nonTwoTorsion` without a well-founded termination proof.

    `ordAt_nonTwoTorsion_aux fuel D P` agrees with the intended
    recursion as long as `fuel ≥ D.a.natDegree + D.b.natDegree + 1`.
    The wrapper `ordAt_nonTwoTorsion` always supplies enough fuel. -/
noncomputable def ordAt_nonTwoTorsion_aux :
    ℕ → CoordRingElt E.q → (ZMod E.q × ZMod E.q) → ℕ
  | 0,       _, _ => 0
  | fuel + 1, D, P =>
      if D.a = 0 ∧ D.b = 0 then 0
      else if D.eval P.1 P.2 ≠ 0 then 0
      else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
      else 1 + ordAt_nonTwoTorsion_aux fuel (D.divLin P.1) P

/-- Order of vanishing of `D = a − b·y` at a non-2-torsion point
    `P = (x₀, y₀)`, `y₀ ≠ 0`.

    Recursive trichotomy:
    * `D(P) ≠ 0`: ord = 0.
    * `D(P) = 0`, `D(P^σ) ≠ 0` (lone sheet): ord =
      `rootMultiplicity x₀ (normPoly E D)`.  This is correct because
      `ord_P(D) + ord_{P^σ}(D) = rootMult x₀ N(D)` (norm identity)
      and the second term is zero.
    * Both vanish (twin): `(X − x₀)` divides both `a` and `b`, write
      `D = (X − x₀) · D'`; since `ord_P(X − x₀) = 1` at non-2-torsion
      `P`, ord_P(D) = 1 + ord_P(D').  Recurse on `D' := D.divLin x₀`.

    The fuel-based implementation gives the value `0` if the
    recursion should keep firing past `D.degE + 1` steps (which
    cannot happen on F_q-rational `P` on `E` for nonzero `D`, but
    needs to be a Nat regardless). -/
noncomputable def ordAt_nonTwoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ :=
  ordAt_nonTwoTorsion_aux E (D.a.natDegree + D.b.natDegree + 1) D P

/-! ## Combined `ordAt` -/

/-- Order of vanishing of `D = a − b·y` at the affine F_q-rational
    point `P` of `E`.

    Dispatches to `ordAt_twoTorsion` when `P.2 = 0` and to
    `ordAt_nonTwoTorsion` otherwise.  Off `E` or for the zero divisor,
    returns `0` by convention.

    This replaces the earlier 0/1 placeholder, which was incompatible
    with the splitting-time identities `sum_ordAt_eq_natDegree_under_split`
    and `ordAt_group_sum_zero_under_split`.  The new definition agrees
    with the textbook ord_P from a chosen uniformizer (Silverman AEC II §1)
    via the closed-form / recursive recipes documented above. -/
noncomputable def ordAt (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if P ∈ E.points ∧ ¬ (D.a = 0 ∧ D.b = 0) then
      if P.2 = 0 then ordAt_twoTorsion E D P
      else ordAt_nonTwoTorsion E D P
    else 0

/-! ## Basic shape lemmas -/

/-- Off `E.points` or for the zero divisor, `ordAt` is `0`. -/
theorem ordAt_eq_zero_of_offE_or_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (h : ¬ (P ∈ E.points ∧ ¬ (D.a = 0 ∧ D.b = 0))) :
    ordAt E D P = 0 := by
  classical
  unfold ordAt
  rw [if_neg h]

/-- On-shell rewrite of `ordAt` into its case-split form. -/
theorem ordAt_eq_dispatch
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ordAt E D P =
      (if P.2 = 0 then ordAt_twoTorsion E D P
       else ordAt_nonTwoTorsion E D P) := by
  classical
  unfold ordAt
  rw [if_pos ⟨hP, hD⟩]

/-! ## Stage-2 lemma: non-vanishing implies `ordAt = 0`

This is the easy case of the local-order ↔ recursive-`ordAt`
compatibility (Stage 2 of the discharge plan in
`docs/divisorClass-discharge-plan.md`). On the project side,
non-vanishing of `D` at `P` collapses both branches of the
trichotomy: 2-torsion via `rootMultiplicity = 0`, non-2-torsion via
the early return `if D.eval ≠ 0 then 0`. -/

/-- For `P = (x₀, 0)` (2-torsion) with `D.eval x₀ 0 ≠ 0`,
`ordAt_twoTorsion` is `0`. -/
theorem ordAt_twoTorsion_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (h : D.eval x₀ 0 ≠ 0) :
    ordAt_twoTorsion E D (x₀, 0) = 0 := by
  classical
  have ha_ne : D.a.eval x₀ ≠ 0 := by
    have := h
    unfold CoordRingElt.eval at this
    simpa using this
  have hRootA : Polynomial.rootMultiplicity x₀ D.a = 0 :=
    Polynomial.rootMultiplicity_eq_zero ha_ne
  have ha_poly_ne : D.a ≠ 0 := by
    intro hzero
    apply ha_ne
    rw [hzero]; simp
  unfold ordAt_twoTorsion
  by_cases hb : D.b = 0
  · simp [ha_poly_ne, hb, hRootA]
  · simp [ha_poly_ne, hb, hRootA]

/-- For `P` non-2-torsion (`P.2 ≠ 0`) with `D.eval P.1 P.2 ≠ 0`,
`ordAt_nonTwoTorsion` is `0`. -/
theorem ordAt_nonTwoTorsion_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (h : D.eval P.1 P.2 ≠ 0) :
    ordAt_nonTwoTorsion E D P = 0 := by
  classical
  unfold ordAt_nonTwoTorsion ordAt_nonTwoTorsion_aux
  -- Fuel ≥ 1 here, so the recursion takes one step and returns 0
  -- via the second branch.
  by_cases hZero : D.a = 0 ∧ D.b = 0
  · -- D = 0: but then D.eval = 0, contradicting h.
    exfalso
    apply h
    obtain ⟨ha, hb⟩ := hZero
    unfold CoordRingElt.eval
    rw [ha, hb]; simp
  · simp [hZero, h]

/-- **Combined non-vanishing case**: `D.eval P.1 P.2 ≠ 0` forces
`ordAt E D P = 0`. -/
theorem ordAt_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points)
    (hEval : D.eval P.1 P.2 ≠ 0) :
    ordAt E D P = 0 := by
  classical
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := by
    intro ⟨ha, hb⟩
    apply hEval
    unfold CoordRingElt.eval
    rw [ha, hb]; simp
  rw [ordAt_eq_dispatch E D hP hD]
  by_cases h2 : P.2 = 0
  · rw [if_pos h2]
    -- P = (P.1, 0); apply 2-torsion lemma.
    have hPeq : P = (P.1, 0) := by
      ext <;> simp [h2]
    rw [hPeq]
    apply ordAt_twoTorsion_eq_zero_of_eval_ne_zero E D
    rw [show D.eval P.1 0 = D.eval P.1 P.2 from by rw [h2]]
    exact hEval
  · rw [if_neg h2]
    exact ordAt_nonTwoTorsion_eq_zero_of_eval_ne_zero E D hEval

/-! ### Symmetry of `ordAt_nonTwoTorsion_aux` for `D.b = 0`

For `D.b = 0`, the project's recursive `ordAt` has the property:
`ord(D, (x, y)) = ord(D, (x, -y))`. The reason is that
`D.eval x y = D.a.eval x` is independent of `y`, so the lone-sheet
branch never fires and the twin-sheet recursion produces equal values
on both sheets. -/

/-- `(D.divLin x).b = 0` whenever `D.b = 0`. -/
private theorem CoordRingElt.divLin_b_zero {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (hb : D.b = 0) (x : ZMod q) :
    (D.divLin x).b = 0 := by
  rw [CoordRingElt.divLin_b, hb, Polynomial.zero_divByMonic]

/-- For `D.b = 0`, `D.eval x y` is independent of `y`. -/
private theorem CoordRingElt.eval_b_zero
    (D : CoordRingElt E.q) (hb : D.b = 0) (x y₁ y₂ : ZMod E.q) :
    D.eval x y₁ = D.eval x y₂ := by
  unfold CoordRingElt.eval
  rw [hb]; simp

/-- For `D.b = 0`, `ordAt_nonTwoTorsion_aux` is symmetric in the
y-coordinate flip. -/
theorem ordAt_nonTwoTorsion_aux_symm_b_zero
    (fuel : ℕ) (D : CoordRingElt E.q) (hb : D.b = 0)
    (P : ZMod E.q × ZMod E.q) :
    ordAt_nonTwoTorsion_aux E fuel D P
      = ordAt_nonTwoTorsion_aux E fuel D (P.1, -P.2) := by
  classical
  induction fuel generalizing D with
  | zero => rfl
  | succ n IH =>
    -- Unfold both calls to the same level.
    show
      (if D.a = 0 ∧ D.b = 0 then 0
       else if D.eval P.1 P.2 ≠ 0 then 0
       else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
       else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P)
      =
      (if D.a = 0 ∧ D.b = 0 then 0
       else if D.eval P.1 (-P.2) ≠ 0 then 0
       else if D.eval P.1 (-(-P.2)) ≠ 0
              then rootMultiplicity P.1 (normPoly E D)
       else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) (P.1, -P.2))
    -- For D.b = 0, eval is independent of y.
    have hEvalEq : D.eval P.1 P.2 = D.eval P.1 (-P.2) :=
      CoordRingElt.eval_b_zero E D hb P.1 P.2 (-P.2)
    have hEvalEq' : D.eval P.1 (-P.2) = D.eval P.1 (-(-P.2)) :=
      CoordRingElt.eval_b_zero E D hb P.1 (-P.2) (-(-P.2))
    by_cases hD : D.a = 0 ∧ D.b = 0
    · rw [if_pos hD, if_pos hD]
    · rw [if_neg hD, if_neg hD]
      by_cases hVan : D.eval P.1 P.2 = 0
      · -- Both sheets vanish for D.b = 0.
        have hVan' : D.eval P.1 (-P.2) = 0 := by rw [← hEvalEq]; exact hVan
        have hVan'' : D.eval P.1 (-(-P.2)) = 0 := by rw [← hEvalEq']; exact hVan'
        rw [if_neg (not_not.mpr hVan), if_neg (not_not.mpr hVan'),
            if_neg (not_not.mpr hVan'), if_neg (not_not.mpr hVan'')]
        -- Both reduce to 1 + ord(D', P) and 1 + ord(D', P.σ); apply IH.
        have hb' : (D.divLin P.1).b = 0 :=
          CoordRingElt.divLin_b_zero D hb P.1
        have hIH := IH (D := D.divLin P.1) hb'
        omega
      · -- Both sheets non-vanishing for D.b = 0.
        push_neg at hVan
        have hVan' : D.eval P.1 (-P.2) ≠ 0 := by rw [← hEvalEq]; exact hVan
        rw [if_pos hVan, if_pos hVan']

end Divisor
