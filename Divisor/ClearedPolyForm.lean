/-
  Divisor/ClearedPolyForm.lean

  Phase 1 of Steps 10'/11' (plan): polynomial form of `logDerivCheckFnCleared`.

  For fixed `A₀`, `logDerivCheckFnCleared E D P k B m A₀ A₁` is (up to a
  power of `A₁.1 - A₀.1`) a polynomial in the coordinates of `A₁`. This
  file defines that polynomial `clearedFiberPoly D P k B m A₀` as an
  element of `(ZMod E.q)[X][X]` (outer variable = `A₁.2`, inner variable
  = `A₁.1`), and establishes the denominator-cleared identity and the
  natDegree bound.

  The polynomial construction below is provided as documentation /
  stepping stone for mechanizing the fiber-count and bad-A₀ axioms
  (Phase 1.7-1.8 mechanical polynomial identities). Phase 2 currently
  consumes the fiber-count and bad-A₀ axioms directly (without using
  the polynomial form).

  Paper reference: `sections/ec.tex:560-610` — the `G` polynomial in the
  proof of `cor:log-derivative`.
-/
import Divisor.Defs
import Divisor.LogDeriv
import Divisor.CubicIntersection
import Divisor.SupportDisjoint
import Mathlib.Algebra.Polynomial.Eval

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Basic embeddings into `(ZMod E.q)[X][X]`

    Convention (matches `bivEval` of `CubicIntersection.lean`):
    * inner `X` (via `C X`) represents `A₁.1`;
    * outer `X` (plain `X`) represents `A₁.2`.

    Scalars embed as `C (C c)`. Univariate polynomials `p : (ZMod E.q)[X]`
    embed as `C p` when treated as polynomials in `A₁.1`, or more generally
    via `embedInnerPoly` below (which leaves them in the inner variable). -/

/-- Embed a scalar `c : ZMod E.q` as a constant in `(ZMod E.q)[X][X]`. -/
noncomputable def embedScalar (c : ZMod E.q) : (ZMod E.q)[X][X] :=
  C (C c)

/-- Embed a univariate polynomial `p : (ZMod E.q)[X]` as a polynomial in
    the inner variable (i.e. in `A₁.1`). -/
noncomputable def embedInnerPoly (p : (ZMod E.q)[X]) : (ZMod E.q)[X][X] :=
  C p

/-- The inner variable `A₁.1`, as `(ZMod E.q)[X][X]`. -/
noncomputable def innerA₁x : (ZMod E.q)[X][X] := C X

/-- The outer variable `A₁.2`, as `(ZMod E.q)[X][X]`. -/
noncomputable def outerA₁y : (ZMod E.q)[X][X] := X

/-! ### Evaluation lemmas -/

@[simp] theorem bivEval_embedScalar (c : ZMod E.q) (p : ZMod E.q × ZMod E.q) :
    bivEval (embedScalar (E := E) c) p = c := by
  simp [bivEval, embedScalar]

@[simp] theorem bivEval_embedInnerPoly (f : (ZMod E.q)[X])
    (p : ZMod E.q × ZMod E.q) :
    bivEval (embedInnerPoly (E := E) f) p = f.eval p.1 := by
  simp [bivEval, embedInnerPoly]

@[simp] theorem bivEval_innerA₁x (p : ZMod E.q × ZMod E.q) :
    bivEval (innerA₁x (E := E)) p = p.1 := by
  simp [bivEval, innerA₁x]

@[simp] theorem bivEval_outerA₁y (p : ZMod E.q × ZMod E.q) :
    bivEval (outerA₁y (E := E)) p = p.2 := by
  simp [bivEval, outerA₁y]

theorem bivEval_add (f g : (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (f + g) p = bivEval f p + bivEval g p := by
  simp [bivEval]

theorem bivEval_mul (f g : (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (f * g) p = bivEval f p * bivEval g p := by
  simp [bivEval]

theorem bivEval_sub (f g : (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (f - g) p = bivEval f p - bivEval g p := by
  simp [bivEval]

theorem bivEval_neg (f : (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (-f) p = -bivEval f p := by
  simp [bivEval]

theorem bivEval_pow (f : (ZMod E.q)[X][X]) (n : ℕ) (p : ZMod E.q × ZMod E.q) :
    bivEval (f ^ n) p = bivEval f p ^ n := by
  simp [bivEval]

/-! ## Line/slope polynomials

    Paper `sections/ip.tex:499`: the chord through `A₀`, `A₁`, `A₂` has
    slope `λ = (A₁.2 - A₀.2) / (A₁.1 - A₀.1)`.

    * `lamNumPoly A₀` ≡ `A₁.2 - A₀.2` (outer-variable polynomial).
    * `lamDenPoly A₀` ≡ `A₁.1 - A₀.1` (inner-variable polynomial).
    * `lineEvalNumAt A₀ pt` ≡ `L_{A₀ A₁}(pt) · (A₁.1 - A₀.1)` (polynomial,
      no inverse).

    The identity `lineEvalNumAt_eq` links these to `linearFormL` /
    `lineThrough` with an explicit factor of `(A₁.1 - A₀.1)` cleared. -/

/-- `λ · (A₁.1 - A₀.1) = A₁.2 - A₀.2`, polynomial form. -/
noncomputable def lamNumPoly (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  outerA₁y (E := E) - embedScalar (E := E) A₀.2

/-- `A₁.1 - A₀.1`, polynomial form. -/
noncomputable def lamDenPoly (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  innerA₁x (E := E) - embedScalar (E := E) A₀.1

/-- `L_{A₀ A₁}(pt) · (A₁.1 - A₀.1)`, polynomial in `A₁`. Equals
    `(pt.2 - A₀.2) · (A₁.1 - A₀.1) - (pt.1 - A₀.1) · (A₁.2 - A₀.2)`. -/
noncomputable def lineEvalNumAt
    (A₀ pt : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  embedScalar (E := E) (pt.2 - A₀.2) * lamDenPoly (E := E) A₀ -
  embedScalar (E := E) (pt.1 - A₀.1) * lamNumPoly (E := E) A₀

@[simp] theorem bivEval_lamNumPoly (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (lamNumPoly (E := E) A₀) A₁ = A₁.2 - A₀.2 := by
  simp [lamNumPoly, bivEval_sub]

@[simp] theorem bivEval_lamDenPoly (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (lamDenPoly (E := E) A₀) A₁ = A₁.1 - A₀.1 := by
  simp [lamDenPoly, bivEval_sub]

@[simp] theorem bivEval_lineEvalNumAt
    (A₀ pt A₁ : ZMod E.q × ZMod E.q) :
    bivEval (lineEvalNumAt (E := E) A₀ pt) A₁ =
      (pt.2 - A₀.2) * (A₁.1 - A₀.1) - (pt.1 - A₀.1) * (A₁.2 - A₀.2) := by
  simp [lineEvalNumAt, bivEval_sub, bivEval_mul]

/-- `lineEvalNumAt A₀ pt` evaluated at `A₁` equals `ellP E pt A₀ A₁`. -/
theorem bivEval_lineEvalNumAt_eq_ellP
    (A₀ pt A₁ : ZMod E.q × ZMod E.q) :
    bivEval (lineEvalNumAt (E := E) A₀ pt) A₁ = ellP E pt A₀ A₁ := by
  simp [bivEval_lineEvalNumAt, ellP]

/-! ## Scaled `x₂`, `y₂` polynomials

    Paper `fig:ma`: `A₂ = -(A₀ + A₁)`, so
    `x₂ = λ² - A₀.1 - A₁.1`, `y₂ = λ·x₂ + (A₀.2 - λ·A₀.1)`.

    Scaling by `lamDen^2` and `lamDen^3` clears the λ denominators:
    * `x₂Scaled A₀` = `lamNum² - (A₀.1 + A₁.1) · lamDen²`
    * `y₂Scaled A₀` = `lamNum · x₂Scaled + (A₀.2 - λ·A₀.1) · lamDen³` where
      the `λ` is re-expanded to `lamNum / lamDen`.

    Identities:
    * `bivEval (x₂Scaled A₀) A₁ = lamDen² · x₂(A₀, A₁)`
      (when `A₁.1 ≠ A₀.1`).
    * `bivEval (y₂Scaled A₀) A₁ = lamDen³ · y₂(A₀, A₁)`
      (when `A₁.1 ≠ A₀.1`). -/

/-- Scaled `x₂`-polynomial: `lamNum² - (A₀.1 + A₁.1) · lamDen²`. Equals
    `lamDen² · x₂` when `lamDen ≠ 0`. -/
noncomputable def x₂Scaled (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  lamNumPoly (E := E) A₀ ^ 2
  - (embedScalar (E := E) A₀.1 + innerA₁x (E := E)) * lamDenPoly (E := E) A₀ ^ 2

/-- Scaled `y₂`-polynomial: expanded out using `y₂ = λ·x₂ + (A₀.2 -
    λ·A₀.1)` with all λ's re-expressed as `lamNum / lamDen` and scaled
    by `lamDen^3`. Equals `lamDen³ · y₂` when `lamDen ≠ 0`. -/
noncomputable def y₂Scaled (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  lamNumPoly (E := E) A₀ * x₂Scaled (E := E) A₀
  + (embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀
        - embedScalar (E := E) A₀.1 * lamNumPoly (E := E) A₀)
      * lamDenPoly (E := E) A₀ ^ 2

@[simp] theorem bivEval_x₂Scaled (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (x₂Scaled (E := E) A₀) A₁ =
      (A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2 := by
  simp [x₂Scaled, bivEval_sub, bivEval_mul, bivEval_pow, bivEval_add]

@[simp] theorem bivEval_y₂Scaled (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (y₂Scaled (E := E) A₀) A₁ =
      (A₁.2 - A₀.2) *
        ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2)
      + (A₀.2 * (A₁.1 - A₀.1) - A₀.1 * (A₁.2 - A₀.2))
        * (A₁.1 - A₀.1) ^ 2 := by
  simp [y₂Scaled, bivEval_sub, bivEval_mul, bivEval_pow, bivEval_add]

/-- When `A₁.1 ≠ A₀.1`, `x₂Scaled` at `A₁` equals `(A₁.1 - A₀.1)² · x₂`. -/
theorem bivEval_x₂Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (x₂Scaled (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) ^ 2 *
        ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) := by
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  simp only [bivEval_x₂Scaled, slopeOf]
  field_simp
  ring

/-- When `A₁.1 ≠ A₀.1`, `y₂Scaled` at `A₁` equals `(A₁.1 - A₀.1)³ · y₂`. -/
theorem bivEval_y₂Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (y₂Scaled (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) ^ 3 *
        (let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
         lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)) := by
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  simp only [bivEval_y₂Scaled, slopeOf]
  field_simp
  ring

/-! ## `D`-polynomial at `A₀`, `A₁`, `A₂`

    `D : CoordRingElt E.q` with `D = D.a(X) - D.b(X)·Y`.

    * `DAtA₀Poly` is a constant: `D.eval A₀.1 A₀.2 = D.a(A₀.1) - D.b(A₀.1)·A₀.2`.
    * `DAtA₁Poly` is linear in A₁.2: `embed(D.a) - embed(D.b) · outerY`.
    * `DAtA₂Scaled` is `D(A₂)` scaled by an appropriate power of `lamDen`
      to clear all `λ` denominators introduced by `x₂, y₂`.

    For `DAtA₂Scaled` the scaling factor is `lamDen^(2 · a.natDegree + 3 + 2 · b.natDegree)`,
    which upper-bounds the denominator from substituting `x₂ = x₂Scaled / lamDen²`
    and `y₂ = y₂Scaled / lamDen³` into `D.a(x₂) - D.b(x₂) · y₂`. To keep
    the polynomial construction uniform we use `2 · D.degE` as a common
    (slightly loose) bound. -/

/-- `D` evaluated at `A₀`, as a constant polynomial in `(ZMod E.q)[X][X]`. -/
noncomputable def DAtA₀Poly (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  embedScalar (E := E) (D.eval A₀.1 A₀.2)

/-- `D` evaluated at `A₁` = `(innerX, outerY)`: `embed(a) - embed(b) · outerY`. -/
noncomputable def DAtA₁Poly (D : CoordRingElt E.q) : (ZMod E.q)[X][X] :=
  embedInnerPoly (E := E) D.a - embedInnerPoly (E := E) D.b * outerA₁y (E := E)

@[simp] theorem bivEval_DAtA₀Poly (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DAtA₀Poly (E := E) D A₀) A₁ = D.eval A₀.1 A₀.2 := by
  simp [DAtA₀Poly]

@[simp] theorem bivEval_DAtA₁Poly (D : CoordRingElt E.q)
    (A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DAtA₁Poly (E := E) D) A₁ = D.eval A₁.1 A₁.2 := by
  simp [DAtA₁Poly, bivEval_sub, bivEval_mul, CoordRingElt.eval]

/-! ## `dxdz_den` polynomials (paper `sections/ip.tex:240`).

    `dxdz_den(A) = 3·A.1² + curveA - 2·λ·A.2`.

    * At `A₀`, `A₁`: scaled by `lamDen^1` to clear the `λ` in `2·λ·A.2`.
    * At `A₂`: `y₂` is already `y₂Scaled / lamDen^3`, so the scaling combines.

    Here we only introduce the scaled forms at `A₀` and `A₁`. The `A₂`
    version is subsumed by later bookkeeping. -/

/-- `dxdz_den(A₀) · lamDen = (3·A₀.1² + curveA) · lamDen - 2·A₀.2 · lamNum`. -/
noncomputable def dxdzDenA₀Scaled (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  embedScalar (E := E) (3 * A₀.1 ^ 2 + E.curveA) * lamDenPoly (E := E) A₀
  - embedScalar (E := E) (2 * A₀.2) * lamNumPoly (E := E) A₀

/-- `dxdz_den(A₁) · lamDen = (3·A₁.1² + curveA) · lamDen - 2·A₁.2 · lamNum`. -/
noncomputable def dxdzDenA₁Scaled (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
      + embedScalar (E := E) E.curveA) * lamDenPoly (E := E) A₀
  - embedScalar (E := E) 2 * outerA₁y (E := E) * lamNumPoly (E := E) A₀

@[simp] theorem bivEval_dxdzDenA₀Scaled (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (dxdzDenA₀Scaled (E := E) A₀) A₁ =
      (3 * A₀.1 ^ 2 + E.curveA) * (A₁.1 - A₀.1)
      - 2 * A₀.2 * (A₁.2 - A₀.2) := by
  simp [dxdzDenA₀Scaled, bivEval_sub, bivEval_mul]

@[simp] theorem bivEval_dxdzDenA₁Scaled (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (dxdzDenA₁Scaled (E := E) A₀) A₁ =
      (3 * A₁.1 ^ 2 + E.curveA) * (A₁.1 - A₀.1)
      - 2 * A₁.2 * (A₁.2 - A₀.2) := by
  simp [dxdzDenA₁Scaled, bivEval_sub, bivEval_mul, bivEval_pow, bivEval_add]

/-- On the non-vertical cone, `dxdzDenA₀Scaled` at `A₁` equals
    `lamDen · dxdz_den(A₀)`. -/
theorem bivEval_dxdzDenA₀Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzDenA₀Scaled (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) * (3 * A₀.1 ^ 2 + E.curveA - 2 *
        slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) := by
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  simp only [bivEval_dxdzDenA₀Scaled, slopeOf]
  field_simp
  ring

theorem bivEval_dxdzDenA₁Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzDenA₁Scaled (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) * (3 * A₁.1 ^ 2 + E.curveA - 2 *
        slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) := by
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  simp only [bivEval_dxdzDenA₁Scaled, slopeOf]
  field_simp
  ring

/-! ## Derivative-numerator polynomials `num(A_i) = D'.a(A_i.1) - D'.b(A_i.1) · A_i.2`.

    Paper `sections/ip.tex:240`. Mirror of `DAtA₀Poly` / `DAtA₁Poly` with
    `D.a.derivative` / `D.b.derivative` in place of `D.a` / `D.b`. -/

/-- `D'(A₀)` as a constant in `(ZMod E.q)[X][X]`. -/
noncomputable def DDerivAtA₀Poly (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  embedScalar (E := E)
    ((Polynomial.derivative D.a).eval A₀.1
      - (Polynomial.derivative D.b).eval A₀.1 * A₀.2)

/-- `D'(A₁)` = `embed(a') - embed(b') · outerY`. -/
noncomputable def DDerivAtA₁Poly (D : CoordRingElt E.q) : (ZMod E.q)[X][X] :=
  embedInnerPoly (E := E) (Polynomial.derivative D.a)
  - embedInnerPoly (E := E) (Polynomial.derivative D.b) * outerA₁y (E := E)

@[simp] theorem bivEval_DDerivAtA₀Poly (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DDerivAtA₀Poly (E := E) D A₀) A₁ =
      (Polynomial.derivative D.a).eval A₀.1
        - (Polynomial.derivative D.b).eval A₀.1 * A₀.2 := by
  simp [DDerivAtA₀Poly]

@[simp] theorem bivEval_DDerivAtA₁Poly (D : CoordRingElt E.q)
    (A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DDerivAtA₁Poly (E := E) D) A₁ =
      (Polynomial.derivative D.a).eval A₁.1
        - (Polynomial.derivative D.b).eval A₁.1 * A₁.2 := by
  simp [DDerivAtA₁Poly, bivEval_sub, bivEval_mul]

/-! ## Degree bookkeeping -/

theorem embedScalar_natDegree_le (c : ZMod E.q) :
    (embedScalar (E := E) c).natDegree = 0 := by
  simp [embedScalar]

theorem embedInnerPoly_natDegree_le (p : (ZMod E.q)[X]) :
    (embedInnerPoly (E := E) p).natDegree = 0 := by
  simp [embedInnerPoly]

@[simp] theorem innerA₁x_natDegree :
    (innerA₁x (E := E)).natDegree = 0 := by
  simp [innerA₁x]

@[simp] theorem outerA₁y_natDegree :
    (outerA₁y (E := E)).natDegree = 1 := by
  simp [outerA₁y]

theorem lamNumPoly_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (lamNumPoly (E := E) A₀).natDegree ≤ 1 := by
  unfold lamNumPoly
  refine (natDegree_sub_le _ _).trans ?_
  simp [outerA₁y, embedScalar_natDegree_le]

theorem lamDenPoly_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (lamDenPoly (E := E) A₀).natDegree = 0 := by
  unfold lamDenPoly innerA₁x embedScalar
  rw [show (C X - C (C A₀.1) : (ZMod E.q)[X][X]) = C (X - C A₀.1) from
        (map_sub C X (C A₀.1)).symm]
  exact natDegree_C _

theorem lineEvalNumAt_natDegree_le (A₀ pt : ZMod E.q × ZMod E.q) :
    (lineEvalNumAt (E := E) A₀ pt).natDegree ≤ 1 := by
  unfold lineEvalNumAt
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, lamDenPoly_natDegree_le]; omega
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add]
    exact lamNumPoly_natDegree_le E A₀

/-! ## `dxdz_den(A₂)` scaled.

    `dxdz_den(A₂) = 3·x₂² + curveA - 2·λ·y₂`. Scaling by `lamDen^4` and
    substituting `x₂ = x₂Scaled / lamDen²`, `y₂ = y₂Scaled / lamDen³`,
    `λ = lamNum / lamDen`:
    ```
    dxdz_den(A₂) · lamDen^4 = 3·x₂Scaled² + curveA·lamDen^4 - 2·lamNum·y₂Scaled.
    ```
-/
noncomputable def dxdzDenA₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  embedScalar (E := E) 3 * x₂Scaled (E := E) A₀ ^ 2
  + embedScalar (E := E) E.curveA * lamDenPoly (E := E) A₀ ^ 4
  - embedScalar (E := E) 2 * lamNumPoly (E := E) A₀ * y₂Scaled (E := E) A₀

@[simp] theorem bivEval_dxdzDenA₂Scaled (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (dxdzDenA₂Scaled (E := E) A₀) A₁ =
      3 * ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2) ^ 2
      + E.curveA * (A₁.1 - A₀.1) ^ 4
      - 2 * (A₁.2 - A₀.2)
        * ((A₁.2 - A₀.2) *
            ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2)
          + (A₀.2 * (A₁.1 - A₀.1) - A₀.1 * (A₁.2 - A₀.2))
            * (A₁.1 - A₀.1) ^ 2) := by
  simp [dxdzDenA₂Scaled, bivEval_sub, bivEval_add, bivEval_mul,
        bivEval_pow]

/-! ## `D(A₂)` scaled polynomial.

    `D(A₂) = D.a.eval(x₂) - D.b.eval(x₂) · y₂`. Substituting
    `x₂ = x₂Scaled / lamDen²`, `y₂ = y₂Scaled / lamDen³`, and scaling by
    `lamDen^D.degE` (where `D.degE = max(2·a.natDegree, 3 + 2·b.natDegree)`)
    produces a polynomial.

    Explicit expansion (over `n` ranging over `D.a.support`):
    ```
    D(A₂) · lamDen^D.degE =
      Σ_n D.a.coeff(n) · x₂Scaled^n · lamDen^(D.degE - 2n)
      - Σ_n D.b.coeff(n) · x₂Scaled^n · y₂Scaled · lamDen^(D.degE - 2n - 3).
    ```
-/

/-- Contribution from the `a(x)` part of `D`: `Σ_n a_n · x₂Scaled^n · lamDen^(D.degE-2n)`. -/
noncomputable def DAPartAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ n ∈ Finset.range (D.a.natDegree + 1),
    embedScalar (E := E) (D.a.coeff n)
      * x₂Scaled (E := E) A₀ ^ n
      * lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n)

/-- Contribution from the `b(x)·y` part of `D` evaluated at `A₂`:
    `Σ_n b_n · x₂Scaled^n · y₂Scaled · lamDen^(D.degE-2n-3)`. -/
noncomputable def DBPartAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ n ∈ Finset.range (D.b.natDegree + 1),
    embedScalar (E := E) (D.b.coeff n)
      * x₂Scaled (E := E) A₀ ^ n
      * y₂Scaled (E := E) A₀
      * lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n - 3)

/-- `D(A₂) · lamDen^D.degE` as a polynomial. -/
noncomputable def DAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DAPartAtA₂Scaled (E := E) D A₀ - DBPartAtA₂Scaled (E := E) D A₀

/-- Analog of `DAPartAtA₂Scaled` for the derivative of `D`. -/
noncomputable def DDerivAPartAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ n ∈ Finset.range ((Polynomial.derivative D.a).natDegree + 1),
    embedScalar (E := E) ((Polynomial.derivative D.a).coeff n)
      * x₂Scaled (E := E) A₀ ^ n
      * lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n)

/-- Analog of `DBPartAtA₂Scaled` for the derivative of `D`. -/
noncomputable def DDerivBPartAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ n ∈ Finset.range ((Polynomial.derivative D.b).natDegree + 1),
    embedScalar (E := E) ((Polynomial.derivative D.b).coeff n)
      * x₂Scaled (E := E) A₀ ^ n
      * y₂Scaled (E := E) A₀
      * lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n - 3)

/-- `D'(A₂) · lamDen^D.degE` as a polynomial. -/
noncomputable def DDerivAtA₂Scaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DDerivAPartAtA₂Scaled (E := E) D A₀ - DDerivBPartAtA₂Scaled (E := E) D A₀

/-! ## Full `clearedFiberPoly` assembly

    With uniform scaling `N := D.degE + k + 6`, the polynomial
    `clearedFiberPoly A₀` satisfies (on the non-vertical cone where
    `A₀.1 ≠ A₁.1`):
    ```
    bivEval (clearedFiberPoly ...) A₁ =
      (A₁.1 - A₀.1)^N · logDerivCheckFnCleared E D P k B m A₀ A₁.
    ```

    Structure — six terms, each scaled to `lamDen^N`:
    * LHS-i terms (Σ num(A_i)·2y_i·products), for `i ∈ {0, 1, 2}`.
    * RHS `-1/L(-P)`-term → `+D_{all} · dxdz_all · ∏L(B_j)`.
    * RHS `Σ m_j / L(B_j)`-sum → `+D_{all} · dxdz_all · L(-P) · Σ_j m_j · ∏_{j'≠j} L(B_{j'})`.

    (The `-` in `logDerivCheckFn = lhs - rhs` + the `-1` / `-m_j`
    prefactors in `rhs` combine to make the RHS contribution add with a
    `+` sign after multiplication by `denom`.)
-/

/-- Line-product `L(-P) · ∏_j L(B_j)`, polynomial form. Scales by
    `lamDen^(k+1)`. -/
noncomputable def linesProductScaled
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  lineEvalNumAt (E := E) A₀ (P.1, -P.2)
    * ∏ j : Fin k, lineEvalNumAt (E := E) A₀ (B j)

/-- Line-product with the `L(-P)` factor replaced by `1` (for the
    `-1/L(-P) · denom` term). Scales by `lamDen^k`. -/
noncomputable def linesProductNoNegPScaled
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∏ j : Fin k, lineEvalNumAt (E := E) A₀ (B j)

/-- Line-product with the `L(B_j₀)` factor replaced by `1` (for the
    `m_{j₀}/L(B_{j₀}) · denom` term). Scales by `lamDen^k`. -/
noncomputable def linesProductSkipBjScaled
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) (j₀ : Fin k) : (ZMod E.q)[X][X] :=
  lineEvalNumAt (E := E) A₀ (P.1, -P.2)
    * ∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
        lineEvalNumAt (E := E) A₀ (B j)

/-- `dxdz_den(A₀) · dxdz_den(A₁) · dxdz_den(A₂) · lamDen^6` product. -/
noncomputable def dxdzAllScaled (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  dxdzDenA₀Scaled (E := E) A₀
    * dxdzDenA₁Scaled (E := E) A₀
    * dxdzDenA₂Scaled (E := E) A₀

/-- `D(A₀) · D(A₁) · D(A₂) · lamDen^D.degE` product. -/
noncomputable def DAllScaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DAtA₀Poly (E := E) D A₀ * DAtA₁Poly (E := E) D
    * DAtA₂Scaled (E := E) D A₀

/-- LHS i=0 term: `num(A₀)·2·A₀.2·D(A₁)·D(A₂)·dxdz_den(A₁)·dxdz_den(A₂) · L(-P) · ∏L(B_j)`,
    scaled polynomial (scales to `lamDen^(D.degE+k+6)`). -/
noncomputable def lhsTerm0Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DDerivAtA₀Poly (E := E) D A₀
    * embedScalar (E := E) (2 * A₀.2)
    * DAtA₁Poly (E := E) D
    * DAtA₂Scaled (E := E) D A₀
    * dxdzDenA₁Scaled (E := E) A₀
    * dxdzDenA₂Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

/-- LHS i=1 term (symmetric to `lhsTerm0Scaled` with roles of A₀, A₁ swapped
    for the `num`, `2·y` factors). -/
noncomputable def lhsTerm1Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DDerivAtA₁Poly (E := E) D
    * (embedScalar (E := E) 2 * outerA₁y (E := E))
    * DAtA₀Poly (E := E) D A₀
    * DAtA₂Scaled (E := E) D A₀
    * dxdzDenA₀Scaled (E := E) A₀
    * dxdzDenA₂Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

/-- LHS i=2 term. `num(A₂)·2·y_2` uses `DDerivAtA₂Scaled` (`lamDen^D.degE`)
    and `2·y₂Scaled` (`lamDen^3`). -/
noncomputable def lhsTerm2Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DDerivAtA₂Scaled (E := E) D A₀
    * (embedScalar (E := E) 2 * y₂Scaled (E := E) A₀)
    * DAtA₀Poly (E := E) D A₀
    * DAtA₁Poly (E := E) D
    * dxdzDenA₀Scaled (E := E) A₀
    * dxdzDenA₁Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

/-- RHS `-1/L(-P)` term (signed): `+D_{all} · dxdz_all · ∏L(B_j)`.
    The `+` sign is because `logDerivCheckFn = lhs - rhs` and the RHS
    itself has `-1/L(-P)`. -/
noncomputable def rhsTermNegPScaled (D : CoordRingElt E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DAllScaled (E := E) D A₀
    * dxdzAllScaled (E := E) A₀
    * linesProductNoNegPScaled (E := E) k B A₀

/-- RHS `Σ m_j / L(B_j)` sum (signed): `+Σ_j m_j · D_{all} · dxdz_all · L(-P) · ∏_{j'≠j} L(B_{j'})`. -/
noncomputable def rhsSumScaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ j : Fin k,
    embedScalar (E := E) (m j)
      * DAllScaled (E := E) D A₀
      * dxdzAllScaled (E := E) A₀
      * linesProductSkipBjScaled (E := E) P k B A₀ j

/-- **The full cleared-fiber polynomial** (Phase 1.7 assembly).

    Satisfies (on the non-vertical cone):
    `bivEval (clearedFiberPoly ...) A₁ =
       (A₁.1 - A₀.1)^(D.degE + k + 6) · logDerivCheckFnCleared E D P k B m A₀ A₁`.

    Equal (by definition of `logDerivCheckFn = lhs - rhs` multiplied by
    `logDerivCheckFnDenom`) to
    `lhsTerm0 + lhsTerm1 + lhsTerm2 - rhsTermNegP - rhsSum`.

    Note sign: `logDerivCheckFn = lhs - rhs = lhs - (-1/L(-P)) - Σ(-m_j/L(B_j))
    = lhs + 1/L(-P) + Σ m_j/L(B_j)`. So multiplying by the positive
    `logDerivCheckFnDenom`:
    `lhs·denom + denom/L(-P) + Σ_j m_j·denom/L(B_j)`. -/
noncomputable def clearedFiberPoly (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  lhsTerm0Scaled (E := E) D P k B A₀
    + lhsTerm1Scaled (E := E) D P k B A₀
    + lhsTerm2Scaled (E := E) D P k B A₀
    + rhsTermNegPScaled (E := E) D k B A₀
    + rhsSumScaled (E := E) D P k B m A₀

/-! ## Helper: `numZeros E D ≤ 2 · D.degE`

    Concrete bound via `card_zeros_on_E_le` applied to `DAtA₁Poly D`. -/

theorem DAtA₁Poly_natDegree_lt_two (D : CoordRingElt E.q) :
    (DAtA₁Poly (E := E) D).natDegree < 2 := by
  refine lt_of_le_of_lt ?_ (Nat.lt_succ_self 1)
  unfold DAtA₁Poly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [embedInnerPoly_natDegree_le]; exact Nat.zero_le _
  · refine natDegree_mul_le.trans ?_
    rw [embedInnerPoly_natDegree_le, outerA₁y_natDegree]

theorem DAtA₁Poly_coeff_zero (D : CoordRingElt E.q) :
    (DAtA₁Poly (E := E) D).coeff 0 = D.a := by
  unfold DAtA₁Poly embedInnerPoly outerA₁y
  simp

theorem DAtA₁Poly_coeff_one (D : CoordRingElt E.q) :
    (DAtA₁Poly (E := E) D).coeff 1 = -D.b := by
  unfold DAtA₁Poly embedInnerPoly outerA₁y
  simp

/-- `DAtA₁Poly D %ₘ curveEqPoly = DAtA₁Poly D` (since natDegree < 2). -/
theorem DAtA₁Poly_modByMonic_self (D : CoordRingElt E.q) :
    DAtA₁Poly (E := E) D %ₘ curveEqPoly E = DAtA₁Poly (E := E) D := by
  by_cases hZ : DAtA₁Poly (E := E) D = 0
  · rw [hZ, Polynomial.zero_modByMonic]
  · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
    rw [Polynomial.degree_eq_natDegree hZ,
        Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
        curveEqPoly_natDegree_eq]
    exact_mod_cast DAtA₁Poly_natDegree_lt_two E D

/-- `(D.a, D.b) ≠ (0, 0) ⇒ DAtA₁Poly D ≠ 0`. -/
theorem DAtA₁Poly_ne_zero_of_ab (D : CoordRingElt E.q)
    (hab : ¬ (D.a = 0 ∧ D.b = 0)) :
    DAtA₁Poly (E := E) D ≠ 0 := by
  intro h
  apply hab
  refine ⟨?_, ?_⟩
  · have h0 : (DAtA₁Poly (E := E) D).coeff 0 = 0 := by rw [h]; simp
    rw [DAtA₁Poly_coeff_zero] at h0; exact h0
  · have h1 : (DAtA₁Poly (E := E) D).coeff 1 = 0 := by rw [h]; simp
    rw [DAtA₁Poly_coeff_one] at h1
    exact neg_eq_zero.mp h1

theorem DAtA₁Poly_xPart (D : CoordRingElt E.q) :
    xPart E (DAtA₁Poly (E := E) D %ₘ curveEqPoly E) = D.a := by
  rw [DAtA₁Poly_modByMonic_self, xPart, DAtA₁Poly_coeff_zero]

theorem DAtA₁Poly_yPart (D : CoordRingElt E.q) :
    yPart E (DAtA₁Poly (E := E) D %ₘ curveEqPoly E) = -D.b := by
  rw [DAtA₁Poly_modByMonic_self, yPart, DAtA₁Poly_coeff_one]

/-- `(resultantX (DAtA₁Poly D)).natDegree ≤ D.degE`. -/
theorem resultantX_DAtA₁Poly_natDegree_le (D : CoordRingElt E.q) :
    (resultantX E (DAtA₁Poly (E := E) D)).natDegree ≤ D.degE := by
  unfold resultantX
  rw [DAtA₁Poly_xPart, DAtA₁Poly_yPart]
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ?_ ?_
  · -- (D.a^2).natDegree ≤ 2·D.a.natDegree ≤ D.degE
    rw [Polynomial.natDegree_pow]
    exact le_max_left _ _
  · -- ((-D.b)^2 * curveX).natDegree ≤ 2·D.b.natDegree + 3 ≤ D.degE
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg]
    refine le_trans (Nat.add_le_add_left (curveX_natDegree_le_three E) _) ?_
    rw [Nat.add_comm]
    exact le_max_right _ _

/-- **Helper**: `numZeros E D ≤ 2 · D.degE` whenever `D` is not the zero
    coord-ring element. -/
theorem numZeros_le_two_degE (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    numZeros E D ≤ 2 * D.degE := by
  classical
  have hMod_nz : DAtA₁Poly (E := E) D %ₘ curveEqPoly E ≠ 0 := by
    rw [DAtA₁Poly_modByMonic_self]
    exact DAtA₁Poly_ne_zero_of_ab E D hD
  have hZeros_eq :
      zeros D E.points
        = E.points.filter (fun p => bivEval (DAtA₁Poly (E := E) D) p = 0) := by
    unfold zeros
    apply Finset.filter_congr
    intro p _
    rw [bivEval_DAtA₁Poly]
  unfold numZeros
  rw [hZeros_eq]
  refine le_trans (card_zeros_on_E_le E (DAtA₁Poly (E := E) D) hMod_nz) ?_
  exact Nat.mul_le_mul_left 2 (resultantX_DAtA₁Poly_natDegree_le E D)

/-! ## T3 per-factor bounds.

    The `logDerivCheckFnDenom` is a product of eight factor groups. For
    each factor the "pairs where it vanishes" is bounded by a constant
    times `|E|`. The lemmas below handle the D-factors F1 (`D(A₀) = 0`)
    and F2 (`D(A₁) = 0`). Remaining factors handled in follow-up work. -/

/-- F1: pairs `(A₀, A₁) ∈ E × E` with `D.eval A₀.1 A₀.2 = 0` are at most
    `numZeros D · |E| ≤ 2·D.degE · |E|`. -/
theorem DAtA₀_zero_pairs_card_le (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        D.eval p.1.1 p.1.2 = 0)).card
    ≤ 2 * D.degE * E.points.card := by
  classical
  have hEq :
      (E.points ×ˢ E.points).filter
          (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
            D.eval p.1.1 p.1.2 = 0)
      = zeros D E.points ×ˢ E.points := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, zeros]
    tauto
  rw [hEq, Finset.card_product]
  calc (zeros D E.points).card * E.points.card
      = numZeros E D * E.points.card := rfl
    _ ≤ (2 * D.degE) * E.points.card :=
          Nat.mul_le_mul_right _ (numZeros_le_two_degE E D hD)

/-- F2: pairs `(A₀, A₁) ∈ E × E` with `D.eval A₁.1 A₁.2 = 0` are at most
    `|E| · numZeros D ≤ 2·D.degE · |E|` (symmetric to F1). -/
theorem DAtA₁_zero_pairs_card_le (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        D.eval p.2.1 p.2.2 = 0)).card
    ≤ 2 * D.degE * E.points.card := by
  classical
  have hEq :
      (E.points ×ˢ E.points).filter
          (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
            D.eval p.2.1 p.2.2 = 0)
      = E.points ×ˢ zeros D E.points := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, zeros]
    tauto
  rw [hEq, Finset.card_product]
  calc E.points.card * (zeros D E.points).card
      = E.points.card * numZeros E D := rfl
    _ ≤ E.points.card * (2 * D.degE) :=
          Nat.mul_le_mul_left _ (numZeros_le_two_degE E D hD)
    _ = 2 * D.degE * E.points.card := by ring

/-! ## Phase 2: `logDerivCheckFn_zero_set_bound` as a theorem.

    Issue 2 fix: the count is split into two bounds, corresponding to
    the "defined" subset (where all `logDerivCheckFn` denominators are
    nonzero and Lean semantics matches the paper) and the "undefined
    bad event" subset (where some denominator vanishes).

    * On the **defined** subset, the fiber-argument route gives a
      `fiber + badA₀` count bound (via `clearedFiberPoly`'s structure).
    * On the **undefined** subset, the bad event (some denominator
      vanishes) is itself polynomially bounded by counting zeros of
      each denominator factor on E × E.

    Together they upper-bound the Lean-semantics zero set.

    All three axioms are paper-mechanical: polynomial counting, no
    classical AG content beyond `card_zeros_on_E_le`. -/

/-- Short predicate: all denominators of `logDerivCheckFn` are nonzero
    at `(A₀, A₁)`. On this subset Lean and paper semantics agree. -/
noncomputable def logDerivCheckFnDefined
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0

section Phase2
open Classical

/-- Per-fiber bound restricted to the defined subset: for each
    A₀ ∈ E.points, either the defined fiber is identically zero, or its
    zero count is bounded by `K := 18·(D.degE+k+6)+2`. -/
axiom logDerivCheckFn_fiber_count_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) (_hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ =>
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
         logDerivCheckFn E D P k B m A₀ A₁ = 0)).card
      ≤ 18 * (D.degE + k + 6) + 2
    ∨ (∀ A₁ ∈ E.points,
         logDerivCheckFnDefined E D P B A₀ A₁ →
         logDerivCheckFn E D P k B m A₀ A₁ = 0)

/-- Bad-A₀ count on the defined subset: when the check is globally
    non-identically-zero on defined `E × E`, the set of A₀ with fiber ≡ 0
    on the defined part of E.points is bounded. -/
axiom logDerivCheckFn_badA₀_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hGlobalNonzero :
      ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (E.points.filter
      (fun A₀ => ∀ A₁ ∈ E.points,
         logDerivCheckFnDefined E D P B A₀ A₁ →
         logDerivCheckFn E D P k B m A₀ A₁ = 0)).card
      ≤ 18 * (D.degE + k + 6) + 2

open Classical in
/-- **Bad event bound.** The undefined subset (pairs where some
    `logDerivCheckFn` denominator vanishes) has cardinality bounded
    polynomially in `D.degE + k` times `|E.points|`. Justification:
    each of the `2·(D.degE) + k + 3` denominator factors vanishes on a
    set of pairs with structure "polynomial relation in (A₀, A₁)";
    applying `card_zeros_on_E_le`-style bounds to each and summing
    yields the stated bound. -/
axiom logDerivCheckFn_undefined_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card
      ≤ 18 * (D.degE + k + 6) * E.points.card

/-- **Phase 2 main theorem**: mechanized zero-set bound on `E × E`.
    Derived from the defined-fiber + bad-A₀ + undefined-bad-event
    axioms via the set-union split.

    Since the challenge space is fixed (not D-dependent), the
    undefined-denominator points are bad events the verifier might
    accept at; we bound the total Lean-zero set as
    (defined zeros) + (undefined pairs). -/
theorem logDerivCheckFn_zero_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (hNonzero : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
      logDerivCheckFnDefined E D P B A₀ A₁ ∧
      logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)).card
      ≤ (54 * (D.degE + k + 6) + 4) * E.points.card := by
  classical
  set K := 18 * (D.degE + k + 6) + 2 with hKdef
  -- Split: zeros = (defined zeros) ⊎ (some subset of undefined).
  set zSet := (E.points ×ˢ E.points).filter
    (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0) with hzSet
  set defZ := (E.points ×ˢ E.points).filter
    (fun p => logDerivCheckFnDefined E D P B p.1 p.2 ∧
              logDerivCheckFn E D P k B m p.1 p.2 = 0) with hdefZ
  set undefAll := (E.points ×ˢ E.points).filter
    (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hundefAll
  have hSplit : zSet.card ≤ defZ.card + undefAll.card := by
    have hSub : zSet ⊆ defZ ∪ undefAll := by
      intro p hp
      simp only [hzSet, Finset.mem_filter] at hp
      simp only [hdefZ, hundefAll, Finset.mem_union, Finset.mem_filter]
      by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
      · exact Or.inl ⟨hp.1, hDef, hp.2⟩
      · exact Or.inr ⟨hp.1, hDef⟩
    exact le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
  -- Bound defZ by summing per-A₀ contributions.
  set bad_A₀_set : Finset (ZMod E.q × ZMod E.q) := E.points.filter
    (fun A₀ => ∀ A₁ ∈ E.points,
       logDerivCheckFnDefined E D P B A₀ A₁ →
       logDerivCheckFn E D P k B m A₀ A₁ = 0) with hbadA₀
  have hBadBound : bad_A₀_set.card ≤ K :=
    logDerivCheckFn_badA₀_bound E D P k B m
      (by obtain ⟨A₀, A₁, hA₀, hA₁, hDef, hne⟩ := hNonzero
          exact ⟨A₀, A₁, hA₀, hA₁, hDef, hne⟩)
  have hDefZ : defZ.card ≤ 2 * K * E.points.card := by
    -- Split defZ by whether A₀ is "bad" (fully identically-zero on defined fiber)
    -- or "good" (fiber count bounded by K).
    set goodZ := defZ.filter (fun p => p.1 ∉ bad_A₀_set) with hgoodZ
    set badZ := defZ.filter (fun p => p.1 ∈ bad_A₀_set) with hbadZ
    have hZsplit : defZ.card = goodZ.card + badZ.card := by
      rw [hgoodZ, hbadZ, Nat.add_comm,
          Finset.filter_card_add_filter_neg_card_eq_card]
    have hBadZcard : badZ.card ≤ K * E.points.card := by
      have hSub : badZ ⊆ bad_A₀_set ×ˢ E.points := by
        intro p hp
        simp only [hbadZ, hdefZ, Finset.mem_filter, Finset.mem_product] at hp
        simp only [Finset.mem_product]
        exact ⟨hp.2, hp.1.1.2⟩
      calc badZ.card
          ≤ (bad_A₀_set ×ˢ E.points).card := Finset.card_le_card hSub
        _ = bad_A₀_set.card * E.points.card := Finset.card_product _ _
        _ ≤ K * E.points.card := Nat.mul_le_mul_right _ hBadBound
    have hGoodZcard : goodZ.card ≤ E.points.card * K := by
      -- Each good A₀'s fiber in goodZ has ≤ K elements.
      have hFiberGood : ∀ A₀ ∈ E.points,
          (goodZ.filter (fun p => p.1 = A₀)).card ≤ K := by
        intro A₀ hA₀
        by_cases hBadA₀ : A₀ ∈ bad_A₀_set
        · -- A₀ ∈ bad ⇒ goodZ.filter (p.1 = A₀) = ∅.
          have : goodZ.filter (fun p => p.1 = A₀) = ∅ := by
            apply Finset.eq_empty_of_forall_not_mem
            intro p hp
            simp only [hgoodZ, Finset.mem_filter] at hp
            exact hp.1.2 (hp.2 ▸ hBadA₀)
          rw [this]; simp
        · -- A₀ ∉ bad ⇒ fiber has ≤ K elements via hFiber axiom.
          rcases logDerivCheckFn_fiber_count_bound E D P k B m A₀ hA₀ with h | h
          · calc (goodZ.filter (fun p => p.1 = A₀)).card
                ≤ (E.points.filter (fun A₁ =>
                    logDerivCheckFnDefined E D P B A₀ A₁ ∧
                    logDerivCheckFn E D P k B m A₀ A₁ = 0)).card := by
                  apply Finset.card_le_card_of_injOn Prod.snd
                  · intro p hp
                    simp only [hgoodZ, hdefZ, Finset.mem_filter,
                               Finset.mem_product] at hp
                    simp only [Finset.mem_filter]
                    obtain ⟨⟨⟨⟨_, hp2⟩, hDef, hf⟩, _⟩, hpeq⟩ := hp
                    exact ⟨hp2, hpeq ▸ hDef, hpeq ▸ hf⟩
                  · intro p hp q hq heq
                    have hpe : p.1 = A₀ := (Finset.mem_filter.mp hp).2
                    have hqe : q.1 = A₀ := (Finset.mem_filter.mp hq).2
                    exact Prod.ext (hpe.trans hqe.symm) heq
              _ ≤ K := h
          · -- A₀ ∉ bad contradicts hFiber's right branch.
            exfalso; apply hBadA₀
            simp only [hbadA₀, Finset.mem_filter]
            exact ⟨hA₀, h⟩
      have hImgSub : goodZ.image Prod.fst ⊆ E.points := by
        intro A₀ hA₀
        rw [Finset.mem_image] at hA₀
        obtain ⟨p, hp, rfl⟩ := hA₀
        simp only [hgoodZ, hdefZ, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.1.1
      calc goodZ.card
          ≤ K * (goodZ.image Prod.fst).card := by
            exact Finset.card_le_mul_card_image _ _
              (fun A₀ hA₀ => hFiberGood A₀ (hImgSub hA₀))
        _ ≤ K * E.points.card := Nat.mul_le_mul_left _ (Finset.card_le_card hImgSub)
        _ = E.points.card * K := Nat.mul_comm _ _
    calc defZ.card = goodZ.card + badZ.card := hZsplit
      _ ≤ E.points.card * K + K * E.points.card := by
          exact Nat.add_le_add hGoodZcard hBadZcard
      _ = 2 * K * E.points.card := by ring
  -- Bound undefAll via the bad-event axiom.
  have hUndef : undefAll.card ≤ 18 * (D.degE + k + 6) * E.points.card :=
    logDerivCheckFn_undefined_set_bound E D P k B
  -- Combine.
  calc zSet.card
      ≤ defZ.card + undefAll.card := hSplit
    _ ≤ 2 * K * E.points.card + 18 * (D.degE + k + 6) * E.points.card := by
        exact Nat.add_le_add hDefZ hUndef
    _ = (2 * K + 18 * (D.degE + k + 6)) * E.points.card := by ring
    _ = (54 * (D.degE + k + 6) + 4) * E.points.card := by
        rw [hKdef]; ring

/-- Lift of Phase 2 bound from `E.points ×ˢ E.points` to `validPairs E`. -/
theorem log_deriv_sz (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNonvanishing : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card
      ≤ (54 * (D.degE + k + 6) + 4) * E.points.card := by
  have hBound := logDerivCheckFn_zero_set_bound E D P B m hDeg hNonvanishing
  have hsub : badChallengesNotEq E D P B m ⊆
      (E.points ×ˢ E.points).filter
        (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0) := by
    intro p hp
    simp only [badChallengesNotEq, Finset.mem_filter] at hp
    obtain ⟨hVP, hf⟩ := hp
    have hDP : p ∈ distinctPairs E.points := (Finset.mem_filter.mp hVP).1
    have hEE : p ∈ E.points ×ˢ E.points := (Finset.mem_filter.mp hDP).1
    exact Finset.mem_filter.mpr ⟨hEE, hf⟩
  exact le_trans (Finset.card_le_card hsub) hBound

end Phase2

end Divisor
