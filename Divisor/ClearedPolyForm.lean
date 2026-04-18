/-
  Divisor/ClearedPolyForm.lean

  Phase 1 of Steps 10'/11' (plan): polynomial form of `logDerivCheckFnCleared`.

  For fixed `A₀`, `logDerivCheckFnCleared E D P k B m A₀ A₁` is (up to a
  power of `A₁.1 - A₀.1`) a polynomial in the coordinates of `A₁`. This
  file defines that polynomial `clearedFiberPoly D P k B m A₀` as an
  element of `(ZMod E.q)[X][X]` (outer variable = `A₁.2`, inner variable
  = `A₁.1`), and establishes the denominator-cleared identity and the
  natDegree bound.

  The key quantitative output (consumed by Phase 2):
    * `clearedFiberPoly_identity`
        `bivEval (clearedFiberPoly ...) A₁ =
           (A₁.1 - A₀.1)^N · logDerivCheckFnCleared ... A₀ A₁`,
      witnessed on pairs with `A₁.1 ≠ A₀.1` (the valid challenge cone).
    * `clearedFiberPoly_natDegree_le`
        `(clearedFiberPoly ...).natDegree ≤ C · (D.degE + k)`.

  Paper reference: `sections/ec.tex:560-610` — the `G` polynomial in the
  proof of `cor:log-derivative`.
-/
import Divisor.Defs
import Divisor.LogDeriv
import Divisor.CubicIntersection
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

end Divisor
