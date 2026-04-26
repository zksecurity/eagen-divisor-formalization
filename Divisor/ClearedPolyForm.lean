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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Eval.Irreducible

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

theorem bivEval_dxdzDenA₁Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzDenA₁Scaled (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) * (3 * A₁.1 ^ 2 + E.curveA - 2 *
        slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) := by
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  simp only [bivEval_dxdzDenA₁Scaled, slopeOf]
  field_simp

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

/-! ## Finset-sum bivEval identities

    The `DAtA₂Scaled`, `DDerivAtA₂Scaled` polynomials are expressed as
    Finset sums indexed by monomial degrees. Their bivEval values, on
    the non-vertical cone, collapse to `lamDen^D.degE · D.eval(x₂, y₂)`
    via per-term factor extraction. -/

/-- `bivEval` distributes over `Finset.sum`. -/
theorem bivEval_finset_sum {α : Type*} (s : Finset α)
    (f : α → (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (∑ i ∈ s, f i) p = ∑ i ∈ s, bivEval (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bivEval]
  | @insert _ _ h ih =>
      rw [Finset.sum_insert h, bivEval_add, Finset.sum_insert h, ih]

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

/-! ## Paper-faithful numerator polynomials

    The paper-faithful `logDerivTerm(A, λ)` has numerator
    `num_x(A) · (2·A.2) + num_y(A) · (3·A.1² + A_curve)` where
    `num_x = a'(x) − b'(x)·y` and `num_y = −b(x)`. We split the
    per-point numerator into an `x`-chain-rule piece (handled by the
    existing `DDeriv` polynomials) and a `y`-chain-rule correction
    piece (new below). -/

/-- `−b(A₀.1) · (3·A₀.1² + curveA)` as a scalar, embedded polynomially. -/
noncomputable def DBdydzAtA₀Poly (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  embedScalar (E := E) ((- D.b.eval A₀.1) * (3 * A₀.1 ^ 2 + E.curveA))

/-- `−b(A₁.1) · (3·A₁.1² + curveA)` as a polynomial in `(innerX, outerY)`. -/
noncomputable def DBdydzAtA₁Poly (D : CoordRingElt E.q) : (ZMod E.q)[X][X] :=
  (- embedInnerPoly (E := E) D.b)
    * (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
         + embedScalar (E := E) E.curveA)

/-! ### `D.b` at `A₂` scaled by `lamDen^(2·b.natDegree)` (tight).

    Needed for the `num_y(A₂) = −b(chordX₂)` correction term scaled
    polynomially.  Tight scaling `2·b.natDegree ≤ D.degE − 3` keeps
    the combined `lhsTerm2Scaled` factor (including dydz_num at A₂
    scaled by `lamDen^4` and the other factors totalling `lamDen^(k+3)`)
    within the uniform `lamDen^(D.degE+k+6)` budget. -/

/-- `b(chordX₂)` times `lamDen^(2·b.natDegree)`, as a polynomial. -/
noncomputable def DbAtA₂TightScaled (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  ∑ n ∈ Finset.range (D.b.natDegree + 1),
    embedScalar (E := E) (D.b.coeff n)
      * x₂Scaled (E := E) A₀ ^ n
      * lamDenPoly (E := E) A₀ ^ (2 * D.b.natDegree - 2 * n)

/-- `(3·chordX₂² + curveA) · lamDen^4`, as a polynomial. -/
noncomputable def dydzNumA₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  embedScalar (E := E) 3 * x₂Scaled (E := E) A₀ ^ 2
    + embedScalar (E := E) E.curveA * lamDenPoly (E := E) A₀ ^ 4

/- The `correctionA₂ScaledCore` below pads the intrinsic
    `lamDen^(2·b.natDegree + 4)` scaling of `-b(chordX₂)·(3·chordX₂²+A)`
    up to `lamDen^(D.degE + 1)` using the guaranteed margin
    `D.degE ≥ 2·b.natDegree + 3`. The lhsTerm2Scaled overall scaling is
    `(A-B)^(D.degE + k + 6)` — the correction contributes
    `(A-B)^(D.degE + 1)` and combines with the `dxdz(A₀)·dxdz(A₁)·lines`
    scaling `(A-B)^(k+3)` plus a factor `(A-B)^2` from factorisation,
    totalling `(A-B)^(D.degE + k + 6)`. See `bivEval_lhsTerm2Scaled_eq`. -/

/-- Combined scaled form: `−b(chordX₂) · (3·chordX₂² + curveA) · lamDen^(2·b.natDegree+4)`
    multiplied by `lamDen^(D.degE − 2·b.natDegree − 3)` to reach
    `lamDen^(D.degE + 1)` uniform scaling. Uses `Nat.sub` which pins to
    zero when `D.degE < 2·b.natDegree + 3`, but such `D` are excluded by
    the `D.degE ≥ 2·b.natDegree + 3` invariant. -/
noncomputable def correctionA₂ScaledCore (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  (- DbAtA₂TightScaled (E := E) D A₀)
    * dydzNumA₂Scaled (E := E) A₀
    * lamDenPoly (E := E) A₀ ^ (D.degE - 2 * D.b.natDegree - 3)

/-- LHS i=0 term: the OLD `num_x·2y` factor only (pre-correction). -/
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

/-- LHS i=1 term (old `num_x·2y` factor only). -/
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

/-- LHS i=2 term (old `num_x·2y` factor only). -/
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

/-! ### Correction terms

    The paper-faithful `logDerivTerm` adds a `num_y · dydz_num =
    -b(x)·(3x² + A)` numerator to the old `num_x · 2y`. In polynomial
    form, this contributes three correction summands (one per point),
    each at scaling `(A-B)^(D.degE+k+6)`. -/

/-- Correction for i=0: `-b(A₀.1)·(3·A₀.1²+A) · D(A₁)·D(A₂)·dxdz_den(A₁)·dxdz_den(A₂)·lines`.

    Padded by `lamDen^2` (absorbing the `lamDen^2` mismatch between the
    correction's natural `lamDen^(k+3)` scaling and target `lamDen^(k+5)`
    needed to match total `lamDen^(D.degE+k+6)` when combined with
    `DAtA₂Scaled`'s `lamDen^D.degE`). -/
noncomputable def correctionTerm0Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DBdydzAtA₀Poly (E := E) D A₀
    * DAtA₁Poly (E := E) D
    * DAtA₂Scaled (E := E) D A₀
    * dxdzDenA₁Scaled (E := E) A₀
    * dxdzDenA₂Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

/-- Correction for i=1. -/
noncomputable def correctionTerm1Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DBdydzAtA₁Poly (E := E) D
    * DAtA₀Poly (E := E) D A₀
    * DAtA₂Scaled (E := E) D A₀
    * dxdzDenA₀Scaled (E := E) A₀
    * dxdzDenA₂Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

/-- Correction for i=2. Uses `correctionA₂ScaledCore` (which has scaling
    `lamDen^(D.degE+1)` for `-b(chordX₂)·(3·chordX₂²+A)`) multiplied by
    `lamDen^2` via `dxdzDen(A₀)·dxdzDen(A₁)` scaling. Combined with
    `D(A₀)·D(A₁)·lines`, total scaling `lamDen^(D.degE+k+4)`.
    We pad by multiplying with `lamDenPoly^2` to reach `lamDen^(D.degE+k+6)`. -/
noncomputable def correctionTerm2Scaled (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  correctionA₂ScaledCore (E := E) D A₀
    * DAtA₀Poly (E := E) D A₀
    * DAtA₁Poly (E := E) D
    * dxdzDenA₀Scaled (E := E) A₀
    * dxdzDenA₁Scaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀
    * lamDenPoly (E := E) A₀ ^ 2

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
    + correctionTerm0Scaled (E := E) D P k B A₀
    + correctionTerm1Scaled (E := E) D P k B A₀
    + correctionTerm2Scaled (E := E) D P k B A₀
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

/-! ### Chord-case `x₂, y₂` formulas

    `logDerivCheckFn` and `logDerivCheckFnDenom` use `x₂ := λ² − A₀.1 − A₁.1`,
    `y₂ := λ · x₂ + (A₀.2 − λ · A₀.1)` with `λ := slopeOf A₀ A₁`. On the
    non-vertical cone (`A₀.1 ≠ A₁.1`) these match `thirdPoint E A₀ A₁` as
    an affine point. -/

/-- Chord-case `x₂` formula. -/
noncomputable def chordX₂ {q : ℕ} [Fact (Nat.Prime q)]
    (A₀ A₁ : ZMod q × ZMod q) : ZMod q :=
  (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)^2 - A₀.1 - A₁.1

/-- Chord-case `y₂` formula. -/
noncomputable def chordY₂ {q : ℕ} [Fact (Nat.Prime q)]
    (A₀ A₁ : ZMod q × ZMod q) : ZMod q :=
  slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * chordX₂ A₀ A₁
    + (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)

/-- On non-vertical pairs (`A₀.1 ≠ A₁.1`), `thirdPoint E A₀ A₁` is the
    affine point `(chordX₂ A₀ A₁, chordY₂ A₀ A₁)`. -/
theorem thirdPoint_of_xne (A₀ A₁ : ZMod E.q × ZMod E.q) (h : A₀.1 ≠ A₁.1) :
    thirdPoint E A₀ A₁ = ECPoint.affine (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) := by
  simp only [thirdPoint, chordX₂, chordY₂, slopeOf, if_neg h]

/-! ### Symmetry of slope, chord, and line under `A₀ ↔ A₁` swap

    `slopeOf`, `chordX₂`, `chordY₂`, and `lineThrough` are symmetric in the
    pair `(A₀, A₁)` (with the latter two requiring `A₀.1 ≠ A₁.1`).
    These facts flow through to symmetry of `logDerivCheckFnDenom` and
    `logDerivCheckFn` on the non-vertical cone, which is needed by T2. -/

theorem slopeOf_symm (x₀ y₀ x₁ y₁ : ZMod E.q) :
    slopeOf x₀ y₀ x₁ y₁ = slopeOf x₁ y₁ x₀ y₀ := by
  unfold slopeOf
  by_cases h : x₀ = x₁
  · subst h
    have hzero : (x₀ - x₀ : ZMod E.q) = 0 := sub_self x₀
    rw [hzero]; simp
  · rw [show (x₀ - x₁ : ZMod E.q) = -(x₁ - x₀) from by ring, inv_neg]
    ring

theorem chordX₂_symm (A₀ A₁ : ZMod E.q × ZMod E.q) :
    chordX₂ A₀ A₁ = chordX₂ A₁ A₀ := by
  unfold chordX₂
  rw [slopeOf_symm E A₀.1 A₀.2 A₁.1 A₁.2]; ring

theorem chordY₂_symm (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    chordY₂ A₀ A₁ = chordY₂ A₁ A₀ := by
  unfold chordY₂
  have hslope := slopeOf_symm E A₀.1 A₀.2 A₁.1 A₁.2
  have hchord := chordX₂_symm E A₀ A₁
  rw [hslope, hchord]
  -- Need: lam' · cx + (A₀.2 - lam' · A₀.1) = lam' · cx + (A₁.2 - lam' · A₁.1).
  -- Suffices: A₀.2 - lam' · A₀.1 = A₁.2 - lam' · A₁.1, i.e., lam' · (A₁.1 - A₀.1) = A₁.2 - A₀.2.
  set lam' := slopeOf A₁.1 A₁.2 A₀.1 A₀.2 with hlam_def
  have hcancel : lam' * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    have hne : (A₀.1 - A₁.1 : ZMod E.q) ≠ 0 := sub_ne_zero.mpr hNV
    simp only [hlam_def, slopeOf]
    field_simp
    ring
  linear_combination hcancel

theorem lineThrough_symm (x₀ y₀ x₁ y₁ : ZMod E.q) (h : x₀ ≠ x₁) :
    lineThrough x₀ y₀ x₁ y₁ = lineThrough x₁ y₁ x₀ y₀ := by
  unfold lineThrough
  refine Line.mk.injEq .. |>.mpr ⟨?_, ?_⟩
  · exact slopeOf_symm E x₀ y₀ x₁ y₁
  · have hslope := slopeOf_symm E x₀ y₀ x₁ y₁
    rw [hslope]
    have hcancel : slopeOf x₁ y₁ x₀ y₀ * (x₁ - x₀) = y₁ - y₀ := by
      unfold slopeOf
      have hne : (x₀ - x₁ : ZMod E.q) ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring
    linear_combination hcancel

/-! ## Finset-sum bivEval identities for D@A₂ parts

    The `DAtA₂Scaled`, `DDerivAtA₂Scaled` polynomials are Finset sums
    indexed by monomial degrees. Their bivEval values, on the
    non-vertical cone with `A₀.1 ≠ A₁.1`, collapse to
    `lamDen^D.degE · D.eval(chordX₂, chordY₂)` via per-term factor
    extraction. -/

/-- On the non-vertical cone, `bivEval (DAPartAtA₂Scaled D A₀) A₁`
    equals `(A₁.1 − A₀.1)^D.degE · D.a.eval (chordX₂ A₀ A₁)`. -/
theorem bivEval_DAPartAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DAPartAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE * D.a.eval (chordX₂ A₀ A₁) := by
  unfold DAPartAtA₂Scaled
  rw [bivEval_finset_sum, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h2nle : 2 * n ≤ D.degE := by
    have hn' : n ≤ D.a.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    unfold CoordRingElt.degE
    omega
  simp only [bivEval_mul, bivEval_pow, bivEval_embedScalar, bivEval_lamDenPoly,
             bivEval_x₂Scaled_eq _ _ _ hNV]
  unfold chordX₂
  have hpow : (A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)
            = (A₁.1 - A₀.1) ^ D.degE := by
    rw [← pow_add]; congr 1; omega
  have hsq : ((A₁.1 - A₀.1) ^ 2) ^ n = (A₁.1 - A₀.1) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  calc D.a.coeff n * ((A₁.1 - A₀.1) ^ 2 *
          ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)) ^ n
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)
      = D.a.coeff n
         * (((A₁.1 - A₀.1) ^ 2) ^ n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n) := by rw [mul_pow]
    _ = D.a.coeff n
         * ((A₁.1 - A₀.1) ^ (2 * n)
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n) := by rw [hsq]
    _ = D.a.coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * ((A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)) := by ring
    _ = D.a.coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * (A₁.1 - A₀.1) ^ D.degE := by rw [hpow]
    _ = (A₁.1 - A₀.1) ^ D.degE
         * (D.a.coeff n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n) := by ring

/-- On the non-vertical cone, `bivEval (DBPartAtA₂Scaled D A₀) A₁`
    equals `(A₁.1 − A₀.1)^D.degE · D.b.eval (chordX₂ A₀ A₁) · chordY₂ A₀ A₁`. -/
theorem bivEval_DBPartAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DBPartAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE * D.b.eval (chordX₂ A₀ A₁) * chordY₂ A₀ A₁ := by
  unfold DBPartAtA₂Scaled
  rw [bivEval_finset_sum, Polynomial.eval_eq_sum_range, mul_assoc,
      Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h2n3le : 2 * n + 3 ≤ D.degE := by
    have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    unfold CoordRingElt.degE
    omega
  simp only [bivEval_mul, bivEval_pow, bivEval_embedScalar, bivEval_lamDenPoly,
             bivEval_x₂Scaled_eq _ _ _ hNV,
             bivEval_y₂Scaled_eq _ _ _ hNV]
  unfold chordY₂ chordX₂ slopeOf
  have hpow : (A₁.1 - A₀.1) ^ (2 * n)
              * (A₁.1 - A₀.1) ^ 3
              * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)
            = (A₁.1 - A₀.1) ^ D.degE := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hsq : ((A₁.1 - A₀.1) ^ 2) ^ n = (A₁.1 - A₀.1) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  set lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
  calc D.b.coeff n
        * ((A₁.1 - A₀.1) ^ 2 * (lam ^ 2 - A₀.1 - A₁.1)) ^ n
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)
      = D.b.coeff n
        * (((A₁.1 - A₀.1) ^ 2) ^ n * (lam ^ 2 - A₀.1 - A₁.1) ^ n)
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3) := by rw [mul_pow]
    _ = D.b.coeff n
        * ((A₁.1 - A₀.1) ^ (2 * n) * (lam ^ 2 - A₀.1 - A₁.1) ^ n)
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3) := by rw [hsq]
    _ = D.b.coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
         * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
         * ((A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ 3
             * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)) := by ring
    _ = D.b.coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
         * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
         * (A₁.1 - A₀.1) ^ D.degE := by rw [hpow]
    _ = (A₁.1 - A₀.1) ^ D.degE
         * (D.b.coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
             * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))) := by ring

/-- On the non-vertical cone, `bivEval DAtA₂Scaled` equals
    `(A₁.1 − A₀.1)^D.degE · D.eval (chordX₂, chordY₂)`. -/
theorem bivEval_DAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE *
          D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) := by
  unfold DAtA₂Scaled CoordRingElt.eval
  rw [bivEval_sub, bivEval_DAPartAtA₂Scaled_eq E D A₀ A₁ hNV,
      bivEval_DBPartAtA₂Scaled_eq E D A₀ A₁ hNV]
  ring

theorem bivEval_DDerivAPartAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DDerivAPartAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE *
          (Polynomial.derivative D.a).eval (chordX₂ A₀ A₁) := by
  unfold DDerivAPartAtA₂Scaled
  rw [bivEval_finset_sum, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h2nle : 2 * n ≤ D.degE := by
    have hn' : n ≤ (Polynomial.derivative D.a).natDegree :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hda : (Polynomial.derivative D.a).natDegree ≤ D.a.natDegree :=
      (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
    have : n ≤ D.a.natDegree := hn'.trans hda
    unfold CoordRingElt.degE
    omega
  simp only [bivEval_mul, bivEval_pow, bivEval_embedScalar, bivEval_lamDenPoly,
             bivEval_x₂Scaled_eq _ _ _ hNV]
  unfold chordX₂
  have hpow : (A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)
            = (A₁.1 - A₀.1) ^ D.degE := by
    rw [← pow_add]; congr 1; omega
  have hsq : ((A₁.1 - A₀.1) ^ 2) ^ n = (A₁.1 - A₀.1) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  calc (Polynomial.derivative D.a).coeff n
          * ((A₁.1 - A₀.1) ^ 2 *
              ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)) ^ n
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)
      = (Polynomial.derivative D.a).coeff n
         * (((A₁.1 - A₀.1) ^ 2) ^ n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n) := by rw [mul_pow]
    _ = (Polynomial.derivative D.a).coeff n
         * ((A₁.1 - A₀.1) ^ (2 * n)
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (D.degE - 2 * n) := by rw [hsq]
    _ = (Polynomial.derivative D.a).coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * ((A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ (D.degE - 2 * n)) := by ring
    _ = (Polynomial.derivative D.a).coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * (A₁.1 - A₀.1) ^ D.degE := by rw [hpow]
    _ = (A₁.1 - A₀.1) ^ D.degE
         * ((Polynomial.derivative D.a).coeff n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n) := by ring

theorem bivEval_DDerivBPartAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DDerivBPartAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE *
          (Polynomial.derivative D.b).eval (chordX₂ A₀ A₁) *
          chordY₂ A₀ A₁ := by
  unfold DDerivBPartAtA₂Scaled
  rw [bivEval_finset_sum, Polynomial.eval_eq_sum_range, mul_assoc,
      Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h2n3le : 2 * n + 3 ≤ D.degE := by
    have hn' : n ≤ (Polynomial.derivative D.b).natDegree :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hdb : (Polynomial.derivative D.b).natDegree ≤ D.b.natDegree :=
      (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
    have : n ≤ D.b.natDegree := hn'.trans hdb
    unfold CoordRingElt.degE
    omega
  simp only [bivEval_mul, bivEval_pow, bivEval_embedScalar, bivEval_lamDenPoly,
             bivEval_x₂Scaled_eq _ _ _ hNV,
             bivEval_y₂Scaled_eq _ _ _ hNV]
  unfold chordY₂ chordX₂ slopeOf
  have hpow : (A₁.1 - A₀.1) ^ (2 * n)
              * (A₁.1 - A₀.1) ^ 3
              * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)
            = (A₁.1 - A₀.1) ^ D.degE := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hsq : ((A₁.1 - A₀.1) ^ 2) ^ n = (A₁.1 - A₀.1) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  set lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
  calc (Polynomial.derivative D.b).coeff n
        * ((A₁.1 - A₀.1) ^ 2 * (lam ^ 2 - A₀.1 - A₁.1)) ^ n
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)
      = (Polynomial.derivative D.b).coeff n
        * (((A₁.1 - A₀.1) ^ 2) ^ n * (lam ^ 2 - A₀.1 - A₁.1) ^ n)
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3) := by rw [mul_pow]
    _ = (Polynomial.derivative D.b).coeff n
        * ((A₁.1 - A₀.1) ^ (2 * n) * (lam ^ 2 - A₀.1 - A₁.1) ^ n)
        * ((A₁.1 - A₀.1) ^ 3 *
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
        * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3) := by rw [hsq]
    _ = (Polynomial.derivative D.b).coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
         * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
         * ((A₁.1 - A₀.1) ^ (2 * n) * (A₁.1 - A₀.1) ^ 3
             * (A₁.1 - A₀.1) ^ (D.degE - 2 * n - 3)) := by ring
    _ = (Polynomial.derivative D.b).coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
         * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
         * (A₁.1 - A₀.1) ^ D.degE := by rw [hpow]
    _ = (A₁.1 - A₀.1) ^ D.degE
         * ((Polynomial.derivative D.b).coeff n * (lam ^ 2 - A₀.1 - A₁.1) ^ n
             * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))) := by ring

theorem bivEval_DDerivAtA₂Scaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DDerivAtA₂Scaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE *
          ((Polynomial.derivative D.a).eval (chordX₂ A₀ A₁)
            - (Polynomial.derivative D.b).eval (chordX₂ A₀ A₁) * chordY₂ A₀ A₁) := by
  unfold DDerivAtA₂Scaled
  rw [bivEval_sub,
      bivEval_DDerivAPartAtA₂Scaled_eq E D A₀ A₁ hNV,
      bivEval_DDerivBPartAtA₂Scaled_eq E D A₀ A₁ hNV]
  ring

/-- On the non-vertical cone, `bivEval (dxdzDenA₂Scaled A₀) A₁` equals
    `(A₁.1 - A₀.1)^4 · (3·chordX₂² + curveA - 2·slopeOf·chordY₂)`. -/
theorem bivEval_dxdzDenA₂Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzDenA₂Scaled (E := E) A₀) A₁
      = (A₁.1 - A₀.1) ^ 4 *
          (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * chordY₂ A₀ A₁) := by
  rw [bivEval_dxdzDenA₂Scaled]
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  have hlam : slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    unfold slopeOf; field_simp
  have hX₂ : chordX₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 2
      = (A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (A₀.1 + A₁.1) := by
    unfold chordX₂
    linear_combination
      (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) + (A₁.2 - A₀.2)) * hlam
  have hY₂ : chordY₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 3
      = (A₁.2 - A₀.2) *
          ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (2 * A₀.1 + A₁.1))
        + A₀.2 * (A₁.1 - A₀.1) ^ 3 := by
    unfold chordY₂ chordX₂
    linear_combination
      ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 * (A₁.1 - A₀.1) ^ 2
        + slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) * (A₁.2 - A₀.2)
        + (A₁.2 - A₀.2) ^ 2
        - (2 * A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2) * hlam
  linear_combination
    (-3 * ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (A₀.1 + A₁.1)
            + chordX₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 2)) * hX₂
    + (2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1)) * hY₂
    + 2 * ((A₁.2 - A₀.2) *
            ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (2 * A₀.1 + A₁.1))
           + A₀.2 * (A₁.1 - A₀.1) ^ 3) * hlam

/-! ## BivEval of paper-faithful correction polynomials -/

@[simp] theorem bivEval_DBdydzAtA₀Poly (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DBdydzAtA₀Poly (E := E) D A₀) A₁
      = (- D.b.eval A₀.1) * (3 * A₀.1 ^ 2 + E.curveA) := by
  simp [DBdydzAtA₀Poly]

@[simp] theorem bivEval_DBdydzAtA₁Poly (D : CoordRingElt E.q)
    (A₁ : ZMod E.q × ZMod E.q) :
    bivEval (DBdydzAtA₁Poly (E := E) D) A₁
      = (- D.b.eval A₁.1) * (3 * A₁.1 ^ 2 + E.curveA) := by
  simp [DBdydzAtA₁Poly, bivEval_mul, bivEval_add, bivEval_neg, bivEval_pow]

/-- On non-vertical pairs, `bivEval DbAtA₂TightScaled A₁
      = (A₁.1 - A₀.1)^(2·b.natDegree) · b(chordX₂)`. -/
theorem bivEval_DbAtA₂TightScaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DbAtA₂TightScaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ (2 * D.b.natDegree) * D.b.eval (chordX₂ A₀ A₁) := by
  unfold DbAtA₂TightScaled
  rw [bivEval_finset_sum, Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have h2nle : 2 * n ≤ 2 * D.b.natDegree := by
    have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    omega
  simp only [bivEval_mul, bivEval_pow, bivEval_embedScalar, bivEval_lamDenPoly,
             bivEval_x₂Scaled_eq _ _ _ hNV]
  unfold chordX₂
  have hpow : (A₁.1 - A₀.1) ^ (2 * n)
              * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree - 2 * n)
            = (A₁.1 - A₀.1) ^ (2 * D.b.natDegree) := by
    rw [← pow_add]; congr 1; omega
  have hsq : ((A₁.1 - A₀.1) ^ 2) ^ n = (A₁.1 - A₀.1) ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm]
  calc D.b.coeff n * ((A₁.1 - A₀.1) ^ 2 *
          ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)) ^ n
         * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree - 2 * n)
      = D.b.coeff n
         * (((A₁.1 - A₀.1) ^ 2) ^ n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree - 2 * n) := by rw [mul_pow]
    _ = D.b.coeff n
         * ((A₁.1 - A₀.1) ^ (2 * n)
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n)
         * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree - 2 * n) := by rw [hsq]
    _ = D.b.coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * ((A₁.1 - A₀.1) ^ (2 * n)
             * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree - 2 * n)) := by ring
    _ = D.b.coeff n
         * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n
         * (A₁.1 - A₀.1) ^ (2 * D.b.natDegree) := by rw [hpow]
    _ = (A₁.1 - A₀.1) ^ (2 * D.b.natDegree)
         * (D.b.coeff n
             * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) ^ n) := by ring

/-- On non-vertical pairs, `bivEval dydzNumA₂Scaled A₁
      = (A₁.1 - A₀.1)^4 · (3·chordX₂² + E.curveA)`. -/
theorem bivEval_dydzNumA₂Scaled_eq (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dydzNumA₂Scaled (E := E) A₀) A₁
      = (A₁.1 - A₀.1) ^ 4 * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA) := by
  unfold dydzNumA₂Scaled
  simp only [bivEval_add, bivEval_mul, bivEval_embedScalar, bivEval_pow,
             bivEval_x₂Scaled_eq _ _ _ hNV, bivEval_lamDenPoly]
  -- After substitution: 3·((A₁.1-A₀.1)^2 · ((λ²-A₀.1-A₁.1)))² + curveA·(A₁.1-A₀.1)^4
  --   = (A₁.1-A₀.1)^4 · (3·chordX₂² + curveA)
  -- `chordX₂` on RHS matches by definition after unfolding.
  show 3 * ((A₁.1 - A₀.1) ^ 2
          * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)) ^ 2
        + E.curveA * (A₁.1 - A₀.1) ^ 4
      = (A₁.1 - A₀.1) ^ 4 * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)
  unfold chordX₂
  ring

/-- On non-vertical pairs, `bivEval correctionA₂ScaledCore A₁
      = (A₁.1-A₀.1)^(D.degE+1) · (-b(chordX₂))·(3·chordX₂²+E.curveA)`. -/
theorem bivEval_correctionA₂ScaledCore_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (correctionA₂ScaledCore (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + 1) *
          ((- D.b.eval (chordX₂ A₀ A₁)) * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)) := by
  unfold correctionA₂ScaledCore
  simp only [bivEval_mul, bivEval_neg, bivEval_pow, bivEval_lamDenPoly,
             bivEval_DbAtA₂TightScaled_eq _ _ _ _ hNV,
             bivEval_dydzNumA₂Scaled_eq _ _ _ hNV]
  have hb_le : 2 * D.b.natDegree + 3 ≤ D.degE := by
    unfold CoordRingElt.degE
    omega
  have hpow : (A₁.1 - A₀.1) ^ (2 * D.b.natDegree) * (A₁.1 - A₀.1) ^ 4
              * (A₁.1 - A₀.1) ^ (D.degE - 2 * D.b.natDegree - 3)
            = (A₁.1 - A₀.1) ^ (D.degE + 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  calc _
      = (- ((A₁.1 - A₀.1) ^ (2 * D.b.natDegree) * D.b.eval (chordX₂ A₀ A₁)))
          * ((A₁.1 - A₀.1) ^ 4 * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA))
          * (A₁.1 - A₀.1) ^ (D.degE - 2 * D.b.natDegree - 3) := rfl
    _ = ((A₁.1 - A₀.1) ^ (2 * D.b.natDegree) * (A₁.1 - A₀.1) ^ 4
           * (A₁.1 - A₀.1) ^ (D.degE - 2 * D.b.natDegree - 3)) *
        ((- D.b.eval (chordX₂ A₀ A₁)) * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)) := by
        ring
    _ = (A₁.1 - A₀.1) ^ (D.degE + 1) *
        ((- D.b.eval (chordX₂ A₀ A₁)) * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)) := by
        rw [hpow]

/-! ## helpers: line-product bivEval extractions

    On the non-vertical cone, each `lineEvalNumAt A₀ pt` evaluates to
    `(A₁.1 - A₀.1) · L.eval pt.1 pt.2` where `L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2`.
    Products over `k+1` factors (with various skip patterns) extract
    `(A₁.1 - A₀.1)^(k+1)` times the corresponding product of `L.eval`s. -/

/-- On non-vertical pairs, `bivEval (lineEvalNumAt A₀ pt) A₁ =
    (A₁.1 - A₀.1) · L.eval pt.1 pt.2` where `L = lineThrough A₀ A₁`. -/
theorem bivEval_lineEvalNumAt_eq_mul
    (A₀ pt A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (lineEvalNumAt (E := E) A₀ pt) A₁
      = (A₁.1 - A₀.1) *
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval pt.1 pt.2 := by
  rw [bivEval_lineEvalNumAt_eq_ellP, ellP_eq_lineEval_mul E pt A₀ A₁ hNV]
  ring

/-- Product over a Finset: `bivEval` distributes. -/
theorem bivEval_finset_prod {α : Type*} (s : Finset α)
    (f : α → (ZMod E.q)[X][X]) (p : ZMod E.q × ZMod E.q) :
    bivEval (∏ i ∈ s, f i) p = ∏ i ∈ s, bivEval (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bivEval]
  | @insert _ _ h ih =>
      rw [Finset.prod_insert h, bivEval_mul, Finset.prod_insert h, ih]

/-- On non-vertical pairs, `bivEval (linesProductScaled P k B A₀) A₁ =
    (A₁.1 - A₀.1)^(k+1) · L.eval P.1 (-P.2) · ∏ j, L.eval (B j).1 (B j).2`. -/
theorem bivEval_linesProductScaled_eq
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (linesProductScaled (E := E) P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (k + 1)
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
  unfold linesProductScaled
  rw [bivEval_mul, bivEval_finset_prod]
  rw [bivEval_lineEvalNumAt_eq_mul _ _ _ _ hNV]
  have hprod : ∀ j : Fin k,
      bivEval (lineEvalNumAt (E := E) A₀ (B j)) A₁
        = (A₁.1 - A₀.1)
          * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
    intro j; exact bivEval_lineEvalNumAt_eq_mul E A₀ (B j) A₁ hNV
  rw [Finset.prod_congr rfl (fun j _ => hprod j),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  ring

/-- On non-vertical pairs, `bivEval (linesProductNoNegPScaled k B A₀) A₁ =
    (A₁.1 - A₀.1)^k · ∏ j, L.eval (B j).1 (B j).2`. -/
theorem bivEval_linesProductNoNegPScaled_eq
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (linesProductNoNegPScaled (E := E) k B A₀) A₁
      = (A₁.1 - A₀.1) ^ k
        * ∏ j : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
  unfold linesProductNoNegPScaled
  rw [bivEval_finset_prod]
  have hprod : ∀ j : Fin k,
      bivEval (lineEvalNumAt (E := E) A₀ (B j)) A₁
        = (A₁.1 - A₀.1)
          * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
    intro j; exact bivEval_lineEvalNumAt_eq_mul E A₀ (B j) A₁ hNV
  rw [Finset.prod_congr rfl (fun j _ => hprod j),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

/-- On non-vertical pairs, `bivEval (linesProductSkipBjScaled P k B A₀ j₀) A₁ =
    (A₁.1 - A₀.1)^k · L.eval P.1 (-P.2) · ∏_{j ≠ j₀} L.eval (B j).1 (B j).2`. -/
theorem bivEval_linesProductSkipBjScaled_eq
    (P : ZMod E.q × ZMod E.q) {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) (j₀ : Fin k) :
    bivEval (linesProductSkipBjScaled (E := E) P k B A₀ j₀) A₁
      = (A₁.1 - A₀.1) ^ k
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
  classical
  unfold linesProductSkipBjScaled
  rw [bivEval_mul, bivEval_finset_prod]
  rw [bivEval_lineEvalNumAt_eq_mul _ _ _ _ hNV]
  have hprod : ∀ j ∈ (Finset.univ (α := Fin k)).erase j₀,
      bivEval (lineEvalNumAt (E := E) A₀ (B j)) A₁
        = (A₁.1 - A₀.1)
          * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
    intro j _; exact bivEval_lineEvalNumAt_eq_mul E A₀ (B j) A₁ hNV
  rw [Finset.prod_congr rfl hprod,
      Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : ((Finset.univ (α := Fin k)).erase j₀).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
  rw [hcard]
  -- (A₁.1-A₀.1) · (A₁.1-A₀.1)^(k-1) = (A₁.1-A₀.1)^k
  have hk_pos : k ≥ 1 := Fin.pos_iff_nonempty.mpr ⟨j₀⟩
  have hk : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
  have hpow : (A₁.1 - A₀.1) * (A₁.1 - A₀.1) ^ (k - 1) = (A₁.1 - A₀.1) ^ k := by
    rw [mul_comm, ← pow_succ, hk]
  calc _ = ((A₁.1 - A₀.1) * (A₁.1 - A₀.1) ^ (k - 1))
          * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))
          * ∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
              (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by ring
    _ = (A₁.1 - A₀.1) ^ k
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by rw [hpow]

/-! ## combined factor-group identities

    `DAllScaled` combines the three `D(A_i)` factors into a single
    polynomial scaled to `lamDen^D.degE`. `dxdzAllScaled` combines the
    three `dxdz_den(A_i)` factors with scale `lamDen^6`. -/

/-- On non-vertical, `bivEval DAllScaled = (A₁.1 - A₀.1)^D.degE · D(A₀)·D(A₁)·D(A₂)`. -/
theorem bivEval_DAllScaled_eq (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (DAllScaled (E := E) D A₀) A₁
      = (A₁.1 - A₀.1) ^ D.degE *
          (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
            * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)) := by
  unfold DAllScaled
  simp only [bivEval_mul]
  rw [bivEval_DAtA₀Poly, bivEval_DAtA₁Poly,
      bivEval_DAtA₂Scaled_eq _ _ _ _ hNV]
  ring

/-- On non-vertical, `bivEval dxdzAllScaled = (A₁.1 - A₀.1)^6 · dxdz(A₀)·dxdz(A₁)·dxdz(A₂)`. -/
theorem bivEval_dxdzAllScaled_eq
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzAllScaled (E := E) A₀) A₁
      = (A₁.1 - A₀.1) ^ 6 *
          ((3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
            * (3 * A₁.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
            * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))) := by
  unfold dxdzAllScaled
  simp only [bivEval_mul]
  rw [bivEval_dxdzDenA₀Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₁Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₂Scaled_eq _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ 6
              = (A₁.1 - A₀.1) * (A₁.1 - A₀.1) * (A₁.1 - A₀.1) ^ 4 := by
    rw [show (6 : ℕ) = 1 + 1 + 4 from by omega, pow_add, pow_add, pow_one]
  rw [hpow]
  ring

/-! ### Per-term bivEval identities 

    Each term of `clearedFiberPoly` evaluates on the non-vertical cone to
    `(A₁.1 - A₀.1)^N · [concrete factor product]` where `N = D.degE + k + 6`.
    The five identities below correspond to the five summands of
    `clearedFiberPoly`. Each unfolds the term, distributes `bivEval` across
    the product, applies the per-factor identities, then combines powers
    of `(A₁.1 - A₀.1)` via explicit `pow_add` rewrites. -/

/-- LHS `i=0` term: old `num·2·A₀.2 · [other factors]` bivEval.  -/
theorem bivEval_lhsTerm0Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (lhsTerm0Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          (((Polynomial.derivative D.a).eval A₀.1
              - (Polynomial.derivative D.b).eval A₀.1 * A₀.2)
            * (2 * A₀.2)
            * D.eval A₁.1 A₁.2
            * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
            * (3 * A₁.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
            * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold lhsTerm0Scaled
  simp only [bivEval_mul]
  rw [bivEval_DDerivAtA₀Poly, bivEval_embedScalar, bivEval_DAtA₁Poly,
      bivEval_DAtA₂Scaled_eq _ _ _ _ hNV,
      bivEval_dxdzDenA₁Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₂Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1)
                * (A₁.1 - A₀.1) ^ 4 * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 6 = D.degE + 1 + 4 + (k + 1) from by omega,
        pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

/-- LHS `i=1` term: old factor only. -/
theorem bivEval_lhsTerm1Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (lhsTerm1Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          (((Polynomial.derivative D.a).eval A₁.1
              - (Polynomial.derivative D.b).eval A₁.1 * A₁.2)
            * (2 * A₁.2)
            * D.eval A₀.1 A₀.2
            * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
            * (3 * A₀.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
            * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold lhsTerm1Scaled
  simp only [bivEval_mul, bivEval_add]
  rw [bivEval_DDerivAtA₁Poly, bivEval_embedScalar, bivEval_outerA₁y,
      bivEval_DAtA₀Poly,
      bivEval_DAtA₂Scaled_eq _ _ _ _ hNV,
      bivEval_dxdzDenA₀Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₂Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1)
                * (A₁.1 - A₀.1) ^ 4 * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 6 = D.degE + 1 + 4 + (k + 1) from by omega,
        pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

/-- LHS `i=2` term: old `num·2y` factor only bivEval. -/
theorem bivEval_lhsTerm2Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (lhsTerm2Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          (((Polynomial.derivative D.a).eval (chordX₂ A₀ A₁)
              - (Polynomial.derivative D.b).eval (chordX₂ A₀ A₁)
                * (chordY₂ A₀ A₁))
            * (2 * (chordY₂ A₀ A₁))
            * D.eval A₀.1 A₀.2
            * D.eval A₁.1 A₁.2
            * (3 * A₀.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
            * (3 * A₁.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold lhsTerm2Scaled
  simp only [bivEval_mul]
  rw [bivEval_DDerivAtA₂Scaled_eq _ _ _ _ hNV,
      bivEval_embedScalar, bivEval_y₂Scaled_eq _ _ _ hNV,
      bivEval_DAtA₀Poly, bivEval_DAtA₁Poly,
      bivEval_dxdzDenA₀Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₁Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV]
  have hY₂_eq :
      (slopeOf A₀.1 A₀.2 A₁.1 A₁.2
        * ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
          + (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1))
        = chordY₂ A₀ A₁ := by
    unfold chordY₂ chordX₂; ring
  simp only [hY₂_eq]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1) ^ 3
                * (A₁.1 - A₀.1) * (A₁.1 - A₀.1) * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 6 = D.degE + 3 + 1 + 1 + (k + 1) from by omega,
        pow_add, pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

/-! ### bivEval of correction terms -/

theorem bivEval_correctionTerm0Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (correctionTerm0Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          ((- D.b.eval A₀.1) * (3 * A₀.1 ^ 2 + E.curveA)
            * D.eval A₁.1 A₁.2
            * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
            * (3 * A₁.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
            * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold correctionTerm0Scaled
  simp only [bivEval_mul]
  rw [bivEval_DBdydzAtA₀Poly, bivEval_DAtA₁Poly,
      bivEval_DAtA₂Scaled_eq _ _ _ _ hNV,
      bivEval_dxdzDenA₁Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₂Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1)
                * (A₁.1 - A₀.1) ^ 4 * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 6 = D.degE + 1 + 4 + (k + 1) from by omega,
        pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

theorem bivEval_correctionTerm1Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (correctionTerm1Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          ((- D.b.eval A₁.1) * (3 * A₁.1 ^ 2 + E.curveA)
            * D.eval A₀.1 A₀.2
            * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
            * (3 * A₀.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
            * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold correctionTerm1Scaled
  simp only [bivEval_mul]
  rw [bivEval_DBdydzAtA₁Poly, bivEval_DAtA₀Poly,
      bivEval_DAtA₂Scaled_eq _ _ _ _ hNV,
      bivEval_dxdzDenA₀Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₂Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1)
                * (A₁.1 - A₀.1) ^ 4 * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 6 = D.degE + 1 + 4 + (k + 1) from by omega,
        pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

theorem bivEval_correctionTerm2Scaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (correctionTerm2Scaled (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          ((- D.b.eval (chordX₂ A₀ A₁))
              * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)
            * D.eval A₀.1 A₀.2
            * D.eval A₁.1 A₁.2
            * (3 * A₀.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
            * (3 * A₁.1 ^ 2 + E.curveA
                - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold correctionTerm2Scaled
  simp only [bivEval_mul, bivEval_pow]
  rw [bivEval_correctionA₂ScaledCore_eq _ _ _ _ hNV,
      bivEval_DAtA₀Poly, bivEval_DAtA₁Poly,
      bivEval_dxdzDenA₀Scaled_eq _ _ _ hNV,
      bivEval_dxdzDenA₁Scaled_eq _ _ _ hNV,
      bivEval_linesProductScaled_eq _ _ _ _ _ _ hNV,
      bivEval_lamDenPoly]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ (D.degE + 1)
                * (A₁.1 - A₀.1) * (A₁.1 - A₀.1) * (A₁.1 - A₀.1) ^ (k + 1)
                * (A₁.1 - A₀.1) ^ 2 := by
    rw [show D.degE + k + 6 = (D.degE + 1) + 1 + 1 + (k + 1) + 2 from by omega,
        pow_add, pow_add, pow_add, pow_add, pow_one]
  rw [hpow]; ring

/-- RHS `-1/L(-P)` term (with cleared `-` sign): `D·dxdz·∏L(B_j)`. -/
theorem bivEval_rhsTermNegPScaled_eq
    (D : CoordRingElt E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (rhsTermNegPScaled (E := E) D k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          ((D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
              * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁))
            * ((3 * A₀.1 ^ 2 + E.curveA
                  - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
                * (3 * A₁.1 ^ 2 + E.curveA
                    - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
                * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                    - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)))
            * ∏ j : Fin k,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
  unfold rhsTermNegPScaled
  simp only [bivEval_mul]
  rw [bivEval_DAllScaled_eq _ _ _ _ hNV,
      bivEval_dxdzAllScaled_eq _ _ _ hNV,
      bivEval_linesProductNoNegPScaled_eq _ _ _ _ _ hNV]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1) ^ 6
                * (A₁.1 - A₀.1) ^ k := by
    rw [show D.degE + k + 6 = D.degE + 6 + k from by omega,
        pow_add, pow_add]
  rw [hpow]; ring

/-- RHS `Σ_j m_j/L(B_j)` term: `Σ_j m_j · D·dxdz·L(-P)·∏_{j'≠j} L(B_{j'})`. -/
theorem bivEval_rhsSumScaled_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (rhsSumScaled (E := E) D P k B m A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          ∑ j : Fin k, m j
            * (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
                * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁))
            * ((3 * A₀.1 ^ 2 + E.curveA
                  - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
                * (3 * A₁.1 ^ 2 + E.curveA
                    - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
                * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                    - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)))
            * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
            * ∏ j' ∈ (Finset.univ (α := Fin k)).erase j,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2 := by
  classical
  unfold rhsSumScaled
  rw [bivEval_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [bivEval_mul]
  rw [bivEval_embedScalar,
      bivEval_DAllScaled_eq _ _ _ _ hNV,
      bivEval_dxdzAllScaled_eq _ _ _ hNV,
      bivEval_linesProductSkipBjScaled_eq _ _ _ _ _ hNV j]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 6)
              = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1) ^ 6
                * (A₁.1 - A₀.1) ^ k := by
    rw [show D.degE + k + 6 = D.degE + 6 + k from by omega,
        pow_add, pow_add]
  rw [hpow]; ring

/-! ## main `clearedFiberPoly_identity`

    Assembly of the five B2 per-term identities into the master identity
    `bivEval (clearedFiberPoly …) A₁ = (A₁.1 - A₀.1)^N · logDerivCheckFnCleared`
    under the hypothesis `logDerivCheckFnDenom ≠ 0` (i.e. all denominator
    factors nonzero). -/

/-- Extract the 8 individual non-zero facts from
    `logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0`. -/
theorem logDerivCheckFnDenom_factors_ne_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    D.eval A₀.1 A₀.2 ≠ 0 ∧
    D.eval A₁.1 A₁.2 ≠ 0 ∧
    D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) ≠ 0 ∧
    (3 * A₀.1 ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) ≠ 0 ∧
    (3 * A₁.1 ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) ≠ 0 ∧
    (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) ≠ 0 ∧
    (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0 ∧
    (∀ j : Fin k,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0) := by
  classical
  have hEq : logDerivCheckFnDenom E D P B A₀ A₁ =
      D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 *
      D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) *
      (3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) *
      (3 * A₁.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) *
      (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) *
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) *
      ∏ j : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
    unfold logDerivCheckFnDenom chordX₂ chordY₂
    rfl
  rw [hEq] at hDef
  obtain ⟨h7, hLBjProd⟩ := mul_ne_zero_iff.mp hDef
  obtain ⟨h6a, hLP⟩ := mul_ne_zero_iff.mp h7
  obtain ⟨h5a, hDx2⟩ := mul_ne_zero_iff.mp h6a
  obtain ⟨h4a, hDx1⟩ := mul_ne_zero_iff.mp h5a
  obtain ⟨h3a, hDx0⟩ := mul_ne_zero_iff.mp h4a
  obtain ⟨h2a, hD2⟩ := mul_ne_zero_iff.mp h3a
  obtain ⟨hD0, hD1⟩ := mul_ne_zero_iff.mp h2a
  refine ⟨hD0, hD1, hD2, hDx0, hDx1, hDx2, hLP, ?_⟩
  intro j
  exact (Finset.prod_ne_zero_iff.mp hLBjProd) j (Finset.mem_univ _)

/-- Explicit product form of `logDerivCheckFnDenom` (no `let`-bindings).
    Allows downstream reasoning without forcing `whnf` on the nested lets
    inside `logDerivCheckFnDenom`'s definition. -/
theorem logDerivCheckFnDenom_eq_explicit
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    logDerivCheckFnDenom E D P B A₀ A₁ =
      D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 *
      D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) *
      (3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) *
      (3 * A₁.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) *
      (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) *
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) *
      ∏ j : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 := by
  unfold logDerivCheckFnDenom chordX₂ chordY₂
  rfl

/-- `logDerivCheckFn` rewritten as a "positive" sum (no outer subtraction),
    folding the `chordX₂, chordY₂` abbreviations into the A₂ term. -/
theorem logDerivCheckFn_eq_positive_form
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    logDerivCheckFn E D P k B m A₀ A₁
      = logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            (chordX₂ A₀ A₁, chordY₂ A₀ A₁)
        + ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
        + ∑ j : Fin k,
            m j
              * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹ := by
  classical
  simp only [logDerivCheckFn, chordX₂, chordY₂]
  rw [show (∑ j : Fin k, -(m j)
              * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)
          = -(∑ j : Fin k, m j
                * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)
       from by
         rw [← Finset.sum_neg_distrib]
         apply Finset.sum_congr rfl
         intro j _; ring]
  ring

/-- Explicit form of `logDerivTerm` (paper-faithful).
    The numerator is `num_x·dx/dz + num_y·dy/dz` with
    `num_x = a'(x) − b'(x)·y`, `num_y = −b(x)`,
    `dx/dz (num) = 2y`, `dy/dz (num) = 3x² + A`, and
    common denominator factor `(3x² + A − 2λy)`. -/
theorem logDerivTerm_eq_explicit
    (D : CoordRingElt E.q) (curveA lam : ZMod E.q)
    (pt : ZMod E.q × ZMod E.q) :
    logDerivTerm E D curveA lam pt =
      ((D.a.derivative.eval pt.1 - D.b.derivative.eval pt.1 * pt.2)
            * (2 * pt.2)
          + (-D.b.eval pt.1) * (3 * pt.1 ^ 2 + curveA))
        * (D.eval pt.1 pt.2 * (3 * pt.1 ^ 2 + curveA - 2 * lam * pt.2))⁻¹ := by
  unfold logDerivTerm
  rfl

/-! ### Symmetry of `logDerivCheckFnDenom` and `logDerivCheckFn` on the
      non-vertical cone (A₀ ↔ A₁ swap). Used in T2. -/

theorem logDerivCheckFnDenom_symm
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    logDerivCheckFnDenom E D P B A₀ A₁ = logDerivCheckFnDenom E D P B A₁ A₀ := by
  rw [logDerivCheckFnDenom_eq_explicit, logDerivCheckFnDenom_eq_explicit]
  rw [slopeOf_symm E A₁.1 A₁.2 A₀.1 A₀.2,
      chordX₂_symm E A₁ A₀,
      chordY₂_symm E A₁ A₀ (Ne.symm hNV),
      lineThrough_symm E A₁.1 A₁.2 A₀.1 A₀.2 (Ne.symm hNV)]
  ring

theorem logDerivCheckFn_symm
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    logDerivCheckFn E D P k B m A₀ A₁ = logDerivCheckFn E D P k B m A₁ A₀ := by
  rw [logDerivCheckFn_eq_positive_form E D P B m A₀ A₁,
      logDerivCheckFn_eq_positive_form E D P B m A₁ A₀,
      slopeOf_symm E A₁.1 A₁.2 A₀.1 A₀.2,
      chordX₂_symm E A₁ A₀,
      chordY₂_symm E A₁ A₀ (Ne.symm hNV),
      lineThrough_symm E A₁.1 A₁.2 A₀.1 A₀.2 (Ne.symm hNV)]
  ring

set_option maxHeartbeats 1000000 in
/-- Per-term clearing (i=0): `(old_num_scalar + correction_scalar) · (other) = LT(A₀) · denom`.
    The sum LHS matches the paper-faithful `logDerivTerm` numerator. -/
private lemma clearedFiberPoly_lhs0_eq_LT_mul_denom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hD0 : D.eval A₀.1 A₀.2 ≠ 0)
    (hDx0 : 3 * A₀.1 ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2 ≠ 0) :
    ((Polynomial.derivative D.a).eval A₀.1
        - (Polynomial.derivative D.b).eval A₀.1 * A₀.2)
      * (2 * A₀.2)
      * D.eval A₁.1 A₁.2
      * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
      * (3 * A₁.1 ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
      * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
      * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
      * ∏ j : Fin k,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
    + ((- D.b.eval A₀.1) * (3 * A₀.1 ^ 2 + E.curveA)
        * D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)
    = logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      * logDerivCheckFnDenom E D P B A₀ A₁ := by
  rw [logDerivTerm_eq_explicit, logDerivCheckFnDenom_eq_explicit]
  have hDDx : D.eval A₀.1 A₀.2
      * (3 * A₀.1 ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) ≠ 0 :=
    mul_ne_zero hD0 hDx0
  set T : ZMod E.q := D.eval A₀.1 A₀.2
      * (3 * A₀.1 ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) with hT
  have hT0 : T ≠ 0 := hDDx
  have hTinv : T⁻¹ * T = 1 := inv_mul_cancel₀ hT0
  -- Goal is (...)=(num)*T⁻¹ * (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 * ... * (3*A₀.1^2+...) * ...).
  -- Factor T out of the RHS denom: the RHS denom contains the factors of T.
  have hfact : D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
      = T * (D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
    rw [hT]; ring
  rw [hfact]
  rw [show ∀ (a b : ZMod E.q), a * T⁻¹ * (T * b) = a * (T⁻¹ * T) * b from
        fun a b => by ring, hTinv]
  ring

set_option maxHeartbeats 1000000 in
/-- Per-term clearing (i=1). -/
private lemma clearedFiberPoly_lhs1_eq_LT_mul_denom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hD1 : D.eval A₁.1 A₁.2 ≠ 0)
    (hDx1 : 3 * A₁.1 ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2 ≠ 0) :
    ((Polynomial.derivative D.a).eval A₁.1
        - (Polynomial.derivative D.b).eval A₁.1 * A₁.2)
      * (2 * A₁.2)
      * D.eval A₀.1 A₀.2
      * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
      * (3 * A₀.1 ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
      * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
      * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
      * ∏ j : Fin k,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
    + ((- D.b.eval A₁.1) * (3 * A₁.1 ^ 2 + E.curveA)
        * D.eval A₀.1 A₀.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)
    = logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      * logDerivCheckFnDenom E D P B A₀ A₁ := by
  rw [logDerivTerm_eq_explicit, logDerivCheckFnDenom_eq_explicit]
  have hDDx : D.eval A₁.1 A₁.2
      * (3 * A₁.1 ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) ≠ 0 :=
    mul_ne_zero hD1 hDx1
  set T : ZMod E.q := D.eval A₁.1 A₁.2
      * (3 * A₁.1 ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) with hT
  have hT0 : T ≠ 0 := hDDx
  have hTinv : T⁻¹ * T = 1 := inv_mul_cancel₀ hT0
  have hfact : D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
      = T * (D.eval A₀.1 A₀.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
    rw [hT]; ring
  rw [hfact]
  rw [show ∀ (a b : ZMod E.q), a * T⁻¹ * (T * b) = a * (T⁻¹ * T) * b from
        fun a b => by ring, hTinv]
  ring

set_option maxHeartbeats 1000000 in
/-- Per-term clearing (i=2). -/
private lemma clearedFiberPoly_lhs2_eq_LT_mul_denom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hD2 : D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) ≠ 0)
    (hDx2 : 3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
      - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁) ≠ 0) :
    ((Polynomial.derivative D.a).eval (chordX₂ A₀ A₁)
        - (Polynomial.derivative D.b).eval (chordX₂ A₀ A₁) * (chordY₂ A₀ A₁))
      * (2 * (chordY₂ A₀ A₁))
      * D.eval A₀.1 A₀.2
      * D.eval A₁.1 A₁.2
      * (3 * A₀.1 ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
      * (3 * A₁.1 ^ 2 + E.curveA
          - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
      * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
      * ∏ j : Fin k,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
    + ((- D.b.eval (chordX₂ A₀ A₁)) * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA)
        * D.eval A₀.1 A₀.2
        * D.eval A₁.1 A₁.2
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)
    = logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
        (chordX₂ A₀ A₁, chordY₂ A₀ A₁)
      * logDerivCheckFnDenom E D P B A₀ A₁ := by
  rw [logDerivTerm_eq_explicit, logDerivCheckFnDenom_eq_explicit]
  have hDDx : D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
      * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) ≠ 0 :=
    mul_ne_zero hD2 hDx2
  set T : ZMod E.q := D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
      * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) with hT
  have hT0 : T ≠ 0 := hDDx
  have hTinv : T⁻¹ * T = 1 := inv_mul_cancel₀ hT0
  have hfact : D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁))
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
      = T * (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
        * (3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
        * (3 * A₁.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
        * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
        * ∏ j : Fin k,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) := by
    rw [hT]; ring
  rw [hfact]
  rw [show ∀ (a b : ZMod E.q), a * T⁻¹ * (T * b) = a * (T⁻¹ * T) * b from
        fun a b => by ring, hTinv]
  ring

/-- Per-term clearing (negP): `polyFormNegP = L(-P)⁻¹ · denom`. -/
private lemma clearedFiberPoly_negP_eq_Linv_mul_denom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hLP : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0) :
    (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
        * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁))
      * ((3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
          * (3 * A₁.1 ^ 2 + E.curveA
              - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
          * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
              - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)))
      * ∏ j : Fin k,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2
    = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
      * logDerivCheckFnDenom E D P B A₀ A₁ := by
  rw [logDerivCheckFnDenom_eq_explicit]
  field_simp

/-- Per-term clearing (sum-j): for each `j`, `polyFormSum_j = m j · L(Bⱼ)⁻¹ · denom`. -/
private lemma clearedFiberPoly_sumj_eq_Linv_mul_denom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (j : Fin k)
    (hLBj : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0) :
    m j
      * (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
          * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁))
      * ((3 * A₀.1 ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
          * (3 * A₁.1 ^ 2 + E.curveA
              - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
          * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
              - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)))
      * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
      * ∏ j' ∈ (Finset.univ (α := Fin k)).erase j,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2
    = m j
      * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹
      * logDerivCheckFnDenom E D P B A₀ A₁ := by
  rw [logDerivCheckFnDenom_eq_explicit]
  classical
  have hProdEq :
      ∏ j' : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2
      = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)
        * ∏ j' ∈ (Finset.univ (α := Fin k)).erase j,
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2 := by
    exact (Finset.mul_prod_erase Finset.univ
        (fun j' => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2)
        (Finset.mem_univ j)).symm
  rw [hProdEq]
  field_simp

/-- **Main Phase B3 theorem**: on the non-vertical cone with all denominator
    factors nonzero, `bivEval (clearedFiberPoly …) A₁` equals
    `(A₁.1 - A₀.1)^(D.degE + k + 6) · logDerivCheckFnCleared E D P k B m A₀ A₁`.

    This identity is the core link between the polynomial form (for fiber/
    zero-count bounds) and the scalar `logDerivCheckFn` used in the
    soundness argument. -/
theorem clearedFiberPoly_identity
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    bivEval (clearedFiberPoly (E := E) D P k B m A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          logDerivCheckFnCleared E D P k B m A₀ A₁ := by
  set_option maxHeartbeats 1000000 in
  classical
  obtain ⟨hD0, hD1, hD2, hDx0, hDx1, hDx2, hLP, hLB⟩ :=
    logDerivCheckFnDenom_factors_ne_zero E D P B A₀ A₁ hDef
  -- Step 1: Apply the 8 B2 per-term bivEval identities.
  unfold clearedFiberPoly
  simp only [bivEval_add]
  rw [bivEval_lhsTerm0Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_lhsTerm1Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_lhsTerm2Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_correctionTerm0Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_correctionTerm1Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_correctionTerm2Scaled_eq (E := E) D P B A₀ A₁ hNV,
      bivEval_rhsTermNegPScaled_eq (E := E) D B A₀ A₁ hNV,
      bivEval_rhsSumScaled_eq (E := E) D P B m A₀ A₁ hNV]
  -- Step 2: Factor out (A-B)^N and group lhs_i + correction_i pairs.
  -- After step 1, LHS is Σ_{i∈{lhs0,lhs1,lhs2,corr0,corr1,corr2,rhsNegP,rhsSum}} (A-B)^N · term_i.
  -- Group as (A-B)^N · (lhs0+corr0 + lhs1+corr1 + lhs2+corr2 + rhsNegP + rhsSum).
  -- Each (lhs_i + corr_i) matches `clearedFiberPoly_lhs_i_eq_LT_mul_denom` (up to (A-B)^N factor).
  -- Factor out (A-B)^N from RHS via logDerivCheckFnCleared definition.
  unfold logDerivCheckFnCleared
  rw [logDerivCheckFn_eq_positive_form]
  -- Now: Goal has (A-B)^N · [LT(A₀) + LT(A₁) + LT(A₂) + L(-P)⁻¹ + Σ m·L(B)⁻¹] · denom.
  -- We apply per-term lemmas after aligning to that structure.
  -- Factor out (A-B)^N from LHS via explicit rewriting.
  set N := (A₁.1 - A₀.1) ^ (D.degE + k + 6) with hN_def
  -- LHS = N·old0 + N·old1 + N·old2 + N·corr0 + N·corr1 + N·corr2 + N·rhsNegP + N·rhsSum
  --     = N·((old0 + corr0) + (old1 + corr1) + (old2 + corr2) + rhsNegP + rhsSum)
  rw [show ∀ (a b c d e f g h : ZMod E.q),
        N * a + N * b + N * c + N * d + N * e + N * f + N * g + N * h
          = N * ((a + d) + (b + e) + (c + f) + g + h) from
        fun a b c d e f g h => by ring]
  -- Apply per-term sum lemmas to rewrite each (old_i + corr_i) = LT · denom.
  rw [clearedFiberPoly_lhs0_eq_LT_mul_denom (E := E) D P B A₀ A₁ hNV hD0 hDx0,
      clearedFiberPoly_lhs1_eq_LT_mul_denom (E := E) D P B A₀ A₁ hNV hD1 hDx1,
      clearedFiberPoly_lhs2_eq_LT_mul_denom (E := E) D P B A₀ A₁ hNV hD2 hDx2,
      clearedFiberPoly_negP_eq_Linv_mul_denom (E := E) D P B A₀ A₁ hLP]
  -- Now the Σ_j term — rewrite it via per-j sum lemma.
  rw [show (∑ j : Fin k, m j
             * (D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2
                 * D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁))
             * ((3 * A₀.1 ^ 2 + E.curveA
                   - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2)
                 * (3 * A₁.1 ^ 2 + E.curveA
                     - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2)
                 * (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
                     - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)))
             * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2)
             * ∏ j' ∈ (Finset.univ (α := Fin k)).erase j,
                 (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j').1 (B j').2)
           = ∑ j : Fin k, m j
                * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹
                * logDerivCheckFnDenom E D P B A₀ A₁
         from Finset.sum_congr rfl (fun j _ =>
                clearedFiberPoly_sumj_eq_Linv_mul_denom (E := E) D P B m
                  A₀ A₁ j (hLB j))]
  -- Close via ring.
  set denom := logDerivCheckFnDenom E D P B A₀ A₁
  set LBinv : Fin k → ZMod E.q := fun j =>
    ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹
  rw [show (∑ j : Fin k, m j * LBinv j * denom)
         = (∑ j : Fin k, m j * LBinv j) * denom from (Finset.sum_mul ..).symm]
  ring

/-- F3: pairs `(A₀, A₁) ∈ E × E` with `D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0`
    are at most `(2·D.degE + 2) · |E|`.

    Split: vertical (`A₀.1 = A₁.1`, ≤ 2·|E|) via curve-fiber; non-vertical
    (≤ |E|·numZeros D via `thirdPoint_inj_on_A₁` from support-disjoint lemma). -/
theorem DAtA₂_zero_pairs_card_le (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0)).card
    ≤ (2 * D.degE + 2) * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0) with hSdef
  set Svert := S.filter (fun p => p.1.1 = p.2.1) with hSvertdef
  set Snv := S.filter (fun p => p.1.1 ≠ p.2.1) with hSnvdef
  have hSplit : Svert.card + Snv.card = S.card := by
    rw [hSvertdef, hSnvdef]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  -- Svert bound: Svert ⊆ {A₀.1 = A₁.1}, fiberwise ≤ 2 per A₀ ⇒ ≤ 2·|E|.
  have hSvert_bd : Svert.card ≤ 2 * E.points.card := by
    set T := (E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
         p.1.1 = p.2.1) with hTdef
    have hSub : Svert ⊆ T := by
      intro p hp
      simp only [hSvertdef, hSdef, Finset.mem_filter, Finset.mem_product] at hp
      simp only [hTdef, Finset.mem_filter, Finset.mem_product]
      exact ⟨hp.1.1, hp.2⟩
    have hTcard : T.card ≤ 2 * E.points.card := by
      have hfib : T.card = ∑ A₀ ∈ E.points,
          (E.points.filter (fun A₁ => A₀.1 = A₁.1)).card :=
        card_filter_product_fiber_eq E E.points E.points
          (fun a b => a.1 = b.1)
      rw [hfib]
      have hper : ∀ A₀ ∈ E.points,
          (E.points.filter (fun A₁ => A₀.1 = A₁.1)).card ≤ 2 := by
        intro A₀ _
        have heq : E.points.filter (fun A₁ => A₀.1 = A₁.1)
                 = E.points.filter (fun A₁ => A₁.1 = A₀.1) := by
          apply Finset.filter_congr; intros; tauto
        rw [heq]
        exact card_points_with_fst_eq_le E A₀.1
      calc ∑ A₀ ∈ E.points, (E.points.filter (fun A₁ => A₀.1 = A₁.1)).card
          ≤ ∑ A₀ ∈ E.points, 2 := Finset.sum_le_sum hper
        _ = 2 * E.points.card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    exact le_trans (Finset.card_le_card hSub) hTcard
  -- Snv bound: Snv ⊆ S₃-style set via thirdPoint ≡ (chordX₂, chordY₂) on non-vert.
  have hSnv_bd : Snv.card ≤ E.points.card * numZeros E D := by
    set T := (E.points ×ˢ E.points).filter (fun p =>
      match thirdPoint E p.1 p.2 with
      | ECPoint.infinity => False
      | ECPoint.affine x y => D.eval x y = 0) with hTdef
    have hSub : Snv ⊆ T := by
      intro p hp
      simp only [hSnvdef, hSdef, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hmem, hDval⟩, hn⟩ := hp
      simp only [hTdef, Finset.mem_filter, Finset.mem_product]
      refine ⟨hmem, ?_⟩
      rw [thirdPoint_of_xne E p.1 p.2 hn]
      exact hDval
    calc Snv.card ≤ T.card := Finset.card_le_card hSub
      _ ≤ E.numAffine * numZeros E D :=
          card_thirdPoint_affine_D_zero_pairs_le E D
      _ = E.points.card * numZeros E D := rfl
  have hSnv_bd' : Snv.card ≤ 2 * D.degE * E.points.card := by
    calc Snv.card ≤ E.points.card * numZeros E D := hSnv_bd
      _ ≤ E.points.card * (2 * D.degE) :=
            Nat.mul_le_mul_left _ (numZeros_le_two_degE E D hD)
      _ = 2 * D.degE * E.points.card := by ring
  calc S.card = Svert.card + Snv.card := hSplit.symm
    _ ≤ 2 * E.points.card + 2 * D.degE * E.points.card :=
        Nat.add_le_add hSvert_bd hSnv_bd'
    _ = (2 * D.degE + 2) * E.points.card := by ring


end Divisor
