/-
  Divisor/ClearedFullPoly.lean — 4-variate lift of clearedFiberPoly

  For each component `xScaled A₀` of `clearedFiberPoly` (a 2-variate
  polynomial in `A₁.1, A₁.2` with `A₀ : ZMod E.q × ZMod E.q` as scalar
  parameter), we build a 4-variate version `xFull` where `A₀` is also a
  pair of polynomial variables `(X 0, X 1)` and `A₁` corresponds to
  `(X 2, X 3)`. The defining compatibility lemma is

  `bivEval₂ (xFull ...) A₀ A₁ = bivEval (xScaled ... A₀) A₁`.

  Summing the components yields `clearedFullPoly`, which inherits from
  `clearedFiberPoly_identity` the identity

  `bivEval₂ (clearedFullPoly D P k B m) A₀ A₁
      = (A₁.1 − A₀.1)^(D.degE + k + 6) · logDerivCheckFnCleared E D P k B m A₀ A₁`

  on the non-vertical cone with nonzero denominator factors.

  Phase 4 proves a bi-X-degree bound on `clearedFullPoly`; Phase 5
  combines the identity, the degree bound, and the Lang-Weil axiom
  (`bivariate_poly_zeros_on_ExE_le`) to bound the size of the
  `eventNotEq` set by a linear function of `(D.degE + k)·|E|`.

  Notation convention: use `Xm` / `Cm` for the 4-variate (MvPolynomial)
  generator / constant embed to avoid clashing with `Polynomial.X` in
  expressions like `(ZMod q)[X]`. `Polynomial` is globally opened; the
  `MvPolynomial` namespace is not.
-/
import Divisor.ClearedPolyForm
import Divisor.FourVarPoly
import Divisor.Axioms.AxiomBivariatePolyZerosOnExELe
import Divisor.Axioms.AxiomHasseWeil
import Divisor.SlopeDist

open Polynomial Finset

namespace Divisor

/-- `MvPolynomial.X` with explicit coefficient ring, for 4-variate
    polynomials over `ZMod q`. -/
local notation:max "Xm" i => (MvPolynomial.X i : FourVarPoly _)

/-- `MvPolynomial.C` with explicit coefficient ring. -/
local notation:max "Cm" c => (MvPolynomial.C c : FourVarPoly _)

variable (E : ECSetup)

/-! ## `liftPoly` — univariate polynomial lift to a target variable. -/

/-- Lift `p : (ZMod q)[X]` to a 4-variate polynomial by substituting
    `X` with the target variable `MvPolynomial.X i`. -/
noncomputable def liftPoly (p : (ZMod E.q)[X]) (i : Fin 4) : FourVarPoly E.q :=
  p.eval₂ MvPolynomial.C (MvPolynomial.X i : FourVarPoly E.q)

@[simp] theorem bivEval₂_liftPoly_0 (p : (ZMod E.q)[X])
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (liftPoly E p 0) A₀ A₁ = p.eval A₀.1 := by
  classical
  unfold liftPoly bivEval₂
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.eval₂_add, map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial, map_mul,
            map_pow, bivEval₂Fun]

@[simp] theorem bivEval₂_liftPoly_2 (p : (ZMod E.q)[X])
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (liftPoly E p 2) A₀ A₁ = p.eval A₁.1 := by
  classical
  unfold liftPoly bivEval₂
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [Polynomial.eval₂_add, map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial, map_mul,
            map_pow, bivEval₂Fun]

theorem liftPoly_degreeOf_target_le (p : (ZMod E.q)[X]) (i : Fin 4) :
    (liftPoly E p i).degreeOf i ≤ p.natDegree := by
  classical
  unfold liftPoly
  rw [Polynomial.eval₂_eq_sum_range]
  refine le_trans (MvPolynomial.degreeOf_sum_le i _ _) ?_
  refine Finset.sup_le ?_
  intro n hn
  have hn' : n ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  refine le_trans (MvPolynomial.degreeOf_mul_le i _ _) ?_
  rw [MvPolynomial.degreeOf_C, Nat.zero_add]
  refine le_trans (MvPolynomial.degreeOf_pow_le i
      (MvPolynomial.X i : FourVarPoly E.q) n) ?_
  rw [MvPolynomial.degreeOf_X]
  simp only [if_true, Nat.mul_one]
  exact hn'

theorem liftPoly_degreeOf_other (p : (ZMod E.q)[X]) (i j : Fin 4)
    (hij : i ≠ j) :
    (liftPoly E p i).degreeOf j = 0 := by
  classical
  unfold liftPoly
  rw [Polynomial.eval₂_eq_sum_range]
  refine le_antisymm ?_ (Nat.zero_le _)
  refine le_trans (MvPolynomial.degreeOf_sum_le j _ _) ?_
  refine Finset.sup_le ?_
  intro n _
  refine le_trans (MvPolynomial.degreeOf_mul_le j _ _) ?_
  rw [MvPolynomial.degreeOf_C, Nat.zero_add]
  refine le_trans (MvPolynomial.degreeOf_pow_le j
      (MvPolynomial.X i : FourVarPoly E.q) n) ?_
  rw [MvPolynomial.degreeOf_X, if_neg (Ne.symm hij)]
  simp

/-! ## Basic Full embeddings mirroring `ClearedPolyForm.lean`. -/

/-- Embed a scalar `c : ZMod E.q` as a constant 4-variate polynomial. -/
noncomputable def embedScalarFull (c : ZMod E.q) : FourVarPoly E.q :=
  (MvPolynomial.C c : FourVarPoly E.q)

/-- Embed a univariate poly `p : (ZMod E.q)[X]` as a 4-variate poly in `A₁.1`. -/
noncomputable def embedInnerPolyFull (p : (ZMod E.q)[X]) : FourVarPoly E.q :=
  liftPoly E p 2

/-- The `A₀.1` variable. -/
noncomputable def varA₀x : FourVarPoly E.q := (MvPolynomial.X 0 : FourVarPoly E.q)

/-- The `A₀.2` variable. -/
noncomputable def varA₀y : FourVarPoly E.q := (MvPolynomial.X 1 : FourVarPoly E.q)

/-- The `A₁.1` variable. -/
noncomputable def varA₁x : FourVarPoly E.q := (MvPolynomial.X 2 : FourVarPoly E.q)

/-- The `A₁.2` variable. -/
noncomputable def varA₁y : FourVarPoly E.q := (MvPolynomial.X 3 : FourVarPoly E.q)

@[simp] theorem bivEval₂_embedScalarFull (c : ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (embedScalarFull E c) A₀ A₁ = c := by
  simp [embedScalarFull, bivEval₂]

@[simp] theorem bivEval₂_embedInnerPolyFull (p : (ZMod E.q)[X])
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (embedInnerPolyFull E p) A₀ A₁ = p.eval A₁.1 := by
  simp [embedInnerPolyFull]

@[simp] theorem bivEval₂_varA₀x (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (varA₀x E) A₀ A₁ = A₀.1 := by simp [varA₀x, bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_varA₀y (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (varA₀y E) A₀ A₁ = A₀.2 := by simp [varA₀y, bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_varA₁x (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (varA₁x E) A₀ A₁ = A₁.1 := by simp [varA₁x, bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_varA₁y (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (varA₁y E) A₀ A₁ = A₁.2 := by simp [varA₁y, bivEval₂, bivEval₂Fun]

/-! ## Line/slope polynomials (4-variate). -/

/-- `lamNumFull` = `A₁.2 − A₀.2`, 4-variate form. -/
noncomputable def lamNumFull : FourVarPoly E.q := varA₁y E - varA₀y E

/-- `lamDenFull` = `A₁.1 − A₀.1`, 4-variate form. -/
noncomputable def lamDenFull : FourVarPoly E.q := varA₁x E - varA₀x E

@[simp] theorem bivEval₂_lamNumFull (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lamNumFull E) A₀ A₁ = A₁.2 - A₀.2 := by
  simp [lamNumFull, bivEval₂_sub]

@[simp] theorem bivEval₂_lamDenFull (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lamDenFull E) A₀ A₁ = A₁.1 - A₀.1 := by
  simp [lamDenFull, bivEval₂_sub]

/-- `L_{A₀A₁}(pt) · (A₁.1 − A₀.1)` as a 4-variate polynomial in `(A₀, A₁)`
    for fixed evaluation point `pt`. Equals
    `(pt.2 − A₀.2)·λDen − (pt.1 − A₀.1)·λNum`. -/
noncomputable def lineEvalNumAtFull (pt : ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  (embedScalarFull E pt.2 - varA₀y E) * lamDenFull E -
  (embedScalarFull E pt.1 - varA₀x E) * lamNumFull E

@[simp] theorem bivEval₂_lineEvalNumAtFull (pt : ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lineEvalNumAtFull E pt) A₀ A₁ =
      (pt.2 - A₀.2) * (A₁.1 - A₀.1) - (pt.1 - A₀.1) * (A₁.2 - A₀.2) := by
  simp [lineEvalNumAtFull, bivEval₂_sub, bivEval₂_mul]

/-! ## Phase 2: Full atoms — 4-variate mirror of `clearedFiberPoly`. -/

/-- Scaled `x₂`-polynomial, 4-variate form. Equals `lamDen² · x₂` when
    `A₀.1 ≠ A₁.1`. Mirror of `x₂Scaled`. -/
noncomputable def x₂ScaledFull : FourVarPoly E.q :=
  lamNumFull E ^ 2
  - (varA₀x E + varA₁x E) * lamDenFull E ^ 2

/-- Scaled `y₂`-polynomial, 4-variate form. Mirror of `y₂Scaled`. -/
noncomputable def y₂ScaledFull : FourVarPoly E.q :=
  lamNumFull E * x₂ScaledFull E
  + (varA₀y E * lamDenFull E - varA₀x E * lamNumFull E) * lamDenFull E ^ 2

@[simp] theorem bivEval₂_x₂ScaledFull (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (x₂ScaledFull E) A₀ A₁ =
      (A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2 := by
  simp [x₂ScaledFull, bivEval₂_sub, bivEval₂_mul, bivEval₂_pow, bivEval₂_add]

@[simp] theorem bivEval₂_y₂ScaledFull (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (y₂ScaledFull E) A₀ A₁ =
      (A₁.2 - A₀.2) *
        ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2)
      + (A₀.2 * (A₁.1 - A₀.1) - A₀.1 * (A₁.2 - A₀.2))
        * (A₁.1 - A₀.1) ^ 2 := by
  simp [y₂ScaledFull, bivEval₂_sub, bivEval₂_mul, bivEval₂_pow, bivEval₂_add]

/-- `D(A₀)` as a 4-variate polynomial, mirror of `DAtA₀Poly` (which is
    a constant scalar in the 2-variate `clearedFiberPoly`). -/
noncomputable def DAtA₀Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  liftPoly E D.a 0 - liftPoly E D.b 0 * varA₀y E

/-- `D(A₁)` as a 4-variate polynomial, mirror of `DAtA₁Poly`. -/
noncomputable def DAtA₁Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  liftPoly E D.a 2 - liftPoly E D.b 2 * varA₁y E

@[simp] theorem bivEval₂_DAtA₀Full (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAtA₀Full E D) A₀ A₁ = D.eval A₀.1 A₀.2 := by
  simp [DAtA₀Full, bivEval₂_sub, bivEval₂_mul, CoordRingElt.eval]

@[simp] theorem bivEval₂_DAtA₁Full (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAtA₁Full E D) A₀ A₁ = D.eval A₁.1 A₁.2 := by
  simp [DAtA₁Full, bivEval₂_sub, bivEval₂_mul, CoordRingElt.eval]

/-- `D'(A₀)` 4-variate form. -/
noncomputable def DDerivAtA₀Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  liftPoly E (Polynomial.derivative D.a) 0
  - liftPoly E (Polynomial.derivative D.b) 0 * varA₀y E

/-- `D'(A₁)` 4-variate form. -/
noncomputable def DDerivAtA₁Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  liftPoly E (Polynomial.derivative D.a) 2
  - liftPoly E (Polynomial.derivative D.b) 2 * varA₁y E

@[simp] theorem bivEval₂_DDerivAtA₀Full (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAtA₀Full E D) A₀ A₁ =
      (Polynomial.derivative D.a).eval A₀.1
        - (Polynomial.derivative D.b).eval A₀.1 * A₀.2 := by
  simp [DDerivAtA₀Full, bivEval₂_sub, bivEval₂_mul]

@[simp] theorem bivEval₂_DDerivAtA₁Full (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAtA₁Full E D) A₀ A₁ =
      (Polynomial.derivative D.a).eval A₁.1
        - (Polynomial.derivative D.b).eval A₁.1 * A₁.2 := by
  simp [DDerivAtA₁Full, bivEval₂_sub, bivEval₂_mul]

/-- `dxdz_den(A₀) · lamDen` 4-variate form. -/
noncomputable def dxdzDenA₀Full : FourVarPoly E.q :=
  ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₀x E ^ 2
      + (MvPolynomial.C E.curveA : FourVarPoly E.q)) * lamDenFull E
  - (MvPolynomial.C 2 : FourVarPoly E.q) * varA₀y E * lamNumFull E

/-- `dxdz_den(A₁) · lamDen` 4-variate form. -/
noncomputable def dxdzDenA₁Full : FourVarPoly E.q :=
  ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₁x E ^ 2
      + (MvPolynomial.C E.curveA : FourVarPoly E.q)) * lamDenFull E
  - (MvPolynomial.C 2 : FourVarPoly E.q) * varA₁y E * lamNumFull E

/-- `dxdz_den(A₂) · lamDen⁴` 4-variate form. -/
noncomputable def dxdzDenA₂Full : FourVarPoly E.q :=
  (MvPolynomial.C 3 : FourVarPoly E.q) * x₂ScaledFull E ^ 2
  + (MvPolynomial.C E.curveA : FourVarPoly E.q) * lamDenFull E ^ 4
  - (MvPolynomial.C 2 : FourVarPoly E.q) * lamNumFull E * y₂ScaledFull E

@[simp] theorem bivEval₂_dxdzDenA₀Full (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzDenA₀Full E) A₀ A₁ =
      (3 * A₀.1 ^ 2 + E.curveA) * (A₁.1 - A₀.1)
      - 2 * A₀.2 * (A₁.2 - A₀.2) := by
  simp [dxdzDenA₀Full, bivEval₂_sub, bivEval₂_add, bivEval₂_mul, bivEval₂_pow]

@[simp] theorem bivEval₂_dxdzDenA₁Full (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzDenA₁Full E) A₀ A₁ =
      (3 * A₁.1 ^ 2 + E.curveA) * (A₁.1 - A₀.1)
      - 2 * A₁.2 * (A₁.2 - A₀.2) := by
  simp [dxdzDenA₁Full, bivEval₂_sub, bivEval₂_add, bivEval₂_mul, bivEval₂_pow]

/-- Contribution `Σ a_n · x₂Scaled^n · lamDen^(D.degE-2n)`, 4-variate. -/
noncomputable def DAPartAtA₂ScaledFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  ∑ n ∈ Finset.range (D.a.natDegree + 1),
    (MvPolynomial.C (D.a.coeff n) : FourVarPoly E.q)
      * x₂ScaledFull E ^ n
      * lamDenFull E ^ (D.degE - 2 * n)

/-- Contribution `Σ b_n · x₂Scaled^n · y₂Scaled · lamDen^(D.degE-2n-3)`, 4-variate. -/
noncomputable def DBPartAtA₂ScaledFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  ∑ n ∈ Finset.range (D.b.natDegree + 1),
    (MvPolynomial.C (D.b.coeff n) : FourVarPoly E.q)
      * x₂ScaledFull E ^ n
      * y₂ScaledFull E
      * lamDenFull E ^ (D.degE - 2 * n - 3)

/-- `D(A₂) · lamDen^D.degE`, 4-variate. -/
noncomputable def DAtA₂ScaledFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  DAPartAtA₂ScaledFull E D - DBPartAtA₂ScaledFull E D

/-- Derivative analogues. -/
noncomputable def DDerivAPartAtA₂ScaledFull (D : CoordRingElt E.q) :
    FourVarPoly E.q :=
  ∑ n ∈ Finset.range ((Polynomial.derivative D.a).natDegree + 1),
    (MvPolynomial.C ((Polynomial.derivative D.a).coeff n) : FourVarPoly E.q)
      * x₂ScaledFull E ^ n
      * lamDenFull E ^ (D.degE - 2 * n)

noncomputable def DDerivBPartAtA₂ScaledFull (D : CoordRingElt E.q) :
    FourVarPoly E.q :=
  ∑ n ∈ Finset.range ((Polynomial.derivative D.b).natDegree + 1),
    (MvPolynomial.C ((Polynomial.derivative D.b).coeff n) : FourVarPoly E.q)
      * x₂ScaledFull E ^ n
      * y₂ScaledFull E
      * lamDenFull E ^ (D.degE - 2 * n - 3)

noncomputable def DDerivAtA₂ScaledFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  DDerivAPartAtA₂ScaledFull E D - DDerivBPartAtA₂ScaledFull E D

/-- Line-product `L(-P) · ∏_j L(B_j)`, 4-variate. Scales by `lamDen^(k+1)`. -/
noncomputable def linesProductFull
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  lineEvalNumAtFull E (P.1, -P.2)
    * ∏ j : Fin k, lineEvalNumAtFull E (B j)

/-- Line-product without the `-P` factor. -/
noncomputable def linesProductNoNegPFull
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) : FourVarPoly E.q :=
  ∏ j : Fin k, lineEvalNumAtFull E (B j)

/-- Line-product with the `j₀`th factor skipped. -/
noncomputable def linesProductSkipBjFull
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (j₀ : Fin k) : FourVarPoly E.q :=
  lineEvalNumAtFull E (P.1, -P.2)
    * ∏ j ∈ (Finset.univ (α := Fin k)).erase j₀, lineEvalNumAtFull E (B j)

/-- `D(A₀) · D(A₁) · D(A₂) · lamDen^D.degE`. -/
noncomputable def DAllFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  DAtA₀Full E D * DAtA₁Full E D * DAtA₂ScaledFull E D

/-- `dxdz_den(A₀) · dxdz_den(A₁) · dxdz_den(A₂) · lamDen^6`. -/
noncomputable def dxdzAllFull : FourVarPoly E.q :=
  dxdzDenA₀Full E * dxdzDenA₁Full E * dxdzDenA₂Full E

/-- `-b(A₀.1) · (3·A₀.1² + A)` scalar-ish lift. -/
noncomputable def DBdydzAtA₀Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  (-liftPoly E D.b 0) *
    ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₀x E ^ 2
      + (MvPolynomial.C E.curveA : FourVarPoly E.q))

/-- `-b(A₁.1) · (3·A₁.1² + A)`. -/
noncomputable def DBdydzAtA₁Full (D : CoordRingElt E.q) : FourVarPoly E.q :=
  (-liftPoly E D.b 2) *
    ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₁x E ^ 2
      + (MvPolynomial.C E.curveA : FourVarPoly E.q))

/-- `b(chordX₂) · lamDen^(2·b.natDegree)`, 4-variate (tight scaling). -/
noncomputable def DbAtA₂TightFull (D : CoordRingElt E.q) : FourVarPoly E.q :=
  ∑ n ∈ Finset.range (D.b.natDegree + 1),
    (MvPolynomial.C (D.b.coeff n) : FourVarPoly E.q)
      * x₂ScaledFull E ^ n
      * lamDenFull E ^ (2 * D.b.natDegree - 2 * n)

/-- `(3·chordX₂² + A) · lamDen⁴`. -/
noncomputable def dydzNumA₂Full : FourVarPoly E.q :=
  (MvPolynomial.C 3 : FourVarPoly E.q) * x₂ScaledFull E ^ 2
    + (MvPolynomial.C E.curveA : FourVarPoly E.q) * lamDenFull E ^ 4

/-- Correction core at A₂. -/
noncomputable def correctionA₂CoreFull (D : CoordRingElt E.q) :
    FourVarPoly E.q :=
  (-DbAtA₂TightFull E D) * dydzNumA₂Full E
    * lamDenFull E ^ (D.degE - 2 * D.b.natDegree - 3)

/-! ## 6 term Full definitions. -/

/-- LHS i=0 term (Full). -/
noncomputable def lhsTerm0Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  DDerivAtA₀Full E D
    * ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₀y E)
    * DAtA₁Full E D
    * DAtA₂ScaledFull E D
    * dxdzDenA₁Full E
    * dxdzDenA₂Full E
    * linesProductFull E P k B

noncomputable def lhsTerm1Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  DDerivAtA₁Full E D
    * ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₁y E)
    * DAtA₀Full E D
    * DAtA₂ScaledFull E D
    * dxdzDenA₀Full E
    * dxdzDenA₂Full E
    * linesProductFull E P k B

noncomputable def lhsTerm2Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  DDerivAtA₂ScaledFull E D
    * ((MvPolynomial.C 2 : FourVarPoly E.q) * y₂ScaledFull E)
    * DAtA₀Full E D
    * DAtA₁Full E D
    * dxdzDenA₀Full E
    * dxdzDenA₁Full E
    * linesProductFull E P k B

noncomputable def correctionTerm0Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  DBdydzAtA₀Full E D
    * DAtA₁Full E D
    * DAtA₂ScaledFull E D
    * dxdzDenA₁Full E
    * dxdzDenA₂Full E
    * linesProductFull E P k B

noncomputable def correctionTerm1Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  DBdydzAtA₁Full E D
    * DAtA₀Full E D
    * DAtA₂ScaledFull E D
    * dxdzDenA₀Full E
    * dxdzDenA₂Full E
    * linesProductFull E P k B

noncomputable def correctionTerm2Full (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    FourVarPoly E.q :=
  correctionA₂CoreFull E D
    * DAtA₀Full E D
    * DAtA₁Full E D
    * dxdzDenA₀Full E
    * dxdzDenA₁Full E
    * linesProductFull E P k B
    * lamDenFull E ^ 2

noncomputable def rhsTermNegPFull (D : CoordRingElt E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) : FourVarPoly E.q :=
  DAllFull E D * dxdzAllFull E * linesProductNoNegPFull E k B

noncomputable def rhsSumFull (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) : FourVarPoly E.q :=
  ∑ j : Fin k,
    (MvPolynomial.C (m j) : FourVarPoly E.q)
      * DAllFull E D * dxdzAllFull E
      * linesProductSkipBjFull E P k B j

/-- **The full 4-variate cleared-fiber polynomial.** Mirror of
    `clearedFiberPoly` with `A₀.1, A₀.2` lifted to `X 0, X 1`. -/
noncomputable def clearedFullPoly (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) : FourVarPoly E.q :=
  lhsTerm0Full E D P k B
    + lhsTerm1Full E D P k B
    + lhsTerm2Full E D P k B
    + correctionTerm0Full E D P k B
    + correctionTerm1Full E D P k B
    + correctionTerm2Full E D P k B
    + rhsTermNegPFull E D k B
    + rhsSumFull E D P k B m

/-! ## Compatibility of Full atoms with `clearedFiberPoly` atoms. -/

theorem bivEval₂_x₂ScaledFull_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (x₂ScaledFull E) A₀ A₁ = bivEval (x₂Scaled (E := E) A₀) A₁ := by
  rw [bivEval₂_x₂ScaledFull, bivEval_x₂Scaled]

theorem bivEval₂_y₂ScaledFull_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (y₂ScaledFull E) A₀ A₁ = bivEval (y₂Scaled (E := E) A₀) A₁ := by
  rw [bivEval₂_y₂ScaledFull, bivEval_y₂Scaled]

theorem bivEval₂_DAtA₀Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAtA₀Full E D) A₀ A₁ =
      bivEval (DAtA₀Poly (E := E) D A₀) A₁ := by
  rw [bivEval₂_DAtA₀Full, bivEval_DAtA₀Poly]

theorem bivEval₂_DAtA₁Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAtA₁Full E D) A₀ A₁ =
      bivEval (DAtA₁Poly (E := E) D) A₁ := by
  rw [bivEval₂_DAtA₁Full, bivEval_DAtA₁Poly]

theorem bivEval₂_DDerivAtA₀Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAtA₀Full E D) A₀ A₁ =
      bivEval (DDerivAtA₀Poly (E := E) D A₀) A₁ := by
  rw [bivEval₂_DDerivAtA₀Full, bivEval_DDerivAtA₀Poly]

theorem bivEval₂_DDerivAtA₁Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAtA₁Full E D) A₀ A₁ =
      bivEval (DDerivAtA₁Poly (E := E) D) A₁ := by
  rw [bivEval₂_DDerivAtA₁Full, bivEval_DDerivAtA₁Poly]

theorem bivEval₂_dxdzDenA₀Full_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzDenA₀Full E) A₀ A₁ =
      bivEval (dxdzDenA₀Scaled (E := E) A₀) A₁ := by
  rw [bivEval₂_dxdzDenA₀Full, bivEval_dxdzDenA₀Scaled]

theorem bivEval₂_dxdzDenA₁Full_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzDenA₁Full E) A₀ A₁ =
      bivEval (dxdzDenA₁Scaled (E := E) A₀) A₁ := by
  rw [bivEval₂_dxdzDenA₁Full, bivEval_dxdzDenA₁Scaled]

theorem bivEval₂_dxdzDenA₂Full_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzDenA₂Full E) A₀ A₁ =
      bivEval (dxdzDenA₂Scaled (E := E) A₀) A₁ := by
  rw [bivEval_dxdzDenA₂Scaled]
  simp [dxdzDenA₂Full, bivEval₂_sub, bivEval₂_add, bivEval₂_mul, bivEval₂_pow]

theorem bivEval₂_DAPartAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAPartAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DAPartAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DAPartAtA₂ScaledFull DAPartAtA₂Scaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_pow, bivEval₂_pow,
      bivEval_mul, bivEval_mul, bivEval_pow, bivEval_pow,
      bivEval₂_C, bivEval_embedScalar,
      bivEval₂_x₂ScaledFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_DBPartAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DBPartAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DBPartAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DBPartAtA₂ScaledFull DBPartAtA₂Scaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_mul, bivEval₂_pow, bivEval₂_pow,
      bivEval_mul, bivEval_mul, bivEval_mul, bivEval_pow, bivEval_pow,
      bivEval₂_C, bivEval_embedScalar,
      bivEval₂_x₂ScaledFull_eq_bivEval,
      bivEval₂_y₂ScaledFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_DAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DAtA₂ScaledFull DAtA₂Scaled
  rw [bivEval₂_sub, bivEval_sub,
      bivEval₂_DAPartAtA₂ScaledFull_eq_bivEval,
      bivEval₂_DBPartAtA₂ScaledFull_eq_bivEval]

theorem bivEval₂_DDerivAPartAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAPartAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DDerivAPartAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DDerivAPartAtA₂ScaledFull DDerivAPartAtA₂Scaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_pow, bivEval₂_pow,
      bivEval_mul, bivEval_mul, bivEval_pow, bivEval_pow,
      bivEval₂_C, bivEval_embedScalar,
      bivEval₂_x₂ScaledFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_DDerivBPartAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivBPartAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DDerivBPartAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DDerivBPartAtA₂ScaledFull DDerivBPartAtA₂Scaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_mul, bivEval₂_pow, bivEval₂_pow,
      bivEval_mul, bivEval_mul, bivEval_mul, bivEval_pow, bivEval_pow,
      bivEval₂_C, bivEval_embedScalar,
      bivEval₂_x₂ScaledFull_eq_bivEval,
      bivEval₂_y₂ScaledFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_DDerivAtA₂ScaledFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DDerivAtA₂ScaledFull E D) A₀ A₁ =
      bivEval (DDerivAtA₂Scaled (E := E) D A₀) A₁ := by
  unfold DDerivAtA₂ScaledFull DDerivAtA₂Scaled
  rw [bivEval₂_sub, bivEval_sub,
      bivEval₂_DDerivAPartAtA₂ScaledFull_eq_bivEval,
      bivEval₂_DDerivBPartAtA₂ScaledFull_eq_bivEval]

theorem bivEval₂_lineEvalNumAtFull_eq_bivEval (pt : ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lineEvalNumAtFull E pt) A₀ A₁ =
      bivEval (lineEvalNumAt (E := E) A₀ pt) A₁ := by
  rw [bivEval₂_lineEvalNumAtFull, bivEval_lineEvalNumAt]

theorem bivEval₂_linesProductFull_eq_bivEval
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (linesProductFull E P k B) A₀ A₁ =
      bivEval (linesProductScaled (E := E) P k B A₀) A₁ := by
  classical
  unfold linesProductFull linesProductScaled
  rw [bivEval₂_mul, bivEval_mul,
      bivEval₂_lineEvalNumAtFull_eq_bivEval]
  congr 1
  rw [bivEval₂_prod]
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [bivEval]
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
          bivEval_mul, ← ih, bivEval₂_lineEvalNumAtFull_eq_bivEval]

theorem bivEval₂_linesProductNoNegPFull_eq_bivEval
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (linesProductNoNegPFull E k B) A₀ A₁ =
      bivEval (linesProductNoNegPScaled (E := E) k B A₀) A₁ := by
  classical
  unfold linesProductNoNegPFull linesProductNoNegPScaled
  rw [bivEval₂_prod]
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [bivEval]
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
          bivEval_mul, ← ih, bivEval₂_lineEvalNumAtFull_eq_bivEval]

theorem bivEval₂_linesProductSkipBjFull_eq_bivEval
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (j₀ : Fin k) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (linesProductSkipBjFull E P k B j₀) A₀ A₁ =
      bivEval (linesProductSkipBjScaled (E := E) P k B A₀ j₀) A₁ := by
  classical
  unfold linesProductSkipBjFull linesProductSkipBjScaled
  rw [bivEval₂_mul, bivEval_mul,
      bivEval₂_lineEvalNumAtFull_eq_bivEval]
  congr 1
  rw [bivEval₂_prod]
  induction ((Finset.univ : Finset (Fin k)).erase j₀) using Finset.induction_on with
  | empty => simp [bivEval]
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
          bivEval_mul, ← ih, bivEval₂_lineEvalNumAtFull_eq_bivEval]

theorem bivEval₂_DAllFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DAllFull E D) A₀ A₁ =
      bivEval (DAllScaled (E := E) D A₀) A₁ := by
  unfold DAllFull DAllScaled
  rw [bivEval₂_mul, bivEval₂_mul, bivEval_mul, bivEval_mul,
      bivEval₂_DAtA₀Full_eq_bivEval, bivEval₂_DAtA₁Full_eq_bivEval,
      bivEval₂_DAtA₂ScaledFull_eq_bivEval]

theorem bivEval₂_dxdzAllFull_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dxdzAllFull E) A₀ A₁ =
      bivEval (dxdzAllScaled (E := E) A₀) A₁ := by
  unfold dxdzAllFull dxdzAllScaled
  rw [bivEval₂_mul, bivEval₂_mul, bivEval_mul, bivEval_mul,
      bivEval₂_dxdzDenA₀Full_eq_bivEval, bivEval₂_dxdzDenA₁Full_eq_bivEval,
      bivEval₂_dxdzDenA₂Full_eq_bivEval]

theorem bivEval₂_DBdydzAtA₀Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DBdydzAtA₀Full E D) A₀ A₁ =
      bivEval (DBdydzAtA₀Poly (E := E) D A₀) A₁ := by
  unfold DBdydzAtA₀Full DBdydzAtA₀Poly
  simp [bivEval₂_mul, bivEval₂_neg, bivEval₂_add, bivEval₂_pow,
        bivEval, embedScalar]

theorem bivEval₂_DBdydzAtA₁Full_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DBdydzAtA₁Full E D) A₀ A₁ =
      bivEval (DBdydzAtA₁Poly (E := E) D) A₁ := by
  unfold DBdydzAtA₁Full DBdydzAtA₁Poly
  simp [bivEval₂_mul, bivEval₂_neg, bivEval₂_add, bivEval₂_pow,
        bivEval, embedInnerPoly, innerA₁x, embedScalar]

theorem bivEval₂_DbAtA₂TightFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (DbAtA₂TightFull E D) A₀ A₁ =
      bivEval (DbAtA₂TightScaled (E := E) D A₀) A₁ := by
  unfold DbAtA₂TightFull DbAtA₂TightScaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_pow, bivEval₂_pow,
      bivEval_mul, bivEval_mul, bivEval_pow, bivEval_pow,
      bivEval₂_C, bivEval_embedScalar,
      bivEval₂_x₂ScaledFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_dydzNumA₂Full_eq_bivEval (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (dydzNumA₂Full E) A₀ A₁ =
      bivEval (dydzNumA₂Scaled (E := E) A₀) A₁ := by
  unfold dydzNumA₂Full dydzNumA₂Scaled
  simp [bivEval₂_add, bivEval₂_mul, bivEval₂_pow,
        bivEval_add, bivEval_mul, bivEval_pow]

theorem bivEval₂_correctionA₂CoreFull_eq_bivEval (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (correctionA₂CoreFull E D) A₀ A₁ =
      bivEval (correctionA₂ScaledCore (E := E) D A₀) A₁ := by
  unfold correctionA₂CoreFull correctionA₂ScaledCore
  rw [bivEval₂_mul, bivEval₂_mul, bivEval_mul, bivEval_mul,
      bivEval₂_neg, bivEval_neg, bivEval₂_pow, bivEval_pow,
      bivEval₂_DbAtA₂TightFull_eq_bivEval,
      bivEval₂_dydzNumA₂Full_eq_bivEval, bivEval_lamDenPoly,
      bivEval₂_lamDenFull]

/-! ### Per-term compat lemmas. -/

theorem bivEval₂_lhsTerm0Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lhsTerm0Full E D P k B) A₀ A₁ =
      bivEval (lhsTerm0Scaled (E := E) D P k B A₀) A₁ := by
  unfold lhsTerm0Full lhsTerm0Scaled
  simp only [bivEval₂_mul, bivEval_mul,
      bivEval₂_DDerivAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₁Full_eq_bivEval,
      bivEval₂_DAtA₂ScaledFull_eq_bivEval,
      bivEval₂_dxdzDenA₁Full_eq_bivEval,
      bivEval₂_dxdzDenA₂Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval]
  simp [bivEval₂_mul, bivEval, embedScalar]

theorem bivEval₂_lhsTerm1Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lhsTerm1Full E D P k B) A₀ A₁ =
      bivEval (lhsTerm1Scaled (E := E) D P k B A₀) A₁ := by
  unfold lhsTerm1Full lhsTerm1Scaled
  simp only [bivEval₂_mul, bivEval_mul,
      bivEval₂_DDerivAtA₁Full_eq_bivEval,
      bivEval₂_DAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₂ScaledFull_eq_bivEval,
      bivEval₂_dxdzDenA₀Full_eq_bivEval,
      bivEval₂_dxdzDenA₂Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval]
  simp [bivEval₂_mul, bivEval, embedScalar, outerA₁y]

theorem bivEval₂_lhsTerm2Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (lhsTerm2Full E D P k B) A₀ A₁ =
      bivEval (lhsTerm2Scaled (E := E) D P k B A₀) A₁ := by
  unfold lhsTerm2Full lhsTerm2Scaled
  simp only [bivEval₂_mul, bivEval_mul,
      bivEval₂_DDerivAtA₂ScaledFull_eq_bivEval,
      bivEval₂_DAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₁Full_eq_bivEval,
      bivEval₂_dxdzDenA₀Full_eq_bivEval,
      bivEval₂_dxdzDenA₁Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval,
      bivEval₂_y₂ScaledFull_eq_bivEval]
  simp [bivEval₂_mul, bivEval, embedScalar]

theorem bivEval₂_correctionTerm0Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (correctionTerm0Full E D P k B) A₀ A₁ =
      bivEval (correctionTerm0Scaled (E := E) D P k B A₀) A₁ := by
  unfold correctionTerm0Full correctionTerm0Scaled
  simp only [bivEval₂_mul, bivEval_mul,
      bivEval₂_DBdydzAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₁Full_eq_bivEval,
      bivEval₂_DAtA₂ScaledFull_eq_bivEval,
      bivEval₂_dxdzDenA₁Full_eq_bivEval,
      bivEval₂_dxdzDenA₂Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval]

theorem bivEval₂_correctionTerm1Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (correctionTerm1Full E D P k B) A₀ A₁ =
      bivEval (correctionTerm1Scaled (E := E) D P k B A₀) A₁ := by
  unfold correctionTerm1Full correctionTerm1Scaled
  simp only [bivEval₂_mul, bivEval_mul,
      bivEval₂_DBdydzAtA₁Full_eq_bivEval,
      bivEval₂_DAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₂ScaledFull_eq_bivEval,
      bivEval₂_dxdzDenA₀Full_eq_bivEval,
      bivEval₂_dxdzDenA₂Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval]

theorem bivEval₂_correctionTerm2Full_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (correctionTerm2Full E D P k B) A₀ A₁ =
      bivEval (correctionTerm2Scaled (E := E) D P k B A₀) A₁ := by
  unfold correctionTerm2Full correctionTerm2Scaled
  simp only [bivEval₂_mul, bivEval_mul, bivEval₂_pow, bivEval_pow,
      bivEval₂_correctionA₂CoreFull_eq_bivEval,
      bivEval₂_DAtA₀Full_eq_bivEval,
      bivEval₂_DAtA₁Full_eq_bivEval,
      bivEval₂_dxdzDenA₀Full_eq_bivEval,
      bivEval₂_dxdzDenA₁Full_eq_bivEval,
      bivEval₂_linesProductFull_eq_bivEval,
      bivEval₂_lamDenFull, bivEval_lamDenPoly]

theorem bivEval₂_rhsTermNegPFull_eq_bivEval
    (D : CoordRingElt E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (rhsTermNegPFull E D k B) A₀ A₁ =
      bivEval (rhsTermNegPScaled (E := E) D k B A₀) A₁ := by
  unfold rhsTermNegPFull rhsTermNegPScaled
  rw [bivEval₂_mul, bivEval₂_mul, bivEval_mul, bivEval_mul,
      bivEval₂_DAllFull_eq_bivEval, bivEval₂_dxdzAllFull_eq_bivEval,
      bivEval₂_linesProductNoNegPFull_eq_bivEval]

theorem bivEval₂_rhsSumFull_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (rhsSumFull E D P k B m) A₀ A₁ =
      bivEval (rhsSumScaled (E := E) D P k B m A₀) A₁ := by
  classical
  unfold rhsSumFull rhsSumScaled
  rw [bivEval₂_sum, bivEval_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [bivEval₂_mul, bivEval₂_mul, bivEval₂_mul,
      bivEval_mul, bivEval_mul, bivEval_mul,
      bivEval₂_DAllFull_eq_bivEval, bivEval₂_dxdzAllFull_eq_bivEval,
      bivEval₂_linesProductSkipBjFull_eq_bivEval]
  simp [bivEval, embedScalar]

/-! ### `clearedFullPoly` ↔ `clearedFiberPoly` compat. -/

theorem bivEval₂_clearedFullPoly_eq_bivEval
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ =
      bivEval (clearedFiberPoly (E := E) D P k B m A₀) A₁ := by
  unfold clearedFullPoly clearedFiberPoly
  simp only [bivEval₂_add, bivEval_add,
      bivEval₂_lhsTerm0Full_eq_bivEval,
      bivEval₂_lhsTerm1Full_eq_bivEval,
      bivEval₂_lhsTerm2Full_eq_bivEval,
      bivEval₂_correctionTerm0Full_eq_bivEval,
      bivEval₂_correctionTerm1Full_eq_bivEval,
      bivEval₂_correctionTerm2Full_eq_bivEval,
      bivEval₂_rhsTermNegPFull_eq_bivEval,
      bivEval₂_rhsSumFull_eq_bivEval]

/-- **Phase 3 identity.** Follows from compat with `clearedFiberPoly`
    combined with the existing `clearedFiberPoly_identity`. -/
theorem clearedFullPoly_identity
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          logDerivCheckFnCleared E D P k B m A₀ A₁ := by
  rw [bivEval₂_clearedFullPoly_eq_bivEval,
      clearedFiberPoly_identity E D P B m A₀ A₁ hNV hDef]

/-! ### Phase 4: bi-x-degree bound — atomic helpers -/

private lemma varA₀y_bi : bi_x_degree_le E (varA₀y E) 0 0 := by
  unfold varA₀y; exact bi_x_degree_le.Y₀
private lemma varA₁y_bi : bi_x_degree_le E (varA₁y E) 0 0 := by
  unfold varA₁y; exact bi_x_degree_le.Y₁
private lemma lamNumFull_bi : bi_x_degree_le E (lamNumFull E) 0 0 := by
  unfold lamNumFull
  exact bi_x_degree_le.sub (varA₁y_bi E) (varA₀y_bi E)
private lemma lamDenFull_bi : bi_x_degree_le E (lamDenFull E) 1 1 := by
  unfold lamDenFull
  exact (show bi_x_degree_le E (varA₁x E) 1 1 by
    unfold varA₁x; exact bi_x_degree_le.X₁.mono (by omega) (by omega)).sub
   (show bi_x_degree_le E (varA₀x E) 1 1 by
    unfold varA₀x; exact bi_x_degree_le.X₀.mono (by omega) (by omega))

private lemma lineEvalNumAtFull_bi (pt : ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lineEvalNumAtFull E pt) 1 1 := by
  unfold lineEvalNumAtFull embedScalarFull
  have h1 : bi_x_degree_le E
      (((MvPolynomial.C pt.2 : FourVarPoly E.q) - varA₀y E) * lamDenFull E) 1 1 :=
    ((bi_x_degree_le.C pt.2).sub (varA₀y_bi E)).mul (lamDenFull_bi E)
  have h2 : bi_x_degree_le E
      (((MvPolynomial.C pt.1 : FourVarPoly E.q) - varA₀x E) * lamNumFull E) 1 1 := by
    have hc : bi_x_degree_le E (MvPolynomial.C pt.1 : FourVarPoly E.q) 1 0 :=
      (bi_x_degree_le.C pt.1).mono (by omega) (by omega)
    have hx : bi_x_degree_le E (varA₀x E) 1 0 := by unfold varA₀x; exact bi_x_degree_le.X₀
    have hl : bi_x_degree_le E (lamNumFull E) 1 1 := (lamNumFull_bi E).mono (by omega) (by omega)
    exact ((hc.sub hx).mul (lamNumFull_bi E)).mono (by omega) (by omega)
  exact h1.sub h2

private lemma x₂ScaledFull_bi : bi_x_degree_le E (x₂ScaledFull E) 3 3 := by
  unfold x₂ScaledFull
  exact ((lamNumFull_bi E).pow 2 |>.mono (by omega) (by omega)).sub
    (((show bi_x_degree_le E (varA₀x E) 1 1 by
        unfold varA₀x; exact bi_x_degree_le.X₀.mono (by omega) (by omega)).add
       (show bi_x_degree_le E (varA₁x E) 1 1 by
        unfold varA₁x; exact bi_x_degree_le.X₁.mono (by omega) (by omega))).mul
       ((lamDenFull_bi E).pow 2) |>.mono (by omega) (by omega))

private lemma y₂ScaledFull_bi : bi_x_degree_le E (y₂ScaledFull E) 3 3 := by
  unfold y₂ScaledFull
  have h1 : bi_x_degree_le E (lamNumFull E * x₂ScaledFull E) 3 3 :=
    ((lamNumFull_bi E).mul (x₂ScaledFull_bi E)).mono (by omega) (by omega)
  have h2 : bi_x_degree_le E
      ((varA₀y E * lamDenFull E - varA₀x E * lamNumFull E) * lamDenFull E ^ 2) 3 3 := by
    have ha : bi_x_degree_le E (varA₀y E * lamDenFull E) 1 1 :=
      (varA₀y_bi E).mul (lamDenFull_bi E)
    have hb : bi_x_degree_le E (varA₀x E * lamNumFull E) 1 1 :=
      ((show bi_x_degree_le E (varA₀x E) 1 0 by
        unfold varA₀x; exact bi_x_degree_le.X₀).mul
        (lamNumFull_bi E)).mono (by omega) (by omega)
    exact (ha.sub hb).mul ((lamDenFull_bi E).pow 2)
  exact h1.add h2

private lemma liftPoly_bi_0 (p : (ZMod E.q)[X]) :
    bi_x_degree_le E (liftPoly E p 0) p.natDegree 0 :=
  ⟨liftPoly_degreeOf_target_le E p 0,
   le_of_eq (liftPoly_degreeOf_other E p 0 2 (by decide))⟩

private lemma liftPoly_bi_2 (p : (ZMod E.q)[X]) :
    bi_x_degree_le E (liftPoly E p 2) 0 p.natDegree :=
  ⟨le_of_eq (liftPoly_degreeOf_other E p 2 0 (by decide)),
   liftPoly_degreeOf_target_le E p 2⟩

private lemma a_natDegree_le_degE (D : CoordRingElt E.q) :
    D.a.natDegree ≤ D.degE := by
  unfold CoordRingElt.degE
  exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) (le_max_left _ _)

private lemma b_natDegree_le_degE (D : CoordRingElt E.q) :
    D.b.natDegree ≤ D.degE := by
  unfold CoordRingElt.degE
  exact le_trans (le_trans (Nat.le_mul_of_pos_left _ (by omega))
    (Nat.le_add_left _ _)) (le_max_right _ _)

private lemma two_a_le_degE (D : CoordRingElt E.q) :
    2 * D.a.natDegree ≤ D.degE := by
  unfold CoordRingElt.degE; exact le_max_left _ _

private lemma two_b_plus_3_le_degE (D : CoordRingElt E.q) :
    3 + 2 * D.b.natDegree ≤ D.degE := by
  unfold CoordRingElt.degE; exact le_max_right _ _

private lemma deriv_a_natDegree_le_degE (D : CoordRingElt E.q) :
    (Polynomial.derivative D.a).natDegree ≤ D.degE :=
  le_trans (le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _))
    (a_natDegree_le_degE E D)

private lemma deriv_b_natDegree_le_degE (D : CoordRingElt E.q) :
    (Polynomial.derivative D.b).natDegree ≤ D.degE :=
  le_trans (le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _))
    (b_natDegree_le_degE E D)

private lemma DAtA₀Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DAtA₀Full E D) D.degE 0 := by
  unfold DAtA₀Full
  have ha := a_natDegree_le_degE E D
  have hb := b_natDegree_le_degE E D
  exact ((liftPoly_bi_0 E D.a).mono (by omega) (by omega)).sub
    (((liftPoly_bi_0 E D.b).mul (varA₀y_bi E)).mono (by omega) (by omega))

private lemma DAtA₁Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DAtA₁Full E D) 0 D.degE := by
  unfold DAtA₁Full
  have ha := a_natDegree_le_degE E D
  have hb := b_natDegree_le_degE E D
  exact ((liftPoly_bi_2 E D.a).mono (by omega) (by omega)).sub
    (((liftPoly_bi_2 E D.b).mul (varA₁y_bi E)).mono (by omega) (by omega))

private lemma DDerivAtA₀Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DDerivAtA₀Full E D) D.degE 0 := by
  unfold DDerivAtA₀Full
  have ha := deriv_a_natDegree_le_degE E D
  have hb := deriv_b_natDegree_le_degE E D
  exact ((liftPoly_bi_0 E (Polynomial.derivative D.a)).mono (by omega) (by omega)).sub
    (((liftPoly_bi_0 E (Polynomial.derivative D.b)).mul (varA₀y_bi E)).mono (by omega) (by omega))

private lemma DDerivAtA₁Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DDerivAtA₁Full E D) 0 D.degE := by
  unfold DDerivAtA₁Full
  have ha := deriv_a_natDegree_le_degE E D
  have hb := deriv_b_natDegree_le_degE E D
  exact ((liftPoly_bi_2 E (Polynomial.derivative D.a)).mono (by omega) (by omega)).sub
    (((liftPoly_bi_2 E (Polynomial.derivative D.b)).mul (varA₁y_bi E)).mono (by omega) (by omega))

private lemma APartScaledFull_bi (a_coeff : ℕ → ZMod E.q) (deg bound : ℕ)
    (hbd : deg ≤ bound) (h2d : 2 * deg ≤ bound) :
    bi_x_degree_le E
      (∑ n ∈ Finset.range (deg + 1),
        (MvPolynomial.C (a_coeff n) : FourVarPoly E.q)
          * x₂ScaledFull E ^ n * lamDenFull E ^ (bound - 2 * n))
      (2 * bound) (2 * bound) := by
  apply bi_x_degree_le.sum
  intro n hn
  simp only [Finset.mem_range] at hn
  have hn' : n ≤ deg := by omega
  apply bi_x_degree_le.mono
  · exact ((bi_x_degree_le.C _).mul ((x₂ScaledFull_bi E).pow n)).mul
      ((lamDenFull_bi E).pow (bound - 2 * n))
  · omega
  · omega

private lemma BPartScaledFull_bi (b_coeff : ℕ → ZMod E.q) (deg bound : ℕ)
    (hbd : deg ≤ bound) (h3d : 3 + 2 * deg ≤ bound) :
    bi_x_degree_le E
      (∑ n ∈ Finset.range (deg + 1),
        (MvPolynomial.C (b_coeff n) : FourVarPoly E.q)
          * x₂ScaledFull E ^ n * y₂ScaledFull E
          * lamDenFull E ^ (bound - 2 * n - 3))
      (2 * bound) (2 * bound) := by
  apply bi_x_degree_le.sum
  intro n hn
  simp only [Finset.mem_range] at hn
  have hn' : n ≤ deg := by omega
  apply bi_x_degree_le.mono
  · exact (((bi_x_degree_le.C _).mul ((x₂ScaledFull_bi E).pow n)).mul
      (y₂ScaledFull_bi E)).mul ((lamDenFull_bi E).pow (bound - 2 * n - 3))
  · have : 2 * n + 3 ≤ bound := by omega
    omega
  · have : 2 * n + 3 ≤ bound := by omega
    omega

private lemma DAtA₂ScaledFull_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
  unfold DAtA₂ScaledFull
  have hA : bi_x_degree_le E (DAPartAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
    unfold DAPartAtA₂ScaledFull
    exact APartScaledFull_bi E (D.a.coeff) D.a.natDegree D.degE
      (a_natDegree_le_degE E D) (two_a_le_degE E D)
  have hB : bi_x_degree_le E (DBPartAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
    unfold DBPartAtA₂ScaledFull
    exact BPartScaledFull_bi E (D.b.coeff) D.b.natDegree D.degE
      (b_natDegree_le_degE E D) (two_b_plus_3_le_degE E D)
  exact hA.sub hB

private lemma DDerivAtA₂ScaledFull_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DDerivAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
  unfold DDerivAtA₂ScaledFull
  have hda := deriv_a_natDegree_le_degE E D
  have hdb := deriv_b_natDegree_le_degE E D
  have h2da : 2 * (Polynomial.derivative D.a).natDegree ≤ D.degE := by
    have := Polynomial.natDegree_derivative_le D.a
    have := two_a_le_degE E D; omega
  have h2db : 2 * (Polynomial.derivative D.b).natDegree ≤ D.degE := by
    have := Polynomial.natDegree_derivative_le D.b
    have := two_b_plus_3_le_degE E D; omega
  have h3db : 3 + 2 * (Polynomial.derivative D.b).natDegree ≤ D.degE := by
    have := Polynomial.natDegree_derivative_le D.b
    have := two_b_plus_3_le_degE E D; omega
  have hA : bi_x_degree_le E (DDerivAPartAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
    unfold DDerivAPartAtA₂ScaledFull
    exact APartScaledFull_bi E _ _ _ hda h2da
  have hB : bi_x_degree_le E (DDerivBPartAtA₂ScaledFull E D) (2 * D.degE) (2 * D.degE) := by
    unfold DDerivBPartAtA₂ScaledFull
    exact BPartScaledFull_bi E _ _ _ hdb h3db
  exact hA.sub hB

private lemma dxdzDenA₀Full_bi : bi_x_degree_le E (dxdzDenA₀Full E) 3 1 := by
  unfold dxdzDenA₀Full
  have hx0 : bi_x_degree_le E (varA₀x E) 1 0 := by unfold varA₀x; exact bi_x_degree_le.X₀
  have h3x2 : bi_x_degree_le E
      ((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₀x E ^ 2) 2 0 :=
    (bi_x_degree_le.C _).mul (hx0.pow 2)
  have hfst : bi_x_degree_le E
      (((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₀x E ^ 2
        + (MvPolynomial.C E.curveA : FourVarPoly E.q)) * lamDenFull E) 3 1 :=
    (h3x2.add ((bi_x_degree_le.C E.curveA).mono (by omega) (by omega))).mul (lamDenFull_bi E)
  have hsnd : bi_x_degree_le E
      ((MvPolynomial.C (2 : ZMod E.q) : FourVarPoly E.q) * varA₀y E * lamNumFull E) 3 1 :=
    ((bi_x_degree_le.C _).mul (varA₀y_bi E) |>.mul (lamNumFull_bi E)).mono (by omega) (by omega)
  exact hfst.sub hsnd

private lemma dxdzDenA₁Full_bi : bi_x_degree_le E (dxdzDenA₁Full E) 1 3 := by
  unfold dxdzDenA₁Full
  have hx1 : bi_x_degree_le E (varA₁x E) 0 1 := by unfold varA₁x; exact bi_x_degree_le.X₁
  have h3x2 : bi_x_degree_le E
      ((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₁x E ^ 2) 0 2 :=
    (bi_x_degree_le.C _).mul (hx1.pow 2)
  have hfst : bi_x_degree_le E
      (((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₁x E ^ 2
        + (MvPolynomial.C E.curveA : FourVarPoly E.q)) * lamDenFull E) 1 3 :=
    (h3x2.add ((bi_x_degree_le.C E.curveA).mono (by omega) (by omega))).mul (lamDenFull_bi E)
  have hsnd : bi_x_degree_le E
      ((MvPolynomial.C (2 : ZMod E.q) : FourVarPoly E.q) * varA₁y E * lamNumFull E) 1 3 :=
    ((bi_x_degree_le.C _).mul (varA₁y_bi E) |>.mul (lamNumFull_bi E)).mono (by omega) (by omega)
  exact hfst.sub hsnd

private lemma dxdzDenA₂Full_bi : bi_x_degree_le E (dxdzDenA₂Full E) 6 6 := by
  unfold dxdzDenA₂Full
  have h1 : bi_x_degree_le E
      ((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * x₂ScaledFull E ^ 2) 6 6 :=
    ((bi_x_degree_le.C _).mul ((x₂ScaledFull_bi E).pow 2)).mono (by omega) (by omega)
  have h2 : bi_x_degree_le E
      ((MvPolynomial.C E.curveA : FourVarPoly E.q) * lamDenFull E ^ 4) 6 6 :=
    ((bi_x_degree_le.C E.curveA).mul ((lamDenFull_bi E).pow 4)).mono (by omega) (by omega)
  have h3 : bi_x_degree_le E
      ((MvPolynomial.C (2 : ZMod E.q) : FourVarPoly E.q) * lamNumFull E * y₂ScaledFull E) 6 6 :=
    ((bi_x_degree_le.C _).mul (lamNumFull_bi E) |>.mul (y₂ScaledFull_bi E)).mono (by omega) (by omega)
  exact (h1.add h2).sub h3

private lemma DBdydzAtA₀Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DBdydzAtA₀Full E D) D.degE 0 := by
  unfold DBdydzAtA₀Full
  have hb := b_natDegree_le_degE E D
  have hb3 := two_b_plus_3_le_degE E D
  have hx0 : bi_x_degree_le E (varA₀x E) 1 0 := by unfold varA₀x; exact bi_x_degree_le.X₀
  have h3x2a : bi_x_degree_le E
      ((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₀x E ^ 2
        + (MvPolynomial.C E.curveA : FourVarPoly E.q)) 2 0 :=
    ((bi_x_degree_le.C _).mul (hx0.pow 2)).add ((bi_x_degree_le.C E.curveA).mono (by omega) (by omega))
  exact ((liftPoly_bi_0 E D.b).neg.mul h3x2a).mono (by omega) (by omega)

private lemma DBdydzAtA₁Full_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (DBdydzAtA₁Full E D) 0 D.degE := by
  unfold DBdydzAtA₁Full
  have hb := b_natDegree_le_degE E D
  have hb3 := two_b_plus_3_le_degE E D
  have hx1 : bi_x_degree_le E (varA₁x E) 0 1 := by unfold varA₁x; exact bi_x_degree_le.X₁
  have h3x2a : bi_x_degree_le E
      ((MvPolynomial.C (3 : ZMod E.q) : FourVarPoly E.q) * varA₁x E ^ 2
        + (MvPolynomial.C E.curveA : FourVarPoly E.q)) 0 2 :=
    ((bi_x_degree_le.C _).mul (hx1.pow 2)).add ((bi_x_degree_le.C E.curveA).mono (by omega) (by omega))
  exact ((liftPoly_bi_2 E D.b).neg.mul h3x2a).mono (by omega) (by omega)

private lemma correctionA₂CoreFull_bi (D : CoordRingElt E.q) :
    bi_x_degree_le E (correctionA₂CoreFull E D)
      (2 * D.degE + 3) (2 * D.degE + 3) := by
  unfold correctionA₂CoreFull
  have hb := b_natDegree_le_degE E D
  have h2b3 := two_b_plus_3_le_degE E D
  have hDb : bi_x_degree_le E (DbAtA₂TightFull E D)
      (3 * D.b.natDegree) (3 * D.b.natDegree) := by
    unfold DbAtA₂TightFull
    apply bi_x_degree_le.sum
    intro n hn
    simp only [Finset.mem_range] at hn
    exact ((bi_x_degree_le.C _).mul ((x₂ScaledFull_bi E).pow n) |>.mul
      ((lamDenFull_bi E).pow (2 * D.b.natDegree - 2 * n))).mono (by omega) (by omega)
  have hDyz : bi_x_degree_le E (dydzNumA₂Full E) 6 6 := by
    unfold dydzNumA₂Full
    exact ((bi_x_degree_le.C (3 : ZMod E.q)).mul
      ((x₂ScaledFull_bi E).pow 2) |>.mono (by omega) (by omega)).add
      ((bi_x_degree_le.C E.curveA).mul ((lamDenFull_bi E).pow 4)
        |>.mono (by omega) (by omega))
  exact (hDb.neg.mul hDyz |>.mul
    ((lamDenFull_bi E).pow (D.degE - 2 * D.b.natDegree - 3))).mono (by omega) (by omega)

private lemma linesProductFull_bi (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (linesProductFull E P k B) (k + 1) (k + 1) := by
  unfold linesProductFull
  exact ((lineEvalNumAtFull_bi E (P.1, -P.2)).mul
    (bi_x_degree_le.prod_fin (fun j => lineEvalNumAtFull E (B j))
      (fun j => lineEvalNumAtFull_bi E (B j)))).mono (by omega) (by omega)

private lemma linesProductNoNegPFull_bi
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (linesProductNoNegPFull E k B) k k := by
  unfold linesProductNoNegPFull
  exact (bi_x_degree_le.prod_fin (fun j => lineEvalNumAtFull E (B j))
    (fun j => lineEvalNumAtFull_bi E (B j))).mono (by omega) (by omega)

private lemma bi_x_degree_le_prod_finset_fin {k : ℕ}
    (s : Finset (Fin k)) (f : Fin k → FourVarPoly E.q) {dX dY : ℕ}
    (hf : ∀ i ∈ s, bi_x_degree_le E (f i) dX dY) :
    bi_x_degree_le E (∏ i ∈ s, f i) (s.card * dX) (s.card * dY) := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_⟩ <;> simp [MvPolynomial.degreeOf_C]
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    exact (bi_x_degree_le.mul (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))).mono (by nlinarith) (by nlinarith)

private lemma linesProductSkipBjFull_bi (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (j : Fin k) :
    bi_x_degree_le E (linesProductSkipBjFull E P k B j) k k := by
  unfold linesProductSkipBjFull
  have h1 := lineEvalNumAtFull_bi E (P.1, -P.2)
  have h2 := bi_x_degree_le_prod_finset_fin E ((Finset.univ (α := Fin k)).erase j)
    (fun j => lineEvalNumAtFull E (B j))
    (fun i _ => lineEvalNumAtFull_bi E (B i))
  have hcard_eq : ((Finset.univ (α := Fin k)).erase j).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
  have hk : 0 < k := Fin.pos j
  rw [hcard_eq] at h2
  exact (h1.mul h2).mono (by omega) (by omega)

/-! ### Phase 4: bi-x-degree bound — summand helpers -/

private lemma lhsTerm0Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lhsTerm0Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold lhsTerm0Full
  exact ((((((DDerivAtA₀Full_bi E D).mul
    ((bi_x_degree_le.C (2 : ZMod E.q)).mul (varA₀y_bi E))).mul
    (DAtA₁Full_bi E D)).mul
    (DAtA₂ScaledFull_bi E D)).mul
    (dxdzDenA₁Full_bi E)).mul
    (dxdzDenA₂Full_bi E)).mul
    (linesProductFull_bi E P B) |>.mono (by omega) (by omega)

private lemma lhsTerm1Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lhsTerm1Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold lhsTerm1Full
  exact ((((((DDerivAtA₁Full_bi E D).mul
    ((bi_x_degree_le.C (2 : ZMod E.q)).mul (varA₁y_bi E))).mul
    (DAtA₀Full_bi E D)).mul
    (DAtA₂ScaledFull_bi E D)).mul
    (dxdzDenA₀Full_bi E)).mul
    (dxdzDenA₂Full_bi E)).mul
    (linesProductFull_bi E P B) |>.mono (by omega) (by omega)

private lemma lhsTerm2Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lhsTerm2Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold lhsTerm2Full
  exact ((((((DDerivAtA₂ScaledFull_bi E D).mul
    ((bi_x_degree_le.C (2 : ZMod E.q)).mul (y₂ScaledFull_bi E))).mul
    (DAtA₀Full_bi E D)).mul
    (DAtA₁Full_bi E D)).mul
    (dxdzDenA₀Full_bi E)).mul
    (dxdzDenA₁Full_bi E)).mul
    (linesProductFull_bi E P B) |>.mono (by omega) (by omega)

private lemma correctionTerm0Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (correctionTerm0Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold correctionTerm0Full
  exact (((((DBdydzAtA₀Full_bi E D).mul
    (DAtA₁Full_bi E D)).mul
    (DAtA₂ScaledFull_bi E D)).mul
    (dxdzDenA₁Full_bi E)).mul
    (dxdzDenA₂Full_bi E)).mul
    (linesProductFull_bi E P B) |>.mono (by omega) (by omega)

private lemma correctionTerm1Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (correctionTerm1Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold correctionTerm1Full
  exact (((((DBdydzAtA₁Full_bi E D).mul
    (DAtA₀Full_bi E D)).mul
    (DAtA₂ScaledFull_bi E D)).mul
    (dxdzDenA₀Full_bi E)).mul
    (dxdzDenA₂Full_bi E)).mul
    (linesProductFull_bi E P B) |>.mono (by omega) (by omega)

private lemma correctionTerm2Full_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (correctionTerm2Full E D P k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold correctionTerm2Full
  exact ((((((correctionA₂CoreFull_bi E D).mul
    (DAtA₀Full_bi E D)).mul
    (DAtA₁Full_bi E D)).mul
    (dxdzDenA₀Full_bi E)).mul
    (dxdzDenA₁Full_bi E)).mul
    (linesProductFull_bi E P B)).mul
    ((lamDenFull_bi E).pow 2) |>.mono (by omega) (by omega)

private lemma rhsTermNegPFull_bi (D : CoordRingElt E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (rhsTermNegPFull E D k B)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold rhsTermNegPFull DAllFull dxdzAllFull
  exact (((((DAtA₀Full_bi E D).mul (DAtA₁Full_bi E D)).mul
    (DAtA₂ScaledFull_bi E D)).mul
    ((dxdzDenA₀Full_bi E).mul (dxdzDenA₁Full_bi E) |>.mul (dxdzDenA₂Full_bi E))).mul
    (linesProductNoNegPFull_bi E B)).mono (by omega) (by omega)

private lemma rhsSumFull_bi (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) :
    bi_x_degree_le E (rhsSumFull E D P k B m)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold rhsSumFull
  apply bi_x_degree_le.sum
  intro j _
  unfold DAllFull dxdzAllFull
  exact ((((bi_x_degree_le.C (m j)).mul
    (((DAtA₀Full_bi E D).mul (DAtA₁Full_bi E D)).mul (DAtA₂ScaledFull_bi E D))).mul
    ((dxdzDenA₀Full_bi E).mul (dxdzDenA₁Full_bi E) |>.mul (dxdzDenA₂Full_bi E))).mul
    (linesProductSkipBjFull_bi E P B j)).mono (by omega) (by omega)

/-- **Phase 4 bi-x-degree bound.** `clearedFullPoly` has bi-x-degree
    bounded by `9·(D.degE + k + 6)` in both `X 0` and `X 2`. Each of
    the 8 summands is proven separately via private helpers above. -/
theorem clearedFullPoly_bi_x_degree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    bi_x_degree_le E (clearedFullPoly E D P k B m)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  unfold clearedFullPoly
  exact (lhsTerm0Full_bi E D P B).add (lhsTerm1Full_bi E D P B)
    |>.add (lhsTerm2Full_bi E D P B)
    |>.add (correctionTerm0Full_bi E D P B)
    |>.add (correctionTerm1Full_bi E D P B)
    |>.add (correctionTerm2Full_bi E D P B)
    |>.add (rhsTermNegPFull_bi E D B)
    |>.add (rhsSumFull_bi E D P B m)

/-- **Phase 5 nonzero-witness on E × E.** Any non-degenerate log-deriv
    witness `(A₀, A₁)` yields `bivEval₂ clearedFullPoly A₀ A₁ ≠ 0` via
    the Phase 3 identity: `bivEval₂ clearedFullPoly = (A₁.1 − A₀.1)^N ·
    logDerivCheckFn · logDerivCheckFnDenom`, all three factors nonzero. -/
theorem clearedFullPoly_nonzero_witness
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
      bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ ≠ 0 := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hNVx, hDef, hCheck⟩ := hNV
  refine ⟨A₀, A₁, hA₀, hA₁, ?_⟩
  rw [clearedFullPoly_identity E D P B m A₀ A₁ hNVx hDef]
  unfold logDerivCheckFnCleared
  have hDenNZ : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0 := hDef
  have hPowNZ : (A₁.1 - A₀.1) ^ (D.degE + k + 6) ≠ 0 := by
    apply pow_ne_zero
    exact sub_ne_zero.mpr hNVx.symm
  exact mul_ne_zero hPowNZ (mul_ne_zero hCheck hDenNZ)

/-! ### Log-derivative bad-set inclusion into Lang-Weil zero set

    A pair `(A₀, A₁) ∈ E.points × E.points` at which the verifier's
    log-derivative check vanishes (with denominators defined and line
    non-vertical) also satisfies `bivEval₂ clearedFullPoly A₀ A₁ = 0`.
    This inclusion is the input to Lang-Weil. -/

/-- Non-degenerate bad-pair predicate used by `log_deriv_sz_paper_core`:
    the pair lies on the non-vertical cone, has defined denominators,
    and the check function vanishes. -/
noncomputable def A₀ne_A₁x_cleared_pair
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) : Prop :=
  p.1.1 ≠ p.2.1 ∧
  logDerivCheckFnDenom E D P B p.1 p.2 ≠ 0 ∧
  logDerivCheckFn E D P k B m p.1 p.2 = 0

/-- `A₀ne_A₁x_cleared_pair` is decidable classically. -/
noncomputable instance A₀ne_A₁x_cleared_pair.decidablePred
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    DecidablePred (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      A₀ne_A₁x_cleared_pair E D P B m p) := by
  classical exact fun _ => Classical.propDecidable _

/-- **Bad-pair → clearedFullPoly-zero inclusion.** On the non-vertical
    cone with `logDerivCheckFnDenom ≠ 0`, `logDerivCheckFn = 0`
    implies `bivEval₂ clearedFullPoly = 0`.

    Proof: `bivEval₂ clearedFullPoly = (A₁.1 - A₀.1)^N ·
    logDerivCheckFnCleared = (A₁.1 - A₀.1)^N · logDerivCheckFn · denom`;
    vanishes since `logDerivCheckFn = 0`. -/
theorem bivEval₂_clearedFullPoly_eq_zero_of_bad
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0)
    (hZero : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ = 0 := by
  rw [clearedFullPoly_identity E D P B m A₀ A₁ hNV hDef]
  unfold logDerivCheckFnCleared
  rw [hZero, zero_mul, mul_zero]

/-! ### The paper-faithful Schwartz-Zippel bound via Lang-Weil.

    Combining the three helpers (`clearedFullPoly_identity`,
    `clearedFullPoly_bi_x_degree_le`, `clearedFullPoly_nonzero_witness`)
    with the `bivariate_poly_zeros_on_ExE_le` axiom yields the
    Event_NotEq bound. The bound `36·(D.degE + k + 6)·|E|` comes from
    `2·(dX + dY) = 2·(9 + 9) = 36` at bi-x-degree `(9·(d+k+6), 9·(d+k+6))`.

    A boundary correction accounts for pairs in `eventNotEq`
    where either the line is vertical (`A₀.1 = A₁.1`) or a denominator
    factor vanishes. These pairs lie outside the identity's scope but
    are bounded by existing F1-F6 bounds in `ClearedPolyForm.lean`.

    For this session we deliver the **core inclusion bound**, which is
    the nondegenerate part of the argument. The boundary correction
    term is delegated to a follow-up alongside the `18·(d+k)` tightening
    mentioned in the plan's Phase 5 "Open question".  -/


/-! ### Total-degree bound on `liftPoly`. -/

/-- `liftPoly E p i` has total degree at most `p.natDegree`. -/
theorem liftPoly_total_degree_le (p : (ZMod E.q)[X]) (i : Fin 4) :
    total_degree_le E (liftPoly E p i) p.natDegree := by
  unfold total_degree_le liftPoly
  rw [Polynomial.eval₂_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  have hn' : n ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  calc (MvPolynomial.C (p.coeff n) * (MvPolynomial.X i : FourVarPoly E.q) ^ n).totalDegree
      ≤ (MvPolynomial.C (p.coeff n)).totalDegree +
        ((MvPolynomial.X i : FourVarPoly E.q) ^ n).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + n := by
        apply Nat.add_le_add
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
        · exact (MvPolynomial.totalDegree_pow _ _).trans (by simp [MvPolynomial.totalDegree_X])
    _ = n := by omega
    _ ≤ p.natDegree := hn'

/-! ### Total-degree bound helpers for atoms of `clearedFullPoly`. -/

private theorem lamNumFull_td : total_degree_le E (lamNumFull E) 1 := by
  unfold lamNumFull varA₁y varA₀y
  exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)

private theorem lamDenFull_td : total_degree_le E (lamDenFull E) 1 := by
  unfold lamDenFull varA₁x varA₀x
  exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)

private theorem varA₀x_td : total_degree_le E (varA₀x E) 1 := by
  unfold varA₀x; exact total_degree_le.X _

private theorem varA₀y_td : total_degree_le E (varA₀y E) 1 := by
  unfold varA₀y; exact total_degree_le.X _

private theorem varA₁x_td : total_degree_le E (varA₁x E) 1 := by
  unfold varA₁x; exact total_degree_le.X _

private theorem varA₁y_td : total_degree_le E (varA₁y E) 1 := by
  unfold varA₁y; exact total_degree_le.X _

private theorem lineEvalNumAtFull_td (P : ZMod E.q × ZMod E.q) :
    total_degree_le E (lineEvalNumAtFull E P) 2 := by
  unfold lineEvalNumAtFull
  refine total_degree_le.sub ?_ ?_
  · exact total_degree_le.mul
      (by unfold embedScalarFull varA₀y
          exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
            (total_degree_le.X _))
      (lamDenFull_td E)
  · exact total_degree_le.mul
      (by unfold embedScalarFull varA₀x
          exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
            (total_degree_le.X _))
      (lamNumFull_td E)

private theorem x₂ScaledFull_td : total_degree_le E (x₂ScaledFull E) 3 := by
  unfold x₂ScaledFull
  apply total_degree_le.sub
  · exact ((lamNumFull_td E).pow 2).mono (by omega)
  · exact (total_degree_le.mul
      (total_degree_le.add (varA₀x_td E) (varA₁x_td E))
      ((lamDenFull_td E).pow 2)).mono (by omega)

private theorem y₂ScaledFull_td : total_degree_le E (y₂ScaledFull E) 4 := by
  unfold y₂ScaledFull
  apply total_degree_le.add
  · exact (total_degree_le.mul (lamNumFull_td E) (x₂ScaledFull_td E)).mono (by omega)
  · exact (total_degree_le.mul
      (total_degree_le.sub
        (total_degree_le.mul (varA₀y_td E) (lamDenFull_td E))
        (total_degree_le.mul (varA₀x_td E) (lamNumFull_td E)))
      ((lamDenFull_td E).pow 2)).mono (by omega)

private theorem DAtA₀Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DAtA₀Full E D) D.degE := by
  unfold DAtA₀Full
  apply total_degree_le.sub
  · exact (liftPoly_total_degree_le E D.a 0).mono (a_natDegree_le_degE E D)
  · exact (total_degree_le.mul (liftPoly_total_degree_le E D.b 0) (varA₀y_td E)).mono
      (by have := two_b_plus_3_le_degE E D; omega)

private theorem DAtA₁Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DAtA₁Full E D) D.degE := by
  unfold DAtA₁Full
  apply total_degree_le.sub
  · exact (liftPoly_total_degree_le E D.a 2).mono (a_natDegree_le_degE E D)
  · exact (total_degree_le.mul (liftPoly_total_degree_le E D.b 2) (varA₁y_td E)).mono
      (by have := two_b_plus_3_le_degE E D; omega)

private theorem DDerivAtA₀Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DDerivAtA₀Full E D) D.degE := by
  unfold DDerivAtA₀Full
  apply total_degree_le.sub
  · exact (liftPoly_total_degree_le E (Polynomial.derivative D.a) 0).mono
      (deriv_a_natDegree_le_degE E D)
  · exact (total_degree_le.mul
      (liftPoly_total_degree_le E (Polynomial.derivative D.b) 0) (varA₀y_td E)).mono
      (by have := Polynomial.natDegree_derivative_le D.b
          have := two_b_plus_3_le_degE E D; omega)

private theorem DDerivAtA₁Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DDerivAtA₁Full E D) D.degE := by
  unfold DDerivAtA₁Full
  apply total_degree_le.sub
  · exact (liftPoly_total_degree_le E (Polynomial.derivative D.a) 2).mono
      (deriv_a_natDegree_le_degE E D)
  · exact (total_degree_le.mul
      (liftPoly_total_degree_le E (Polynomial.derivative D.b) 2) (varA₁y_td E)).mono
      (by have := Polynomial.natDegree_derivative_le D.b
          have := two_b_plus_3_le_degE E D; omega)

private theorem dxdzDenA₀Full_td : total_degree_le E (dxdzDenA₀Full E) 3 := by
  unfold dxdzDenA₀Full
  have hCmul : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₀x E ^ 2) 2 :=
    total_degree_le.mul (total_degree_le.C _) ((varA₀x_td E).pow 2)
  have hCa : total_degree_le E (MvPolynomial.C E.curveA : FourVarPoly E.q) 2 :=
    (total_degree_le.C _).mono (Nat.zero_le _)
  have hsum : total_degree_le E _ 2 := total_degree_le.add hCmul hCa
  have hfst : total_degree_le E _ 3 := total_degree_le.mul hsum (lamDenFull_td E)
  have hC2 : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₀y E * lamNumFull E) 2 :=
    total_degree_le.mul (total_degree_le.mul (total_degree_le.C _) (varA₀y_td E)) (lamNumFull_td E)
  exact total_degree_le.sub hfst (hC2.mono (by omega))

private theorem dxdzDenA₁Full_td : total_degree_le E (dxdzDenA₁Full E) 3 := by
  unfold dxdzDenA₁Full
  have hCmul : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₁x E ^ 2) 2 :=
    total_degree_le.mul (total_degree_le.C _) ((varA₁x_td E).pow 2)
  have hCa : total_degree_le E (MvPolynomial.C E.curveA : FourVarPoly E.q) 2 :=
    (total_degree_le.C _).mono (Nat.zero_le _)
  have hsum : total_degree_le E _ 2 := total_degree_le.add hCmul hCa
  have hfst : total_degree_le E _ 3 := total_degree_le.mul hsum (lamDenFull_td E)
  have hC2 : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₁y E * lamNumFull E) 2 :=
    total_degree_le.mul (total_degree_le.mul (total_degree_le.C _) (varA₁y_td E)) (lamNumFull_td E)
  exact total_degree_le.sub hfst (hC2.mono (by omega))

private theorem dxdzDenA₂Full_td : total_degree_le E (dxdzDenA₂Full E) 6 := by
  unfold dxdzDenA₂Full
  have h1 : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * x₂ScaledFull E ^ 2) 6 :=
    total_degree_le.mul (total_degree_le.C _) ((x₂ScaledFull_td E).pow 2)
  have h2 : total_degree_le E
      ((MvPolynomial.C E.curveA : FourVarPoly E.q) * lamDenFull E ^ 4) 4 :=
    total_degree_le.mul (total_degree_le.C _) ((lamDenFull_td E).pow 4)
  have hfst : total_degree_le E _ 6 := total_degree_le.add h1 (h2.mono (by omega))
  have hsnd : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * lamNumFull E * y₂ScaledFull E) 5 :=
    total_degree_le.mul (total_degree_le.mul (total_degree_le.C _) (lamNumFull_td E))
      (y₂ScaledFull_td E)
  exact total_degree_le.sub hfst (hsnd.mono (by omega))

private theorem DAPartAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DAPartAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DAPartAtA₂ScaledFull
  apply total_degree_le.sum
  intro n hn
  have hn' : n ≤ D.a.natDegree := by
    simp [Finset.mem_range] at hn; omega
  have ha := two_a_le_degE E D
  -- bound: 0 + 3*n + 1*(D.degE - 2*n) = D.degE + n ≤ D.degE + D.a.natDegree ≤ 2*D.degE
  exact (total_degree_le.mul
    (total_degree_le.mul (total_degree_le.C _)
      ((x₂ScaledFull_td E).pow n))
    ((lamDenFull_td E).pow (D.degE - 2 * n))).mono
    (by omega)

private theorem DBPartAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DBPartAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DBPartAtA₂ScaledFull
  apply total_degree_le.sum
  intro n hn
  have hn' : n ≤ D.b.natDegree := by
    simp [Finset.mem_range] at hn; omega
  have hb := two_b_plus_3_le_degE E D
  -- bound: 0 + 3*n + 4 + 1*(D.degE-2*n-3) ≤ D.degE+n+1 ≤ D.degE+b.nd+1 ≤ 2*D.degE
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul (total_degree_le.C _)
        ((x₂ScaledFull_td E).pow n))
      (y₂ScaledFull_td E))
    ((lamDenFull_td E).pow (D.degE - 2 * n - 3))).mono
    (by omega)

private theorem DAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DAtA₂ScaledFull
  exact total_degree_le.sub (DAPartAtA₂ScaledFull_td E D) (DBPartAtA₂ScaledFull_td E D)

private theorem DDerivAPartAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DDerivAPartAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DDerivAPartAtA₂ScaledFull
  apply total_degree_le.sum
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.a).natDegree := by
    simp [Finset.mem_range] at hn; omega
  have hda := Polynomial.natDegree_derivative_le D.a
  have ha := two_a_le_degE E D
  exact (total_degree_le.mul
    (total_degree_le.mul (total_degree_le.C _)
      ((x₂ScaledFull_td E).pow n))
    ((lamDenFull_td E).pow (D.degE - 2 * n))).mono
    (by omega)

private theorem DDerivBPartAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DDerivBPartAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DDerivBPartAtA₂ScaledFull
  apply total_degree_le.sum
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.b).natDegree := by
    simp [Finset.mem_range] at hn; omega
  have hdb := Polynomial.natDegree_derivative_le D.b
  have hb := two_b_plus_3_le_degE E D
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul (total_degree_le.C _)
        ((x₂ScaledFull_td E).pow n))
      (y₂ScaledFull_td E))
    ((lamDenFull_td E).pow (D.degE - 2 * n - 3))).mono
    (by omega)

private theorem DDerivAtA₂ScaledFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DDerivAtA₂ScaledFull E D) (2 * D.degE) := by
  unfold DDerivAtA₂ScaledFull
  exact total_degree_le.sub (DDerivAPartAtA₂ScaledFull_td E D) (DDerivBPartAtA₂ScaledFull_td E D)

private theorem linesProductFull_td (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (linesProductFull E P k B) (2 * k + 2) := by
  classical
  unfold linesProductFull
  have h1 := lineEvalNumAtFull_td E (P.1, -P.2)
  have h2 : total_degree_le E (∏ j : Fin k, lineEvalNumAtFull E (B j))
      (Finset.univ.card * 2) :=
    total_degree_le.prod_const _ _ (fun j _ => lineEvalNumAtFull_td E (B j))
  exact (total_degree_le.mul h1 h2).mono (by simp; omega)

private theorem linesProductNoNegPFull_td
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (linesProductNoNegPFull E k B) (2 * k) := by
  classical
  unfold linesProductNoNegPFull
  have h : total_degree_le E (∏ j : Fin k, lineEvalNumAtFull E (B j))
      (Finset.univ.card * 2) :=
    total_degree_le.prod_const _ _ (fun j _ => lineEvalNumAtFull_td E (B j))
  exact h.mono (by simp; omega)

private theorem linesProductSkipBjFull_td (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (j₀ : Fin k) :
    total_degree_le E (linesProductSkipBjFull E P k B j₀) (2 * k) := by
  classical
  unfold linesProductSkipBjFull
  have h1 := lineEvalNumAtFull_td E (P.1, -P.2)
  have h2 : total_degree_le E
      (∏ j ∈ (Finset.univ (α := Fin k)).erase j₀, lineEvalNumAtFull E (B j))
      (((Finset.univ (α := Fin k)).erase j₀).card * 2) :=
    total_degree_le.prod_const _ _ (fun j _ => lineEvalNumAtFull_td E (B j))
  have hcard : ((Finset.univ (α := Fin k)).erase j₀).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀)]; simp
  have hk : k ≥ 1 := Fin.pos j₀
  exact (total_degree_le.mul h1 h2).mono (by omega)

private theorem DAllFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DAllFull E D) (4 * D.degE) := by
  unfold DAllFull
  exact (total_degree_le.mul (total_degree_le.mul (DAtA₀Full_td E D) (DAtA₁Full_td E D))
    (DAtA₂ScaledFull_td E D)).mono (by omega)

private theorem dxdzAllFull_td : total_degree_le E (dxdzAllFull E) 12 := by
  unfold dxdzAllFull
  exact (total_degree_le.mul (total_degree_le.mul (dxdzDenA₀Full_td E) (dxdzDenA₁Full_td E))
    (dxdzDenA₂Full_td E)).mono (by omega)

private theorem DBdydzAtA₀Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DBdydzAtA₀Full E D) D.degE := by
  unfold DBdydzAtA₀Full
  have hb : total_degree_le E (-liftPoly E D.b 0) D.b.natDegree :=
    total_degree_le.neg (liftPoly_total_degree_le E D.b 0)
  have hCmul : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₀x E ^ 2) 2 :=
    total_degree_le.mul (total_degree_le.C _) ((varA₀x_td E).pow 2)
  have hCa : total_degree_le E (MvPolynomial.C E.curveA : FourVarPoly E.q) 2 :=
    (total_degree_le.C _).mono (Nat.zero_le _)
  have hq : total_degree_le E _ 2 := total_degree_le.add hCmul hCa
  exact (total_degree_le.mul hb hq).mono
    (by have := two_b_plus_3_le_degE E D; omega)

private theorem DBdydzAtA₁Full_td (D : CoordRingElt E.q) :
    total_degree_le E (DBdydzAtA₁Full E D) D.degE := by
  unfold DBdydzAtA₁Full
  have hb : total_degree_le E (-liftPoly E D.b 2) D.b.natDegree :=
    total_degree_le.neg (liftPoly_total_degree_le E D.b 2)
  have hCmul : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * varA₁x E ^ 2) 2 :=
    total_degree_le.mul (total_degree_le.C _) ((varA₁x_td E).pow 2)
  have hCa : total_degree_le E (MvPolynomial.C E.curveA : FourVarPoly E.q) 2 :=
    (total_degree_le.C _).mono (Nat.zero_le _)
  have hq : total_degree_le E _ 2 := total_degree_le.add hCmul hCa
  exact (total_degree_le.mul hb hq).mono
    (by have := two_b_plus_3_le_degE E D; omega)

private theorem DbAtA₂TightFull_td (D : CoordRingElt E.q) :
    total_degree_le E (DbAtA₂TightFull E D) (3 * D.b.natDegree) := by
  unfold DbAtA₂TightFull
  apply total_degree_le.sum
  intro n hn
  have hn' : n ≤ D.b.natDegree := by simp [Finset.mem_range] at hn; omega
  exact (total_degree_le.mul
    (total_degree_le.mul (total_degree_le.C _)
      ((x₂ScaledFull_td E).pow n))
    ((lamDenFull_td E).pow (2 * D.b.natDegree - 2 * n))).mono (by omega)

private theorem dydzNumA₂Full_td : total_degree_le E (dydzNumA₂Full E) 6 := by
  unfold dydzNumA₂Full
  have h1 : total_degree_le E
      ((MvPolynomial.C 3 : FourVarPoly E.q) * x₂ScaledFull E ^ 2) 6 :=
    total_degree_le.mul (total_degree_le.C _) ((x₂ScaledFull_td E).pow 2)
  have h2 : total_degree_le E
      ((MvPolynomial.C E.curveA : FourVarPoly E.q) * lamDenFull E ^ 4) 4 :=
    total_degree_le.mul (total_degree_le.C _) ((lamDenFull_td E).pow 4)
  exact total_degree_le.add h1 (h2.mono (by omega))

private theorem correctionA₂CoreFull_td (D : CoordRingElt E.q) :
    total_degree_le E (correctionA₂CoreFull E D) (D.degE + D.b.natDegree + 3) := by
  unfold correctionA₂CoreFull
  have h1 : total_degree_le E (-DbAtA₂TightFull E D) (3 * D.b.natDegree) :=
    total_degree_le.neg (DbAtA₂TightFull_td E D)
  have h2 := dydzNumA₂Full_td E
  have h3 := (lamDenFull_td E).pow (D.degE - 2 * D.b.natDegree - 3)
  exact (total_degree_le.mul (total_degree_le.mul h1 h2) h3).mono
    (by have := two_b_plus_3_le_degE E D; omega)

/-! ### Total-degree bound on `clearedFullPoly`.

    Each of the 8 summands has total degree ≤ 4·D.degE + 2·k + 12.
    We combine the atom bounds via `total_degree_le.add`/`.mul`/`.mono`. -/

private theorem lhsTerm0Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (lhsTerm0Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold lhsTerm0Full
  have h2y : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₀y E) 1 :=
    total_degree_le.mul (total_degree_le.C _) (varA₀y_td E)
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (total_degree_le.mul (DDerivAtA₀Full_td E D) h2y)
            (DAtA₁Full_td E D))
          (DAtA₂ScaledFull_td E D))
        (dxdzDenA₁Full_td E))
      (dxdzDenA₂Full_td E))
    (linesProductFull_td E P B)).mono (by omega)

private theorem lhsTerm1Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (lhsTerm1Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold lhsTerm1Full
  have h2y : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * varA₁y E) 1 :=
    total_degree_le.mul (total_degree_le.C _) (varA₁y_td E)
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (total_degree_le.mul (DDerivAtA₁Full_td E D) h2y)
            (DAtA₀Full_td E D))
          (DAtA₂ScaledFull_td E D))
        (dxdzDenA₀Full_td E))
      (dxdzDenA₂Full_td E))
    (linesProductFull_td E P B)).mono (by omega)

private theorem lhsTerm2Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (lhsTerm2Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold lhsTerm2Full
  have h2y : total_degree_le E
      ((MvPolynomial.C 2 : FourVarPoly E.q) * y₂ScaledFull E) 4 :=
    total_degree_le.mul (total_degree_le.C _) (y₂ScaledFull_td E)
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (total_degree_le.mul (DDerivAtA₂ScaledFull_td E D) h2y)
            (DAtA₀Full_td E D))
          (DAtA₁Full_td E D))
        (dxdzDenA₀Full_td E))
      (dxdzDenA₁Full_td E))
    (linesProductFull_td E P B)).mono (by omega)

private theorem correctionTerm0Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (correctionTerm0Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold correctionTerm0Full
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (DBdydzAtA₀Full_td E D)
            (DAtA₁Full_td E D))
          (DAtA₂ScaledFull_td E D))
        (dxdzDenA₁Full_td E))
      (dxdzDenA₂Full_td E))
    (linesProductFull_td E P B)).mono (by omega)

private theorem correctionTerm1Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (correctionTerm1Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold correctionTerm1Full
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (DBdydzAtA₁Full_td E D)
            (DAtA₀Full_td E D))
          (DAtA₂ScaledFull_td E D))
        (dxdzDenA₀Full_td E))
      (dxdzDenA₂Full_td E))
    (linesProductFull_td E P B)).mono (by omega)

private theorem correctionTerm2Full_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (correctionTerm2Full E D P k B) (4 * D.degE + 2 * k + 12) := by
  unfold correctionTerm2Full
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul
        (total_degree_le.mul
          (total_degree_le.mul
            (total_degree_le.mul
              (correctionA₂CoreFull_td E D)
              (DAtA₀Full_td E D))
            (DAtA₁Full_td E D))
          (dxdzDenA₀Full_td E))
        (dxdzDenA₁Full_td E))
      (linesProductFull_td E P B))
    ((lamDenFull_td E).pow 2)).mono
    (by have := two_b_plus_3_le_degE E D; omega)

private theorem rhsTermNegPFull_td (D : CoordRingElt E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    total_degree_le E (rhsTermNegPFull E D k B) (4 * D.degE + 2 * k + 12) := by
  unfold rhsTermNegPFull
  exact (total_degree_le.mul
    (total_degree_le.mul (DAllFull_td E D) (dxdzAllFull_td E))
    (linesProductNoNegPFull_td E B)).mono (by omega)

private theorem rhsSumFull_td (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    total_degree_le E (rhsSumFull E D P k B m) (4 * D.degE + 2 * k + 12) := by
  unfold rhsSumFull
  apply total_degree_le.sum
  intro j _
  exact (total_degree_le.mul
    (total_degree_le.mul
      (total_degree_le.mul (total_degree_le.C (m j))
        (DAllFull_td E D))
      (dxdzAllFull_td E))
    (linesProductSkipBjFull_td E P B j)).mono (by omega)

theorem clearedFullPoly_total_degree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    total_degree_le E (clearedFullPoly E D P k B m)
      (4 * D.degE + 2 * k + 12) := by
  unfold clearedFullPoly
  apply total_degree_le.add
  · apply total_degree_le.add
    · apply total_degree_le.add
      · apply total_degree_le.add
        · apply total_degree_le.add
          · apply total_degree_le.add
            · apply total_degree_le.add
              · exact lhsTerm0Full_td E D P B
              · exact lhsTerm1Full_td E D P B
            · exact lhsTerm2Full_td E D P B
          · exact correctionTerm0Full_td E D P B
        · exact correctionTerm1Full_td E D P B
      · exact correctionTerm2Full_td E D P B
    · exact rhsTermNegPFull_td E D B
  · exact rhsSumFull_td E D P B m

/-! ### Hasse-Weil derived bound: q ≤ 2·|E| for |E| ≥ 8. -/

/-- From the Hasse-Weil bound `(|E|-q)² ≤ 4q`, deduce `q ≤ 2·|E|`
    whenever `|E| ≥ 8`. Proof: if `q > 2·|E|`, then setting
    `N = |E|`, `q ≥ 2N+1`, so `(q-N)² ≥ (N+1)²`, but Hasse gives
    `(q-N)² ≤ 4q`. Combining with `q ≥ 2N+1` yields
    `N²-6N-3 ≤ 0`, which fails for `N ≥ 8`. -/
theorem hasse_q_le_two_mul_card (hN : 8 ≤ E.points.card) :
    E.q ≤ 2 * E.points.card := by
  by_contra hlt
  push_neg at hlt
  have hH := hasse_weil E
  rw [E.hNumPoints] at hH
  have hH' : ((E.points.card : ℤ) - E.q) ^ 2 ≤ 4 * (E.q : ℤ) := by
    have : (↑(E.points.card + 1) : ℤ) - ↑E.q - 1 = (↑E.points.card : ℤ) - ↑E.q := by push_cast; ring
    rw [this] at hH; exact hH
  have hN' : (E.points.card : ℤ) ≥ 8 := by exact_mod_cast hN
  have hQ' : (E.q : ℤ) ≥ 2 * (E.points.card : ℤ) + 1 := by exact_mod_cast hlt
  nlinarith [sq_nonneg ((E.q : ℤ) - 2 * (E.points.card : ℤ) - 1)]

/-- **Phase 5 `log_deriv_sz_paper` (core, non-degenerate part).**

    The cardinality of the non-degenerate bad set —
    pairs `(A₀, A₁) ∈ E.points × E.points` where the verifier's
    log-derivative check vanishes AND the denominator stays defined
    AND the line is non-vertical — is at most
    `36·(2·D.degE + k + 6)·|E|`.

    This uses the DKL+Bezout axiom (`bivariate_poly_zeros_on_ExE_le`)
    with total degree ≤ 4·D.degE + 2·k + 12 and Hasse `q ≤ 2·|E|`
    (for |E| ≥ 8), combined with a small-|E| case split.

    **Tightened**: previous bound `72·(D.degE+k+6)·|E|` lost precision
    by rounding `36·(2d+k+6)` up to `72·(d+k+6)`. The refined form
    preserves the `2d` vs `d` distinction in the DKL degree bound,
    ultimately yielding a tighter constant in `log_deriv_sz_paper`. -/
theorem log_deriv_sz_paper_core
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          A₀ne_A₁x_cleared_pair E D P B m p)).card
      ≤ 36 * (2 * D.degE + k + 6) * E.points.card := by
  classical
  set S : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => A₀ne_A₁x_cleared_pair E D P B m p) with hSdef
  set T : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (clearedFullPoly E D P k B m) p.1 p.2 = 0) with hTdef
  have hSub : S ⊆ T := by
    intro p hp
    simp only [hSdef, Finset.mem_filter, Finset.mem_product] at hp
    simp only [hTdef, Finset.mem_filter, Finset.mem_product]
    refine ⟨hp.1, ?_⟩
    obtain ⟨hNVx, hDef, hCheck⟩ := hp.2
    exact bivEval₂_clearedFullPoly_eq_zero_of_bad E D P B m p.1 p.2 hNVx
      hDef hCheck
  set N := E.points.card with hN_def
  set d := D.degE with hd_def
  calc S.card ≤ T.card := Finset.card_le_card hSub
    _ ≤ 36 * (2 * d + k + 6) * N := by
      by_cases hSmall : N ≤ 36 * (2 * d + k + 6)
      · -- Small N: T.card ≤ N² ≤ 36*(2d+k+6)*N
        have hTsub : T ⊆ E.points ×ˢ E.points := Finset.filter_subset _ _
        have hTcard : T.card ≤ N * N :=
          le_trans (Finset.card_le_card hTsub)
            (by rw [Finset.card_product])
        calc T.card ≤ N * N := hTcard
          _ ≤ 36 * (2 * d + k + 6) * N := Nat.mul_le_mul_right N hSmall
      · -- Large N: use axiom + Hasse
        push_neg at hSmall
        have hN8 : 8 ≤ N := by omega
        have hQle : E.q ≤ 2 * N := hasse_q_le_two_mul_card E hN8
        have hTD := clearedFullPoly_total_degree_le E D P B m
        have hNZ := clearedFullPoly_nonzero_witness E D P B m hNV
        have hAxiom := bivariate_poly_zeros_on_ExE_le E
          (clearedFullPoly E D P k B m)
          (4 * d + 2 * k + 12) hTD hNZ
        calc T.card
          ≤ 9 * (4 * d + 2 * k + 12) * E.q := hAxiom
          _ ≤ 9 * (4 * d + 2 * k + 12) * (2 * N) :=
              Nat.mul_le_mul_left _ hQle
          _ ≤ 36 * (2 * d + k + 6) * N := by nlinarith

/-- **Phase 5 `log_deriv_sz_paper` (outer, with-boundary form).**

    Combines the tightened core Lang-Weil bound
    (`36·(2d+k+6)·|E|`) on the denom-defined pairs with the tight
    boundary bound (`(6d+9k+71)·|E|`) from
    `logDerivCheckFn_undefined_set_bound_tight` for the
    denom-undefined pairs.  Total: `78·(D.degE + k + 6)·|E|`.

    **Tightened**: previous bound was `84·(D.degE+k+6)·|E|`.
    The improvement comes from preserving the `2d` dependence in the
    DKL degree bound (total degree `4d+2k+12` gives DKL count
    `≤ 9·(4d+2k+12)·q = 36·(2d+k+6)·q`), rather than rounding to
    `72·(d+k+6)·q`. -/
theorem log_deriv_sz_paper
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (eventNotEq E D P B m).card ≤
      78 * (D.degE + k + 6) * E.points.card := by
  classical
  -- eventNotEq splits by `logDerivCheckFnDefined`.
  set badNE := eventNotEq E D P B m with hBNE_def
  set defBad := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      A₀ne_A₁x_cleared_pair E D P B m p) with hDB_def
  set undefAll := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hUA_def
  have hSub : badNE ⊆ defBad ∪ undefAll := by
    intro p hp
    simp only [hBNE_def, eventNotEq, Finset.mem_filter] at hp
    obtain ⟨hVP, hCheck⟩ := hp
    have hDP : p ∈ distinctPairs E.points := (Finset.mem_filter.mp hVP).1
    have hEE : p ∈ E.points ×ˢ E.points := (Finset.mem_filter.mp hDP).1
    have hNeq : p.1.1 ≠ p.2.1 := ((Finset.mem_filter.mp hVP).2).1
    by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hEE, hNeq, hDef, hCheck⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hEE, hDef⟩))
  have hCardSplit : badNE.card ≤ defBad.card + undefAll.card :=
    le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
  have hCoreBound := log_deriv_sz_paper_core E D P B m hDeg hNV
  -- Derive ¬(D.a = 0 ∧ D.b = 0) from the witness.
  have hD : ¬(D.a = 0 ∧ D.b = 0) := by
    obtain ⟨A₀, A₁, _, _, _, hDef, _⟩ := hNV
    intro ⟨ha, hb⟩
    have : logDerivCheckFnDenom E D P B A₀ A₁ = 0 := by
      unfold logDerivCheckFnDenom CoordRingElt.eval
      rw [ha, hb]; simp
    exact hDef this
  have hUndefBound := logDerivCheckFn_undefined_set_bound_tight E D P k B hD
  calc badNE.card
    ≤ defBad.card + undefAll.card := hCardSplit
    _ ≤ 36 * (2 * D.degE + k + 6) * E.points.card +
        (6 * D.degE + 9 * k + 71) * E.points.card :=
        Nat.add_le_add hCoreBound hUndefBound
    _ ≤ 78 * (D.degE + k + 6) * E.points.card := by
        have : 36 * (2 * D.degE + k + 6) + (6 * D.degE + 9 * k + 71)
               ≤ 78 * (D.degE + k + 6) := by omega
        calc 36 * (2 * D.degE + k + 6) * E.points.card +
               (6 * D.degE + 9 * k + 71) * E.points.card
            = (36 * (2 * D.degE + k + 6) + (6 * D.degE + 9 * k + 71)) *
                E.points.card := by ring
          _ ≤ (78 * (D.degE + k + 6)) * E.points.card :=
                Nat.mul_le_mul_right _ this
          _ = 78 * (D.degE + k + 6) * E.points.card := by ring

/- (Deleted Phase 5 chord-symmetry block: swapA₀A₁, bivEval₂_swapA₀A₁,
    clearedFullPoly_swap_signed, bivEval₂_clearedFullPoly_swap_zero,
    log_deriv_sz_paper_core_symmetric — Aristotle project 754ff51a
    determined chord symmetry alone doesn't halve the bound; replaced
    by DKL+Bezout path. Section preserved as a one-line note.) -/

/-! [DELETED] Phase 5 chord-symmetry block — see Phase F cleanup commit.
-/



end Divisor
