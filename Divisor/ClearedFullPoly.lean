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
  `badChallengesNotEq` set by a linear function of `(D.degE + k)·|E|`.

  Notation convention: use `Xm` / `Cm` for the 4-variate (MvPolynomial)
  generator / constant embed to avoid clashing with `Polynomial.X` in
  expressions like `(ZMod q)[X]`. `Polynomial` is globally opened; the
  `MvPolynomial` namespace is not.
-/
import Divisor.ClearedPolyForm
import Divisor.FourVarPoly
import Divisor.Axioms.AxiomBivariatePolyZerosOnExELe

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

/-- **Phase 3 identity (target).** -/
theorem clearedFullPoly_identity
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (_hNV : A₀.1 ≠ A₁.1)
    (_hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 6) *
          logDerivCheckFnCleared E D P k B m A₀ A₁ := by
  sorry

/-- **Phase 4 bi-x-degree bound (target).** -/
theorem clearedFullPoly_bi_x_degree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    bi_x_degree_le E (clearedFullPoly E D P k B m)
      (9 * (D.degE + k + 6)) (9 * (D.degE + k + 6)) := by
  sorry

/-- **Phase 5 nonzero-witness on E × E (target).** -/
theorem clearedFullPoly_nonzero_witness
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
      bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ ≠ 0 := by
  sorry

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

    A boundary correction accounts for pairs in `badChallengesNotEq`
    where either the line is vertical (`A₀.1 = A₁.1`) or a denominator
    factor vanishes. These pairs lie outside the identity's scope but
    are bounded by existing F1-F6 bounds in `ClearedPolyForm.lean`.

    For this session we deliver the **core inclusion bound**, which is
    the nondegenerate part of the argument. The boundary correction
    term is delegated to a follow-up alongside the `18·(d+k)` tightening
    mentioned in the plan's Phase 5 "Open question".  -/

/-- **Phase 5 `log_deriv_sz_paper` (core, non-degenerate part).**

    The cardinality of the non-degenerate bad set —
    pairs `(A₀, A₁) ∈ E.points × E.points` where the verifier's
    log-derivative check vanishes AND the denominator stays defined
    AND the line is non-vertical — is at most `36·(D.degE + k + 6)·|E|`.

    This matches the paper's Event_NotEq bound of
    `sections/ip.tex:462-481` (via Hasse) up to the factor-of-2 gap
    discussed in `docs/bivariate-sz-paper-faithful.md` Phase 5. -/
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
      ≤ 36 * (D.degE + k + 6) * E.points.card := by
  classical
  -- Reduce to: bad-on-cone pairs ⊆ clearedFullPoly-zero pairs.
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
  calc S.card ≤ T.card := Finset.card_le_card hSub
    _ ≤ 2 * (9 * (D.degE + k + 6) + 9 * (D.degE + k + 6)) * E.points.card := by
        have hBideg := clearedFullPoly_bi_x_degree_le E D P B m
        have hNZ := clearedFullPoly_nonzero_witness E D P B m hNV
        exact bivariate_poly_zeros_on_ExE_le E (clearedFullPoly E D P k B m)
          _ _ hBideg hNZ
    _ = 36 * (D.degE + k + 6) * E.points.card := by ring

/-- **Phase 5 `log_deriv_sz_paper` (outer, with-boundary form).**

    Combines the core inclusion with existing boundary bounds (F1-F6 of
    `ClearedPolyForm.lean`) — left as `sorry` pending the boundary
    accumulation step. Target final bound: `K·(D.degE + k + C)·|E|` for
    K ≤ 44, matching plan Phase 5 fallback. -/
theorem log_deriv_sz_paper
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (_hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card ≤
      36 * (D.degE + k + 6) * E.points.card := by
  sorry

end Divisor
