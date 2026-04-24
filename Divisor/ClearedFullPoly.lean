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

    Combines the core Lang-Weil bound (`36·(…)`) on the denom-defined
    pairs with the boundary bound (`18·(…)`) from
    `logDerivCheckFn_undefined_set_bound` for the denom-undefined pairs.
    Total: `54·(D.degE + k + 6)·|E|`, a strict improvement over
    `log_deriv_sz`'s `(72·(d+k+6)+4)·|E|`. -/
theorem log_deriv_sz_paper
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card ≤
      54 * (D.degE + k + 6) * E.points.card := by
  classical
  -- badChallengesNotEq splits by `logDerivCheckFnDefined`.
  set badNE := badChallengesNotEq E D P B m with hBNE_def
  set defBad := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      A₀ne_A₁x_cleared_pair E D P B m p) with hDB_def
  set undefAll := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hUA_def
  have hSub : badNE ⊆ defBad ∪ undefAll := by
    intro p hp
    simp only [hBNE_def, badChallengesNotEq, Finset.mem_filter] at hp
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
  have hUndefBound := logDerivCheckFn_undefined_set_bound E D P k B hD
  calc badNE.card
    ≤ defBad.card + undefAll.card := hCardSplit
    _ ≤ 36 * (D.degE + k + 6) * E.points.card +
        18 * (D.degE + k + 6) * E.points.card := by
        exact Nat.add_le_add hCoreBound hUndefBound
    _ = 54 * (D.degE + k + 6) * E.points.card := by ring

/-! ## Phase 5 tightening (a): chord symmetry halving

    The log-derivative check and its polynomial form `clearedFullPoly`
    are invariant under the chord swap `(A₀, A₁) ↔ (A₁, A₀)`. The
    physical intuition: `A₂ = -(A₀ + A₁)` is symmetric in `A₀, A₁`, as
    is the line through them; the verifier-check value `f(A₀, A₁)`
    is thus symmetric.

    Formally, the substitution `(X 0, X 1) ↔ (X 2, X 3)` fixes
    `clearedFullPoly`. As a consequence the zero set of `clearedFullPoly`
    on `E × E` is symmetric, so bad pairs come in `(A₀, A₁)`-`(A₁, A₀)`
    twins on the non-vertical cone (where `A₀ ≠ A₁`). Halving gives the
    paper's `18·(d+k+6)·|E|` core bound (vs. our current `36·(d+k+6)·|E|`).

    Stated as sorry'd scaffolding; proof dispatched to Aristotle. -/

/-- The `(X 0, X 1) ↔ (X 2, X 3)` swap on FourVarPoly via `MvPolynomial.rename`. -/
noncomputable def swapA₀A₁ (f : FourVarPoly E.q) : FourVarPoly E.q :=
  MvPolynomial.rename
    (fun i : Fin 4 => match i with
      | ⟨0, _⟩ => (2 : Fin 4)
      | ⟨1, _⟩ => (3 : Fin 4)
      | ⟨2, _⟩ => (0 : Fin 4)
      | ⟨3, _⟩ => (1 : Fin 4)) f

/-- `bivEval₂ (swapA₀A₁ f) A₀ A₁ = bivEval₂ f A₁ A₀`. -/
theorem bivEval₂_swapA₀A₁ (f : FourVarPoly E.q) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (swapA₀A₁ E f) A₀ A₁ = bivEval₂ f A₁ A₀ := by
  unfold bivEval₂ swapA₀A₁
  rw [MvPolynomial.eval_rename]
  have : bivEval₂Fun A₀ A₁ ∘ (fun i : Fin 4 => match i with
      | ⟨0, _⟩ => (2 : Fin 4)
      | ⟨1, _⟩ => (3 : Fin 4)
      | ⟨2, _⟩ => (0 : Fin 4)
      | ⟨3, _⟩ => (1 : Fin 4)) = bivEval₂Fun A₁ A₀ := by
    funext i
    fin_cases i <;> simp [bivEval₂Fun]
  rw [this]

/- **Chord symmetry of `clearedFullPoly` is ANTI-symmetric up to sign.**
    The naive `swapA₀A₁ clearedFullPoly = clearedFullPoly` is FALSE:
    `lamNumFull` and `lamDenFull` are anti-symmetric under the swap, and
    tracing the clearing exponents shows each summand picks up
    `(-1)^(D.degE + k)`. For the halving argument only zero-set symmetry
    matters, which holds regardless of the sign. -/

/-- **Signed chord symmetry of `clearedFullPoly`** (target, sorry'd).
    Swapping `(A₀, A₁)` multiplies by `(-1)^(D.degE + k)`. -/
theorem clearedFullPoly_swap_signed
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    swapA₀A₁ E (clearedFullPoly E D P k B m)
      = ((-1 : ZMod E.q) ^ (D.degE + k)) • clearedFullPoly E D P k B m := by
  sorry

/-- **Zero-set symmetry of `clearedFullPoly` evaluation.** Replaces the
    original `bivEval₂_clearedFullPoly_swap` (which claimed pointwise
    equality that turns out to be false up to sign) with the
    zero-equivalence form, which is all that the halving argument
    needs: `ε · x = 0 ↔ x = 0` in a field. -/
theorem bivEval₂_clearedFullPoly_swap_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ = 0 ↔
    bivEval₂ (clearedFullPoly E D P k B m) A₁ A₀ = 0 := by
  have key : bivEval₂ (clearedFullPoly E D P k B m) A₁ A₀
      = ((-1 : ZMod E.q) ^ (D.degE + k)) *
        bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁ := by
    rw [← bivEval₂_swapA₀A₁ E (clearedFullPoly E D P k B m) A₀ A₁]
    rw [clearedFullPoly_swap_signed]
    simp [bivEval₂, MvPolynomial.smul_eval]
  constructor
  · intro h; rw [key, h, mul_zero]
  · intro h
    rw [key] at h
    have hε : ((-1 : ZMod E.q) ^ (D.degE + k)) ≠ 0 := by
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    exact (mul_eq_zero.mp h).resolve_left hε

/-- **SZ bound via chord symmetry (trivial weakening).**

    ANALYTICAL FINDING (Aristotle project 754ff51a): the halving
    argument via the fixed-point-free involution `(A₀, A₁) ↦ (A₁, A₀)`
    only shows the bad set has EVEN cardinality; it does not reduce
    the Lang-Weil bound itself. So chord symmetry alone does not get
    us from `36·(…)` to `18·(…)`.

    To achieve the paper's `18·(d+k)` factor, a different approach is
    needed — most likely a Y-linearity reduction of `clearedFullPoly`
    modulo the curve relations, eliminating the factor of 2 in the
    Lang-Weil axiom statement (`2·(dX+dY)` → `(dX+dY)`).

    For now this theorem is a trivial restatement of
    `log_deriv_sz_paper_core` preserved for provenance. -/
theorem log_deriv_sz_paper_core_symmetric
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
  exact log_deriv_sz_paper_core E D P B m _hDeg hNV

/-! ## Phase 6b: T5 replacement scaffolding

    To eliminate the quadratic `6·q·((d+k+1)+(d+k+1)·(d+k))` summand in
    `ma_extractable`'s bound, we need to close the `hAllZero` branch
    (where `logDerivCheckFn ≡ 0` on non-vertical E×E) without T5's
    `exists_good_lambda` step (whose quadratic threshold on
    `|validPairs|` is the source of the quadratic summand).

    Path: view `polyG` as a 4-variate polynomial (`polyGFull`) and
    apply the Lang-Weil contrapositive. If `polyG` vanishes pointwise
    on all but a small subset of E × E, then by `bivariate_poly_zeros
    _on_ExE_le`, `polyGFull` has no nonzero witness on E × E — a
    stronger statement than pointwise vanishing on non-vertical pairs.
    From there the paper-aligned residue-matching argument
    (`sections/ip.tex:552-634`) extracts the σ-matching directly.

    This section provides the 4-variate polyG scaffold. The
    residue-matching step itself is a separate Aristotle dispatch. -/

/-- 4-variate lift of `polyG`. Each `ellP (P)` becomes `lineEvalNumAtFull P`. -/
noncomputable def polyGFull
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    FourVarPoly E.q :=
  (∑ k : Fin d,
    (MvPolynomial.C (beta k) : FourVarPoly E.q) *
    (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k')) *
    (∏ j : Fin M, lineEvalNumAtFull E (R j))) +
  (∑ j : Fin M,
    (MvPolynomial.C (m j) : FourVarPoly E.q) *
    (∏ k : Fin d, lineEvalNumAtFull E (Q k)) *
    (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j')))

/-- Compat: `polyGFull` at `(A₀, A₁)` agrees with `polyG Q beta R m A₀ A₁`. -/
theorem bivEval₂_polyGFull_eq_polyG
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = polyG E Q beta R m A₀ A₁ := by
  simp only [polyGFull, polyG, bivEval₂_add, bivEval₂_sum, bivEval₂_mul,
    bivEval₂_prod, bivEval₂_C, bivEval₂_lineEvalNumAtFull, ellP]

private theorem lineEvalNumAtFull_bi_x_degree_le (pt : ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lineEvalNumAtFull E pt) 1 1 := by
  unfold lineEvalNumAtFull
  apply bi_x_degree_le.sub
  · have h1 : bi_x_degree_le E (embedScalarFull E pt.2 - varA₀y E) 0 0 :=
      bi_x_degree_le.sub (by unfold embedScalarFull; exact bi_x_degree_le.C _)
        (by unfold varA₀y; exact bi_x_degree_le.Y₀)
    have h2 : bi_x_degree_le E (lamDenFull E) 1 1 := by
      unfold lamDenFull varA₁x varA₀x
      exact bi_x_degree_le.sub (bi_x_degree_le.mono bi_x_degree_le.X₁ (by omega) (by omega))
        (bi_x_degree_le.mono bi_x_degree_le.X₀ (by omega) (by omega))
    simpa using bi_x_degree_le.mul h1 h2
  · have h1 : bi_x_degree_le E (embedScalarFull E pt.1 - varA₀x E) 1 0 :=
      bi_x_degree_le.sub
        (bi_x_degree_le.mono (by unfold embedScalarFull; exact bi_x_degree_le.C _)
          (by omega) (by omega))
        (by unfold varA₀x; exact bi_x_degree_le.mono bi_x_degree_le.X₀ (by omega) (by omega))
    have h2 : bi_x_degree_le E (lamNumFull E) 0 0 := by
      unfold lamNumFull varA₁y varA₀y
      exact bi_x_degree_le.sub bi_x_degree_le.Y₁ bi_x_degree_le.Y₀
    exact bi_x_degree_le.mono (bi_x_degree_le.mul h1 h2) (by omega) (by omega)

private theorem bi_x_degree_le_prod_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → FourVarPoly E.q)
    (hf : ∀ i ∈ s, bi_x_degree_le E (f i) 1 1) :
    bi_x_degree_le E (∏ i ∈ s, f i) s.card s.card := by
  induction s using Finset.induction_on with
  | empty => simp; exact ⟨(MvPolynomial.degreeOf_one _).le, (MvPolynomial.degreeOf_one _).le⟩
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    have hmul := bi_x_degree_le.mul (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hmul using 1 <;> omega

/-- `polyGFull` has bi-x-degree `(d + M - 1, d + M - 1)`.

    Proof: each `lineEvalNumAtFull` has bi-x-degree `(1, 1)`. A product
    of `d + M − 1` such (in each summand of either sum) gives `(d + M −
    1, d + M − 1)`. Summing over `d + M` summands preserves the bound. -/
theorem polyGFull_bi_x_degree_le
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    bi_x_degree_le E (polyGFull E Q beta R m) (d + M) (d + M) := by
  unfold polyGFull
  apply bi_x_degree_le.add
  · apply bi_x_degree_le.sum
    intro k _
    have hC : bi_x_degree_le E (MvPolynomial.C (beta k) : FourVarPoly E.q) 0 0 :=
      bi_x_degree_le.C _
    have hErase : bi_x_degree_le E
        (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k'))
        ((Finset.univ (α := Fin d)).erase k).card
        ((Finset.univ (α := Fin d)).erase k).card :=
      bi_x_degree_le_prod_finset E _ _ (fun i _ => lineEvalNumAtFull_bi_x_degree_le E (Q i))
    have hProd : bi_x_degree_le E
        (∏ j : Fin M, lineEvalNumAtFull E (R j)) (M * 1) (M * 1) :=
      bi_x_degree_le.prod_fin _ (fun j => lineEvalNumAtFull_bi_x_degree_le E (R j))
    have hEraseCard : ((Finset.univ (α := Fin d)).erase k).card ≤ d :=
      le_trans Finset.card_erase_le (by simp)
    have hMul := bi_x_degree_le.mul (bi_x_degree_le.mul hC hErase) hProd
    apply bi_x_degree_le.mono hMul <;> omega
  · apply bi_x_degree_le.sum
    intro j _
    have hC : bi_x_degree_le E (MvPolynomial.C (m j) : FourVarPoly E.q) 0 0 :=
      bi_x_degree_le.C _
    have hProd : bi_x_degree_le E
        (∏ k : Fin d, lineEvalNumAtFull E (Q k)) (d * 1) (d * 1) :=
      bi_x_degree_le.prod_fin _ (fun k => lineEvalNumAtFull_bi_x_degree_le E (Q k))
    have hErase : bi_x_degree_le E
        (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j'))
        ((Finset.univ (α := Fin M)).erase j).card
        ((Finset.univ (α := Fin M)).erase j).card :=
      bi_x_degree_le_prod_finset E _ _ (fun i _ => lineEvalNumAtFull_bi_x_degree_le E (R i))
    have hEraseCard : ((Finset.univ (α := Fin M)).erase j).card ≤ M :=
      le_trans Finset.card_erase_le (by simp)
    have hMul := bi_x_degree_le.mul (bi_x_degree_le.mul hC hProd) hErase
    apply bi_x_degree_le.mono hMul <;> omega

/-- **T5-replacement vanishing lemma (target).**

    If `polyG` vanishes on every non-vertical pair of `E.points ×
    E.points`, and `|E|` is large enough (linear in `d + M`) to make
    the Lang-Weil contrapositive bite, then `polyGFull` has no nonzero
    witness on `E × E` — i.e. `bivEval₂ polyGFull A₀ A₁ = 0` for all
    `(A₀, A₁) ∈ E.points × E.points`, including vertical pairs.

    This is the Stage-B T5 replacement: it derives a strictly stronger
    hypothesis (pointwise vanishing on all of E × E, not just
    non-vertical pairs) from the `hAllZero` input. The resulting
    stronger vanishing is what the paper-aligned σ-matching step
    (`sections/ip.tex:552-634`) consumes. -/
theorem polyGFull_vanishes_on_ExE_of_polyG_zero
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hPolyGZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = 0 := by
  by_contra h
  push_neg at h
  obtain ⟨A₀, A₁, hA₀, hA₁, hNZ⟩ := h
  have hBideg := polyGFull_bi_x_degree_le E Q beta R m
  have hLW := bivariate_poly_zeros_on_ExE_le E (polyGFull E Q beta R m) (d + M) (d + M)
    hBideg ⟨A₀, A₁, hA₀, hA₁, hNZ⟩
  have hNVsub : (E.points ×ˢ E.points).filter
      (fun p : _ × _ => p.1.1 ≠ p.2.1) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (polyGFull E Q beta R m) p.1 p.2 = 0) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨hp.1, by rw [bivEval₂_polyGFull_eq_polyG]; exact hPolyGZero _ _ hp.1.1 hp.1.2 hp.2⟩
  have hVertBd := card_vertical_pairs_le E
  have hCardProd : (E.points ×ˢ E.points).card = E.points.card * E.points.card :=
    Finset.card_product _ _
  have hNVcard : ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 ≠ p.2.1)).card
    + ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 = p.2.1)).card
    = (E.points ×ˢ E.points).card := by
    classical
    have h := @Finset.card_filter_add_card_filter_not
      _ (E.points ×ˢ E.points) (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 = p.2.1)
      _ _
    linarith
  have hZeroCard := Finset.card_le_card hNVsub
  have hNVge : E.points.card * E.points.card - 2 * E.points.card
    ≤ ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 ≠ p.2.1)).card := by
    rw [hCardProd] at hNVcard; omega
  have hChain : E.points.card * E.points.card - 2 * E.points.card
    ≤ 2 * (d + M + (d + M)) * E.points.card := le_trans hNVge (le_trans hZeroCard hLW)
  nlinarith [hELarge]

/-! ### Sub-lemmas for `sigma_matching_core`

    The proof decomposes into five steps:
    1. `ellP_self_eq_zero`: `ellP E P P A₁ = 0` (P = A₀).
    2. `polyG_only_Rj_term`: When `ellP(R_{j₀})=0` and all other factors ≠ 0,
       `polyG` reduces to the `j₀`-th second-sum term.
    3. `polyG_only_Qk_term`: When `ellP(Q_{k₀})=0` and all other factors ≠ 0,
       `polyG` reduces to the `k₀`-th first-sum term.
    4. `exists_avoiding_A1`: For `P ∈ E.points` and finite `T`, find
       `A₁ ∈ E.points` with `A₁ ≠ P` and `ellP(P', P, A₁) ≠ 0` for `P' ∈ T`.
    5. Combine to build `σ` and verify the three properties. -/

/-- `ellP E P P A₁ = 0` — the line numerator through `(A₀, A₁)`
    evaluated at `P = A₀` always vanishes. -/
private lemma ellP_self_eq_zero (P A₁ : ZMod E.q × ZMod E.q) :
    ellP E P P A₁ = 0 := by
  simp [ellP]

/-- When `A₀ = Q k₀ ∈ E.points`, `polyG(Q k₀, A₁)` reduces to the
    `k₀`-th first-sum term with the full `∏_j ellP(R_j)` factor.
    All other terms vanish because they contain `ellP(Q_{k₀}, Q_{k₀}, A₁) = 0`
    as a factor. -/
private lemma polyG_at_self_Q
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (k₀ : Fin d) (A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q beta R m (Q k₀) A₁ =
      beta k₀ *
        (∏ k' ∈ Finset.univ.erase k₀, ellP E (Q k') (Q k₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (Q k₀) A₁) := by
  unfold polyG
  have hFirstSum : ∀ k' : Fin d, k' ≠ k₀ →
      beta k' *
        (∏ k'' ∈ Finset.univ.erase k', ellP E (Q k'') (Q k₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (Q k₀) A₁) = 0 := by
    intro k' hne
    have hk₀mem : k₀ ∈ Finset.univ.erase k' :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hk₀mem (ellP_self_eq_zero E _ _)]
    ring
  have hSecondSum : ∀ j : Fin M,
      m j *
        (∏ k : Fin d, ellP E (Q k) (Q k₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (Q k₀) A₁) = 0 := by
    intro j
    have hk₀mem : k₀ ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
    rw [Finset.prod_eq_zero hk₀mem (ellP_self_eq_zero E _ _)]
    ring
  rw [Finset.sum_eq_zero (fun j _ => hSecondSum j), add_zero]
  exact Finset.sum_eq_single k₀
    (fun k' _ hne => hFirstSum k' hne)
    (fun h => absurd (Finset.mem_univ k₀) h)

/-- When `A₀ = R j₀ ∈ E.points`, `polyG(R j₀, A₁)` reduces to the
    `j₀`-th second-sum term. All first-sum terms vanish (each has
    `∏_j ellP(R_j)` including `ellP(R_{j₀}) = 0`), and all
    second-sum terms with `j ≠ j₀` vanish (they contain
    `ellP(R_{j₀})` in their `∏_{j'≠j}` product). -/
private lemma polyG_at_self_R
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (j₀ : Fin M) (A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q beta R m (R j₀) A₁ =
      m j₀ *
        (∏ k : Fin d, ellP E (Q k) (R j₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j₀, ellP E (R j') (R j₀) A₁) := by
  unfold polyG
  have hFirstSum : ∀ k : Fin d,
      beta k *
        (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') (R j₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (R j₀) A₁) = 0 := by
    intro k
    have hj₀mem : j₀ ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ _
    rw [Finset.prod_eq_zero hj₀mem (ellP_self_eq_zero E _ _)]
    ring
  have hSecondSum : ∀ j : Fin M, j ≠ j₀ →
      m j *
        (∏ k : Fin d, ellP E (Q k) (R j₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (R j₀) A₁) = 0 := by
    intro j hne
    have hj₀mem : j₀ ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hj₀mem (ellP_self_eq_zero E _ _)]
    ring
  rw [Finset.sum_eq_zero (fun k _ => hFirstSum k), zero_add]
  exact Finset.sum_eq_single j₀
    (fun j _ hne => hSecondSum j hne)
    (fun h => absurd (Finset.mem_univ j₀) h)

/-- For `P ∈ E.points` and a finite set `T` of "bad" points, if
    `|E| > 2|T| + 1`, there exists `A₁ ∈ E.points`, `A₁ ≠ P`,
    such that `ellP(P', P, A₁) ≠ 0` for every `P' ∈ T`.

    Geometrically: each `P' ∈ T` determines a line through `P`;
    by Bezout, that line meets `E` in ≤ 3 points, at most 2 besides `P`.
    So the set of "bad" `A₁` values has size ≤ `2|T|`.
    With `|E| > 2|T| + 1`, a "good" `A₁ ≠ P` exists. -/
private lemma exists_avoiding_A1
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points)
    (T : Finset (ZMod E.q × ZMod E.q))
    (hSize : E.points.card > 2 * T.card + 1) :
    ∃ A₁ ∈ E.points, A₁ ≠ P ∧
      ∀ P' ∈ T, ellP E P' P A₁ ≠ 0 := by
  sorry

/-- The 4-variate lift of the "residual" polynomial
    `G = ∑_k c_k · ∏_{j≠σ(k)} lineEvalNumAtFull(R_j)`,
    which arises after simplifying `polyG` under the σ-matching. -/
private noncomputable def residualFull
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M) : FourVarPoly E.q :=
  ∑ k : Fin d,
    (MvPolynomial.C (c k) : FourVarPoly E.q) *
    (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
      lineEvalNumAtFull E (R j))

private lemma residualFull_bi_x_degree_le
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M) :
    bi_x_degree_le E (residualFull E R c σ) (M - 1) (M - 1) := by
  sorry

private lemma bivEval₂_residualFull_eq
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (residualFull E R c σ) A₀ A₁ =
    ∑ k : Fin d, c k *
      ∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
        ellP E (R j) A₀ A₁ := by
  simp only [residualFull, bivEval₂_sum, bivEval₂_mul,
    bivEval₂_prod, bivEval₂_C, bivEval₂_lineEvalNumAtFull, ellP]

/-- After establishing `Q k = R (σ k)` and `m j = 0` for `j ∉ range σ`,
    the simplified `polyG` factors as
    `(∏_k ellP(Q_k)) · G` where `G = residual c σ R` and `c k = β k + m(σ k)`.
    This lemma shows that `G = 0` on all of `E × E` by applying the
    bivariate polynomial zeros axiom contrapositively. -/
private lemma residual_vanishes_on_ExE
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (σ : Fin d ↪ Fin M)
    (hQR : ∀ k, Q k = R (σ k))
    (hMoff : ∀ j, j ∉ Set.range σ → m j = 0)
    (hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) A₀ A₁ = 0 := by
  sorry

/-- **Core σ-matching extraction from polyG ≡ 0 on E × E.**

    Mechanizes paper Steps 3–6 via direct polynomial evaluation.

    **Proof outline:**
    1. For `j₀ : Fin M` with `R j₀ ∉ range Q`: set `A₀ = R j₀`
       (if `R j₀ ∈ E`); `polyG` reduces to
       `m j₀ · (∏_k ellP Q_k) · (∏_{j'≠j₀} ellP R_{j'})`, which is 0;
       picking `A₁` avoiding collinearity with other S-points shows `m j₀ = 0`.
    2. For each `k : Fin d`: assume `Q k ∉ range R`; set `A₀ = Q k`;
       `polyG` reduces to `β_k · (∏_{k'≠k} ellP Q_{k'}) · (∏_j ellP R_j)`;
       picking `A₁` avoiding other S-points gives `β_k = 0`,
       contradicting `hBetaNz`.
    3. Construct `σ : Fin d ↪ Fin M` with `Q k = R (σ k)`.
    4. After simplification, `polyG = (∏_k ellP Q_k) · G`;
       show `G = 0` on `E × E` via the bivariate zeros axiom.
    5. Evaluate `G` at collinear triples: `c_k = β_k + m(σ k) = 0`. -/
private lemma sigma_matching_core
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0) := by
  classical
  -- == Step 1: Q k must be on E for all k ==
  -- (The evaluation trick requires Q k ∈ E.points. The paper assumes this
  -- since Q_k are zeros of a divisor on E. We state this as a sub-claim.)
  have hQonE : ∀ k, Q k ∈ E.points := by
    sorry
  -- == Step 2: Every Q k is in range R ==
  have hSigmaExists : ∀ k : Fin d, ∃ j : Fin M, R j = Q k := by
    intro k
    by_contra h
    push_neg at h
    -- polyG(Q k, A₁) = beta k * (∏_{k'≠k} ellP(Q_{k'})) * (∏_j ellP(R_j))
    -- by polyG_at_self_Q. Since Q k ≠ R j for all j, we pick A₁ avoiding
    -- collinearity with all other S-points.
    set T1 := (Finset.univ.image (fun k' => Q k') |>.erase (Q k)) ∪
                   Finset.univ.image R with hT1_def
    have hTcard : T1.card ≤ d + M := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : ((Finset.univ.image (fun k' => Q k')).erase (Q k)).card ≤ d :=
        Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
      have h3 : (Finset.univ.image R).card ≤ M :=
        Finset.card_image_le.trans (by simp)
      linarith
    have hSizeOK : E.points.card > 2 * T1.card + 1 := by
      linarith
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (Q k) (hQonE k)
      ((Finset.univ.image (fun k' => Q k') |>.erase (Q k)) ∪ Finset.univ.image R)
      hSizeOK
    have hPolyG0 := hPolyGAll (Q k) A₁ (hQonE k) hA₁mem
    rw [polyG_at_self_Q E Q beta R m k A₁] at hPolyG0
    -- beta k * (∏_{k'≠k} ellP(Q_{k'})) * (∏_j ellP(R_j)) = 0
    -- All factors nonzero by A₁good, so beta k = 0, contradiction.
    have hProdQ : (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k' hk'
      apply hA₁good
      rw [Finset.mem_union]
      left
      rw [Finset.mem_erase]
      exact ⟨fun heq => (Finset.mem_erase.mp hk').1 (hDistinctQ heq),
             Finset.mem_image.mpr ⟨k', Finset.mem_univ _, rfl⟩⟩
    have hProdR : (∏ j : Fin M, ellP E (R j) (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j _
      apply hA₁good
      rw [Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact absurd (by
      rcases mul_eq_zero.mp hPolyG0 with h1 | h1
      · exact (mul_eq_zero.mp h1).resolve_right hProdQ
      · exact absurd h1 hProdR) (hBetaNz k)
  -- == Step 3: Build σ ==
  let sigma_fun : Fin d → Fin M := fun k => Classical.choose (hSigmaExists k)
  have hσ_def : ∀ k, R (sigma_fun k) = Q k :=
    fun k => Classical.choose_spec (hSigmaExists k)
  have hσ_inj : Function.Injective sigma_fun := by
    intro k₁ k₂ heq
    have h1 := hσ_def k₁
    have h2 := hσ_def k₂
    rw [heq] at h1
    exact hDistinctQ (h1.symm.trans h2)
  let σ : Fin d ↪ Fin M := ⟨sigma_fun, hσ_inj⟩
  -- == Step 4: m j = 0 for j ∉ range σ ==
  have hRonE : ∀ j, R j ∈ E.points := by
    sorry
  have hM_offrange : ∀ j, j ∉ Set.range σ → m j = 0 := by
    intro j hj
    -- R j ∉ {Q k} since j ∉ range σ. Set A₀ = R j.
    have hRjNotQ : ∀ k, R j ≠ Q k := by
      intro k heq
      exact hj ⟨k, hDistinctR ((hσ_def k).trans heq.symm)⟩
    set T2 := Finset.univ.image Q ∪ (Finset.univ.image R |>.erase (R j)) with hT2_def
    have hTcard2 : T2.card ≤ d + M := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : (Finset.univ.image Q).card ≤ d :=
        Finset.card_image_le.trans (by simp)
      have h3 : ((Finset.univ.image R).erase (R j)).card ≤ M :=
        Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
      omega
    have hSizeOK2 : E.points.card > 2 * T2.card + 1 := by linarith
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (R j) (hRonE j)
      (Finset.univ.image Q ∪ (Finset.univ.image R |>.erase (R j)))
      hSizeOK2
    have hPolyG0 := hPolyGAll (R j) A₁ (hRonE j) hA₁mem
    rw [polyG_at_self_R E Q beta R m j A₁] at hPolyG0
    have hProdQ2 : (∏ k : Fin d, ellP E (Q k) (R j) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k _
      apply hA₁good
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    have hProdR2 : (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (R j) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j' hj'
      apply hA₁good
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => (Finset.mem_erase.mp hj').1 (hDistinctR heq),
         Finset.mem_image.mpr ⟨j', Finset.mem_univ _, rfl⟩⟩)
    rcases mul_eq_zero.mp hPolyG0 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_right hProdQ2
    · exact absurd h1 hProdR2
  -- == Step 5: beta k + m (σ k) = 0 ==
  have hBetaMsigma : ∀ k : Fin d, beta k + m (σ k) = 0 := by
    intro k
    -- Use residual_vanishes_on_ExE to get G = 0 on E×E,
    -- then evaluate at A₀ = R(σ k) = Q k with a good A₁.
    have hResVan := residual_vanishes_on_ExE E Q beta R m σ
      (fun k' => (hσ_def k').symm) hM_offrange hPolyGAll hELarge
    -- G(Q k, A₁) = (beta k + m(σ k)) * ∏_{j≠σ(k)} ellP(R j, Q k, A₁)
    -- for all A₁ ∈ E. The product structure means:
    -- when ellP(R(σ k)) = 0 (automatic since R(σ k) = Q k = A₀),
    -- only the k-th term survives (others have ellP(R(σ k)) in their product).
    have hTcard3 : ((Finset.univ.image R).erase (R (σ k))).card ≤ M := by
      exact Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
    have hSizeOK3 : E.points.card > 2 * ((Finset.univ.image R).erase (R (σ k))).card + 1 := by
      linarith
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (Q k) (hQonE k)
      ((Finset.univ.image R).erase (R (σ k)))
      hSizeOK3
    have hResVal := hResVan (Q k) A₁ (hQonE k) hA₁mem
    rw [bivEval₂_residualFull_eq] at hResVal
    -- At A₀ = Q k = R(σ k): for k' ≠ k, the product ∏_{j≠σ(k')}
    -- includes j = σ(k) (since σ k ≠ σ k'), and
    -- ellP(R(σ k), Q k, A₁) = ellP(Q k, Q k, A₁) = 0.
    -- So only the k-th term survives.
    have hOtherTerms : ∀ k' : Fin d, k' ≠ k →
        (beta k' + m (σ k')) *
          ∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k'),
            ellP E (R j) (Q k) A₁ = 0 := by
      intro k' hne
      have hσkmem : σ k ∈ Finset.univ.erase (σ k') := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hne (by exact (σ.injective h).symm), Finset.mem_univ _⟩
      have : ellP E (R (σ k)) (Q k) A₁ = 0 := by
        change ellP E (R (sigma_fun k)) (Q k) A₁ = 0
        rw [hσ_def k]; exact ellP_self_eq_zero E (Q k) A₁
      rw [Finset.prod_eq_zero hσkmem this]
      ring
    rw [Finset.sum_eq_single k
      (fun k' _ hne => hOtherTerms k' hne)
      (fun h => absurd (Finset.mem_univ k) h)] at hResVal
    -- Now hResVal : (beta k + m(σ k)) * ∏_{j≠σ(k)} ellP(R j, Q k, A₁) = 0
    -- with the product nonzero.
    have hProdNz : (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
        ellP E (R j) (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j hj
      apply hA₁good
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      intro heq
      have := (Finset.mem_erase.mp hj).1
      apply this
      exact hDistinctR heq
    exact (mul_eq_zero.mp hResVal).resolve_right hProdNz
  refine ⟨σ, fun k => (hσ_def k).symm, hBetaMsigma, hM_offrange⟩

/-- **T5 replacement: σ-matching from polyGFull vanishing.**

    Given that `polyGFull` vanishes pointwise on all of `E × E` (a
    strengthening of `polyG = 0` on non-vertical pairs), produce the
    same σ-matching output as the original T5
    (`log_deriv_nonvanishing_criterion`), without its quadratic
    `|validPairs| ≥ 6·q·(d+M)²+…` precondition.

    The linear `hELarge : |E| > 4·(d+M) + 2` is much milder than T5's
    quadratic threshold.

    Internally consolidated via `sigma_matching_core`. -/
theorem sigma_matching_from_polyGFull_vanishing
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hVanishing : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0) := by
  classical
  have hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0 := by
    intro A₀ A₁ h₀ h₁
    rw [← bivEval₂_polyGFull_eq_polyG E Q beta R m A₀ A₁]
    exact hVanishing A₀ A₁ h₀ h₁
  exact sigma_matching_core E Q beta R m hDistinctQ hDistinctR hBetaNz hPolyGAll hELarge

end Divisor
