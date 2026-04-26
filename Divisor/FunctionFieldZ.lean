/-
  Divisor/FunctionFieldZ.lean

  The chord-coordinate norm polynomial `normZ E λ D β_fun` for
  `D = a(x) − y·b(x) ∈ F_q[E]` with respect to the chord coordinate
  `z = y − λ·x`, parameterised over an arbitrary multiplicity function
  `β_fun : ZMod E.q × ZMod E.q → ℕ`.

  Paper reference (`\ref{lem:log-derivative}`, `sections/ec.tex:557-579`):
    `N(D) = lc(D)^3 · ∏_k (z − z(Q_k))^{β_k}`
  where `Q_k` ranges over the affine E-zeros of D, `β_k` are their
  multiplicities, and `z(Q) = y(Q) − λ·x(Q)` is the z-coordinate.

  Design choice: we take the RHS of the paper formula as the DEFINITION
  of `normZ E λ D β_fun`. The downstream chord-fiber-product axiom
  takes a β_fun matching the *true* divisor multiplicity (supplied
  by `CoordRingElt.exists_divisor_multiplicity`); choosing β_fun
  to be `betaConstructive E D` would not give a sound proportionality,
  since `betaConstructive`'s twin Nat-division surrogate is provably
  non-faithful to ord_P (counterexample at
  `AxiomExistsDivisorMultiplicity.lean`).

  Landed content:
    * `normZ E λ D β_fun` — the explicit product polynomial in z.
    * `normZ_ne_zero` — when D is nonzero, so is normZ.
    * `normZ_natDegree_le` — the degree is bounded by `D.degE`
      under the support+sum-bound hypotheses on β_fun.
    * `normZ_eval` — evaluation at an arbitrary μ.
    * `normZ_eval_at_zLambda_of_mem` — vanishing at `z(Q_k)`.

  No new axioms, no `sorry` / `admit`.
-/
import Divisor.BetaConstructive
import Divisor.DivisorPrincipal
import Divisor.PolyGSlopeProjection
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The chord-coordinate norm polynomial

Given the chord coordinate `z = y − λ·x`, a nonzero
`D = a(x) − y·b(x) ∈ F_q[E]`, and a multiplicity function `β_fun`,
the norm of `D` along the cubic fibres of `E → A¹_z` is the
polynomial in `z` whose roots are the `z`-values of D's affine
zeros on E, each raised to its β_fun multiplicity.
-/

/-- Chord-coordinate norm polynomial `normZ E λ D β_fun : (ZMod E.q)[X]`.

    Defined as the explicit product over `D`'s affine `E`-zeros:
    `normZ E λ D β_fun = C lc · ∏_{Q ∈ zerosFinset} (X − C (zLambda λ Q))^(β_fun Q)`
    where `lc = (normPoly E D).leadingCoeff`.

    Note: "X" is the z-variable here (the indeterminate of the resulting
    univariate polynomial in z). -/
noncomputable def normZ (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) : (ZMod E.q)[X] :=
  C ((normPoly E D).leadingCoeff) *
    ∏ Q ∈ zerosFinset E D,
      (X - C (zLambda E lam Q)) ^ (β_fun Q)

/-! ## Basic arithmetic -/

/-- The constant factor of `normZ`. -/
theorem normZ_eq_C_mul_prod (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    normZ E lam D β_fun =
      C ((normPoly E D).leadingCoeff) *
        ∏ Q ∈ zerosFinset E D,
          (X - C (zLambda E lam Q)) ^ (β_fun Q) := rfl

/-- `leadingCoeff (normPoly E D) ≠ 0` when D is nonzero. -/
theorem normPoly_leadingCoeff_ne_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (normPoly E D).leadingCoeff ≠ 0 :=
  leadingCoeff_ne_zero.mpr (normPoly_ne_zero E D hD)

/-! ## Non-vanishing -/

/-- Each factor `(X − C α) ^ m` is monic, hence nonzero. -/
theorem X_sub_C_pow_ne_zero (α : ZMod E.q) (m : ℕ) :
    ((X - C α) ^ m : (ZMod E.q)[X]) ≠ 0 := by
  apply pow_ne_zero
  exact X_sub_C_ne_zero α

/-- The product `∏_{Q ∈ zerosFinset} (X − C (zLambda λ Q))^(β_fun Q)` is nonzero
    (product of monics is monic, hence nonzero). -/
theorem normZ_prod_ne_zero (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (β_fun Q) : (ZMod E.q)[X])
      ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro Q _
  exact X_sub_C_pow_ne_zero E _ _

/-- **Main non-vanishing lemma.** `normZ E λ D β_fun ≠ 0` when D is nonzero. -/
theorem normZ_ne_zero (lam : ZMod E.q)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    normZ E lam D β_fun ≠ 0 := by
  unfold normZ
  apply mul_ne_zero
  · rw [Ne, C_eq_zero]
    exact normPoly_leadingCoeff_ne_zero E D hD
  · exact normZ_prod_ne_zero E lam D β_fun

/-! ## natDegree computation

The natDegree of `normZ` is the sum of the multiplicities (over the
affine D-zeros), bounded above by `∑ β_fun ≤ D.degE` under the
support hypothesis. -/

/-- Each monic factor `(X − C α)^m` has natDegree `m`. -/
theorem X_sub_C_pow_natDegree (α : ZMod E.q) (m : ℕ) :
    ((X - C α) ^ m : (ZMod E.q)[X]).natDegree = m := by
  rw [natDegree_pow]
  rw [natDegree_X_sub_C]
  ring

/-- Each monic factor `(X − C α)^m` is monic, hence has leading coeff 1. -/
theorem X_sub_C_pow_leadingCoeff (α : ZMod E.q) (m : ℕ) :
    ((X - C α) ^ m : (ZMod E.q)[X]).leadingCoeff = 1 := by
  have h : ((X - C α) ^ m : (ZMod E.q)[X]).Monic := (monic_X_sub_C α).pow m
  exact h

/-- The product over `zerosFinset E D` is monic. -/
theorem normZ_prod_monic (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (β_fun Q) : (ZMod E.q)[X]).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro Q _
  exact (monic_X_sub_C _).pow _

/-- The product has natDegree = sum of exponents. -/
theorem normZ_prod_natDegree (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (β_fun Q) : (ZMod E.q)[X]).natDegree =
      ∑ Q ∈ zerosFinset E D, β_fun Q := by
  classical
  induction (zerosFinset E D) using Finset.induction_on with
  | empty => simp
  | @insert Q s hQ ih =>
    rw [Finset.prod_insert hQ, Finset.sum_insert hQ]
    have hMonic : (∏ Q' ∈ s,
          (X - C (zLambda E lam Q')) ^ (β_fun Q') : (ZMod E.q)[X]).Monic := by
      apply Polynomial.monic_prod_of_monic
      intro Q' _
      exact (monic_X_sub_C _).pow _
    have hFactorMonic : ((X - C (zLambda E lam Q)) ^ (β_fun Q) :
          (ZMod E.q)[X]).Monic := (monic_X_sub_C _).pow _
    rw [Polynomial.natDegree_mul hFactorMonic.ne_zero hMonic.ne_zero]
    rw [X_sub_C_pow_natDegree, ih]

/-- **natDegree bound.** `normZ E λ D β_fun` has natDegree at most
    `D.degE` when `D` is nonzero, under the support and sum-bound
    hypotheses on β_fun. -/
theorem normZ_natDegree_le (lam : ZMod E.q)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ D.degE) :
    (normZ E lam D β_fun).natDegree ≤ D.degE := by
  classical
  unfold normZ
  rw [Polynomial.natDegree_mul, Polynomial.natDegree_C, zero_add]
  · rw [normZ_prod_natDegree]
    -- ∑ Q ∈ zerosFinset, β_fun Q ≤ ∑ P ∈ E.points, β_fun P ≤ D.degE.
    have hZerosSubset :
        (∑ Q ∈ E.points.filter (fun P => D.eval P.1 P.2 = 0),
            β_fun Q)
          = ∑ P ∈ E.points, β_fun P := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro P hPE hPNotZero
      by_contra hβne
      apply hPNotZero
      exact Finset.mem_filter.mpr ⟨hPE, (hβsup P hβne).2⟩
    show (∑ Q ∈ E.points.filter (fun P => D.eval P.1 P.2 = 0),
              β_fun Q) ≤ _
    rw [hZerosSubset]
    exact hβsum
  · rw [Ne, C_eq_zero]
    exact normPoly_leadingCoeff_ne_zero E D hD
  · exact normZ_prod_ne_zero E lam D β_fun

/-! ## Evaluation -/

/-- Evaluation of `normZ` at `μ`. -/
theorem normZ_eval (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (μ : ZMod E.q) :
    (normZ E lam D β_fun).eval μ =
      (normPoly E D).leadingCoeff *
        ∏ Q ∈ zerosFinset E D, (μ - zLambda E lam Q) ^ (β_fun Q) := by
  classical
  unfold normZ
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro Q _
  rw [eval_pow, eval_sub, eval_X, eval_C]

/-- **Vanishing of `normZ` at `z(Q)` for an affine E-zero Q with β_fun(Q) > 0.** -/
theorem normZ_eval_at_zLambda_of_mem
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    {Q₀ : ZMod E.q × ZMod E.q} (hQ₀ : Q₀ ∈ zerosFinset E D)
    (hβPos : 0 < β_fun Q₀) :
    (normZ E lam D β_fun).eval (zLambda E lam Q₀) = 0 := by
  classical
  rw [normZ_eval]
  -- The factor at Q₀ is (μ − zLambda λ Q₀)^β_fun Q₀ = 0 since μ = zLambda λ Q₀ and
  -- β_fun(Q₀) > 0.
  rw [show (0 : ZMod E.q) = (normPoly E D).leadingCoeff * 0 by ring]
  congr 1
  apply Finset.prod_eq_zero hQ₀
  rw [sub_self, zero_pow hβPos.ne']

/-! ## Leading coefficient -/

/-- The leading coefficient of `normZ` equals `(normPoly E D).leadingCoeff`.
    The product factor is monic, so the leading coefficient of the whole
    is just the scalar. -/
theorem normZ_leadingCoeff (lam : ZMod E.q) (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    (normZ E lam D β_fun).leadingCoeff = (normPoly E D).leadingCoeff := by
  classical
  unfold normZ
  have hMonic : (∏ Q ∈ zerosFinset E D,
          (X - C (zLambda E lam Q)) ^ (β_fun Q) : (ZMod E.q)[X]).Monic :=
    normZ_prod_monic E lam D β_fun
  rw [Polynomial.leadingCoeff_mul_monic hMonic, Polynomial.leadingCoeff_C]

/-! ## Support: `normZ`'s roots come from `zerosFinset` -/

/-- If `μ` is a root of `normZ`, then `μ = zLambda λ Q` for some
    `Q ∈ zerosFinset E D` with `β_fun(Q) > 0`. -/
theorem normZ_isRoot_iff
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (μ : ZMod E.q) :
    (normZ E lam D β_fun).IsRoot μ ↔
      ∃ Q ∈ zerosFinset E D,
        zLambda E lam Q = μ ∧ 0 < β_fun Q := by
  classical
  constructor
  · intro hRoot
    rw [Polynomial.IsRoot, normZ_eval] at hRoot
    have hLc : (normPoly E D).leadingCoeff ≠ 0 :=
      normPoly_leadingCoeff_ne_zero E D hD
    have hProd : ∏ Q ∈ zerosFinset E D,
        (μ - zLambda E lam Q) ^ (β_fun Q) = 0 := by
      rcases mul_eq_zero.mp hRoot with h | h
      · exact absurd h hLc
      · exact h
    rw [Finset.prod_eq_zero_iff] at hProd
    obtain ⟨Q, hQ, hQeq⟩ := hProd
    -- β_fun(Q) > 0 follows from the factor being zero (otherwise
    -- (anything)^0 = 1 ≠ 0).
    have hBetaPos : 0 < β_fun Q := by
      by_contra hNeg
      push_neg at hNeg
      interval_cases (β_fun Q)
      simp at hQeq
    refine ⟨Q, hQ, ?_, hBetaPos⟩
    have hDiffZero : μ - zLambda E lam Q = 0 :=
      pow_eq_zero_iff hBetaPos.ne' |>.mp hQeq
    exact (sub_eq_zero.mp hDiffZero).symm
  · rintro ⟨Q, hQ, hEq, hBetaPos⟩
    rw [Polynomial.IsRoot, ← hEq]
    exact normZ_eval_at_zLambda_of_mem E lam D β_fun hQ hBetaPos

end Divisor
