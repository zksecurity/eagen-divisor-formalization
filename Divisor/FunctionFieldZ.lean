/-
  Divisor/FunctionFieldZ.lean

  Queue-3 step (Phase 1a of the continuation plan). The chord-coordinate
  norm polynomial `normZ E λ D` for `D = a(x) − y·b(x) ∈ F_q[E]` with
  respect to the chord coordinate `z = y − λ·x`.

  Paper reference (Lemma 6, `sections/ec.tex:557-579`):
    `N(D) = lc(D)^3 · ∏_k (z − z(Q_k))^{β_k}`
  where `Q_k` ranges over the affine E-zeros of D, `β_k` are their
  multiplicities, and `z(Q) = y(Q) − λ·x(Q)` is the z-coordinate.

  Design choice: we take the RHS of the paper formula as the DEFINITION
  of `normZ E λ D`, using the constructive multiplicity function
  `betaConstructive E D` and the projection `zLambda E λ`. This matches
  the behaviour of the function-field norm on the "split" locus
  (`normPoly_splits_over_Fq E D`); equivalence with the abstract norm
  via a Sylvester resultant is deferred to Phase 1b. Downstream Phase 2
  only needs the explicit product form for the partial-fraction
  expansion of `(normZ)'(μ) / normZ(μ)` at the chord intercept, so this
  definition is the right compile target.

  Landed content:
    * `normZ E λ D` — the explicit product polynomial in z.
    * `normZ_ne_zero` — when D is nonzero (¬(a=0 ∧ b=0)), so is normZ
      (product of monics times nonzero constant).
    * `normZ_natDegree_le` — the degree is bounded by `D.degE`
      (replacement for the former `normZ_natDegree_eq`, which relied on
      the now-deleted `betaConstructive_sum_eq_degE`).
    * `normZ_eval` — evaluation at an arbitrary μ is
      `lc · ∏_Q (μ − z(Q))^{β(Q)}`.
    * `normZ_eval_at_zLambda_of_mem` — vanishing at `z(Q_k)` for any
      zero `Q_k` with β(Q_k) > 0.

  No new axioms, no `sorry` / `admit`. Preparatory for Lemma 6
  mechanization (see `docs/continuation-plan.md` Phase 1a).
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

Given the chord coordinate `z = y − λ·x` and a nonzero
`D = a(x) − y·b(x) ∈ F_q[E]`, the norm of `D` along the cubic fibres
of `E → A¹_z` is the polynomial in `z` whose roots are the `z`-values
of D's affine zeros on E, each with the corresponding multiplicity.
Concretely we take the paper formula
  `N(D) = lc(D)^3 · ∏_k (z − z(Q_k))^{β_k}`
as a definition, using the leading coefficient of `normPoly E D`
(which coincides with `lc(D)^3` in the function-field sense) as the
scalar, `betaConstructive E D` for the multiplicities, and
`zLambda E λ` for the z-coordinate projection. -/

/-- Chord-coordinate norm polynomial `normZ E λ D : (ZMod E.q)[X]`.

    Defined as the explicit product over `D`'s affine `E`-zeros:
    `normZ E λ D = C lc · ∏_{Q ∈ zerosFinset} (X − C (zLambda λ Q))^(β Q)`
    where `lc = (normPoly E D).leadingCoeff` and `β = betaConstructive E D`.

    The product is over the Finset `zerosFinset E D` (distinct affine
    E-zeros of D), with each factor raised to `betaConstructive E D Q`.
    On D-nonzeros this function is 0, and on D's affine E-zeros it is
    the multiplicity — so the product is well-defined and matches the
    paper's Lemma 6 decomposition.

    Note: "X" is the z-variable here (the indeterminate of the resulting
    univariate polynomial in z). -/
noncomputable def normZ (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (ZMod E.q)[X] :=
  C ((normPoly E D).leadingCoeff) *
    ∏ Q ∈ zerosFinset E D,
      (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q)

/-! ## Basic arithmetic -/

/-- The constant factor of `normZ`. -/
theorem normZ_eq_C_mul_prod (lam : ZMod E.q) (D : CoordRingElt E.q) :
    normZ E lam D =
      C ((normPoly E D).leadingCoeff) *
        ∏ Q ∈ zerosFinset E D,
          (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) := rfl

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

/-- The product `∏_{Q ∈ zerosFinset} (X − C (zLambda λ Q))^(β Q)` is nonzero
    (product of monics is monic, hence nonzero). -/
theorem normZ_prod_ne_zero (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) : (ZMod E.q)[X])
      ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro Q _
  exact X_sub_C_pow_ne_zero E _ _

/-- **Main non-vanishing lemma.** `normZ E λ D ≠ 0` when D is nonzero. -/
theorem normZ_ne_zero (lam : ZMod E.q)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    normZ E lam D ≠ 0 := by
  unfold normZ
  apply mul_ne_zero
  · rw [Ne, C_eq_zero]
    exact normPoly_leadingCoeff_ne_zero E D hD
  · exact normZ_prod_ne_zero E lam D

/-! ## natDegree computation

The natDegree of `normZ` is the sum of the multiplicities, which is
bounded above by `D.degE` via `betaConstructive_sum_le_degE`. -/

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
theorem normZ_prod_monic (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) : (ZMod E.q)[X]).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro Q _
  exact (monic_X_sub_C _).pow _

/-- The product has natDegree = sum of exponents. -/
theorem normZ_prod_natDegree (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (∏ Q ∈ zerosFinset E D,
        (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) : (ZMod E.q)[X]).natDegree =
      ∑ Q ∈ zerosFinset E D, betaConstructive E D Q := by
  classical
  induction (zerosFinset E D) using Finset.induction_on with
  | empty => simp
  | @insert Q s hQ ih =>
    rw [Finset.prod_insert hQ, Finset.sum_insert hQ]
    have hMonic : (∏ Q' ∈ s,
          (X - C (zLambda E lam Q')) ^ (betaConstructive E D Q') : (ZMod E.q)[X]).Monic := by
      apply Polynomial.monic_prod_of_monic
      intro Q' _
      exact (monic_X_sub_C _).pow _
    have hFactorMonic : ((X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) :
          (ZMod E.q)[X]).Monic := (monic_X_sub_C _).pow _
    rw [Polynomial.natDegree_mul hFactorMonic.ne_zero hMonic.ne_zero]
    rw [X_sub_C_pow_natDegree, ih]

/-- **natDegree bound (via `betaConstructive_sum_le_degE`).** `normZ E λ D`
    has natDegree at most `D.degE` when `D` is nonzero. Replaces the
    former `normZ_natDegree_eq`, which required the now-deleted
    `betaConstructive_sum_eq_degE` (invalidated by Aristotle's
    counterexample). -/
theorem normZ_natDegree_le (lam : ZMod E.q)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (normZ E lam D).natDegree ≤ D.degE := by
  classical
  unfold normZ
  rw [Polynomial.natDegree_mul, Polynomial.natDegree_C, zero_add]
  · rw [normZ_prod_natDegree]
    -- ∑ Q ∈ zerosFinset, β Q ≤ ∑ P ∈ E.points, β P ≤ D.degE.
    have hSumLe : (∑ P ∈ E.points, betaConstructive E D P) ≤ D.degE :=
      betaConstructive_sum_le_degE E D
    have hZerosSubset :
        (∑ Q ∈ E.points.filter (fun P => D.eval P.1 P.2 = 0),
            betaConstructive E D Q)
          = ∑ P ∈ E.points, betaConstructive E D P := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro P hPE hPNotZero
      apply betaConstructive_of_not_zero
      intro ⟨_, hPzero⟩
      apply hPNotZero
      exact Finset.mem_filter.mpr ⟨hPE, hPzero⟩
    show (∑ Q ∈ E.points.filter (fun P => D.eval P.1 P.2 = 0),
              betaConstructive E D Q) ≤ _
    rw [hZerosSubset]
    exact hSumLe
  · rw [Ne, C_eq_zero]
    exact normPoly_leadingCoeff_ne_zero E D hD
  · exact normZ_prod_ne_zero E lam D

/-! ## Evaluation

`normZ` is an explicit product, so evaluation at any μ ∈ F_q is
immediate: it's the leading coefficient times the product of
`(μ − z(Q))^{β(Q)}` over Q ∈ zerosFinset. -/

/-- Evaluation of `normZ` at `μ`. -/
theorem normZ_eval (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : ZMod E.q) :
    (normZ E lam D).eval μ =
      (normPoly E D).leadingCoeff *
        ∏ Q ∈ zerosFinset E D, (μ - zLambda E lam Q) ^ (betaConstructive E D Q) := by
  classical
  unfold normZ
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro Q _
  rw [eval_pow, eval_sub, eval_X, eval_C]

/-- **Vanishing of `normZ` at `z(Q)` for an affine E-zero Q.**
    When `Q ∈ zerosFinset E D` and `D` is nonzero, `eval (zLambda λ Q) normZ = 0`.
    The factor `(X − C (zLambda λ Q))^(β Q)` vanishes when β(Q) > 0 (guaranteed
    by `betaConstructive_covers`). -/
theorem normZ_eval_at_zLambda_of_mem
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {Q₀ : ZMod E.q × ZMod E.q} (hQ₀ : Q₀ ∈ zerosFinset E D) :
    (normZ E lam D).eval (zLambda E lam Q₀) = 0 := by
  classical
  rw [normZ_eval]
  -- The factor at Q₀ is (μ − zLambda λ Q₀)^β Q₀ = 0 since μ = zLambda λ Q₀ and
  -- β Q₀ > 0.
  have hBetaPos : 0 < betaConstructive E D Q₀ := by
    have hQ₀mem : Q₀ ∈ E.points ∧ D.eval Q₀.1 Q₀.2 = 0 := by
      simpa [zerosFinset, zeros, Finset.mem_filter] using hQ₀
    have hBetaNe := betaConstructive_covers E D hD Q₀ hQ₀mem.1 hQ₀mem.2
    omega
  -- Product at Q₀ gives the zero factor.
  rw [show (0 : ZMod E.q) = (normPoly E D).leadingCoeff * 0 by ring]
  congr 1
  apply Finset.prod_eq_zero hQ₀
  rw [sub_self, zero_pow hBetaPos.ne']

/-! ## Leading coefficient

Under the split hypothesis, `normZ`'s leading coefficient is
`(normPoly E D).leadingCoeff`; this corresponds to the paper's
`lc(D)^3` identification. The explicit form makes this immediate.
-/

/-- The leading coefficient of `normZ` equals `(normPoly E D).leadingCoeff`.
    The product factor is monic, so the leading coefficient of the whole
    is just the scalar. -/
theorem normZ_leadingCoeff (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (normZ E lam D).leadingCoeff = (normPoly E D).leadingCoeff := by
  classical
  unfold normZ
  have hMonic : (∏ Q ∈ zerosFinset E D,
          (X - C (zLambda E lam Q)) ^ (betaConstructive E D Q) : (ZMod E.q)[X]).Monic :=
    normZ_prod_monic E lam D
  rw [Polynomial.leadingCoeff_mul_monic hMonic, Polynomial.leadingCoeff_C]

/-! ## Support: `normZ`'s roots come from `zerosFinset`

A useful property for Phase 2: every root of `normZ` comes from
`zerosFinset E D` via `zLambda λ`. The product structure makes this a
direct consequence of the root of a product identity. -/

/-- If `μ` is a root of `normZ`, then `μ = zLambda λ Q` for some
    `Q ∈ zerosFinset E D`. -/
theorem normZ_isRoot_iff
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (μ : ZMod E.q) :
    (normZ E lam D).IsRoot μ ↔
      ∃ Q ∈ zerosFinset E D,
        zLambda E lam Q = μ ∧ 0 < betaConstructive E D Q := by
  classical
  constructor
  · intro hRoot
    rw [Polynomial.IsRoot, normZ_eval] at hRoot
    have hLc : (normPoly E D).leadingCoeff ≠ 0 :=
      normPoly_leadingCoeff_ne_zero E D hD
    have hProd : ∏ Q ∈ zerosFinset E D,
        (μ - zLambda E lam Q) ^ (betaConstructive E D Q) = 0 := by
      rcases mul_eq_zero.mp hRoot with h | h
      · exact absurd h hLc
      · exact h
    rw [Finset.prod_eq_zero_iff] at hProd
    obtain ⟨Q, hQ, hQeq⟩ := hProd
    have hBetaPos : 0 < betaConstructive E D Q := by
      have hQmem : Q ∈ E.points ∧ D.eval Q.1 Q.2 = 0 := by
        simpa [zerosFinset, zeros, Finset.mem_filter] using hQ
      have hBetaNe := betaConstructive_covers E D hD Q hQmem.1 hQmem.2
      omega
    refine ⟨Q, hQ, ?_, hBetaPos⟩
    have hDiffZero : μ - zLambda E lam Q = 0 :=
      pow_eq_zero_iff hBetaPos.ne' |>.mp hQeq
    exact (sub_eq_zero.mp hDiffZero).symm
  · rintro ⟨Q, hQ, hEq, _⟩
    rw [Polynomial.IsRoot, ← hEq]
    exact normZ_eval_at_zLambda_of_mem E lam D hD hQ

end Divisor
