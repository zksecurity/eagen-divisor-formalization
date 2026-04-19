/-
  Divisor/PartialFraction.lean

  Simple-pole partial-fraction uniqueness.

  Given distinct poles α_i in a field K, the basis polynomials
  P_i := ∏_{j ∈ s \ {i}} (X - α_j) are linearly independent over K. Any
  K-linear combination Σ_i c_i · P_i that vanishes as a polynomial has
  all coefficients c_i = 0.

  This is the core algebraic input for the log-derivative non-vanishing
  criterion (`log_deriv_nonvanishing_criterion` axiom, T5 in the axiom
  elimination plan). The lemma is standalone and independent of the rest
  of the Divisor development.
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Eval

open Polynomial Finset

namespace Divisor

/-- **Simple-pole uniqueness.**
    If `α : ι → K` is injective on `s` and
    `∑ i ∈ s, C (c i) · ∏ j ∈ s.erase i, (X - C (α j)) = 0`,
    then `c i = 0` for every `i ∈ s`. -/
lemma simple_pole_fraction_zero {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → K) (c : ι → K) (hα : Set.InjOn α s)
    (h : (∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, (X - C (α j))) = 0) :
    ∀ k ∈ s, c k = 0 := by
  intro k hk
  -- Evaluate the identity at α k.
  have hE : (∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, (X - C (α j))).eval (α k) = 0 := by
    rw [h]; simp
  rw [Polynomial.eval_finset_sum] at hE
  -- For i ∈ s with i ≠ k, the product in the i-th summand contains the factor
  -- (X - C (α k)), which evaluates to zero at α k. Hence that summand is zero.
  have hOther : ∀ i ∈ s, i ≠ k →
      (C (c i) * ∏ j ∈ s.erase i, (X - C (α j))).eval (α k) = 0 := by
    intro i _ hne
    have hk_erase : k ∈ s.erase i :=
      Finset.mem_erase.mpr ⟨fun heq => hne heq.symm, hk⟩
    rw [eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero.mpr (Or.inr ?_)
    exact Finset.prod_eq_zero hk_erase (by simp)
  -- Only the k-th summand survives.
  have hSingle :
      ∑ i ∈ s, (C (c i) * ∏ j ∈ s.erase i, (X - C (α j))).eval (α k) =
        (C (c k) * ∏ j ∈ s.erase k, (X - C (α j))).eval (α k) :=
    Finset.sum_eq_single k hOther (fun hnotin => absurd hk hnotin)
  rw [hSingle] at hE
  rw [eval_mul, eval_C, Polynomial.eval_prod] at hE
  -- The product ∏ j ∈ s.erase k, (α k - α j) is nonzero by injectivity of α on s.
  have hProdNZ : ∏ j ∈ s.erase k, eval (α k) (X - C (α j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (fun heq => hjk (hα hjs hk heq.symm))
  exact (mul_eq_zero.mp hE).resolve_right hProdNZ

end Divisor
