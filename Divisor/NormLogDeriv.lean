/-
  Divisor/NormLogDeriv.lean

  Log-derivative of `normPoly E D` in denominator-cleared form,
  specialized from the generic partial-fraction expansion
  (`derivative_eq_sum_rootMultiplicity`) and the total / per-x₀
  `betaConstructive` <-> `rootMultiplicity` bridges.

  Exports (all in namespace `Divisor`):

  * `normPoly_splits_factorization` : the split factorization hypothesis
    for `p = normPoly E D` packaged from `normPoly_splits_over_Fq`.
  * `normPoly_derivative_eq_sum_of_splits` : denominator-cleared PFE for
    `derivative (normPoly E D)`, as a single Finset sum over
    `(normPoly E D).roots.toFinset`.
  * `normPoly_derivative_eq_isolate_of_splits` : the same identity with
    the summand at a distinguished root `α₀` pulled out.
  * `normPoly_derivative_eval_at_root_of_splits` : evaluation of
    `derivative (normPoly E D)` at a root `α₀`. Only the `α = α₀`
    summand survives; all others have a `(X - C α₀)^(rootMult α₀)`
    factor that evaluates to `0` when `rootMult α₀ > 0`.
  * `normPoly_derivative_eval_simple_root_of_splits` (Identity C, simple
    form): clean "isolate-at-α₀" denominator-cleared evaluation at a
    *simple* root (rootMult = 1), expressing
    `eval α₀ (derivative (normPoly E D))` as
    `leadingCoeff · ∏_{β ≠ α₀} (α₀ - β)^{rootMult β}`.

  No new axioms, no `sorry` / `admit`. Purely univariate polynomial
  algebra plus the `rootMultiplicity`-form Identity C.
-/
import Divisor.BetaConstructive
import Divisor.PartialFractionExpansion

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Split factorization of `normPoly E D` -/

/-- Under the split hypothesis `normPoly_splits_over_Fq`, the norm
polynomial admits the explicit Finset factorization
`N(D) = C lc · ∏ α ∈ roots.toFinset, (X - C α) ^ (rootMult α N(D))`.

Direct instantiation of `splits_factorization_of_roots_card_eq` at
`p = normPoly E D`. -/
theorem normPoly_splits_factorization
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D) :
    normPoly E D = C (normPoly E D).leadingCoeff *
      ∏ α ∈ (normPoly E D).roots.toFinset,
        (X - C α) ^ (rootMultiplicity α (normPoly E D)) :=
  splits_factorization_of_roots_card_eq (normPoly E D) hSplit

/-! ## Identity A : denominator-cleared PFE on `normPoly E D` -/

/-- **Identity A (denominator-cleared PFE on `N(D)`).** Under the split
hypothesis, `derivative (normPoly E D)` equals a single Finset sum over
its `F_q`-rational roots, each summand being a polynomial:

  `N(D)' = C lc · ∑_{α ∈ S} C (rootMult α) · (X - C α)^(rootMult α - 1) ·
            ∏_{β ∈ S.erase α} (X - C β)^(rootMult β)`

where `S = (normPoly E D).roots.toFinset`.

Direct instantiation of
`derivative_eq_sum_rootMultiplicity_of_roots_card_eq` at
`p = normPoly E D`. -/
theorem normPoly_derivative_eq_sum_of_splits
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D) :
    derivative (normPoly E D) = C (normPoly E D).leadingCoeff *
      ∑ α ∈ (normPoly E D).roots.toFinset,
        (C ((rootMultiplicity α (normPoly E D) : ZMod E.q)) *
          (X - C α) ^ ((rootMultiplicity α (normPoly E D)) - 1) *
          ∏ β ∈ (normPoly E D).roots.toFinset.erase α,
            (X - C β) ^ (rootMultiplicity β (normPoly E D))) :=
  derivative_eq_sum_rootMultiplicity_of_roots_card_eq
    (normPoly E D) hSplit

/-! ## Identity B : isolate-at-α₀ form -/

/-- **Identity B (isolate at a distinguished root `α₀`).** Pull out the
`α = α₀` summand of Identity A, leaving a sum over
`roots.toFinset.erase α₀`. -/
theorem normPoly_derivative_eq_isolate_of_splits
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D)
    {α₀ : ZMod E.q} (hα₀ : α₀ ∈ (normPoly E D).roots.toFinset) :
    derivative (normPoly E D) =
      C (normPoly E D).leadingCoeff *
        (C ((rootMultiplicity α₀ (normPoly E D) : ZMod E.q)) *
          (X - C α₀) ^ ((rootMultiplicity α₀ (normPoly E D)) - 1) *
          ∏ β ∈ (normPoly E D).roots.toFinset.erase α₀,
            (X - C β) ^ (rootMultiplicity β (normPoly E D)))
      + C (normPoly E D).leadingCoeff *
        ∑ α ∈ (normPoly E D).roots.toFinset.erase α₀,
          (C ((rootMultiplicity α (normPoly E D) : ZMod E.q)) *
            (X - C α) ^ ((rootMultiplicity α (normPoly E D)) - 1) *
            ∏ β ∈ (normPoly E D).roots.toFinset.erase α,
              (X - C β) ^ (rootMultiplicity β (normPoly E D))) := by
  classical
  -- Rewrite via the split factorization and apply the isolate lemma.
  have hFact := normPoly_splits_factorization E D hSplit
  -- Apply the isolate lemma specialized to `c = leadingCoeff`,
  -- `S = roots.toFinset`, `m = rootMultiplicity`.
  have h := derivative_C_mul_prod_X_sub_C_pow_isolate
    (K := ZMod E.q) (normPoly E D).leadingCoeff
    (normPoly E D).roots.toFinset
    (fun α => rootMultiplicity α (normPoly E D)) hα₀
  -- `h` speaks of `derivative (C lc * ∏ ...)` which is `derivative N(D)` by hFact.
  have hLHS : derivative
      (C (normPoly E D).leadingCoeff *
        ∏ α ∈ (normPoly E D).roots.toFinset,
          (X - C α) ^ (rootMultiplicity α (normPoly E D)))
        = derivative (normPoly E D) := by
    congr 1
    exact hFact.symm
  rw [hLHS] at h
  exact h

/-! ## Evaluation at a root : all "off-diagonal" summands vanish

Fix a root `α₀ ∈ roots.toFinset` and evaluate Identity A at `X = α₀`.
For every `α ∈ roots.toFinset \ {α₀}`, the factor
`(X - C α₀)^(rootMult α₀)` (which is one of the `β`-factors in the
product `∏ β ∈ S.erase α, ...` since `α₀ ∈ S.erase α` when `α ≠ α₀`)
evaluates to `0` at `X = α₀` (because `rootMult α₀ ≥ 1` at a root).
So only the `α = α₀` summand survives. -/

/-- Auxiliary: evaluating `(X - C α₀)^k` at `α₀` is `0` if `k ≥ 1`,
`1` if `k = 0`. -/
theorem eval_X_sub_C_pow_self {K : Type*} [CommRing K] (α₀ : K) (k : ℕ) :
    eval α₀ ((X - C α₀) ^ k) = if k = 0 then 1 else 0 := by
  rw [eval_pow, eval_sub, eval_X, eval_C, sub_self]
  split_ifs with h
  · simp [h]
  · exact zero_pow h

/-- For `α ∈ S` and `α ≠ α₀` with `α₀ ∈ S`, the Finset `S.erase α`
contains `α₀`. Hence the product `∏ β ∈ S.erase α, (X - C β)^(m β)`
evaluated at `α₀` vanishes whenever `m α₀ ≥ 1`. -/
theorem eval_prod_X_sub_C_pow_off_diag_eq_zero
    {K : Type*} [CommRing K] [DecidableEq K]
    (S : Finset K) (m : K → ℕ)
    {α α₀ : K} (hα₀ : α₀ ∈ S) (_ : α ∈ S) (hne : α ≠ α₀)
    (hm : 1 ≤ m α₀) :
    eval α₀ (∏ β ∈ S.erase α, (X - C β) ^ (m β)) = 0 := by
  classical
  -- α₀ ∈ S.erase α since α₀ ∈ S and α₀ ≠ α.
  have hα₀mem : α₀ ∈ S.erase α := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hα₀⟩
  rw [eval_prod]
  refine Finset.prod_eq_zero hα₀mem ?_
  rw [eval_X_sub_C_pow_self]
  -- m α₀ ≥ 1, so m α₀ ≠ 0.
  have hne0 : m α₀ ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  simp [hne0]

/-- Evaluation of the "off-diagonal summand" at `α₀`: zero. -/
theorem eval_off_diag_summand_eq_zero
    {K : Type*} [CommRing K] [DecidableEq K]
    (S : Finset K) (m : K → ℕ) {α α₀ : K}
    (hα₀ : α₀ ∈ S) (hα : α ∈ S) (hne : α ≠ α₀)
    (hm : 1 ≤ m α₀) :
    eval α₀ (C ((m α : K)) * (X - C α) ^ (m α - 1) *
        ∏ β ∈ S.erase α, (X - C β) ^ (m β)) = 0 := by
  classical
  rw [eval_mul]
  rw [eval_prod_X_sub_C_pow_off_diag_eq_zero S m hα₀ hα hne hm]
  ring

/-- **Off-diagonal sum vanishes on evaluation.** -/
theorem eval_sum_off_diag_eq_zero
    {K : Type*} [CommRing K] [DecidableEq K]
    (S : Finset K) (m : K → ℕ) {α₀ : K}
    (hα₀ : α₀ ∈ S) (hm : 1 ≤ m α₀) :
    eval α₀
      (∑ α ∈ S.erase α₀,
        (C ((m α : K)) * (X - C α) ^ (m α - 1) *
          ∏ β ∈ S.erase α, (X - C β) ^ (m β))) = 0 := by
  classical
  rw [eval_finsetSum]
  refine Finset.sum_eq_zero ?_
  intro α hα
  rw [Finset.mem_erase] at hα
  obtain ⟨hne, hαS⟩ := hα
  exact eval_off_diag_summand_eq_zero S m hα₀ hαS hne hm

/-! ## Identity C : evaluation at a root in the split case -/

/-- Auxiliary: positivity of rootMultiplicity at a member of
`roots.toFinset`. -/
theorem rootMultiplicity_pos_of_mem_toFinset
    {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {p : K[X]} {α : K}
    (hα : α ∈ p.roots.toFinset) :
    1 ≤ rootMultiplicity α p := by
  -- p ≠ 0 because roots of zero is ∅.
  have hNZ : p ≠ 0 := by
    intro h
    rw [h] at hα
    simp at hα
  -- α ∈ p.roots.toFinset iff α ∈ p.roots iff p.IsRoot α (for p ≠ 0).
  have hR : α ∈ p.roots := Multiset.mem_toFinset.mp hα
  have hIR : p.IsRoot α := (Polynomial.mem_roots hNZ).mp hR
  rw [Nat.one_le_iff_ne_zero]
  intro hZero
  have hPos := (Polynomial.rootMultiplicity_pos hNZ).mpr hIR
  omega

/-- **Identity C (evaluation at a root of `N(D)`, split case).**

Evaluating the PFE identity A at `X = α₀ ∈ roots.toFinset`, the
"off-diagonal" sum vanishes, leaving only the `α = α₀` summand:

  `eval α₀ (N(D)') = lc · rootMult α₀ · 0^(rootMult α₀ - 1)
                        · ∏_{β ≠ α₀} (α₀ - β)^(rootMult β)`.

When `rootMult α₀ = 1`, the `0^0 = 1` factor is trivial.
When `rootMult α₀ ≥ 2`, the `0^(≥1) = 0` factor kills the RHS (and LHS
is `0` because the derivative has a multiple root).

The statement below encodes the unsimplified evaluation; the simple-root
simplification is `normPoly_derivative_eval_simple_root_of_splits`. -/
theorem normPoly_derivative_eval_at_root_of_splits
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D)
    {α₀ : ZMod E.q} (hα₀ : α₀ ∈ (normPoly E D).roots.toFinset) :
    eval α₀ (derivative (normPoly E D)) =
      (normPoly E D).leadingCoeff *
        ((rootMultiplicity α₀ (normPoly E D) : ZMod E.q) *
          ((0 : ZMod E.q)) ^ ((rootMultiplicity α₀ (normPoly E D)) - 1) *
          ∏ β ∈ (normPoly E D).roots.toFinset.erase α₀,
            (α₀ - β) ^ (rootMultiplicity β (normPoly E D))) := by
  classical
  -- Start from the isolated identity, then evaluate.
  have hIso := normPoly_derivative_eq_isolate_of_splits E D hSplit hα₀
  -- m α₀ ≥ 1 because α₀ ∈ roots.toFinset of a nonzero polynomial.
  have hm : 1 ≤ rootMultiplicity α₀ (normPoly E D) :=
    rootMultiplicity_pos_of_mem_toFinset hα₀
  -- Off-diagonal sum evaluates to 0.
  have hOffDiag : eval α₀
      (∑ α ∈ (normPoly E D).roots.toFinset.erase α₀,
        (C ((rootMultiplicity α (normPoly E D) : ZMod E.q)) *
          (X - C α) ^ ((rootMultiplicity α (normPoly E D)) - 1) *
          ∏ β ∈ (normPoly E D).roots.toFinset.erase α,
            (X - C β) ^ (rootMultiplicity β (normPoly E D)))) = 0 :=
    eval_sum_off_diag_eq_zero
      (normPoly E D).roots.toFinset
      (fun α => rootMultiplicity α (normPoly E D)) hα₀ hm
  -- Apply congr, then simplify using eval_add, eval_mul, etc.
  rw [hIso]
  rw [eval_add, eval_mul, eval_C, eval_mul, eval_mul, eval_C,
      eval_pow, eval_sub, eval_X, eval_C, sub_self,
      eval_prod, eval_mul, eval_C, hOffDiag, mul_zero, add_zero]
  -- Unfold (α₀ - β) = eval α₀ (X - C β).
  have hProd :
      ∏ β ∈ (normPoly E D).roots.toFinset.erase α₀,
          eval α₀ ((X - C β) ^ (rootMultiplicity β (normPoly E D)))
      = ∏ β ∈ (normPoly E D).roots.toFinset.erase α₀,
          (α₀ - β) ^ (rootMultiplicity β (normPoly E D)) := by
    refine Finset.prod_congr rfl ?_
    intro β _
    rw [eval_pow, eval_sub, eval_X, eval_C]
  rw [hProd]

/-- **Identity C', simple form (rootMult α₀ = 1).** When the root `α₀` is
*simple* (rootMultiplicity = 1), the evaluation of the derivative is a
clean scalar product of leading coefficient and "off-root" factors:

  `eval α₀ (N(D)') = lc · ∏_{β ∈ roots \ {α₀}} (α₀ - β)^(rootMult β)`. -/
theorem normPoly_derivative_eval_simple_root_of_splits
    (D : CoordRingElt E.q) (hSplit : normPoly_splits_over_Fq E D)
    {α₀ : ZMod E.q} (hα₀ : α₀ ∈ (normPoly E D).roots.toFinset)
    (hSimple : rootMultiplicity α₀ (normPoly E D) = 1) :
    eval α₀ (derivative (normPoly E D)) =
      (normPoly E D).leadingCoeff *
        ∏ β ∈ (normPoly E D).roots.toFinset.erase α₀,
          (α₀ - β) ^ (rootMultiplicity β (normPoly E D)) := by
  classical
  rw [normPoly_derivative_eval_at_root_of_splits E D hSplit hα₀, hSimple]
  -- rootMult α₀ = 1 ⇒ 0^(1-1) = 0^0 = 1, and ((1:ℕ):ZMod E.q) = 1.
  simp

end Divisor
