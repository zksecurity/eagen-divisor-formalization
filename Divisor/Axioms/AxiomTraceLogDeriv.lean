/-
  Divisor/Axioms/AxiomTraceLogDeriv.lean

  Lang's trace-of-logarithmic-derivative formula for finite separable
  algebraic extensions of differential fields.

  This is the **singular textbook target** for the trace/log-derivative
  step in the soundness analysis. The current
  `Polynomial.resultant_logDeriv_at_split_specialization` axiom (in
  `AxiomResultantLogDerivAtSplit.lean`) is a *combined* form
  (Lang VI.5 + Lang VIII.5 Case 1 + the standard `Res = N`); the
  axiom in this file is the **single textbook fact**. The plan is to
  discharge the resultant-form axiom against this one via project-side
  splitting-field + specialisation bridges, leaving only the singular
  Lang formula in the headline closure.

  Reference: Lang, *Algebra* (3rd ed., GTM 211), §VI.5 Theorem 5.1
  (p. 285) — norm and trace as products and sums over distinct
  embeddings of `E` in `k^a`; §VIII.5 Theorem 5.1 Case 1 (p. 370) —
  extension of a derivation to a separable algebraic extension via
  the implicit-function formula `ξ' = -f^D(ξ) / f'(ξ)`. The README
  links the archived snippets for these source statements.
-/
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

namespace Differential

/-- Galois case of Lang's trace-of-logarithmic-derivative formula.

This is the case needed by the intended splitting-field route from the
generic resultant logarithmic derivative to the textbook norm/trace identity:
over a finite Galois differential field extension, mathlib's product and
sum formulas for norm and trace reduce the identity to
`Differential.logDeriv_prod` and `Differential.algEquiv_deriv'`. -/
theorem logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois
    {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (α : K) (hα : α ≠ 0) :
  Differential.logDeriv (Algebra.norm F α)
    = Algebra.trace F K (Differential.logDeriv α) := by
  apply FaithfulSMul.algebraMap_injective F K
  rw [← Differential.logDeriv_algebraMap]
  rw [Algebra.norm_eq_prod_automorphisms]
  rw [trace_eq_sum_automorphisms]
  rw [Differential.logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro σ _
    simp [Differential.logDeriv, Differential.algEquiv_deriv']
  · intro σ _
    exact (map_ne_zero σ).mpr hα

/-- **Lang's trace-of-logarithmic-derivative formula** for a finite
separable field extension `F → K` between differential fields where
the derivation extends compatibly:

```
logDeriv (Algebra.norm F α) = Algebra.trace F K (logDeriv α)
```

Human-readable version: in a finite separable extension of differential
fields, taking the logarithmic derivative after applying the field norm
is the same as taking the trace of the logarithmic derivative upstairs.

This is the single textbook fact (Lang, *Algebra* GTM 211, §VI.5
Thm 5.1 + §VIII.5 Thm 5.1 Case 1). The two ingredients are:

* `N(α) = ∏_σ σ α` for `σ` over embeddings (Lang VI.5);
* derivations commute with field automorphisms in separable algebraic
  extensions (consequence of Lang VIII.5 Case 1's
  `ξ' = -f^D(ξ)/f'(ξ)`).

The Galois case is already proved above from mathlib. This broader
finite-separable form remains as a temporary target if we need the
non-Galois statement directly; the resultant-discharge path should use
the proved Galois theorem through a splitting field whenever possible. -/
axiom logDeriv_algebraNorm_eq_algebraTrace_logDeriv
    {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (α : K) (hα : α ≠ 0) :
  Differential.logDeriv (Algebra.norm F α)
    = Algebra.trace F K (Differential.logDeriv α)

end Differential
