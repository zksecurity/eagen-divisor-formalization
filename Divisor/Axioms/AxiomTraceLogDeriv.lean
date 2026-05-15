/-
  Divisor/Axioms/AxiomTraceLogDeriv.lean

  Lang's trace-of-logarithmic-derivative formula for finite Galois
  differential field extensions.

  The Galois case is fully proved here from mathlib's norm/trace and
  differential machinery; it is the form used by the intended
  splitting-field route for the resultant log-derivative bridge.

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

end Differential
