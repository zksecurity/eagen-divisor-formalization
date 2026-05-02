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
  the implicit-function formula `ξ' = -f^D(ξ) / f'(ξ)`. See
  `axioms/trace_logDeriv.md`.
-/
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

namespace Differential

/-- **Lang's trace-of-logarithmic-derivative formula** for a finite
separable field extension `F → K` between differential fields where
the derivation extends compatibly:

```
logDeriv (Algebra.norm F α) = Algebra.trace F K (logDeriv α)
```

This is the single textbook fact (Lang, *Algebra* GTM 211, §VI.5
Thm 5.1 + §VIII.5 Thm 5.1 Case 1). The two ingredients are:

* `N(α) = ∏_σ σ α` for `σ` over embeddings (Lang VI.5);
* derivations commute with field automorphisms in separable algebraic
  extensions (consequence of Lang VIII.5 Case 1's
  `ξ' = -f^D(ξ)/f'(ξ)`).

Mathlib has the building blocks (`Differential.algEquiv_deriv'` +
`Differential.logDeriv_prod` + `Algebra.norm_eq_prod_galois_symm` /
`Algebra.trace_eq_sum_galois`) — see `Mathlib.FieldTheory.Differential.Liouville`
where the proof of Liouville's theorem already executes this chain
inline. A clean extraction as a mathlib theorem (and consequently a
project theorem here) is the discharge plan; until that lands, the
formula is stated as an axiom. -/
axiom logDeriv_algebraNorm_eq_algebraTrace_logDeriv
    {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (α : K) (hα : α ≠ 0) :
  Differential.logDeriv (Algebra.norm F α)
    = Algebra.trace F K (Differential.logDeriv α)

end Differential
