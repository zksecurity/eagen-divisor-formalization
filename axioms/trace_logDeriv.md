# `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv`

- **Lean source**: `Divisor/Axioms/AxiomTraceLogDeriv.lean`
- **Status**: Singular target axiom for the trace/log-derivative step.
- **Replaces (planned)**: `Polynomial.resultant_logDeriv_at_split_specialization` in `AxiomResultantLogDerivAtSplit.lean`, which is a combined form awaiting discharge.

## Statement

For a finite separable field extension `F → K` between differential fields where the derivation extends compatibly, and for any nonzero `α ∈ K`:

```
logDeriv (Algebra.norm F α) = Algebra.trace F K (logDeriv α)
```

This is **the** trace-of-logarithmic-derivative formula in differential Galois theory: the logarithmic derivative of the norm equals the trace of the logarithmic derivative.

## Citation

Lang, *Algebra* (3rd ed., GTM 211):

- **§VI.5 Theorem 5.1**, p. 285 — `N^E_k(α) = ∏_σ σα` and `Tr^E_k(α) = Σ_σ σα` over the distinct embeddings of `E` in `k^a`.
- **§VIII.5 Theorem 5.1 Case 1**, p. 370 — for `ξ` separable algebraic over `K` with minimal polynomial `f`, the derivation `D` extends uniquely to `K(ξ)` via the implicit-function formula `D ξ = -f^D(ξ) / f'(ξ)`.

The trace-of-log-derivative formula is the one-line corollary: differentiate `N(α) = ∏_σ σα`, use the product rule + Galois-equivariance of the extended derivation (§VIII.5 Case 1), recognize the resulting sum as `Tr(α'/α)`.

## Discharge plan

The formula is currently stated as an axiom because mathlib does not yet expose it directly. The building blocks all exist:

- `Differential.algEquiv_deriv'` (in `Mathlib.RingTheory.Derivation.MapCoeffs`) — derivations commute with `K`-algebra automorphisms when the extension is separable.
- `Differential.logDeriv_prod` (in `Mathlib.FieldTheory.Differential.Basic`) — logDeriv of a product is a sum.
- `Algebra.norm_eq_prod_galois` / `Algebra.trace_eq_sum_galois` (in `Mathlib.RingTheory.Norm` / `Mathlib.RingTheory.Trace`) — norm/trace as products/sums over Galois automorphisms.
- The non-Galois case is reduced to the Galois case via the Galois closure (the same lifting used by `isLiouville_of_finiteDimensional` in `Mathlib.FieldTheory.Differential.Liouville`).

A direct mathlib-style proof is a moderate refactor of the inline chain inside `Liouville.lean`. Once mathlib exposes the formula as a theorem, this axiom can be deleted and the chord-fiber log-derivative discharge can be re-routed through the (now-theorem) formula.

## Why this replaces the resultant log-derivative axiom

The current resultant log-derivative axiom

```
F'(t₀) / F(t₀) = Σ_{x ∈ f(X, t₀).roots}
                   (g_T · f_X − g_X · f_T) / (f_X · g) (x, t₀)
```

is a *project-side composition* of three textbook facts:

1. **Lang VI.5**: `Algebra.norm L K (g(ξ)) = ∏_σ σ(g(ξ)) = ∏_i g(ξ_i, T)` over the conjugates `ξ_i` of a root `ξ` of `f` over `K(T)`.
2. **Lang VIII.5 Case 1**: `ξ_i'(T) = -f^D(ξ_i, T) / f'(ξ_i, T)` for each conjugate.
3. **`Polynomial.resultant_eq_prod_eval`** (mathlib theorem): `Res_X(f, g) = (lc f)^{deg g} · ∏_i g(ξ_i, T)` when `f` splits.

Compositing the three (and applying logDeriv via this trace-of-log-derivative axiom) gives the resultant log-derivative formula. Each ingredient is textbook; the axiom in this file is the *single* deepest one. The composition is then a project theorem, not an axiom.

The bridge from this trace-of-log-derivative axiom down to the resultant log-derivative formula at a split specialisation point requires:

1. A `Differential` instance on `K(T) = RatFunc K` with `T' = 1`.
2. Construction of the splitting field `L` of `f` over `K(T)`, with the derivation extended to `L` via `Differential.deriv_aeval_eq_implicitDeriv` (mathlib has this).
3. Identifying `Algebra.norm K(T) L (g(ξ))` with `Res_X(f, g) / (lc f)^{deg g}` (using `Polynomial.resultant_eq_prod_eval` + Lang VI.5).
4. Specialisation: pulling the K(T)-valued identity at the generic `T` back to a K-valued identity at a specific `T = t₀`, using ordinary polynomial / rational function evaluation.

This bridge is project-side Lean engineering (no new axioms required). It is the path to making the resultant log-derivative formula a *theorem* and removing it from the axiom closure entirely.

## Status today

- This axiom (`Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv`) is declared but not yet imported by any headline-closure file.
- The `Polynomial.resultant_logDeriv_at_split_specialization` axiom (the combined form) remains active in the headline closure.
- The discharge plan above is the path to swapping them: once the bridge is mechanised, the combined-form axiom becomes a theorem, and only this singular textbook axiom remains.
