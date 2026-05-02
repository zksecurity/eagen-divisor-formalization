# `Polynomial.resultant_logDeriv_at_split_specialization`

- **Lean source**: `Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean`
- **Downstream consumer**: `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` in `Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean` (now a theorem).

## Statement

For `f, g : K[T][X]` (a bivariate polynomial pair, with the *outer* `Polynomial.X` playing the resultant variable and the *inner* `Polynomial.X` the specialization parameter `T`) and `t₀ : K`, set `F(T) := Res_X(f, g) ∈ K[T]`. Under the hypotheses

- `F(t₀) ≠ 0`,
- `f(X, t₀) := f.map (evalRingHom t₀)` splits over `K`,
- `g(x, t₀) ≠ 0` for every chord root `x` of `f(X, t₀)`,
- `f_X(x, t₀) ≠ 0` (the outer X-derivative; rules out double roots),

the formal logarithmic derivative of the resultant equals a multiset sum of per-chord-root contributions:

```
F'(t₀) / F(t₀) =
  Σ_{x ∈ f(X, t₀).roots}
    (g_T(x, t₀) · f_X(x, t₀) - g_X(x, t₀) · f_T(x, t₀)) /
    (f_X(x, t₀) · g(x, t₀))
```

where partial derivatives are encoded directly via `Polynomial.derivative` and `Polynomial.eval`:

- `f_X(x, t₀) := ((f.map (evalRingHom t₀)).derivative).eval x`,
- `f_T(x, t₀) := ((f.eval (C x)).derivative).eval t₀`,
- `g_X`, `g_T` analogously, and
- `g(x, t₀) := (g.map (evalRingHom t₀)).eval x`.

The numerator `g_T · f_X − g_X · f_T` is the standard implicit-function chain-rule combination for `d/dt [g(x(t), t)]` along a moving root `x(t)` defined by `f(x(t), t) = 0`.

## Citation

Lang, *Algebra* (3rd ed., GTM 211):

- **§VI.5 Theorem 5.1**, p. 285 — multiplicativity of the norm and the product-of-embeddings formula `N^E_k(α) = ∏_σ σα`.
- **§VIII.5 Theorem 5.1 Case 1**, p. 370 — a derivation extends uniquely to a separable algebraic extension via the implicit-function formula `ξ′ = -f^D(ξ)/f'(ξ)`.

The identity is the trace-of-log-derivative formula `Tr_{L/K}(dα/α) = d N_{L/K}(α) / N_{L/K}(α)` specialised to the bivariate resultant: `F = Res_X(f, g)` is the norm of `g` from the splitting field `L = K(T)[ξ_1, …, ξ_n]/(f)` down to `K(T)`, and the per-root sum is the trace of the log-derivative of `g` along the moving roots.

## Discharge plan

The mathlib infrastructure for mechanizing the discharge exists modulo plumbing:

1. **Splitting field.** Construct `L := Polynomial.SplittingField (f : K(T)[X])`; the chord roots `ξ_1, …, ξ_n ∈ L` lift the `K`-roots of `f(X, t₀)` after specialisation.

2. **Extension of derivation.** Use `Differential.deriv_aeval_eq_implicitDeriv` (in `Mathlib.RingTheory.Derivation.MapCoeffs`) to extend the formal `T`-derivation on `K[T]` to `L` via the implicit-function formula `ξ_i′ = -f^D(ξ_i)/f'(ξ_i)`. This is exactly Lang VIII.5 Theorem 5.1 Case 1, mechanised.

3. **Logarithmic derivative of a product.** In `L`, factor `F(T) = c · ∏_i g(ξ_i, T)` (a finite product). Apply `Differential.logDeriv_multisetProd` (in `Mathlib.FieldTheory.Differential.Basic`) to obtain `logDeriv F = Σ_i logDeriv (g(ξ_i, T))`.

4. **Specialisation.** Specialise both sides at `T = t₀`. The `K(T)`-roots `ξ_i` that are separable specialise to the chord roots in `K`, and the per-summand expression collapses to the stated chain-rule combination via direct calculation.

The bridge between `Polynomial.derivative` on `K[T]` (the formal-derivative function) and the `Differential` instance on the splitting field `L` is the only missing bit of mathlib infrastructure. Once added, this axiom becomes a theorem.

## Boundary status

This axiom is the citable *narrowing* of the previous project-shaped axiom `chord_fiber_product_logDeriv_eq_logDerivTerm_trace`. The chord-specific identity is now a theorem in `Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean`, derived from this axiom plus chord-cubic-specific algebra (computing `f_X`, `f_T`, `g_X`, `g_T`, `g_val` for `f := chordCubicBiv` and `g := DLineBiv` and matching to `logDerivTerm`).
