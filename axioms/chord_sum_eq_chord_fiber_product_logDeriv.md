# `chord_fiber_product_logDeriv_eq_logDerivTerm_trace`

- **Lean source**: `Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean`
- **Derived API theorem**: `chord_sum_eq_chord_fiber_product_logDeriv`

The trace-of-logarithmic-derivative identity

    Tr_{L/K}(dg/g) = d(N_{L/K}(g)) / N_{L/K}(g)

specialised to `g = D`, `K = F_q(z)`, `L = F_q(E)`, evaluated at the chord intercept `μ = zLambda λ A₀`.

## Boundary status

Both the project-specific statement `chord_sum_eq_chord_fiber_product_logDeriv` and the chord-specific intermediate `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` are now **theorems**, not axioms. They are derived from the strictly narrower generic axiom `Polynomial.resultant_logDeriv_at_split_specialization` (in `axioms/resultant_logDeriv_at_split.md`) plus chord-cubic-specific algebra:

1. The chord-specific identity is obtained by applying the generic resultant log-derivative formula with `f := chordCubicBiv E lam` and `g := DLineBiv E lam D`, then identifying each per-chord-root partial-derivative combination with `logDerivTerm` via direct chord-cubic-specific computation (the helper lemmas `chordCubicBiv_map_derivative_eval`, `chordCubicBiv_eval_C_derivative_eval`, `DLineBiv_map_derivative_eval`, `DLineBiv_eval_C_derivative_eval`, `DLineBiv_map_eval_at_root` in `Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean`).

2. The exported chord-vertex form `chord_sum_eq_chord_fiber_product_logDeriv` follows from the chord-specific identity by chord-cubic factorisation (`Sketch.intersectionPoly_factor_at_zLambda`, `Sketch.intersectionPoly_splits_at_zLambda`) plus the slope identity.

The citable boundary for the trace/log-derivative step is now `Polynomial.resultant_logDeriv_at_split_specialization`. The remaining formal work is to discharge that single axiom against mathlib's `Differential` / splitting-field infrastructure (see `axioms/resultant_logDeriv_at_split.md` for the discharge plan).

## Citation

Lang, *Algebra* (3rd ed., GTM 211):

- **§VI.5 Theorem 5.1**, p. 285 — multiplicativity of the norm + product-of-embeddings formula `N^E_k(α) = ∏_σ σα`.
- **§VIII.5 Theorem 5.1 Case 1**, p. 370 — a derivation extends uniquely to a separable algebraic extension.

The identity follows by differentiating `N_{L/K}(g) = ∏_σ σ(g)` over a Galois closure (using VI.5 for the product form, VIII.5 for extending the derivation).

## Verbatim

Lang §VI.5 (product-of-embeddings, p. 285):

> Thus if E is separable over k, we have
>
> N^E_k(α) = ∏ σα
>
> where the product is taken over the distinct embeddings of E in k^a over k. Similarly, if E/k is separable, then
>
> Tr(α) = Σ σα.

Lang §VI.5 Theorem 5.1 (p. 285):

> Theorem 5.1. Let E/k be a finite extension. Then the norm N^E_k is a multiplicative homomorphism of E* into k* and the trace is an additive homomorphism of E into k. If E ⊃ F ⊃ k is a tower of fields, then the two maps are transitive, in other words,
>
> N^E_k = N^F_k ∘ N^E_F   and   Tr^E_k = Tr^F_k ∘ Tr^E_F.
>
> If E = k(α), and f(X) = Irr(α, k, X) = X^n + a_{n−1} X^{n−1} + ⋯ + a_0, then
>
> N^E_k(α) = (−1)^n a_0   and   Tr^E_k(α) = −a_{n−1}.

Lang §VIII.5 Theorem 5.1 Case 1 (p. 370):

> Theorem 5.1. Let D be a derivation of a field K. Let (x) = (x_1, …, x_n) be a finite family of elements in an extension of K. Let {f_α(X)} be a set of generators for the ideal determined by (x) in K[X]. Then, if (u) is any set of elements of K(x) satisfying the equations
>
> 0 = f_α^D(x) + Σ (∂f_α/∂x_i) u_i,
>
> there is one and only one derivation D* of K(x) coinciding with D on K, and such that D* x_i = u_i for every i.
>
> Case 1. x is separable algebraic over K. Let f(X) be the irreducible polynomial satisfied by x over K. Then f′(x) ≠ 0. We have
>
> 0 = f^D(x) + f′(x) u,
>
> whence u = −f^D(x)/f′(x). Hence D extends to K(x) uniquely. If D is trivial on K, then D is trivial on K(x).

## Snippets

![Lang §VI.5 Thm 5.1](snippets/lang-VI.5-thm-5.1-norm-trace-300.png)

![Lang §VIII.5 Thm 5.1](snippets/lang-VIII.5-thm-5.1-derivations-385.png)
