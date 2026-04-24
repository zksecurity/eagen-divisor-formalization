# `principal_divisor_iff`

- **Lean source**: `Divisor/Axioms.lean:57`

```lean
axiom principal_divisor_iff
    (coeffs : ECPoint E.q → ℤ)
    (hFinSupp : Set.Finite (Function.support coeffs)) :
    IsPrincipal E coeffs ↔
      (∑ P ∈ hFinSupp.toFinset, coeffs P = 0) ∧
      (ECPoint.weightedSum E hFinSupp.toFinset
          (fun P => ECPoint.zsmul E (coeffs P) P) = 0)
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Corollary III.3.5**, p. 63.

Silverman's proof derives the Corollary from Proposition III.3.4(a,e) — the Abel–Jacobi isomorphism `σ : Pic⁰(E) ≅ E`.

## Verbatim

> Corollary 3.5. Let E be an elliptic curve and let D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
>
> Σ_{P ∈ E} n_P = 0     and     Σ_{P ∈ E} [n_P] P = O.
>
> (Note that the first sum is of integers, while the second is addition on E.)

## Snippet

![Silverman Cor III.3.5](snippets/silverman-cor-III.3.5-principal-divisor-081.png)

## Notes

Silverman states Cor III.3.5 over `E(K̄)`. The Lean form restricts to `ECPoint E.q` (F_q-rational points). F_q-descent follows from Remark III.3.5.1 + Exercise II.2.13(b) (G_{K̄/K}-invariance of the Abel–Jacobi sequence).
