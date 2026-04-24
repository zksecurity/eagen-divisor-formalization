# `CoordRingElt.divisor_group_sum_zero`

- **Lean source**: `Divisor/BetaConstructive.lean:538`

```lean
axiom CoordRingElt.divisor_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0
```

Narrow form of Abel's theorem on `E`: under the splitting hypothesis, the `β`-weighted group sum of the geometric zeros of `D = a(x) − b(x)·y` vanishes in the group law.

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Corollary III.3.5 (⇒ direction)**, p. 63.

Same textbook location as `principal_divisor_iff`, but this axiom uses only the `(⇒)` direction (principal ⇒ group-sum-zero), specialised to the F_q-rational setting under the splitting hypothesis.

## Verbatim

> Corollary 3.5. Let E be an elliptic curve and let D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
>
> Σ_{P ∈ E} n_P = 0     and     Σ_{P ∈ E} [n_P] P = O.

## Snippet

![Silverman Cor III.3.5](snippets/silverman-cor-III.3.5-principal-divisor-081.png)

## Notes

The splitting hypothesis `normPoly_splits_over_Fq E D` is essential — without it, conjugate orbits `{P, P^φ}` in `E(F_{q^r}) \ E(F_q)` contribute to `Σ [n_P] P` sums that are F_q-rational but nonzero. Counterexample: on `E : y² = x³ + 1 / F_5` the line `y = 2x + 1` meets `E` at `P₃ = (0,1) ∈ E(F_5)` and a Frobenius-conjugate pair `P₁, P₂ ∈ E(F_{25}) \ E(F_5)`; Cor 3.5 gives `P₁ + P₂ + P₃ = O`, but the F_5-sum `β(P₃)·P₃ = (0,1) ≠ O`.

Splitting ensures every geometric zero of `D` on `E` is F_q-rational, so the F_q-sum matches the full `Σ [n_P] P` of Cor 3.5.
