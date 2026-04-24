# `hasse_weil`

- **Lean source**: `Divisor/Axioms.lean:104`

```lean
axiom hasse_weil :
  ((E.numPoints : ℤ) - E.q - 1)^2 ≤ 4 * E.q
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Theorem V.1.1 (Hasse)**, p. 138.

Supplementary: Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.), **Theorem 5.2.3 (Hasse–Weil Bound)**, p. 198 — the function-field generalisation for higher-genus curves.

## Verbatim

Silverman V.1.1:

> Theorem 1.1. (Hasse) Let E/F_q be an elliptic curve defined over a finite field. Then
>
> |#E(F_q) − q − 1| ≤ 2√q.

Stichtenoth 5.2.3:

> Theorem 5.2.3 (Hasse–Weil Bound). The number N = N(F) of places of F/F_q of degree one satisfies the inequality
>
> |N − (q + 1)| ≤ 2g·q^{1/2}.

## Snippets

![Silverman V.1.1](snippets/silverman-thm-V.1.1-hasse-155.png)

![Stichtenoth 5.2.3](snippets/stichtenoth-thm-5.2.3-hasse-weil-bound-209.png)

## Notes

The Lean statement is the integer-squared form `((#E − q − 1))² ≤ 4q`, equivalent to `|#E − q − 1| ≤ 2√q` for integers but sharper than `2·⌊√q⌋` (e.g. at `q = 7`, `2·⌊√7⌋ = 4` while `⌊2·√7⌋ = 5`).
