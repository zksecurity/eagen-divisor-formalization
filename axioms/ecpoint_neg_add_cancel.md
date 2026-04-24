# `ECPoint.neg_add_cancel`

- **Lean source**: `Divisor/Defs.lean:214`

```lean
axiom ECPoint.neg_add_cancel (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.add E (-p) p = (0 : ECPoint E.q)
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Proposition III.2.2(d)**, p. 51.

## Verbatim

> Proposition 2.2. The composition law (III.2.1) has the following properties:
> …
> (d) Let P ∈ E. There is a point of E, denoted by ⊖P, satisfying P ⊕ (⊖P) = O.

## Snippet

![Silverman Prop III.2.2](snippets/silverman-prop-III.2.2-group-law-069.png)

## Notes

Follows from the chord-and-tangent definition: the vertical line through `P = (x, y)` and `-P = (x, -y)` meets `E` a third time at `∞`, so `P ⊕ (⊖P) = ⊖∞ = O`. Axiomatised to avoid a case split on `P = -P` (2-torsion, `y = 0`) matching the `thirdPoint` branches.
