# `ECPoint.add_assoc`

- **Lean source**: `Divisor/Defs.lean:202`

```lean
axiom ECPoint.add_assoc (E : ECSetup) (p q r : ECPoint E.q) :
    ECPoint.add E (ECPoint.add E p q) r = ECPoint.add E p (ECPoint.add E q r)
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Proposition III.2.2(e)**, p. 51.

Silverman's proof (p. 59–61) goes via **Proposition III.3.4(e)**: the Abel–Jacobi map `σ : Pic⁰(E) → E` is a group isomorphism, reducing associativity of `⊕` to associativity in `Pic⁰(E)`.

## Verbatim

> Proposition 2.2. The composition law (III.2.1) has the following properties:
> …
> (e) Let P, Q, R ∈ E. Then (P ⊕ Q) ⊕ R = P ⊕ (Q ⊕ R).

## Snippet

![Silverman Prop III.2.2](snippets/silverman-prop-III.2.2-group-law-069.png)

## Notes

The nontrivial group-law axiom. A direct proof by cases on the chord-and-tangent construction requires matching nine sub-cases against `thirdPoint`'s branches; formalising via Riemann–Roch/divisor classes is the standard textbook route but far beyond the current surface.
