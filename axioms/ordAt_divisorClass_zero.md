# `ordAt_divisorClass_zero` (derived theorem)

- **Lean source**: `Divisor/OrdP/LocalRing.lean`

```lean
theorem ordAt_divisorClass_zero
    (D : CoordRingElt E.q) (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hSplit : splitsOnE E D)
    (hFinSup : Set.Finite (Function.support (divisorOfD E D))) :
    divisorClass E (divisorOfD E D) hFinSup = 0
```

This was formerly the remaining function-field bridge behind the
proved theorem `CoordRingElt.exists_divisor_multiplicity`. It is now a
theorem derived from the narrower principal fractional-ideal axiom
`CoordRingElt.divisorClass_isPrincipal`.

It says that the concrete divisor attached to the regular function
`D = a - b*y`,

```text
sum_P ord_P(D) * (P) - natDegree(normPoly E D) * (infinity),
```

has trivial class in mathlib's elliptic-curve class group, once
`splitsOnE E D` ensures all relevant geometric divisor mass is visible
over `F_q`.

## Why this axiom is narrower

The previous MA extraction path used two facts:

1. `ordAt_divisor_isPrincipal : IsPrincipal E (divisorOfD E D)`;
2. `principal_divisor_iff.mp` to extract group-sum-zero from
   principalness.

The code now avoids the opaque `IsPrincipal` layer.  The file
`Divisor/OrdP/PrincipalClass.lean` proves, using mathlib's
`WeierstrassCurve.Affine.Point.toClass` API, that
`divisorClass E coeffs h = 0` implies the weighted elliptic-curve group
sum is zero.  Therefore the MA extraction path needs only the zero
class of this specific divisor, not the full principal-divisor
biconditional.

Pinned closure now names the underlying axiom:

```lean
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity
-- propext, Classical.choice, Quot.sound,
-- Divisor.CoordRingElt.divisorClass_isPrincipal_of_not_const_unit
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106):

* **§II.1**: local orders at smooth points;
* **Corollary III.3.5**: a degree-zero divisor on an elliptic curve is
  principal exactly when its weighted group sum is zero.

Mathlib supplies the class-group interface used by the replacement:

* `WeierstrassCurve.Affine.Point.toClass`;
* `WeierstrassCurve.Affine.Point.toClass_eq_zero`.

## Snippets

![Silverman II.3 divisors](snippets/silverman-II.3-divisors-027.png)

![Silverman II.3 principal divisors](snippets/silverman-II.3-principal-divisors-028.png)

![Silverman Cor III.3.5](snippets/silverman-cor-III.3.5-principal-divisor-081.png)

## Discharge target

To remove this axiom, prove that `divisorOfD E D` is the divisor class
of the rational function represented by `D` in the coordinate ring.
The concrete proof obligations are:

1. identify the project `ordAt E D P` with the local valuation of `D`
   at each affine smooth point `P`;
2. identify the pole order at infinity with `natDegree(normPoly E D)`;
3. use the standard class-group fact that a principal divisor has
   trivial class.

The first item is the main formalisation work; the rest should be
bookkeeping once the local-order compatibility theorem exists.
