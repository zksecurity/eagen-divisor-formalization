# `CoordRingElt.divisorClass_isPrincipal`

- **Lean source**: `Divisor/OrdP/LocalRing.lean`

```lean
axiom CoordRingElt.divisorClass_isPrincipal
    (D : CoordRingElt E.q) (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hSplit : splitsOnE E D) :
    ∃ I : (FractionalIdeal (nonZeroDivisors E.toW.toAffine.CoordinateRing)
              (FractionRing E.toW.toAffine.CoordinateRing))ˣ,
      (I : Submodule E.toW.toAffine.CoordinateRing
            (FractionRing E.toW.toAffine.CoordinateRing)).IsPrincipal ∧
      Additive.toMul
        (divisorClass E (divisorOfD E D)
          (divisorOfD_finiteSupport E D)) =
      ClassGroup.mk I
```

This is the remaining function-field bridge behind the proved theorem
`CoordRingElt.exists_divisor_multiplicity`.

It says that the concrete divisor attached to the regular function
`D = a - b*y`,

```text
sum_P ord_P(D) * (P) - natDegree(normPoly E D) * (infinity),
```

is represented in mathlib's class group by a principal fractional
ideal, once `splitsOnE E D` ensures all relevant geometric divisor
mass is visible over `F_q`.

## Why this is the current boundary

The old bridge axiom was the already-unwrapped statement
`ordAt_divisorClass_zero`. That statement is now a theorem: Lean gets
it from this axiom using mathlib's `ClassGroup.mk_eq_one_iff`.

This is still not the final trust boundary, but it is closer to the
standard algebraic statement. The remaining mathematical work is to
identify the project's explicit `ordAt` divisor with the principal
divisor of the coordinate-ring element `D`.

Pinned closure:

```lean
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity
-- propext, Classical.choice, Quot.sound,
-- Divisor.CoordRingElt.divisorClass_isPrincipal
```

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106):

* **II §1**: local orders at smooth points;
* **Corollary III.3.5**: principal divisors and weighted group sums.

Mathlib supplies the class-group interface used by the derivation:

* `ClassGroup.mk_eq_one_iff`;
* `WeierstrassCurve.Affine.Point.toClass`;
* `WeierstrassCurve.Affine.Point.toClass_eq_zero`.

## Discharge target

To remove this axiom, prove that `divisorOfD E D` is the divisor class
of the rational function represented by `D` in the coordinate ring. The
concrete proof obligations are:

1. identify the project `ordAt E D P` with the local valuation of `D`
   at each affine smooth point `P`;
2. identify the pole order at infinity with `natDegree(normPoly E D)`;
3. use the standard class-group fact that a principal fractional ideal
   has trivial class.

The first item is the main formalisation work; the rest should be
bookkeeping once the local-order compatibility theorem exists.
