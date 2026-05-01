# Axiom Boundary Target

This branch currently proves the MA extraction theorem with a narrow,
sound axiom closure, but not yet with the final trust boundary we want.

The final standard is:

1. axioms should be simple textbook theorems;
2. theorem statements should not mention project-specific proof
   plumbing unless that plumbing is unavoidable;
3. coordinate-heavy protocol identities should be Lean theorems derived
   from those textbook axioms plus project algebra.

## Acceptable Shape

`hasse_weil` is the model: it states one standard theorem in a familiar
form, has a direct textbook citation, and does not expose proof
internals.

The same shape is acceptable for:

- the Hasse-Weil bound;
- a residue theorem or Weil reciprocity theorem;
- the divisor class of a principal divisor being zero;
- a norm/divisor push-forward theorem for finite separable function
  field extensions;
- a trace/logarithmic-derivative theorem
  `Tr(dg/g) = d(N(g))/N(g)`.

## Temporary Bridge Axioms

The current chord axioms are mathematically standard consequences, but
their Lean statements are too proof-specific to be the final trust
boundary:

- `chord_sum_eq_chord_fiber_product_logDeriv` combines the abstract
  trace/log-derivative theorem with the project-specific chord
  parameterization, `logDerivTerm`, explicit third-intersection
  coordinates, and denominator side conditions.
- `chord_fiber_product_eq_normZ_under_split` combines the
  divisor-of-norm theorem with the old rational `normZ` encoding and
  `splitsOnE` accounting.
- `chord_fiber_product_bar_eq_geom_prod` is better because it is
  geometric and avoids `splitsOnE`, but it still states the final
  factorization of the project-specific opaque
  `chord_fiber_product`.

These should be treated as bridge lemmas waiting to be proved or
re-expressed from simpler axioms, not as final assumptions.

## Target Refactor

The intended replacement is:

1. Define or expose the finite separable extension
   `F_qbar(E) / F_qbar(zLambdaBar lam)` at the level needed by the
   proof.
2. State one clean norm/divisor axiom, or use mathlib if available:
   the divisor of a norm is the push-forward of the divisor.
3. State one clean trace/log-derivative axiom, or use mathlib if
   available:
   `Tr(dg/g) = d(N(g))/N(g)` for a finite separable extension with
   nonzero denominator at the evaluation place.
4. Prove the current chord-specific statements as coordinate
   consequences:
   chord fibers are the three intersections with the line, the
   `logDerivTerm` formula is the derivative of `D` along the chord, and
   the geometric product descends to the concrete polynomial used in
   the SZ argument.

Until those steps land, the axiom closure is sound but not yet in the
desired "all axioms are simple and natural" form.
