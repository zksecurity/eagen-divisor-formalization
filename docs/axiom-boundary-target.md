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

## Current Remaining Bridges

The current MA/IP closure has already moved the trace/log-derivative
step to the desired citable shape:

- The trace/log-derivative step is now a generic (chord-agnostic)
  axiom `Polynomial.resultant_logDeriv_at_split_specialization`
  about the logarithmic derivative of `Res_X(f, g)` at a split
  inner-specialisation of `f`. The chord-specific identity
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` is now a
  *theorem* derived from this axiom plus chord-cubic-specific
  algebra (computing `f_X`, `f_T`, `g_X`, `g_T`, `g_val` for
  `f := chordCubicBiv` and `g := DLineBiv`). The older
  coordinate-heavy `chord_sum_eq_chord_fiber_product_logDeriv`
  statement is also a theorem, derived in turn from the
  chord-specific identity by chord-cubic factorisation. See
  `axioms/resultant_logDeriv_at_split.md` for the citable boundary
  and discharge plan.

The remaining bridges are:

- `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber`, the
  coefficientwise norm/divisor push-forward statement for the concrete
  resultant. This is narrow and citable, but still coordinate-level.
- `ordAt_eq_rationalMultAt_of_gd_support_rational`, local-order
  compatibility between the affine `ordAt` definition and the geometric
  multiplicity data after rational support descent.
- `CoordRingElt.divisorClass_isPrincipal`, the concrete principal-class
  bridge for the divisor of `D`.

The legacy rational bridge `chord_fiber_product_eq_normZ_under_split`
still exists for the off-path rational tight-bound chain, but it is no
longer in the MA/IP closure and now explicitly requires
`β_fun = betaTrue` pointwise.

## Target Refactor

The intended replacement is:

1. Define or expose the finite separable extension
   `F_qbar(E) / F_qbar(zLambdaBar lam)` at the level needed by the
   proof.
2. State one clean norm/divisor axiom, or use mathlib if available:
   the divisor of a norm is the push-forward of the divisor.
3. Replace the local-order compatibility and concrete principal-class
   bridge by the corresponding local-ring/function-field theorems when
   that infrastructure is available.
4. Prove the remaining chord-specific statements as coordinate
   consequences:
   chord fibers are the three intersections with the line, the
   `logDerivTerm` formula is the derivative of `D` along the chord, and
   the geometric product descends to the concrete polynomial used in
   the SZ argument.

Until those steps land, the axiom closure is sound and narrow, but not
yet entirely reduced to textbook-shaped infrastructure theorems.
