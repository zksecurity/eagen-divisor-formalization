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

The current MA/IP closure has moved the trace/log-derivative step away
from a chord-specific axiom, but it has not yet reached the final
boundary:

- The trace/log-derivative step is now a generic, chord-agnostic
  axiom `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree`
  about the logarithmic derivative of `Res_X(f, g)` at a split
  inner-specialisation of `f`. The axiom carries an explicit
  `Monic f` hypothesis (added after a code review caught that the
  non-monic case picks up an extra `d/dT log(lc(f)^{deg g})` term per
  mathlib's `Polynomial.resultant_eq_prod_eval`) and a `0 < f.natDegree`
  hypothesis (the trivial degree-zero case is now a theorem). The
  project caller `chordCubicBiv` is monic of degree 3. This is a
  useful intermediate bridge, not the final trust boundary. The final target is to prove it from the
  Galois norm/trace/log-derivative theorem
  `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
  (already proved from mathlib) plus resultant and specialisation
  algebra. The chord-specific identity
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` is now a
  *theorem* derived from this axiom plus chord-cubic-specific
  algebra (computing `f_X`, `f_T`, `g_X`, `g_T`, `g_val` for
  `f := chordCubicBiv` and `g := DLineBiv`). The older
  coordinate-heavy `chord_sum_eq_chord_fiber_product_logDeriv`
  statement is also a theorem, derived in turn from the
  chord-specific identity by chord-cubic factorisation. See
  `axioms/resultant_logDeriv_at_split.md` for the discharge plan.

The remaining bridges are:

- `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image`,
  the coefficientwise norm/divisor push-forward statement for the
  concrete resultant, *narrowed to the in-image case* (off-image
  multiplicity = 0 is now a theorem). This is narrow and citable, but
  still coordinate-level.
- `CoordRingElt.divisorClass_isPrincipal_of_not_const_unit`, the
  concrete principal-class bridge for the divisor of `D`, *narrowed
  to the non-constant-unit case* (constant-unit case is now a
  theorem). The unrestricted form is a re-exported theorem.

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

## Reusable plumbing

`Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`
(`Divisor/PartialFractionExpansion.lean`) is a generic squeeze lemma
that converts a multiplicity equality into a fibrewise divisibility
plus a global degree bound. It is the cleanest landing target for a
future divisibility-based discharge of axiom 1: replace the equality
axiom by a divisibility axiom (the local divisor-of-norm content), add
a `chord_fiber_product` natDegree bound (mathlib's resultant-degree
machinery applied to the Sylvester matrix of `chordCubicBiv` and
`DLineBiv`), and apply the helper to recover the equality form. The
helper itself is purely polynomial and unused today; it is recorded
for that future refactor.
