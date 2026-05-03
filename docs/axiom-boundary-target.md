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

The branch added several pieces of project-side infrastructure that the
future axiom-1 discharge can build on:

1. `Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`
   (`Divisor/PartialFractionExpansion.lean`) — generic squeeze lemma
   that converts a multiplicity equality into a fibrewise divisibility
   plus a global degree bound.

2. `Divisor.GeometricDivisorData.mult_sum_eq_normPoly_natDegree`
   (`Divisor/GeomLocalOrder.lean`) — exact equality form of the
   X-fibre degree accounting: `∑ Q ∈ gd.support, gd.mult Q = (normPoly E D).natDegree`.
   This identifies the `∑ gd.mult` total appearing in the squeeze
   helper's degree-bound hypothesis with a concrete polynomial natDegree.

3. **`Divisor/ChordFiberMultiplicativity.lean`** (new module) — the
   inductive structure for `divLin`-based natDegree induction. Both
   linear-factor (`X − C x₀`) and arbitrary-monic-factor versions of:
   - DLineBiv multiplicativity (`DLineBiv_eq_X_sub_C_mul_divLin`,
     `DLineBiv_eq_C_mul_divByMonic`).
   - chord_fiber_product multiplicativity
     (`chord_fiber_product_concrete_eq_resXSubC_mul_of_div`,
     `chord_fiber_product_concrete_eq_resPmap_mul_of_div`).
   - normPoly recurrences
     (`normPoly_eq_X_sub_C_sq_mul_of_div`,
     `normPoly_eq_p_sq_mul_of_div`).
   - natDegree inductive steps
     (`chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step`,
     `_step_general`); plus streamlined wrappers (`_step'`,
     `_step_general'`) that take only the project-standard
     non-degeneracy hypothesis `¬ (D'.a = 0 ∧ D'.b = 0)` and derive
     the DLineBiv/chord_fiber_product non-vanishing internally via
     `DLineBiv_ne_zero` and the existing
     `chord_fiber_product_concrete_ne_zero`.

   Closed-form natDegree theorems for special `p` (resolving the
   resultant natDegree formula
   `Res(chordCubic, p.map C, 3, p.natDegree).natDegree = 2 · p.natDegree`):
   - `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_one` — `p = 1`.
   - `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C` — `p = X − C x₀`.
   - `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C_pow` — `p = (X − C x₀)^k`.
   - `resultant_chordCubicBiv_pmap_C_natDegree_of_splits` — any monic `p`
     splitting over `ZMod E.q` (multiset induction on `p.roots`).
   - `resultant_chordCubicBiv_pmap_C_natDegree_of_monic` — any monic `p`
     (no splits hypothesis), via lifting along
     `K = SplittingField p`, applying the splits-generic theorem over
     `K`, then descending the natDegree along `Polynomial.resultant_map_map`
     plus `Polynomial.natDegree_map_eq_of_injective`.

   Inductive-step combinators for the natDegree-equality recurrence:
   - `_step_X_sub_C_pow` — composes `(X − C x₀)^k` natDegree with the
     general-monic step.
   - `_step_splits` — composes the general splits-over-ZMod-q natDegree
     with the general-monic step.
   - `_step_monic` — composes the general-monic (no splits) natDegree
     with the general-monic step. This is the no-hypothesis form
     needed for the gcd-extraction induction.
   - `chord_fiber_product_concrete_natDegree_le_normPoly_natDegree_step_monic`
     — the `≤` (inequality) form of `_step_monic`. Uses
     `Polynomial.natDegree_mul_le` instead of `natDegree_mul`, which
     avoids the resultant-non-vanishing side-conditions the equality
     form needs. This is the form the squeeze helper consumes; it
     reduces the bound `(chord_fiber_product D).natDegree ≤
     (normPoly D).natDegree` to the same statement on `D'` after
     extracting any monic common divisor of `D.a, D.b`.

   The linear case includes the resultant-against-linear-factor
   natDegree calculation
   (`resultant_chordCubicBiv_X_sub_C_natDegree`), proven via
   `compute_degree!` on the explicit
   `chordCubicBiv.eval (C x₀) = -T² + …` form.

4. `Divisor/Sketch/ChordFiberProductConcrete.lean` —
   `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_via_squeeze`
   shows the discharge architecture as code: two stubs (a fibrewise
   divisibility + a degree comparison) plus the squeeze helper give
   the multiplicity equality. The two stubs are precisely the
   substantive content remaining:

   - `chord_fiber_product_concrete_bar_zfiber_pow_dvd` — local
     divisor-of-norm content (genuine math, splitting field route
     or local intersection theory).
   - `chord_fiber_product_concrete_bar_natDegree_le_normPoly` — degree
     comparison between two norm polynomials. Stacks Project Lemma
     [42.18.1 (Principal divisors and pushforward)](https://stacks.math.columbia.edu/tag/02RS)
     gives the underlying theorem; in Lean the natural routes are
     either to axiomatise the general norm/divisor pushforward (a
     textbook-shape replacement for axiom 1) or to prove it via a
     weighted-leading-term Sylvester analysis with `wt(T) = 3`,
     `wt(X) = 2`. The arbitrary-monic resultant natDegree formula
     `Res(chordCubic, p.map C, 3, p.natDegree).natDegree = 2 · p.natDegree`
     is now a *theorem*
     (`resultant_chordCubicBiv_pmap_C_natDegree_of_monic`) via the
     splitting-field lift, so the inductive `_step_monic` combinator
     can compose all of D's `divLin`-recursive steps. The remaining
     gap is the **base case** (`gcd(D.a, D.b) = 1`) of the natDegree
     inequality, which the inductive structure cannot reduce further.

     **Recommended Lean route for the gcd-1 base case** (no deep
     function-field machinery): direct weighted-Sylvester degree
     bound. Assign weights `wt(x) = 2`, `wt(Z) = 3`. Then in
     `(ZMod E.q)[Z][x]`:
     - `wt(chordCubicBiv) = 6` (matched by both `x³` and `Z²`).
     - `wt(DLineBiv) = w` where, in the coprime / not-both-zero case,
       `w = max(2·D.a.natDegree, 2·D.b.natDegree + 3) =
        (normPoly E D).natDegree`.
     The Sylvester matrix `S(chordCubic, DLineBiv)` is square. By
     `Matrix.det_apply`, `det(S)` is a sum of products; each product
     selects 3 entries of weight ≤ 6 (chord-cubic rows) and `n` entries
     of weight ≤ w (DLine rows), where `n = deg_x DLineBiv`. The
     selected x-degrees sum to `3·n`, and the weight identity gives
     `3·degZ(term) ≤ 6n + 3w − 2·(3n) = 3w`, i.e. `degZ(term) ≤ w`.
     Then `natDegree_sum_le` and `natDegree_prod_le` close the bound.
     This stays coordinate-native and uses only mathlib's matrix /
     polynomial degree lemmas, avoiding any norm/divisor pushforward
     theorem.
