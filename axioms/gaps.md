# Textbook Alignment Gap Plan

This file tracks the gap between the current Lean axiom surface and the
textbook statements cited for that surface. A "gap" here does not mean a
Lean `sorry`. It means that the Lean declaration is a project-shaped
specialization of a cited theorem, and the missing work is the bridge
from the textbook theorem to the exact Lean statement.

The headline MA soundness and completeness theorems have no `sorryAx` in
their pinned closure, but they still depend on named project axioms. The
goal of this plan is to replace those project-shaped axioms with theorems
derived from textbook-shaped declarations or from mathlib.

## Current Headline Closure

The closure is pinned by:

```sh
lake env lean Tests/AxiomClosurePin.lean
```

As of 2026-05-14:

| Theorem family | Project axioms in closure |
|---|---|
| `Divisor.ma_extractable`, `Divisor.ip_knowledge_sound` | `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`, `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`, `Divisor.hasse_weil_textbook`, `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero` |
| `Divisor.ma_completeness` | `Divisor.chord_fiber_product_eq_normZ_under_split`, `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g` |
| `Divisor.ma_completeness_clean` | `Divisor.chord_fiber_product_eq_normZ_under_split`, `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`, `Divisor.hasse_weil_textbook` |

## Axioms In Scope

### Headline Dependencies

| Lean declaration | Textbook source | Bridge to close |
|---|---|---|
| `Divisor.hasse_weil_textbook` | Silverman AEC V.1.1; Stichtenoth 5.2.3 | Closed: the axiom now states the textbook absolute-value/sqrt bound verbatim. The legacy integer-squared `Divisor.hasse_weil` is a derived theorem. |
| `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero` | Silverman II.3, Silverman III.3.5, Stichtenoth 1.4.2 | Identify the project divisor `divisorOfD E D`, built from `ordAt`, with the principal divisor of the coordinate-ring element `D = a(x) - b(x)y`, then map it to the affine class-group zero statement. |
| `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd` | Stacks tag 02RS; Stichtenoth 3.1.9 | Instantiate norm pushforward for the chord projection and identify pushed-forward local multiplicities with divisibility of the concrete resultant over `Fqbar E`. |
| `Divisor.chord_fiber_product_eq_normZ_under_split` | Stacks tag 02RS; Stichtenoth 3.1.9 and 3.1.11 | Under `splitsOnE` and `betaTrue` accounting, identify `chord_fiber_product` and `normZ` as the same norm divisor up to a nonzero scalar over `ZMod E.q`. |
| `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g` | Lang IV.8, VI.5, VIII.5 | Build the splitting-field/differential setup, identify `Res_X(f,g)` with a norm, apply trace-of-log-derivative, and specialize at `t0`. |

### Full Alignment Surface

Every remaining project `axiom` is now a headline-closure dependency
(see the table above). The previously listed off-closure axioms
`Divisor.principal_divisor_iff`, `Divisor.weil_reciprocity_textbook`,
and `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv` have
been **deleted** — they were not used by any proof. The finite-separable
log-derivative fact remains available in its theorem-backed Galois form
`Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`.

Note: `Divisor.weil_reciprocity_textbook` was found to be **false** as
stated (it omits multiplicities and the point at infinity); it was
removed rather than retained as a target.

| Lean declaration | Status |
|---|---|
| `Divisor.IsPrincipal` | Opaque predicate, not an axiom. Alignment requires either replacing it with a concrete divisor-of-function predicate or proving every use through a concrete bridge. |

## Execution Order

### Phase 0: Ledger and Guardrails

Status: in progress.

Deliverables:

- Restore this file as the single bridge-gap ledger.
- Link it from `README.md`.
- Keep `Tests/AxiomClosurePin.lean` as the mechanical guardrail.
- Record every closure-changing edit by running:

```sh
lake env lean Tests/AxiomClosurePin.lean
```

### Phase 1: Hasse-Weil Boundary

Status: completed.

- The closure axiom is now `Divisor.hasse_weil_textbook`, stating the
  textbook absolute-value/sqrt bound verbatim.
- The legacy `Divisor.hasse_weil` (integer-squared form) is a derived
  theorem retained for downstream compatibility.
- Closure documentation in `README.md`, `axioms/gaps.md`, and
  `Tests/AxiomClosurePin.lean` reflects the renamed axiom.

Verification (pinned closure):

```sh
lake build Divisor.Axioms.AxiomHasseWeil Tests.AxiomClosurePin
```

### Phase 2: Resultant Log-Derivative Bridge

Status: not started.

Why second: it is algebraic and relatively self-contained compared with
the divisor/class-group and chord-pushforward work. It also affects both
soundness and completeness.

Tasks:

1. Keep the already proved trivial cases:
   `f.natDegree = 0`, `f.natDegree = 1`, and `g.natDegree = 0`.
2. Prove or isolate the theorem identifying the bivariate resultant with
   an algebra norm over the quotient/splitting field.
3. Connect `Polynomial.derivative` on `K[T]` with the `Differential`
   typeclass instance.
4. Apply `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`.
5. Specialize at `t0` and rewrite the trace sum into the current
   `resultantLogDerivConclusion`.

Primary files:

- `Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean`
- `Divisor/Axioms/AxiomTraceLogDeriv.lean`
- `Divisor/PolynomialDifferential.lean`

Verification:

```sh
lake env lean Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean
lake env lean Tests/AxiomClosurePin.lean
```

### Phase 3: Principal Divisor/Class-Group Bridge

Status: not started.

Why third: it removes the soundness-side Abel-Jacobi/class-group bridge,
but it touches local-order and coordinate-ring infrastructure.

Tasks:

1. Define or identify the concrete rational function represented by
   `D : CoordRingElt E.q`.
2. Prove that `divisorOfD E D` agrees pointwise with the principal
   divisor of that rational function.
3. Bridge the divisor to mathlib's affine coordinate-ring class group.
4. Replace `CoordRingElt.divisorClass_eq_zero_of_b_ne_zero` with a theorem.
5. Decide whether `IsPrincipal` remains opaque only as documentation or
   becomes a concrete predicate.

Primary files:

- `Divisor/OrdP/LocalRing.lean`
- `Divisor/CoordinateRingBridge.lean`

Verification:

```sh
lake env lean Divisor/OrdP/LocalRing.lean
lake env lean Tests/AxiomClosurePin.lean
```

### Phase 4: Chord Projection Norm Pushforward

Status: not started.

Why fourth: this is the largest geometry/function-field block. It should
reuse the principal-divisor bridge from Phase 3.

Tasks:

1. Formalize the chord projection `pi_lam : E -> P1`.
2. Identify `chord_fiber_product_concrete E lam D` as the norm/resultant
   of `D` along `pi_lam`.
3. Prove the divisor pushforward identity in this concrete setting.
4. Translate pushforward multiplicities into the divisibility statement:
   `(X - C z) ^ fiber_sum | chord_fiber_product_concrete.map ...`.
5. Use the existing weighted-Sylvester upper bound to recover
   multiplicity equality where needed.

Primary files:

- `Divisor/Axioms/AxiomChordFiberDivisibility.lean`
- `Divisor/ChordFiberProductConcrete.lean`
- `Divisor/ChordFiberWeightedDegree.lean`
- `Divisor/GeomLocalOrder.lean`

Verification:

```sh
lake env lean Divisor/Axioms/AxiomChordFiberDivisibility.lean
lake env lean Tests/AxiomClosurePin.lean
```

### Phase 5: Split `normZ` Proportionality

Status: not started.

Why after Phase 4: this is the split/rational specialization of the same
norm pushforward story, with additional `betaTrue` accounting and descent
from `Fqbar E` to `ZMod E.q`.

Tasks:

1. Prove the bar-level proportionality from geometric factorization.
2. Use `hbetaTrue` to rule out wrong pointwise multiplicity
   distributions.
3. Descend the nonzero scalar from `Fqbar E` to `ZMod E.q` using leading
   coefficients and injectivity of `Polynomial.map`.
4. Replace `chord_fiber_product_eq_normZ_under_split` with a theorem.

Primary files:

- `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`
- `Divisor/Sketch/ChordFiberProductConcrete.lean`
- `Divisor/FunctionFieldZ.lean`
- `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`

Verification:

```sh
lake env lean Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean
lake env lean Tests/AxiomClosurePin.lean
```

### Phase 6: Weil Reciprocity Alignment

Status: closed by deletion.

The `Divisor.weil_reciprocity_textbook` axiom was found to be **false**
as stated — the finite zero-product specialization omits multiplicities
(`ord_P`) and the point at infinity. A concrete counterexample exists
(`E : y^2 = x^3 + 1` over `F_5`, `f = x - 2`, `g = y`). Because the
axiom was not used by any proof (only referenced in comments), it was
deleted rather than realigned. A correct multiplicity-weighted
restatement remains future work if full protocol-level reciprocity is
needed; `Divisor/WeilReciprocityDescent.lean` still carries a `sorry`
in `weil_residue_identity` that would consume such a statement.

## Completion Criteria

The plan is complete when:

1. `Tests/AxiomClosurePin.lean` shows no project-shaped bridge axioms in
   the MA soundness/completeness closures.
2. Any remaining project axioms are textbook-shaped statements whose
   Lean statements directly match the cited theorem, up to routine
   notation.
3. Every old project-shaped axiom is either deleted or retained only as
   a theorem-backed compatibility name.
4. The README and this file agree with the output of:

```sh
lake env lean Tests/AxiomClosurePin.lean
```
