# divisors

Lean 4 mechanization of an elliptic-curve-based dlog knowledge-sound IP.

## Build

```
lake build
```

Requires elan + Lean 4 toolchain (see `lean-toolchain`).

## Theorem surface

The headline theorems live in `Divisor/ExtractorBridgeTheorems.lean` and `Divisor/Soundness.lean`:

- `Divisor.ma_extractable` — knowledge soundness of the MA protocol.
- `Divisor.ip_knowledge_sound` — knowledge soundness of the IP protocol.
- `Divisor.ma_completeness` — completeness of the MA protocol.

### `Divisor.ma_extractable` (MA knowledge soundness)

Fix a statement `stmt` over the finite field `F_q`: bases `B_1, ..., B_k` in `E(F_q)`, a target `T` in `E(F_q)`, and a degree bound `d`. Fix a prover first-round message `msg` encoding a divisor representative `D = a(x) - b(x) y` in `F_q[E]` together with scalars `m_1, ..., m_k`, such that the `E`-degree of `D` is at most `d`.

**Hypotheses** (`Divisor/ExtractorBridgeTheorems.lean`):

- smoothness of `E`: `4 a_E^3 + 27 b_E^2 ≠ 0`
- denominator non-vanishing on `A_0` outside `zerosFinset(D)` and avoiding `distinctR`
- size condition on the number of points of `E`:

$$|E(F_q)| > 2\bigl(5(\deg_E D + k + 2) + 3\bigr) + 21(\deg_E D + k + 2) + 72.$$

**Conclusion.** One of the two branches holds.

1. *Witness branch.* There exists a witness `w` such that `maExtractor(stmt, msg) = some w` and

$$T = \sum_{i=1}^{k} [n_i]\, B_i \qquad \text{in } E(F_q),$$

where `n_i = w.scalars(i)` in `Z` with `|n_i| < d`.

2. *Small-accept-set branch.* The set of challenges `(A_0, A_1)` in `validPairs` on which the verifier accepts has cardinality at most `B(d, k, q)`, where

$$B(d, k, q) = 18(d+k)q + (3d+9k+71)|E(F_q)|.$$

The active soundness path uses the geometric-zero skeleton in
`Divisor/GeometricSoundness.lean`: zeros of `D` are represented over
`F_qbar`, the cleared numerator is required to descend to `F_q`, and
the headline theorem no longer assumes `splitsOnE E D`. The shared
base-change model is factored into `Divisor/GeomBase.lean`; the true
local-order/fiber-accounting obligation is isolated in
`Divisor/GeomLocalOrder.lean`.

### `Divisor.ip_knowledge_sound` (IP knowledge soundness)

The same disjunction as `ma_extractable`, conjoined with *uniqueness of the third-round response*: for every challenge and intercept `A_2` with `D` non-vanishing at `A_0, A_1, A_2` and the chord line `L(A_0, A_1)` non-vanishing at `-T`, any two third-round messages `msg3, msg3'` both accepted by the IP verifier must be equal.

### `Divisor.ma_completeness`

For an honest prover message `msg` witnessing `(stmt, wit)` with `degE(D) ≤ d` and `(a, b) ∈ admSet`, the rejecting-challenge set is bounded:

$$\bigl| \{ (A_0, A_1) \in E \times E : V \text{ rejects} \} \bigr| \le  (3N + 1) \cdot |E_{\mathrm{aff}}|,$$

where `N = numZeros(D)` and `E_aff` is the set of affine `F_q`-points of `E`. Proof uses Weil reciprocity plus Lemma 2 (`support_disjointness`).

## Axiom surface

`#print axioms Divisor.ma_extractable` (same for `Divisor.ip_knowledge_sound`):

```
propext, Classical.choice, Quot.sound,
Divisor.hasse_weil,
Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree,
Divisor.CoordRingElt.divisorClass_isPrincipal_of_not_const_unit
```

No `sorryAx`. Production paths build with no in-flight obligations.

`#print axioms Divisor.ma_completeness`:

```
propext, Classical.choice, Quot.sound,
Divisor.weil_reciprocity_honest
```

`#print axioms Divisor.ma_completeness_clean` adds:

```
Divisor.hasse_weil
```

The pinned closure is verified at `Tests/AxiomClosurePin.lean`; reading
the build log catches drift from the expected set.

### Textbook Axioms

#### `CoordRingElt.divisorClass_isPrincipal_of_not_const_unit` — Silverman AEC III Cor 3.5, p. 63 (Abel's theorem)

Principal-divisor class statement for the regular function `D = a - b·y`
on `E`, narrowed to the non-constant-unit case (constant-unit case
already a theorem). Says: under `splitsOnE E D`, the divisor class
attached to `D` in mathlib's class group is represented by some
principal fractional ideal.

This replaces the older direct `CoordRingElt.exists_divisor_multiplicity`
axiom (which is now a *theorem* derived from this principal-class
axiom via mathlib's `ClassGroup.mk_eq_one_iff` plus existing
geometric-data plumbing).

The axiom is intended to be discharged in Phase 1 of the trust-
closure plan by mechanising `ord_P` from local uniformizers
(Silverman II §1) and applying `principal_divisor_iff.mp` from
Cor 3.5.

#### `chord_fiber_product_concrete_bar_zfiber_pow_dvd` — Stacks Project [02RS](https://stacks.math.columbia.edu/tag/02RS) (lower bound)

Coefficientwise *divisibility* lower bound for the chord-projection
norm. For each chord-intercept `z`, the chord-fibre product has
multiplicity at least `Σ_{Q ∈ gd.support, π(Q) = z} gd.mult(Q)` at `z`.

Strict shape improvement: the previous chord-specific multiplicity-
*equality* axiom is now a derived theorem, since the matching upper
bound (the global natDegree inequality) is fully formalised via the
weighted-Sylvester proof in `Divisor/ChordFiberWeightedDegree.lean`:

```lean
theorem chord_fiber_product_concrete_natDegree_le_normPoly_natDegree
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (chord_fiber_product_concrete E lam D).natDegree
      ≤ (normPoly E D).natDegree
```

Squeeze argument (`rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`)
combines the divisibility axiom with the natDegree theorem to derive
multiplicity equality at every fibre. Detailed write-up in
`axioms/chord_fiber_product_concrete_bar_zfiber_pow_dvd.md`.

#### `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree` — Lang *Algebra* §VI.5 + §VIII.5

Logarithmic derivative of a bivariate resultant at a split
specialisation, with `0 < f.natDegree` and `f.Monic`. The trivial
`f.natDegree = 0` case is now a theorem.

The Galois case of Lang's underlying trace-of-log-derivative identity
`Tr_{L/K}(dα/α) = d N_{L/K}(α) / N_{L/K}(α)` is fully formalised as
`Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
(in `Divisor/Axioms/AxiomTraceLogDeriv.lean`). Discharging this
remaining axiom requires the splitting-field/resultant/specialisation
plumbing connecting `Polynomial.derivative` to mathlib's `Differential`
typeclass; see `axioms/resultant_logDeriv_at_split.md` for the plan.

#### `weil_reciprocity_honest` — Silverman AEC II Exercise 2.11, p. 39

Weil reciprocity specialized to the honest-prover setting. Classical statement: for nonzero rational functions `f, g` on a smooth curve `C` with `div(f)` and `div(g)` of disjoint support,

$$f\bigl(\mathrm{div}(g)\bigr) = g\bigl(\mathrm{div}(f)\bigr),$$

where by convention

$$f(D) = \prod_P f(P)^{n_P} \qquad \text{for } D = \sum_P n_P (P).$$

The axiom concludes the project-specific log-derivative consequence: for an honest divisor `D` and every challenge `(A_0, A_1)` off the bad set, `logDerivCheckFn(D, target, k, bases, m, A_0, A_1) = 0`. This packages Weil reciprocity applied to the rational function `D / L^m` (where `L` is the chord line) plus residue/differential arithmetic not stated in Exercise 2.11.

#### `hasse_weil` — Silverman AEC V Thm 1.1, p. 138

Classical Hasse bound on the number of `F_q`-points of `E`. Stated in `Divisor/Axioms.lean` in the equivalent integer-squared form

$$\bigl(|E(F_q)| - q - 1\bigr)^2 \le  4q,$$

which is equivalent to

$$\bigl| |E(F_q)| - q - 1 \bigr| \le  2\sqrt{q}.$$

#### `bivariate_poly_zeros_on_ExE_le` — discharged

Previously listed as an axiom; now a *theorem* (see
`Divisor/BivariateZerosOnExE.lean`) whose only project-axiom
dependency is `hasse_weil`. The DKL'14 Claim 7.2 + Bezout content
has been mechanised. Removed from the headline axiom surface.

The point-count step is Dvir-Kollar-Lovett Claim 7.2. The geometric
degree input is the standard Bezout/intersection-theory estimate
`deg((E × E) ∩ {f = 0}) ≤ 9D`.
