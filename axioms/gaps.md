# Provenance gaps

Axiom-by-axiom status of textbook coverage in `/Users/rot256/paper/crypto-books/`.

| Axiom | Status |
|---|---|
| `principal_divisor_iff` | Covered — Silverman AEC Cor III.3.5 |
| `CoordRingElt.divisorClass_isPrincipal_of_not_const_unit` | Open bridge — principal fractional-ideal replacement for the former `ordAt_divisor_isPrincipal`/`principal_divisor_iff` path on MA extraction. Now narrowed: the trivial constant-unit case `(D.a = C c, D.b = 0, c ≠ 0)` is a theorem (since `divisorOfD = 0`), and the unrestricted form `CoordRingElt.divisorClass_isPrincipal` is a re-exported theorem. The old `ordAt_divisorClass_zero` statement is also a theorem derived from this axiom. See `divisorClass_isPrincipal.md`. |
| `hasse_weil` | Covered — Silverman AEC Thm V.1.1 + Stichtenoth Thm 5.2.3 |
| `ECPoint.add_comm` | Covered — Silverman AEC Prop III.2.2(c) |
| `ECPoint.add_assoc` | Covered — Silverman AEC Prop III.2.2(e) |
| `ECPoint.neg_add_cancel` | Covered — Silverman AEC Prop III.2.2(d) |
| `chord_fiber_product_eq_normZ_under_split` | **Legacy temporary bridge** — mathematically covered by divisor/norm pushforward plus Stichtenoth Prop 3.1.9 and Thm 3.1.11 place accounting; Thm 3.7.1 is only supporting background for a Galois-closure route. The statement is proof-specific (`chord_fiber_product`, `normZ`, `splitsOnE`). It now explicitly requires `β_fun = betaTrue` pointwise, avoiding the older too-broad arbitrary-β shape. It is no longer in the MA/IP headline closure. |
| `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image` | **Now a theorem** (no longer an axiom). Discharged via the squeeze argument from the strictly weaker divisibility axiom `chord_fiber_product_concrete_bar_zfiber_pow_dvd` plus the just-landed weighted-Sylvester upper bound `chord_fiber_product_concrete_natDegree_le_normPoly_natDegree`. |
| `chord_fiber_product_concrete_bar_zfiber_pow_dvd` | **Narrow remaining divisibility axiom** — coefficientwise *lower bound* of the divisor pushforward under the chord projection: `(X − C z)^(fibre_sum) ∣ chord_fiber_product`. This *replaces* the older multiplicity-equality axiom. Stacks Project [02RS](https://stacks.math.columbia.edu/tag/02RS) is the direct pushforward-of-principal-divisor citation; the matching upper bound (the natDegree inequality) is a coordinate-native theorem via the weighted-Sylvester analysis in `Divisor/ChordFiberWeightedDegree.lean`. Detailed write-up in `axioms/chord_fiber_product_concrete_bar_zfiber_pow_dvd.md`; local HTML archive at `axioms/papers/stacks-02RS.html`. |
| `chord_fiber_product_bar_eq_geom_prod` | **Theorem from the narrow multiplicity axiom** — no longer an independent axiom. |
| `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` | **Theorem** — derived from the strictly narrower generic axiom `Polynomial.resultant_logDeriv_at_split_specialization` plus chord-cubic-specific algebra. No longer in the headline closure. |
| `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree_pos_g` | **Temporary generic trace bridge** — replaces the older project-shaped chord-specific axiom, but is still a composed polynomial/resultant specialisation. Now carries an explicit `Monic f` hypothesis that brings the statement in line with mathlib's `Polynomial.resultant_eq_prod_eval` (without monicity the per-root sum picks up an extra `d/dT log(lc(f)^{deg g})` term). Both trivial degree-zero cases are now theorems: `f.natDegree = 0` via `Monic + natDegree = 0 ⇒ f = 1` (both sides collapse to `0`), and `g.natDegree = 0` via `derivative_pow` plus the constant `(g.coeff 0)`'s logarithmic derivative being constant on the chord-root multiset. The unrestricted form `Polynomial.resultant_logDeriv_at_split_specialization` is a re-exported theorem case-splitting on both degrees. The final target is to prove the remaining `0 < f.natDegree ∧ 0 < g.natDegree` axiom from the already-proved Galois theorem `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois` plus resultant and specialisation algebra. See `axioms/resultant_logDeriv_at_split.md`. |
| `weil_reciprocity_honest` | Covered — Stichtenoth Cor 4.3.3 (Residue Theorem) + Silverman AEC Ex II.2.11. Descent skeleton in `Divisor/WeilReciprocityDescent.lean` (sorry'd; in-flight, see P3 of soundness plan). |
| `CoordRingElt.exists_divisor_multiplicity` | **Proven modulo `CoordRingElt.divisorClass_isPrincipal`** — theorem-backed by `Divisor.exists_divisor_multiplicity_proved`; the new `CoordRingElt.exists_divisor_multiplicity_ecpoint` exposes the cleaner `ECPoint`-indexed form. Replaces the previously-listed `CoordRingElt.divisor_group_sum_zero`, which was provably unsound (counterexample over `F_5`; see file header in `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`). |
| `bivariate_poly_zeros_on_ExE_le` | **Proven** — derived from `hasse_weil` via fiber-counting (`Divisor/BivariateZerosOnExE.lean` + `Divisor/CurveEvalZerosHelper.lean`). No longer an axiom. |

## Status

The old false divisor-group axiom is removed. The current MA extraction
closure has four narrow axioms:

1. `Divisor.hasse_weil` — Hasse-Weil bound (textbook).
2. `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd` — chord
   pushforward divisibility (Stacks 02RS lower bound). Replaces the
   older multiplicity-equality axiom: the matching upper bound is now
   a coordinate-native theorem via the weighted-Sylvester analysis.
3. `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree_pos_g`
   — Lang's trace-of-log-derivative formula at a split specialisation,
   narrowed to `0 < f.natDegree`, `0 < g.natDegree`, and `Monic f`.
4. `Divisor.CoordRingElt.divisorClass_isPrincipal_of_not_const_unit`
   — Abel-style principal-class statement for the regular function `D`,
   narrowed to the non-constant-unit case.

The exact closure is pinned in `Tests/AxiomClosurePin.lean`.

The desired final boundary is tracked in
[`docs/axiom-boundary-target.md`](../docs/axiom-boundary-target.md):
Hasse-Weil is in the desired shape. The chord pushforward is now in
divisibility-only Stacks-02RS shape. The trace/log-derivative boundary
has made progress: the chord-specific axiom is a theorem, and the
Galois norm/trace/log-derivative identity is proved from mathlib;
remaining is the generic resultant-specialisation plumbing connecting
`Polynomial.derivative` to mathlib's `Differential` typeclass (the
typeclass instance for `K[T]` is now provided in
`Divisor/PolynomialDifferential.lean`).

### `weil_reciprocity_honest`

Resolved by citing Stichtenoth **Corollary 4.3.3 (Residue Theorem)**, p. 171 — the underlying theorem — alongside Silverman AEC Ex II.2.11. Stichtenoth does not name "Weil reciprocity" as a standalone theorem; Rosen's "reciprocity law" is the unrelated d-th power reciprocity for function fields (quadratic-reciprocity analogue). The Residue Theorem is the standard textbook route: Weil reciprocity is its one-line corollary for `f · dg/g` and `g · df/f`.

### `bivariate_poly_zeros_on_ExE_le`

**Now proven** (no longer an axiom). Derived from `hasse_weil` plus elementary fiber-counting:

1. Reduce a bivariate polynomial of total degree `d` modulo the Weierstrass relation `Y² = X³ + AX + B` to canonical form `α(X) + β(X)·Y` with `deg α, deg β ≤ ⌈3d/2⌉`.
2. Bound zeros on `E(F_q)` via the norm polynomial `α² − β²·c(X)` and `rootMultiplicity ≥ 2` at common roots of α, β (paper-tight `≤ degE`, sharper than the previous `≤ 2·degE`).
3. Lift to the 4-variate setting by specialising one coordinate, applying the per-curve bound to each fiber, and using Hasse–Weil's `2·|E(F_q)| ≤ 3q + 3` to absorb the bad-fiber contribution.

Proof in `Divisor/BivariateZerosOnExE.lean` and `Divisor/CurveEvalZerosHelper.lean`. The `Divisor.bivariate_poly_zeros_on_ExE_le` theorem is declared at the bottom of `BivariateZerosOnExE.lean`.

Provenance retained for documentation: Lang & Weil 1954 Thm 1 (`papers/lang-weil-1954.pdf`); DKL'14 Claim 7.2 (`papers/DvirKollarLovett14.pdf`); EOT'10 Lemma A.3 (`papers/EllenbergOberlinTao10.pdf`).
