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
| `chord_fiber_product_eq_normZ_under_split` | **Legacy temporary bridge** — mathematically covered by Stichtenoth Prop 3.1.9 + Thm 3.7.1, but the statement is proof-specific (`chord_fiber_product`, `normZ`, `splitsOnE`). It now explicitly requires `β_fun = betaTrue` pointwise, avoiding the older too-broad arbitrary-β shape. It is no longer in the MA/IP headline closure. |
| `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image` | **Narrow remaining norm/divisor axiom** — coefficientwise push-forward of the zero divisor under the chord projection *restricted to intercepts that actually appear in `gd.support`*. The off-image case is now a theorem, derived from the existing `chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image` root-set bridge plus `Polynomial.rootMultiplicity_eq_zero`; the unrestricted form `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber` is a re-exported theorem. Covered by Stichtenoth Prop 3.1.9, with coordinate/resultant plumbing still formalized locally. |
| `chord_fiber_product_bar_eq_geom_prod` | **Theorem from the narrow multiplicity axiom** — no longer an independent axiom. |
| `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` | **Theorem** — derived from the strictly narrower generic axiom `Polynomial.resultant_logDeriv_at_split_specialization` plus chord-cubic-specific algebra. No longer in the headline closure. |
| `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree` | **Temporary generic trace bridge** — replaces the older project-shaped chord-specific axiom, but is still a composed polynomial/resultant specialisation. Now carries an explicit `Monic f` hypothesis that brings the statement in line with mathlib's `Polynomial.resultant_eq_prod_eval` (without monicity the per-root sum picks up an extra `d/dT log(lc(f)^{deg g})` term), and the trivial `f.natDegree = 0` case is now a theorem (since `Monic + natDegree = 0` forces `f = 1`, both sides collapse to `0`). The unrestricted form `Polynomial.resultant_logDeriv_at_split_specialization` is a re-exported theorem. The final target is to prove the remaining `0 < f.natDegree` axiom from the already-proved Galois theorem `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois` plus resultant and specialisation algebra. See `axioms/resultant_logDeriv_at_split.md`. |
| `weil_reciprocity_honest` | Covered — Stichtenoth Cor 4.3.3 (Residue Theorem) + Silverman AEC Ex II.2.11. Descent skeleton in `Divisor/WeilReciprocityDescent.lean` (sorry'd; in-flight, see P3 of soundness plan). |
| `CoordRingElt.exists_divisor_multiplicity` | **Proven modulo `CoordRingElt.divisorClass_isPrincipal`** — theorem-backed by `Divisor.exists_divisor_multiplicity_proved`; the new `CoordRingElt.exists_divisor_multiplicity_ecpoint` exposes the cleaner `ECPoint`-indexed form. Replaces the previously-listed `CoordRingElt.divisor_group_sum_zero`, which was provably unsound (counterexample over `F_5`; see file header in `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`). |
| `bivariate_poly_zeros_on_ExE_le` | **Proven** — derived from `hasse_weil` via fiber-counting (`Divisor/BivariateZerosOnExE.lean` + `Divisor/CurveEvalZerosHelper.lean`). No longer an axiom. |

## Status

The old false divisor-group axiom is removed. The current MA extraction
closure has one explicit class-group bridge,
`CoordRingElt.divisorClass_isPrincipal`, plus Hasse-Weil, the narrow
root-multiplicity norm/divisor axiom, and the temporary generic
resultant log-derivative bridge. The exact closure is pinned in
`Tests/AxiomClosurePin.lean`.

The desired final boundary is tracked in
[`docs/axiom-boundary-target.md`](../docs/axiom-boundary-target.md):
Hasse-Weil is in the desired shape. The trace/log-derivative boundary has
made one step: the chord-specific axiom is now a theorem, and the Galois
norm/trace/log-derivative identity is proved from mathlib, but the generic
resultant specialisation is still an axiom. The remaining norm/divisor and
principal-class assumptions are narrow, but still need the project-specific
coordinate statements proved downstream.

### `weil_reciprocity_honest`

Resolved by citing Stichtenoth **Corollary 4.3.3 (Residue Theorem)**, p. 171 — the underlying theorem — alongside Silverman AEC Ex II.2.11. Stichtenoth does not name "Weil reciprocity" as a standalone theorem; Rosen's "reciprocity law" is the unrelated d-th power reciprocity for function fields (quadratic-reciprocity analogue). The Residue Theorem is the standard textbook route: Weil reciprocity is its one-line corollary for `f · dg/g` and `g · df/f`.

### `bivariate_poly_zeros_on_ExE_le`

**Now proven** (no longer an axiom). Derived from `hasse_weil` plus elementary fiber-counting:

1. Reduce a bivariate polynomial of total degree `d` modulo the Weierstrass relation `Y² = X³ + AX + B` to canonical form `α(X) + β(X)·Y` with `deg α, deg β ≤ ⌈3d/2⌉`.
2. Bound zeros on `E(F_q)` via the norm polynomial `α² − β²·c(X)` and `rootMultiplicity ≥ 2` at common roots of α, β (paper-tight `≤ degE`, sharper than the previous `≤ 2·degE`).
3. Lift to the 4-variate setting by specialising one coordinate, applying the per-curve bound to each fiber, and using Hasse–Weil's `2·|E(F_q)| ≤ 3q + 3` to absorb the bad-fiber contribution.

Proof in `Divisor/BivariateZerosOnExE.lean` and `Divisor/CurveEvalZerosHelper.lean`. The `Divisor.bivariate_poly_zeros_on_ExE_le` theorem is declared at the bottom of `BivariateZerosOnExE.lean`.

Provenance retained for documentation: Lang & Weil 1954 Thm 1 (`papers/lang-weil-1954.pdf`); DKL'14 Claim 7.2 (`papers/DvirKollarLovett14.pdf`); EOT'10 Lemma A.3 (`papers/EllenbergOberlinTao10.pdf`).
