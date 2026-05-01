# Provenance gaps

Axiom-by-axiom status of textbook coverage in `/Users/rot256/paper/crypto-books/`.

| Axiom | Status |
|---|---|
| `principal_divisor_iff` | Covered — Silverman AEC Cor III.3.5 |
| `ordAt_divisorClass_zero` | Open bridge — narrower replacement for the former `ordAt_divisor_isPrincipal`/`principal_divisor_iff` path on MA extraction. See `ordAt_divisorClass_zero.md`. |
| `hasse_weil` | Covered — Silverman AEC Thm V.1.1 + Stichtenoth Thm 5.2.3 |
| `ECPoint.add_comm` | Covered — Silverman AEC Prop III.2.2(c) |
| `ECPoint.add_assoc` | Covered — Silverman AEC Prop III.2.2(e) |
| `ECPoint.neg_add_cancel` | Covered — Silverman AEC Prop III.2.2(d) |
| `chord_fiber_product_eq_normZ_under_split` | **Temporary bridge** — mathematically covered by Stichtenoth Prop 3.1.9 + Thm 3.7.1, but the current statement is proof-specific (`chord_fiber_product`, `normZ`, `splitsOnE`). Final target: replace by a clean norm/divisor push-forward axiom plus coordinate theorems. |
| `chord_fiber_product_bar_eq_geom_prod` | **Temporary bridge** — better than the split rational statement because it uses geometric divisor data, but still proof-specific. Final target: theorem from the norm/divisor push-forward axiom. |
| `chord_sum_eq_chord_fiber_product_logDeriv` | **Temporary bridge** — mathematically covered by Lang *Algebra* §VI.5 Thm 5.1 + §VIII.5 Thm 5.1 Case 1, but the current statement packages trace/log-derivative with chord coordinates and denominator bookkeeping. Final target: theorem from a clean `Tr(dg/g)=dN(g)/N(g)` axiom. |
| `weil_reciprocity_honest` | Covered — Stichtenoth Cor 4.3.3 (Residue Theorem) + Silverman AEC Ex II.2.11. Descent skeleton in `Divisor/WeilReciprocityDescent.lean` (sorry'd; in-flight, see P3 of soundness plan). |
| `CoordRingElt.exists_divisor_multiplicity` | **Proven modulo `ordAt_divisorClass_zero`** — theorem-backed by `Divisor.exists_divisor_multiplicity_proved`; the new `CoordRingElt.exists_divisor_multiplicity_ecpoint` exposes the cleaner `ECPoint`-indexed form. Replaces the previously-listed `CoordRingElt.divisor_group_sum_zero`, which was provably unsound (counterexample over `F_5`; see file header in `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`). |
| `bivariate_poly_zeros_on_ExE_le` | **Proven** — derived from `hasse_weil` via fiber-counting (`Divisor/BivariateZerosOnExE.lean` + `Divisor/CurveEvalZerosHelper.lean`). No longer an axiom. |

## Status

The old false divisor-group axiom is removed. The current MA extraction
closure has one explicit class-group bridge,
`ordAt_divisorClass_zero`, plus Hasse-Weil and the temporary chord
bridges pinned in `Tests/AxiomClosurePin.lean`.

The desired final boundary is tracked in
[`docs/axiom-boundary-target.md`](../docs/axiom-boundary-target.md):
Hasse-Weil is already in the desired shape; the chord bridges are
sound but too proof-specific and should be replaced by clean textbook
norm/divisor and trace/log-derivative axioms, with project-specific
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
