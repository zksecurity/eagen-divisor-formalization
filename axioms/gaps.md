# Provenance gaps

Axiom-by-axiom status of textbook coverage in `/Users/rot256/paper/crypto-books/`.

| Axiom | Status |
|---|---|
| `principal_divisor_iff` | Covered — Silverman AEC Cor III.3.5 |
| `hasse_weil` | Covered — Silverman AEC Thm V.1.1 + Stichtenoth Thm 5.2.3 |
| `ECPoint.add_comm` | Covered — Silverman AEC Prop III.2.2(c) |
| `ECPoint.add_assoc` | Covered — Silverman AEC Prop III.2.2(e) |
| `ECPoint.neg_add_cancel` | Covered — Silverman AEC Prop III.2.2(d) |
| `chord_fiber_product_eq_normZ_under_split` | Covered — Stichtenoth Prop 3.1.9 + Thm 3.7.1 |
| `chord_sum_eq_chord_fiber_product_logDeriv` | Covered — Lang *Algebra* §VI.5 Thm 5.1 + §VIII.5 Thm 5.1 Case 1 |
| `weil_reciprocity_honest` | Covered — Stichtenoth Cor 4.3.3 (Residue Theorem) + Silverman AEC Ex II.2.11. Descent skeleton in `Divisor/WeilReciprocityDescent.lean` (sorry'd; in-flight, see P3 of soundness plan). |
| `CoordRingElt.exists_divisor_multiplicity` | Covered — Silverman AEC Cor III.3.5 + II §1 (local order ord_P at smooth points). Replaces the previously-listed `CoordRingElt.divisor_group_sum_zero`, which was provably unsound (counterexample over `F_5`; see file header in `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`). |
| `bivariate_poly_zeros_on_ExE_le` | **Proven** — derived from `hasse_weil` via fiber-counting (`Divisor/BivariateZerosOnExE.lean` + `Divisor/CurveEvalZerosHelper.lean`). No longer an axiom. |

## Status — all closed

All axioms have textbook or primary-source citations archived. No further papers required.

### `weil_reciprocity_honest`

Resolved by citing Stichtenoth **Corollary 4.3.3 (Residue Theorem)**, p. 171 — the underlying theorem — alongside Silverman AEC Ex II.2.11. Stichtenoth does not name "Weil reciprocity" as a standalone theorem; Rosen's "reciprocity law" is the unrelated d-th power reciprocity for function fields (quadratic-reciprocity analogue). The Residue Theorem is the standard textbook route: Weil reciprocity is its one-line corollary for `f · dg/g` and `g · df/f`.

### `bivariate_poly_zeros_on_ExE_le`

**Now proven** (no longer an axiom). Derived from `hasse_weil` plus elementary fiber-counting:

1. Reduce a bivariate polynomial of total degree `d` modulo the Weierstrass relation `Y² = X³ + AX + B` to canonical form `α(X) + β(X)·Y` with `deg α, deg β ≤ ⌈3d/2⌉`.
2. Bound zeros on `E(F_q)` via the norm polynomial `α² − β²·c(X)` and `rootMultiplicity ≥ 2` at common roots of α, β (paper-tight `≤ degE`, sharper than the previous `≤ 2·degE`).
3. Lift to the 4-variate setting by specialising one coordinate, applying the per-curve bound to each fiber, and using Hasse–Weil's `2·|E(F_q)| ≤ 3q + 3` to absorb the bad-fiber contribution.

Proof in `Divisor/BivariateZerosOnExE.lean` and `Divisor/CurveEvalZerosHelper.lean`. The `Divisor.bivariate_poly_zeros_on_ExE_le` theorem is declared at the bottom of `BivariateZerosOnExE.lean`.

Provenance retained for documentation: Lang & Weil 1954 Thm 1 (`papers/lang-weil-1954.pdf`); DKL'14 Claim 7.2 (`papers/DvirKollarLovett14.pdf`); EOT'10 Lemma A.3 (`papers/EllenbergOberlinTao10.pdf`).
