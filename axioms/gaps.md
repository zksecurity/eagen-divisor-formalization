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
| `weil_reciprocity_honest` | Covered — Stichtenoth Cor 4.3.3 (Residue Theorem) + Silverman AEC Ex II.2.11 |
| `CoordRingElt.divisor_group_sum_zero` | Covered — Silverman AEC Cor III.3.5 (⇒ direction) |
| `bivariate_poly_zeros_on_ExE_le` (planned) | Covered — Lang–Weil 1954 Thm 1 (`papers/lang-weil-1954.pdf`) |

## Status — all closed

All axioms have textbook or primary-source citations archived. No further papers required.

### `weil_reciprocity_honest`

Resolved by citing Stichtenoth **Corollary 4.3.3 (Residue Theorem)**, p. 171 — the underlying theorem — alongside Silverman AEC Ex II.2.11. Stichtenoth does not name "Weil reciprocity" as a standalone theorem; Rosen's "reciprocity law" is the unrelated d-th power reciprocity for function fields (quadratic-reciprocity analogue). The Residue Theorem is the standard textbook route: Weil reciprocity is its one-line corollary for `f · dg/g` and `g · df/f`.

### `bivariate_poly_zeros_on_ExE_le`

Resolved by Lang & Weil 1954, *Number of Points of Varieties in Finite Fields*, Am. J. Math. 76, pp. 819–827 — archived in repo at `papers/lang-weil-1954.pdf`. Theorem 1 (p. 819) gives the compound bound directly.
