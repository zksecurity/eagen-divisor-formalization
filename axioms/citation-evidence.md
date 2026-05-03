# Citation Evidence Inventory

This file records the local evidence behind the current MA extraction
axiom boundary.

## Local full sources

In-repo archived sources:

* `axioms/papers/stacks-02RS.html` — Stacks Project, Lemma 42.18.1
  (Principal divisors and pushforward), downloaded from
  <https://stacks.math.columbia.edu/tag/02RS>.
* `axioms/papers/chow.pdf` — Stacks Project chapter PDF containing
  Section 42.18, "Principal divisors and pushforward".
* `axioms/papers/lang-weil-1954.pdf`
* `axioms/papers/DvirKollarLovett14.pdf`
* `axioms/papers/EllenbergOberlinTao10.pdf`

Book PDFs used for snippets are present outside this Lean repo at:

* `/Users/rot256/paper/crypto-books/Silverman-Arithmetic_of_EC.pdf`
* `/Users/rot256/paper/crypto-books/Stichtenoth-Algebraic-Function-Fields-and-Codes.pdf`
* `/Users/rot256/paper/crypto-books/Lang-Algebra-3rd.pdf`

## MA Extraction Closure

`Divisor.ma_extractable` currently depends on these project axioms:

* `Divisor.hasse_weil`
  * Citation: Silverman AEC V.1.1; Stichtenoth 5.2.3.
  * Snippets:
    `snippets/silverman-thm-V.1.1-hasse-155.png`,
    `snippets/stichtenoth-thm-5.2.3-hasse-weil-bound-209.png`.

* `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`
  * Primary citation: Stacks Project 42.18.1 / tag 02RS.
  * Local sources: `papers/stacks-02RS.html`, `papers/chow.pdf`.
  * Supporting snippets:
    `snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png`,
    `snippets/stichtenoth-thm-3.1.11-fundamental-equality-074.png`.

* `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`
  * Citation: Lang IV.8, VI.5, VIII.5.
  * Snippets:
    `snippets/lang-IV.8-prop-8.1-8.3-resultant-202.png`,
    `snippets/lang-IV.8-prop-8.3-resultant-product-proof-203.png`,
    `snippets/lang-VI.5-thm-5.1-norm-trace-300.png`,
    `snippets/lang-VIII.5-thm-5.1-derivations-385.png`.

* `Divisor.CoordRingElt.divisorClass_eq_zero_of_not_const_unit`
  * Citation: Silverman II.3 and III.3.5, with Stichtenoth 1.4.1 /
    1.4.2 / 1.4.11 as function-field divisor background.
  * Snippets:
    `snippets/silverman-II.3-divisors-027.png`,
    `snippets/silverman-II.3-principal-divisors-028.png`,
    `snippets/silverman-cor-III.3.5-principal-divisor-081.png`,
    `snippets/stichtenoth-def-1.4.1-divisors-015.png`,
    `snippets/stichtenoth-def-1.4.2-principal-divisor-016.png`,
    `snippets/stichtenoth-thm-1.4.11-principal-degree-zero-019.png`.

## Citation Corrections Applied

* Stichtenoth Theorem 3.7.1 is no longer described as a ramification or
  Hasse-Arf-style theorem. It states Galois transitivity on extensions
  of a place and is only supporting background for Galois-closure routes.
* Stacks 02RS is now recorded as the direct citation for
  pushforward of principal divisors under norm.
* Lang IV.8 resultant snippets have been added for the resultant/norm
  bridge used by the resultant log-derivative axiom.
