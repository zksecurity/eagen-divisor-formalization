# Axiom Provenance and Bridge Gaps

This file tracks the Lean `axiom` declarations in the project and the
textbook or paper statement supporting each one.

Here, a "bridge gap" is not a missing citation. It means the Lean statement is
a project-specific specialization of a cited theorem, and the remaining work is
the coordinate, resultant, local-order, or specialization plumbing needed to
derive the Lean statement from the source theorem.

## Axiom Declarations

| Lean declaration | Source statement | Bridge gap |
|---|---|---|
| `Divisor.hasse_weil` | Silverman AEC Theorem V.1.1: `\|#E(F_q) - q - 1\| <= 2 sqrt q`. See `hasse_weil.md` and `snippets/silverman-thm-V.1.1-hasse-155.png`. | Only the integer-squared restatement `(#E(F_q) - q - 1)^2 <= 4q`. |
| `Divisor.principal_divisor_iff` | Silverman AEC Corollary III.3.5: a divisor `Σ n_P(P)` on an elliptic curve is principal iff `Σ n_P = 0` and `Σ [n_P]P = O`. See `principal_divisor_iff.md` and `snippets/silverman-cor-III.3.5-principal-divisor-081.png`. | The Lean statement is restricted to the `ECPoint E` coefficient model; the citation note records the finite-field descent justification. |
| `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero` | Silverman II.3 defines divisors of rational functions by local orders; Stichtenoth Def. 1.4.2 names principal divisors; Silverman III.3.5 characterizes principal divisors on elliptic curves. See `divisorClass_isPrincipal.md`, `snippets/silverman-II.3-divisors-027.png`, `snippets/stichtenoth-def-1.4.2-principal-divisor-016.png`, and `snippets/silverman-cor-III.3.5-principal-divisor-081.png`. | Identify the project divisor `divisorOfD E D`, built from `ordAt`, with the principal divisor of the coordinate-ring element `D = a(x) - b(x)y`, then map that divisor to the class-group statement. |
| `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd` | Stacks Project tag 02RS: principal divisors and norm pushforward, `p_* div(f) = div(Nm(f))`. Stichtenoth Prop. 3.1.9 supplies supporting conorm/principal-divisor calculus. See `chord_fiber_product_concrete_bar_zfiber_pow_dvd.md`, `papers/stacks-02RS.html`, and `snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png`. | Instantiate the norm-pushforward theorem for the chord projection and identify the pushed-forward local multiplicities with divisibility of the concrete resultant over `Fqbar E`. |
| `Divisor.chord_fiber_product_eq_normZ_under_split` | Stacks Project tag 02RS plus Stichtenoth Prop. 3.1.9 and Thm. 3.1.11 place accounting. See `chord_fiber_product_eq_normZ_under_split.md`, `papers/stacks-02RS.html`, `snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png`, and `snippets/stichtenoth-thm-3.1.11-fundamental-equality-074.png`. | Under `splitsOnE` and `β_fun = betaTrue`, identify the project polynomial `chord_fiber_product` and the split polynomial `normZ` as the same norm divisor up to a nonzero scalar. |
| `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g` | Lang IV.8 gives resultants as products over roots; Lang VI.5 gives norm/trace as products/sums over embeddings; Lang VIII.5 gives the separable derivative formula `ξ' = -f^D(ξ)/f'(ξ)`. See `resultant_logDeriv_at_split.md`, `snippets/lang-IV.8-prop-8.1-8.3-resultant-202.png`, `snippets/lang-VI.5-thm-5.1-norm-trace-300.png`, and `snippets/lang-VIII.5-thm-5.1-derivations-385.png`. | Construct the splitting-field/differential setup, identify `Res_X(f,g)` with the norm of `g`, and specialize the trace-of-log-derivative identity at `t₀`. |
| `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv` | Lang VI.5 gives norm/trace over embeddings; Lang VIII.5 gives compatible derivation extension to separable algebraic extensions. See `trace_logDeriv.md`, `snippets/lang-VI.5-thm-5.1-norm-trace-300.png`, and `snippets/lang-VIII.5-thm-5.1-derivations-385.png`. | The Lean axiom is the finite-separable form. The Galois case is theorem-backed in `Divisor/Axioms/AxiomTraceLogDeriv.lean`; deriving the broader form requires reducing through a Galois closure or proving the non-Galois trace formula directly. |
| `Divisor.weil_reciprocity_textbook` | Silverman AEC Exercise II.2.11 states Weil reciprocity `f(div g) = g(div f)` for disjoint supports; Stichtenoth Cor. 4.3.3 is the residue theorem supporting the logarithmic-differential proof. See `weil_reciprocity_honest.md`, `snippets/silverman-ex-II.2.11-weil-reciprocity-057.png`, and `snippets/stichtenoth-cor-4.3.3-residue-theorem-182.png`. | Match the project coordinate-ring product over `E.points` with divisor evaluation, including the support-disjointness and multiplicity conventions required by the textbook statement. |

## Opaque Predicate

`Divisor.IsPrincipal` is an opaque predicate, not a Lean `axiom`
declaration:

```lean
opaque IsPrincipal (E : ECSetup) (coeffs : ECPoint E → ℤ) : Prop
```

Its intended meaning is pinned by `Divisor.principal_divisor_iff`.

## Theorem-Backed Surfaces

The following names are theorem-backed surfaces whose axiom dependencies are
tracked through the declarations above:

- `CoordRingElt.exists_divisor_multiplicity`
- `CoordRingElt.exists_divisor_multiplicity_ecpoint`
- `Divisor.bivariate_poly_zeros_on_ExE_le`
- `Divisor.chord_fiber_product_bar_eq_geom_prod`
- `Divisor.chord_sum_eq_chord_fiber_product_logDeriv`

The headline closure is pinned in `Tests/AxiomClosurePin.lean`.
