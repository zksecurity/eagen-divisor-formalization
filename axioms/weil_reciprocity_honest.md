# `weil_reciprocity_honest`

- **Lean source**: deleted (was `Divisor/Axioms/AxiomWeilReciprocityHonest.lean`).
- **Status (post-discharge)**: **discharged**. The axiom is no longer in
  the closure of `ma_completeness` or `ma_completeness_clean`. Replaced
  by routing through `Divisor.ma_completeness_via_isHonestForExplicit`
  (in `Divisor/EagenBuildRecursive.lean`), which derives the residue
  identity from the strengthened `MAProverMsg.isHonestFor` predicate
  using `principal_divisor_iff` (Silverman III.3.5) plus the
  chord-resultant axioms already in the soundness-side closure.
- **Status (pre-discharge)**: precondition strengthened in
  `Divisor/SupportDisjoint.lean` to make the axiom statement sound.
  Empirical verification: `divisors-axiom-tests/test_weil_reciprocity_honest.py`
  STRONG-BAD-SET PASS shows 0 failures across 28 curves.

Completeness form of Weil reciprocity: for an honest prover's
divisor, `logDerivCheckFn` vanishes at every challenge pair off the
(strengthened) bad set. The bad set excludes:
* `D` vanishing at `A_0`, `A_1`, or `A_2`;
* `A_2 = ∞` (vertical chord);
* **diagonal `A_0 = A_1`** (added in audit fix; Lean's `slopeOf`
  returns `0/0 = 0` here instead of the geometric tangent);
* **tangent collisions `A_2 ∈ {A_0, A_1}`** (added in audit fix; the
  `dx/dz` denominator vanishes at the affected sheet).

The original (pre-fix) axiom statement was unsound at the diagonal
and tangent-collision configurations — concretely demonstrated by
the F_5 doubling counterexample in
`Tests/RegressionDoublingChallenge.lean`.

## Citation

Primary (theorem statement it descends from):

- Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.), **Corollary 4.3.3 (Residue Theorem)**, p. 171.

Secondary (Weil reciprocity as such):

- Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Exercise II.2.11**, p. 39. Exercise 2.10 (same page) defines `f(D) = ∏_P f(P)^{n_P}` for `D = Σ n_P (P)` when `div(f)` and `D` have disjoint supports.

Weil reciprocity `f(div g) = g(div f)` is a direct consequence of the Residue Theorem applied to the logarithmic differential `(df/f)·log g` (formally, to `g · df/f` and `f · dg/g`): sum of residues vanishes, and computing residues at the support of `div f` vs. `div g` yields the stated identity.

## Verbatim

Stichtenoth 4.3.3:

> Corollary 4.3.3 (Residue Theorem). Let F/K be an algebraic function field over an algebraically closed field, and let ω ∈ Δ_F be a differential of F/K. Then res_P(ω) = 0 for almost all places P ∈ IP_F, and
>
> Σ_{P ∈ IP_F} res_P(ω) = 0.

Silverman Ex II.2.11:

> 2.11. Let C be a smooth curve and let f, g ∈ K̄(C)* be functions such that div(f) and div(g) have disjoint support. (See Exercise 2.10.) Prove Weil's reciprocity law
>
> f(div(g)) = g(div(f))
>
> using the following two steps:
> (a) Verify Weil's reciprocity law directly for C = P¹.
> (b) Now prove it for arbitrary C by using the map g : C → P¹ to reduce to (a).

## Snippets

![Stichtenoth Cor 4.3.3 (Residue Theorem)](snippets/stichtenoth-cor-4.3.3-residue-theorem-182.png)

![Silverman Ex II.2.11](snippets/silverman-ex-II.2.11-weil-reciprocity-057.png)

## Notes

The axiom applies Weil reciprocity to the principal divisor of the rational function `D / L^m`, where `L` is the chord line through `A₀, A₁, A₂`: the log-derivative identity follows from "sum of residues of a principal divisor = 0" on `E` (Stichtenoth Cor 4.3.3), so summing residues over the zeros yields the stated identity whenever evaluation points avoid the divisor support.
