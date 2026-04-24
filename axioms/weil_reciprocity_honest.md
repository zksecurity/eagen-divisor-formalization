# `weil_reciprocity_honest`

- **Lean source**: `Divisor/Soundness.lean:286`

Completeness form of Weil reciprocity: for an honest prover's divisor, `logDerivCheckFn` vanishes at every challenge pair off the bad set.

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
