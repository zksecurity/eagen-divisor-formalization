# `chord_fiber_product_eq_normZ_under_split`

- **Lean source**: `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`

```lean
axiom chord_fiber_product_eq_normZ_under_split
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      chord_fiber_product E lam D = C c * normZ E lam D β_fun
```

Identifies the function-field norm `N_{F_q(E)/F_q(z)}(D)` (the chord-fiber product) with a nonzero constant multiple of `normZ` under `splitsOnE` and pointwise faithful multiplicity accounting (`β_fun = betaTrue`).

## Boundary status

This is now a sound but legacy bridge statement. It is not in the
headline MA/IP closure. The explicit `hβtrue` hypothesis is essential:
support, coverage, and total accounting alone do not determine
pointwise local multiplicities, so the older arbitrary-β shape was too
broad.

The statement is still not the desired final axiom shape. It packages
the textbook divisor-of-norm theorem together with the project-specific
`chord_fiber_product`, rational `normZ`, and `splitsOnE` accounting.

Final target: use a clean norm/divisor push-forward theorem for finite
separable function-field extensions, then prove this rational split
statement and the geometric `chord_fiber_product_bar_eq_geom_prod`
statement as coordinate consequences.

## Citation

Primary pushforward citation:

* **Stacks Project**, [Lemma 42.18.1 (Principal divisors and pushforward)](https://stacks.math.columbia.edu/tag/02RS):
  `p_* div(f) = div(Nm(f))`. Local archive:
  `axioms/papers/stacks-02RS.html`.

Supporting function-field divisor references:

Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.):

- **Proposition 3.1.9**, p. 73 — conorm of a principal divisor is principal.
- **Theorem 3.1.11**, p. 74 — the fundamental equality
  `Σ_i e_i f_i = [F' : F]`, used for finite-extension place accounting.
- **Theorem 3.7.1**, p. 121 — Galois transitivity on extensions of a place.
  This is only supporting background for a Galois-closure route; it is
  not the principal norm/pushforward theorem and is logically redundant
  for the F_q-split corollary stated here.

A separate "this concrete resultant is the function-field norm for the extension `F_qbar(E) / F_qbar(zLambdaBar lam)` and `gd.mult` is the local divisor multiplicity at the corresponding place" bridge is also needed; the textbook content of that bridge is Lang IV.8 (resultant as product over roots) plus the standard identification of local multiplicities with adic valuations on the function field.

## Verbatim

Stichtenoth 3.1.9:

> Proposition 3.1.9. Let F′/K′ be an algebraic extension of the function field F/K. For 0 ≠ x ∈ F let (x)₀^F, (x)∞^F, (x)^F resp. (x)₀^{F′}, (x)∞^{F′}, (x)^{F′} denote the zero, pole, principal divisor of x in Div(F) resp. in Div(F′). Then
>
> Con_{F′/F}((x)₀^F) = (x)₀^{F′},
> Con_{F′/F}((x)∞^F) = (x)∞^{F′},   and
> Con_{F′/F}((x)^F)  = (x)^{F′}.

Stichtenoth 3.1.11:

> Theorem 3.1.11 (Fundamental Equality). Let F′/K′ be a finite extension
> of F/K, let P be a place of F/K and let P₁, …, Pₘ be all the places of
> F′/K′ lying over P. Let eᵢ := e(Pᵢ|P) and fᵢ := f(Pᵢ|P). Then
> Σᵢ eᵢ fᵢ = [F′ : F].

Stichtenoth 3.7.1:

> Theorem 3.7.1. Let F′/K′ be a Galois extension of F/K and P₁, P₂ ∈ IP_{F′} be extensions of P ∈ IP_F. Then P₂ = σ(P₁) for some σ ∈ Gal(F′/F). In other words, the Galois group acts transitively on the set of extensions of P.

## Snippets

![Stichtenoth Prop 3.1.9](snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png)

![Stichtenoth Thm 3.1.11](snippets/stichtenoth-thm-3.1.11-fundamental-equality-074.png)

![Stichtenoth Thm 3.7.1](snippets/stichtenoth-thm-3.7.1-galois-transitive-132.png)

![Lang IV.8 resultant](snippets/lang-IV.8-prop-8.1-8.3-resultant-202.png)
