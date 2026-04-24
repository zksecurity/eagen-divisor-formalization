/-
  Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean

  Divisor-of-norm identity: under splitting + accounting, the chord-
  fiber product equals a nonzero constant multiple of `normZ`.

  Reference: Stichtenoth, *Algebraic Function Fields and Codes* (GTM
  254, 2nd ed.), Proposition 3.1.9 (p. 73) + Theorem 3.7.1 (p. 121).
  See `axioms/chord_fiber_product_eq_normZ_under_split.md`.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Divisor.FunctionFieldZ

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-- The chord-fiber product: ∏ᵢ D(Aᵢ(z)) as a polynomial in z.
    Represents the function-field norm N_{F_q(E)/F_q(z)}(D).

    Left opaque: concrete construction requires resultant infrastructure
    (Sylvester matrix over three sheets) beyond current scope. The axiom
    `chord_fiber_product_eq_normZ_under_split` captures the key property
    the proof needs. -/
noncomputable opaque chord_fiber_product (E : ECSetup) (lam : ZMod E.q) (D : CoordRingElt E.q) : (ZMod E.q)[X]

/-! ## Divisor-of-norm formula (Stichtenoth Prop 3.1.9 + Thm 3.7.1)

Under the splitting and accounting hypotheses, the chord-fiber product
∏ᵢ D(Aᵢ(z)) (the function-field norm) equals a nonzero constant times
normZ(z). Both polynomials have the same roots with the same
multiplicities: the norm's roots are the z-coordinates of D's zeros on
E, with multiplicities matching `betaConstructive`.

**Citation**: Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., GTM 254, Proposition 3.1.9 (p. 73) — the conorm of a
principal divisor is a principal divisor:
  `Con_{F'/F}(div(x)) = div_{F'}(x)`,
together with the norm map `N_{F'/F}` (defined in Appendix A, used in
§3.7 Theorem 3.7.1, p. 121) which sends a function in F' to its
product of Galois conjugates in F. The divisor-of-norm identity, for
`y ∈ F'`,
  `div_F(N_{F'/F}(y)) = "Tr on divisors"(div_{F'}(y))`,
identifies (under the splitting hypothesis) the roots and
multiplicities of N(D)(z) with those of normZ(z), establishing
proportionality.

**Textbook statement (verbatim), Stichtenoth Proposition 3.1.9, p. 73:**

> "Proposition 3.1.9. Let F′/K′ be an algebraic extension of the
> function field F/K. For 0 ≠ x ∈ F let (x)₀^F, (x)∞^F, (x)^F resp.
> (x)₀^{F′}, (x)∞^{F′}, (x)^{F′} denote the zero, pole, principal
> divisor of x in Div(F) resp. in Div(F′). Then
>   Con_{F′/F}((x)₀^F) = (x)₀^{F′},
>   Con_{F′/F}((x)∞^F) = (x)∞^{F′},   and
>   Con_{F′/F}((x)^F)  = (x)^{F′}."

**Textbook statement (verbatim), Stichtenoth Theorem 3.7.1, p. 121:**

> "Theorem 3.7.1. Let F′/K′ be a Galois extension of F/K and
> P₁, P₂ ∈ IP_{F′} be extensions of P ∈ IP_F. Then P₂ = σ(P₁) for
> some σ ∈ Gal(F′/F). In other words, the Galois group acts
> transitively on the set of extensions of P." -/
axiom chord_fiber_product_eq_normZ_under_split
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree) :
    ∃ c : ZMod E.q, c ≠ 0 ∧ chord_fiber_product E lam D = C c * normZ E lam D

end Divisor
