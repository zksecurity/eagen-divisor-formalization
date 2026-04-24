/-
  Divisor/Axioms/AxiomECPointAddAssoc.lean

  Associativity of the elliptic-curve group law.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Proposition III.2.2(e), p. 51. See `axioms/ecpoint_add_assoc.md` +
  `axioms/snippets/silverman-prop-III.2.2-group-law-069.png`.

  Silverman's proof (p. 59-61) goes via Proposition III.3.4(e): the
  Abel-Jacobi map σ : Pic⁰(E) → E is a group isomorphism, reducing
  associativity of ⊕ to associativity in Pic⁰(E).
-/
import Divisor.DefsPre

namespace Divisor

/-- Associativity of `ECPoint.add`. Classical; Silverman AEC III Prop 2.2(e)
    (`(P ⊕ Q) ⊕ R = P ⊕ (Q ⊕ R)`, p. 51). The nontrivial group-law
    axiom — Silverman's proof uses the Riemann-Roch / divisor-class
    equivalence via the σ-isomorphism (AEC III Prop 3.4(e)).

    Verbatim: *"(e) Let P, Q, R ∈ E. Then (P ⊕ Q) ⊕ R = P ⊕ (Q ⊕ R)."* -/
axiom ECPoint.add_assoc (E : ECSetup) (p q r : ECPoint E.q) :
    ECPoint.add E (ECPoint.add E p q) r = ECPoint.add E p (ECPoint.add E q r)

end Divisor
