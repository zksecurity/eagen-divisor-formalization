/-
  Divisor/Axioms/AxiomECPointAddComm.lean

  Commutativity of the elliptic-curve group law.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Proposition III.2.2(c), p. 51. See `axioms/ecpoint_add_comm.md` +
  `axioms/snippets/silverman-prop-III.2.2-group-law-069.png`.
-/
import Divisor.DefsPre

namespace Divisor

/-- Commutativity of `ECPoint.add`. Classical; Silverman AEC III Prop 2.2(c)
    (commutativity of the composition law `P ⊕ Q = Q ⊕ P`, p. 51).

    Verbatim: *"(c) P ⊕ Q = Q ⊕ P for all P, Q ∈ E."* -/
axiom ECPoint.add_comm (E : ECSetup) (p q : ECPoint E.q) :
    ECPoint.add E p q = ECPoint.add E q p

end Divisor
