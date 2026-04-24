/-
  Divisor/Axioms/AxiomECPointNegAddCancel.lean

  Left-inverse property of the elliptic-curve group law.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Proposition III.2.2(d), p. 51. See `axioms/ecpoint_neg_add_cancel.md` +
  `axioms/snippets/silverman-prop-III.2.2-group-law-069.png`.
-/
import Divisor.DefsPre

namespace Divisor

/-- Left inverse: `-p + p = 0`. Classical; Silverman AEC III Prop 2.2(d)
    (existence of inverse `P ⊕ (⊖P) = O`, p. 51). Follows from the
    chord-and-tangent definition (vertical line through `p` and `-p` has
    third intersection at `∞`). We keep as an axiom to avoid a case split
    on `p = -p` (2-torsion) matching the `thirdPoint` branches; downstream
    uses are abstract over this statement.

    Verbatim: *"(d) Let P ∈ E. There is a point of E, denoted by ⊖P, satisfying
    P ⊕ (⊖P) = O."* -/
axiom ECPoint.neg_add_cancel (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.add E (-p) p = (0 : ECPoint E.q)

end Divisor
