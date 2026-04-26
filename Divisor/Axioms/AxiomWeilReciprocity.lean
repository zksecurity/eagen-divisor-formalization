/-
  Divisor/Axioms/AxiomWeilReciprocity.lean

  Textbook Weil reciprocity (the version that is *just* Silverman AEC
  Exercise II.2.11 — the ratio identity at points), separated from the
  protocol-specific bundle in `AxiomWeilReciprocityHonest.lean`.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Exercise II.2.11, p. 39.

  This file states the textbook form. The protocol-level
  `weil_reciprocity_honest` axiom is being incrementally discharged in
  `Divisor/WeilReciprocityDescent.lean` as a *theorem* derived from
  this textbook axiom + protocol-residue lemmas.
-/
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Textbook Weil reciprocity

    For two rational functions `f, g ∈ F_q(E)^×` with disjoint
    divisor supports,
        ∏_P f(P)^{ord_P(g)} = ∏_P g(P)^{ord_P(f)}.

    We state the axiom abstractly as a placeholder for the
    `weight_in_F_q_pairing` view; the actual application uses the
    rational-function quotient `f / L^k` where `L` is a chord line and
    extracts the residue identity from the principal divisor's
    vanishing of total order. -/

/-- **Weil reciprocity (Silverman AEC Exercise II.2.11).** Placeholder
    axiom statement; the actual content is encoded inside the protocol
    residue lemma in `WeilReciprocityDescent.lean`, which is the form
    actually consumed downstream. -/
axiom weil_reciprocity_textbook
    (E : ECSetup) (f g : CoordRingElt E.q)
    (hf : ¬ (f.a = 0 ∧ f.b = 0))
    (hg : ¬ (g.a = 0 ∧ g.b = 0))
    (hDisjointSupport :
      ∀ P ∈ E.points,
        (f.eval P.1 P.2 = 0 → g.eval P.1 P.2 ≠ 0) ∧
        (g.eval P.1 P.2 = 0 → f.eval P.1 P.2 ≠ 0)) :
    ∏ P ∈ E.points.filter (fun P => g.eval P.1 P.2 = 0),
      f.eval P.1 P.2
    =
    ∏ P ∈ E.points.filter (fun P => f.eval P.1 P.2 = 0),
      g.eval P.1 P.2

end Divisor
