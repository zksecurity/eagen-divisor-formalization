/-
  Divisor/Axioms/AxiomChordFiberDivisibility.lean

  Narrow divisibility axiom for the base-changed chord-fiber product.

  This is the *lower-bound* half of the divisor-of-norm pushforward
  identity for the chord projection π = y - λx : E → ℙ¹. It says
  that the chord-fibre product (the resultant), as a polynomial over
  `F_qbar`, has rootMultiplicity ≥ fibre_sum at each chord-intercept
  z that's the image of some affine zero of D.

  Combined with the global natDegree bound

      (chord_fiber_product_concrete D).natDegree ≤ (normPoly D).natDegree

  from `Divisor/ChordFiberWeightedDegree.lean`, the squeeze argument
  (`Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`) forces
  equality of multiplicities at every fibre.

  Citation: Stacks Project,
  [Lemma 42.18.1 (Principal divisors and pushforward)](https://stacks.math.columbia.edu/tag/02RS).
  Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.),
  Proposition 3.1.9 (conorm of a principal divisor is principal).
  This axiom states the lower bound of that identity coefficientwise,
  which is the local-intersection / order-of-vanishing content that
  mathlib v4.28.0 does not yet supply for the affine coordinate ring of
  an elliptic curve.
-/
import Divisor.GeomBase
import Divisor.GeomLocalOrder
import Divisor.ChordFiberProductConcrete

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-- **Narrow divisor-of-norm divisibility axiom for the concrete resultant.**

For each chord-intercept `z : F_qbar`, the chord-fibre product (the
concrete resultant), as a polynomial over `F_qbar`, is divisible by
`(X - C z)^(fibre_sum)` where `fibre_sum` is the sum of geometric
multiplicities at the points `Q ∈ gd.support` projecting to `z` under
`zLambdaBar lam`.

Human-readable version: under the chord projection `pi_lam`, every
geometric zero `Q` of `D` contributes its local multiplicity to the
zero divisor of the norm at `pi_lam(Q)`. After collecting all zeros in
one fibre over `z`, the factor `(X - z)` divides the chord-fibre
resultant to at least the summed multiplicity of that fibre.

This is the lower-bound (≥) half of the divisor-of-norm pushforward
identity at the place `(z)` of `F_qbar(zLambdaBar lam)`. The matching
upper bound is the global natDegree inequality
(`chord_fiber_product_concrete_natDegree_le_normPoly_natDegree` in
`Divisor/ChordFiberWeightedDegree.lean` via weighted Sylvester
analysis).

The k=1 case (single linear factor at each fibre) follows from
`chord_fiber_product_concrete_bar_X_sub_C_zLambda_pow_one_dvd_of_mem_support`.
This axiom encapsulates the higher-multiplicity cases (k ≥ 2): when
the affine multiplicities at points in the fibre sum to ≥ 2, the
chord-projection norm absorbs that multiplicity. Mathematically this
follows from the local form of Stacks 02RS at each closed point of
ℙ¹; in Lean it is the local-intersection content not yet supplied by
mathlib v4.28.0. -/
axiom chord_fiber_product_concrete_bar_zfiber_pow_dvd
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.X - Polynomial.C z) ^
      (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      ∣ (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E))

end Divisor
