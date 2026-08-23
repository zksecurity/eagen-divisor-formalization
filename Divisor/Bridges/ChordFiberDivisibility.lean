/-
  Divisor/Bridges/ChordFiberDivisibility.lean

  Divisibility lower bound for the base-changed chord-fiber product.

  This is the *lower-bound* half of the divisor-of-norm pushforward
  identity for the chord projection π = y - λx : E → ℙ¹. It says
  that the chord-fibre product (the resultant), as a polynomial over
  `F_qbar`, has rootMultiplicity ≥ fibre_sum at each chord-intercept
  z that's the image of some affine zero of D.

  Proof chain (`Divisor/OrdP/`):
  * `ChordNorm.X_sub_C_pow_fiberSum_dvd_intNorm` — at every geometric
    zero `Q` of `D` above `z`, `D̄` lies in the `mult Q`-th power of
    the point ideal of the chord model `F̄[Z] → R̄`; taking
    `Ideal.relNorm` gives
    `(Z − z)^{Σ mult Q} ∣ intNorm F̄[Z] (ChordModel) D̄`.
  * `ChordResultant.intNorm_chordD_eq` — that integral norm *is* the
    base-changed chord-fibre resultant, by comparing the product over
    the embeddings `Frac(R̄) →ₐ Frac(F̄[Z])‾` (the norm) with the
    product over the roots of the chord cubic (the resultant).

  Combined with the global natDegree bound

      (chord_fiber_product_concrete D).natDegree ≤ (normPoly D).natDegree

  from `Divisor/ChordFiberWeightedDegree.lean`, the squeeze argument
  (`Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`) forces
  equality of multiplicities at every fibre.
-/
import Divisor.GeomBase
import Divisor.GeomLocalOrder
import Divisor.ChordFiberProductConcrete
import Divisor.OrdP.ChordResultant

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-- **Narrow divisor-of-norm divisibility for the concrete resultant**
(via the chord-algebra norm calculus).

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

Proof: `X_sub_C_pow_fiberSum_dvd_intNorm` (the relNorm calculus lower
bound along the chord algebra `F̄[Z] → R̄`) rewritten through
`intNorm_chordD_eq` (the norm *is* the base-changed resultant). -/
theorem chord_fiber_product_concrete_bar_zfiber_pow_dvd
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.X - Polynomial.C z) ^
      (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      ∣ (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E)) := by
  have h := X_sub_C_pow_fiberSum_dvd_intNorm E lam D hD gd z
  rwa [intNorm_chordD_eq] at h

end Divisor
