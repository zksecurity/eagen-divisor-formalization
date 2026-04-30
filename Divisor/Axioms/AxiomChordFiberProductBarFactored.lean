/-
  Divisor/Axioms/AxiomChordFiberProductBarFactored.lean

  Narrow factored-form bridge for the base-changed chord-fiber product.

  Over `F_qbar`, the chord-fiber product of `D` (a function-field norm
  for the extension `F_qbar(E) / F_qbar(zLambdaBar lam)`) splits as a
  nonzero scalar times a product of linear factors indexed by the
  geometric support of `D`. Local multiplicities are the geometric
  divisor multiplicities.

  Reference: same as `AxiomChordFiberProductEqNormZUnderSplit`
  (Stichtenoth, *Algebraic Function Fields and Codes*, GTM 254,
  Proposition 3.1.9 + Theorem 3.7.1). Mathematically: the divisor of
  the norm equals the push-forward of the divisor of `D`. Over an
  algebraically closed base, the push-forward zero divisor unfolds
  into linear factors with multiplicities equal to `gd.mult Q`. The
  remaining unit is a nonzero leading scalar.

  This is a strictly narrower obligation than the previously bundled
  `chord_fiber_product_bar_factorisation` theorem in
  `Divisor/GeometricSoundness.lean`: the bundled theorem is now
  derivable from this axiom, and so are the per-place
  `chord_fiber_product_bar_rootMultiplicity_eq_zfiber` and the
  rational `chord_fiber_product_ne_zero` (via injectivity of the
  algebraMap base-change), so the dependency direction is

      this axiom  ⇒  rootMultiplicity_eq_zfiber  ⇒  z_fiber_accounting

  rather than the previous

      ne_zero  +  rootMultiplicity_eq_zfiber  ⇒  z_fiber_accounting
                                            ⇒  factorisation.

  No projection / accounting hypotheses are needed in the statement;
  the geometric data carried by `gd` (a `GeometricDivisorData E D`)
  already pins them down.
-/
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.GeomBase
import Divisor.GeomLocalOrder

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-- **Geometric factored-form bridge for the chord-fiber product.**

    Over `F_qbar`, the base-changed chord-fiber product of a nonzero
    `D` splits as a nonzero leading scalar times a product of linear
    factors `(X - C (zLambdaBar E lam Q))^(gd.mult Q)` indexed by the
    geometric support of `D`.

    This is the divisor-of-norm formula
    `div(N(D)) = π_*(div D)` for the function-field extension
    `F_qbar(E) / F_qbar(zLambdaBar lam)`, evaluated globally over the
    algebraically closed base: every prime divisor of the base is a
    `(z)` for some `z : F_qbar`, the push-forward zero divisor is
    `∑_Q gd.mult Q · (zLambdaBar Q)`, and the principal divisor of
    the norm reads back as the product of linear factors above.

    Local multiplicities and the global non-vanishing follow from this
    bridge alone (see `chord_fiber_product_bar_rootMultiplicity_eq_zfiber`
    and `chord_fiber_product_ne_zero` in `Divisor/GeometricSoundness.lean`).
-/
axiom chord_fiber_product_bar_eq_geom_prod
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)

end Divisor
