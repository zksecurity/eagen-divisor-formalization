/-
  Divisor/Axioms/AxiomChordFiberProductBarFactorisation.lean

  Geometric divisor-of-norm identity: over the algebraic closure of
  `F_q`, the base-change of `chord_fiber_product` factors completely
  into linear factors corresponding to the geometric zero divisor.

  Reference: Stichtenoth, *Algebraic Function Fields and Codes* (GTM
  254, 2nd ed.), Proposition 3.1.9 (p. 73) + Theorem 3.7.1 (p. 121),
  applied to `F'/F = F_qbar(E)/F_qbar(z)` instead of
  `F_q(E)/F_q(z)`. Over the algebraic closure the splitting is
  automatic, so the formula has no `splitsOnE`-style hypothesis.

  This is the geometric counterpart of
  `chord_fiber_product_eq_normZ_under_split`: the latter relates
  `chord_fiber_product` to `normZ` under `splitsOnE`; this version
  relates the base-changed `chord_fiber_product` to a `Fqbar`-valued
  product over `gd.support` with no splittedness assumption.
-/
import Divisor.Defs
import Divisor.GeomBase
import Divisor.GeomLocalOrder
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Divisor-of-norm formula at the algebraic closure

Over `F_qbar`, the chord-fiber product `N_{F_qbar(E)/F_qbar(z)}(D)`
factors completely:

  `chord_fiber_product_bar = c · ∏ Q ∈ gd.support, (X − zLambdaBar Q)^(mult Q)`

with `c ∈ F_qbar^×`.

**Reasoning.** Stichtenoth Prop 3.1.9 (the conorm identity) plus
Thm 3.7.1 (transitivity of the Galois action on places) yield, for
any algebraic extension `F′/F` of function fields and `0 ≠ x ∈ F′`,

  `div_F(N_{F′/F}(x)) = "Tr on divisors"(div_{F′}(x))`.

Applied to `F′/F = F_qbar(E)/F_qbar(z)` and `x = D`, this identifies
the divisor of `N_{F_qbar(E)/F_qbar(z)}(D)` with the projection of
`div_{F_qbar(E)}(D)` to `F_qbar(z)`. Splitting is automatic in
`F_qbar`, so every geometric zero contributes exactly one linear
factor with the geometric local-order multiplicity (= `gd.mult Q`)
to `N(D)(z)`. The leading coefficient `c` is the leading coefficient
of `(normPolyBar E D)` in `Fqbar`. -/
axiom chord_fiber_product_bar_factorisation
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)

end Divisor
