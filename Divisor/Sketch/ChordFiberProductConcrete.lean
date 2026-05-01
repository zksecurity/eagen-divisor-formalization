/-
  Divisor/Sketch/ChordFiberProductConcrete.lean

  PROTOTYPE — concrete candidate for `chord_fiber_product`.

  The current `chord_fiber_product E lam D : (ZMod E.q)[X]` is opaque
  (declared as `noncomputable opaque` in
  `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`) and
  pinned only via two axioms:

    chord_fiber_product_eq_normZ_under_split  -- proportionality to normZ
    chord_fiber_product_bar_eq_geom_prod      -- bar-level factored form

  plus a third axiom for the log-derivative identity
  (`chord_sum_eq_chord_fiber_product_logDeriv`).

  The axiom-free *concrete plumbing* (bivariate setup, base-change to
  `F_qbar`, the resultant candidate `chord_fiber_product_concrete`,
  the four already-proved evaluation/factorisation helpers, and the
  proved non-vanishing theorem) has been promoted to the production
  module `Divisor/ChordFiberProductConcrete.lean` and lives in
  `namespace Divisor`. This file now contains only the three
  outstanding `sorry`-bearing obligations against that candidate:
  `chord_fiber_product_concrete_bar_eq_geom_prod`,
  `chord_fiber_product_concrete_eq_normZ_under_split`, and
  `chord_fiber_product_concrete_logDeriv`. Each is restated against
  the production-namespace decl; the accompanying note
  `docs/chord-fiber-product-concrete-sketch.md` categorises them. -/
import Divisor.ChordFiberProductConcrete
import Divisor.FunctionFieldZ
import Divisor.GeomLocalOrder
import Divisor.LogDeriv

open Polynomial

namespace Divisor.Sketch

variable (E : ECSetup)

/-! ## Outstanding obligations against the concrete candidate

Each `theorem` below mirrors a downstream consumer of the opaque
`chord_fiber_product`. The proofs are stubbed with `sorry`; the
accompanying doc note categorises them. -/

/-- **Narrow hard lemma: chord-projection multiplicity accounting.**

This is the citable mathematical core of the old bar-factorisation axiom:
the multiplicity of a chord intercept `z` as a root of the concrete
resultant equals the sum of the local multiplicities of the geometric
`D`-zeros in the fibre `zLambdaBar = z`.

Mathematically this is the divisor-of-norm identity
`div(N_{F_qbar(E)/F_qbar(z)} D) = π_*(div D)` for the chord projection
`π = zLambdaBar`, with the right-hand side written fibrewise
(Stichtenoth Prop. 3.1.9 and Thm. 3.7.1). -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  sorry

/-- **Plumbing from multiplicity accounting to factored form.**

Once the root set is known (`ChordFiberProductConcrete` proves it) and every
root multiplicity is the sum over the corresponding geometric fibre, the
usual `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` factorisation over
the algebraically closed field `Fqbar E` gives the factored form. -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hZ : ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = Polynomial.C c * ∏ Q ∈ gd.support,
            (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  sorry

/-- **Bar-level factored form** (replacement of
`chord_fiber_product_bar_eq_geom_prod`).

*Math (deepest)*: combine `bar_eval_eq_prod` (resultant ↦ ∏ chord-root
evaluations) with the geometric divisor data: each `D`-zero `Q` in
`gd.support` contributes `gd.mult Q` factors of `(X − zLambdaBar Q)`,
because for `μ` near `zLambdaBar Q` the chord-line `y = λx + μ` passes
through `Q` (with the prescribed local order). The leading coefficient
matches `(normPoly E D).leadingCoeff` after passing through Hasse +
geom-divisor accounting. This is the divisor-of-norm formula
`div(N(D)) = π_*(div D)` for the cover
`F_qbar(E) / F_qbar(zLambdaBar lam)` (Stichtenoth Prop 3.1.9 +
Thm 3.7.1). Provable in mathlib once we have:
  (a) the inertial-degree / ramification computation for the chord
      projection (already encoded by `gd.mult` via the local-order
      machinery in `GeomLocalOrder`);
  (b) a finite product expansion for the resultant.
The hardest sub-step is (a): linking `gd.mult Q` to the multiplicity of
`zLambdaBar Q` as a root of the resultant. -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod
    (lam : ZMod E.q) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = Polynomial.C c * ∏ Q ∈ gd.support,
            (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  exact chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity E lam D hD gd
    (chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber E lam D hD gd)

/-- **Proportionality to `normZ` under splitting** (replacement of
`chord_fiber_product_eq_normZ_under_split`).

*Plumbing once `bar_eq_geom_prod` is in hand.*

Both sides are polynomials in `(ZMod E.q)[X]`. Pass to `Fqbar`; the
left factors via `bar_eq_geom_prod`, the right factors directly via the
splitting hypothesis (rational `D`-zeros = `gd.support` over the bar).
The two factored forms agree up to a leading scalar, which descends to
`ZMod E.q` since both originals do. -/
theorem chord_fiber_product_concrete_eq_normZ_under_split
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      chord_fiber_product_concrete E lam D = Polynomial.C c * normZ E lam D β_fun := by
  sorry

/-- **Log-derivative identity** (replacement of
`chord_sum_eq_chord_fiber_product_logDeriv`).

*Math (medium)*: from the resultant-as-product form
`F(μ) = ∏_{i=0,1,2} D.eval(x_i(μ), λx_i(μ) + μ)`, take the logarithmic
derivative. The implicit-function derivatives `dx_i/dμ` are determined
by differentiating the chord cubic `x_i³ − λ²x_i² + (A−2λμ)x_i + (B−μ²) = 0`,
giving `dx_i/dμ = (2λx_i + 2μ) / (3x_i² + A − 2λx_i·(dy_i/dx_i)) `; the
chain-rule combination of `D` then collapses to the `logDerivTerm`
formula already encoded in the project. The non-degeneracy hypothesis
`hDen` rules out the cusp where the implicit-function step would fail. -/
theorem chord_fiber_product_concrete_logDeriv
    (D : CoordRingElt E.q) (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂ := lam ^ 2 - A₀.1 - A₁.1
              let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hChordNorm :
      (chord_fiber_product_concrete E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let μ := zLambda E lam A₀
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = Polynomial.eval μ
        (Polynomial.derivative (chord_fiber_product_concrete E lam D))
      / (chord_fiber_product_concrete E lam D).eval μ := by
  sorry

end Divisor.Sketch
