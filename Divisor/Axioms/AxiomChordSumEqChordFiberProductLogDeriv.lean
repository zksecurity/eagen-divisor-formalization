/-
  Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean

  Trace-of-log-derivative identity: sum of logDerivTerms at the three
  chord-fiber points equals the log-derivative of the chord-fiber
  product at the chord intercept.

  Reference: Lang, *Algebra* (3rd ed., GTM 211), §VI.5 Theorem 5.1
  (p. 285) + §VIII.5 Theorem 5.1 Case 1 (p. 370). See
  `axioms/chord_sum_eq_chord_fiber_product_logDeriv.md`.
-/
import Divisor.Defs
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.BivariateLogDeriv
import Divisor.FunctionFieldZ

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Trace-of-log-derivative identity

The sum of logDerivTerms at the three chord-fiber points equals the
logarithmic derivative of the chord-fiber product at the chord
intercept μ. This is the function-field trace-of-log-derivative formula:

    Tr_{L/K}(dg/g) = d(N_{L/K}(g)) / N_{L/K}(g)

specialised to `g = D`, `K = F_q(z)`, `L = F_q(E)`, and evaluated at
the chord intercept μ = zLambda λ A₀.

**Citation**: Lang, *Algebra*, 3rd ed., GTM 211, §VI.5 "The Norm and
Trace" (p. 284–285), Theorem 5.1 (multiplicativity of the norm +
product-of-embeddings `N^E_k(α) = ∏_σ σα`); combined with §VIII.5
"Derivations" (p. 369), Theorem 5.1 Case 1 (p. 370, unique extension
of a derivation to a separable algebraic extension). -/
axiom chord_sum_eq_chord_fiber_product_logDeriv
    (E : ECSetup) (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hChordNorm : (chord_fiber_product E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let μ := zLambda E lam A₀
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = eval μ (derivative (chord_fiber_product E lam D))
      / (chord_fiber_product E lam D).eval μ

end Divisor
