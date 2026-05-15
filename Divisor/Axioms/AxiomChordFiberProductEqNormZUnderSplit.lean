/-
  Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean

  Divisor-of-norm identity: under splitting + accounting, the chord-
  fiber product equals a nonzero constant multiple of `normZ`.

  This statement is now a theorem (proved via the bridge file
  `Divisor/Bridges/ChordFiberProductEqNormZUnderSplit.lean`), not an
  axiom.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Divisor.FunctionFieldZ
import Divisor.ChordFiberProductConcrete
import Divisor.Bridges.ChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomExistsDivisorMultiplicity

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-- The chord-fiber product: `∏ᵢ D(Aᵢ(z))` as a polynomial in `z`.

    This is the concrete resultant of the chord cubic against the
    D-on-line lift, i.e. the function-field norm candidate
    `N_{F_q(E)/F_q(z)}(D)`. -/
noncomputable def chord_fiber_product
    (E : ECSetup) (lam : ZMod E.q) (D : CoordRingElt E.q) : (ZMod E.q)[X] :=
  chord_fiber_product_concrete E lam D

/-! ## Divisor-of-norm formula

Under the splitting and pointwise true-multiplicity hypotheses, the
chord-fiber product ∏ᵢ D(Aᵢ(z)) (the function-field norm) equals a
nonzero constant times normZ(z). Both polynomials have the same roots
with the same multiplicities: the norm's roots are the z-coordinates of
D's zeros on E, with multiplicities matching `betaTrue`.

This is the divisor-of-norm pushforward identity `div(Nm(f))` =
pushforward of `div(f)`, specialised to the chord projection: under the
splitting hypothesis the roots and multiplicities of N(D)(z) match
those of normZ(z), establishing proportionality. -/
/-- **Chord-fiber product as a constant multiple of `normZ` under
    splitting + accounting.**

    Parameterised over a multiplicity function `β_fun`, with an explicit
    pointwise hypothesis that `β_fun` is the true local-order witness
    `betaTrue E D hD`. Support, coverage, total accounting, and
    pointwise truth are all explicit because support and total accounting
    alone do not determine local multiplicities.

    Human-readable version: if the zeros of `D` split over `E(F_q)` and
    `β_fun` is the true local multiplicity function, then the chord-fiber
    product, viewed as the norm of `D` along the chord projection, has the
    same zero divisor as `normZ E lam D β_fun`; therefore the two
    polynomials differ by a nonzero scalar.

    The explicit `hβtrue` hypothesis prevents substituting a
    support-only or degree-only surrogate for the local-order
    multiplicity function. -/
theorem chord_fiber_product_eq_normZ_under_split
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      chord_fiber_product E lam D = C c * normZ E lam D β_fun := by
  simpa [chord_fiber_product] using
    chord_fiber_product_concrete_eq_normZ_under_split
      E D lam hD hSplitOnE β_fun hβsup hβcov hAccount hβtrue

end Divisor
