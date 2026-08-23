/-
  Divisor/SplitsOnE.lean

  The `splitsOnE` predicate.

  Lives in its own module so that both the existence theorem in
  `Divisor/Bridges/DivisorMultiplicity.lean` and its underlying proof
  in `Divisor.OrdP.LocalRing` can refer to `splitsOnE` without an
  import cycle.

  `normPoly_splits_over_Fq E D` only requires that `normPoly E D`
  splits as a univariate polynomial in `X` over `F_q`. That is *not*
  enough to make the F_q-restricted accounting / group-sum clauses
  sound: a root `α` of `normPoly E D` carries no F_q-mass if there are
  no F_q-rational `(α, y) ∈ E.points`.

  The stronger predicate `splitsOnE E D` adds the missing fiber-
  rationality condition: every root of `normPoly E D` lifts to at
  least one F_q-rational point of `E`.
-/
import Divisor.Defs
import Divisor.BetaConstructive

namespace Divisor

variable (E : ECSetup)

/-- `splitsOnE E D` ↔ `normPoly E D` splits over F_q AND every root
    of `normPoly E D` is the x-coordinate of some F_q-point of E. -/
def splitsOnE (D : CoordRingElt E.q) : Prop :=
  normPoly_splits_over_Fq E D ∧
  (∀ α ∈ (normPoly E D).roots, ∃ y : ZMod E.q, (α, y) ∈ E.points)

theorem splitsOnE.toSplits {D : CoordRingElt E.q}
    (h : splitsOnE E D) : normPoly_splits_over_Fq E D := h.1

theorem splitsOnE.fiber {D : CoordRingElt E.q}
    (h : splitsOnE E D) :
    ∀ α ∈ (normPoly E D).roots, ∃ y : ZMod E.q, (α, y) ∈ E.points := h.2

end Divisor
