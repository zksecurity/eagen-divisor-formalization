/-
  Divisor/HasPrincipalDivisor.lean

  `CoordRingElt.has_principal_divisor` packages four facts about a
  nonzero `D = a(x) - b(x)·y ∈ F_q[E]`:
  * there is a multiplicity function `β : ZMod E.q × ZMod E.q → ℕ`
    supported on `D`'s affine zeros on `E`,
  * `β` covers every `E`-rational `D`-zero,
  * `∑_{P ∈ E.points} β(P) ≤ D.degE`, and
  * the `β`-weighted group sum on `E.points` vanishes.

  The witness is supplied existentially by
  `CoordRingElt.exists_divisor_multiplicity` (the true ord_P
  divisor of `D`), not `betaConstructive` — the latter's twin-sheet
  Nat-division surrogate is provably non-faithful to ord_P and
  fails the group-sum-zero condition over F_5.
-/
import Divisor.Defs
import Divisor.Bridges.DivisorMultiplicity

namespace Divisor

variable (E : ECSetup)

/-- **Principal divisor of a nonzero `D ∈ F_q[E]`**
    (Silverman AEC III Cor 3.5, specialised).

    Requires `splitsOnE E D` (the strengthening of
    `normPoly_splits_over_Fq` that adds fiber-rationality of every
    root of `normPoly E D`) — this is the precondition under which
    the F_q-restricted accounting / group-sum-zero clauses can hold. -/
theorem CoordRingElt.has_principal_divisor
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0 := by
  obtain ⟨β, hSupp, hCov, hBound, _hAcc, hGroup⟩ :=
    CoordRingElt.exists_divisor_multiplicity E D hD
  exact ⟨β, hSupp, hCov, hBound, hGroup hSplitOnE⟩

end Divisor
