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
import Divisor.Axioms.AxiomExistsDivisorMultiplicity

namespace Divisor

variable (E : ECSetup)

/-- **Principal divisor of a nonzero `D ∈ F_q[E]`**
    (Silverman AEC III Cor 3.5, specialised — partial form with
    `≤` in place of `=` in the degree identity; group-sum-zero under
    `normPoly_splits_over_Fq E D`).

    For a nonzero `D = a(x) - b(x)·y` (with `(a, b) ≠ (0, 0)`) and
    under the splitting hypothesis, there is a multiplicity function
    `β : ZMod E.q × ZMod E.q → ℕ` such that:
    * `β`'s support is contained in `D`'s affine zeros on `E`,
    * every `E`-rational affine `D`-zero is in `β`'s support,
    * `∑_{P ∈ E.points} β(P) ≤ D.degE`, and
    * the `β`-weighted group sum on `E.points` is `0`
      (the Abel-theorem content under splitting). -/
theorem CoordRingElt.has_principal_divisor
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0 := by
  obtain ⟨β, hSupp, hCov, hBound, _hAcc, hGroup⟩ :=
    CoordRingElt.exists_divisor_multiplicity E D hD
  exact ⟨β, hSupp, hCov, hBound, hGroup hSplit⟩

end Divisor
