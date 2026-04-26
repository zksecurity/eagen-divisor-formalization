/-
  Divisor/HasPrincipalDivisor.lean

  Queue-2 Phase-B step QB3: derive `CoordRingElt.has_principal_divisor`
  as a THEOREM from the Queue-2 artifacts, eliminating the previous
  axiom of the same name in `Divisor/Axioms.lean`.

  The statement packages four facts about a nonzero
  `D = a(x) - b(x)·y ∈ F_q[E]`:
  * there is a multiplicity function `β : ZMod E.q × ZMod E.q → ℕ`
    supported on `D`'s affine zeros on `E`,
  * `β` covers every `E`-rational `D`-zero,
  * `∑_{P ∈ E.points} β(P) ≤ D.degE`, and
  * the `β`-weighted group sum on `E.points` vanishes.

  The witness is `β := betaConstructive E D` (QB1). The four properties
  are the QB1 lemmas `betaConstructive_support`, `betaConstructive_covers`,
  the QB2 unconditional bound `betaConstructive_sum_le_degE` (≤, not =
  — see `docs/divisor-degree-axiom-bug.md`), and the QB2 derived theorem
  `betaConstructive_group_sum_zero` (requires `normPoly_splits_over_Fq E D`
  so it matches Silverman AEC III Cor 3.5 exactly — without splitting,
  F_q-restricted sums miss Frobenius-conjugate orbit contributions, so
  the F_q-sum identity is strictly weaker than Cor 3.5's F̄_q-sum).

  This module keeps downstream code shape-compatible: it re-exposes
  the signature that `Divisor/Axioms.lean` used to state as an axiom,
  modulo the degree-sum being an inequality instead of an equality and
  the splitting precondition on the group-sum-zero component.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Divisor.Axioms.AxiomCoordRingEltDivisorGroupSumZero

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
      (the Abel-theorem content under splitting).

    Previously an axiom with `=` in the third clause and no splitting
    precondition; the equality direction was falsified by Aristotle's
    counterexample (see `docs/divisor-degree-axiom-bug.md`) and is now
    weakened to `≤`. The group-sum-zero clause inherits the splitting
    hypothesis from `betaConstructive_group_sum_zero`, which is the
    F_q-restricted specialisation of Silverman AEC III Cor 3.5 that is
    valid precisely when every geometric zero of `D` descends to
    `E(F_q)` (no Frobenius-conjugate orbits missed). -/
theorem CoordRingElt.has_principal_divisor
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0 := by
  refine ⟨betaConstructive E D, ?_, ?_, ?_, ?_⟩
  · exact fun P hP => betaConstructive_support E D P hP
  · exact fun P hP hZ => betaConstructive_covers E D hD P hP hZ
  · exact betaConstructive_sum_le_degE E D
  · exact betaConstructive_group_sum_zero E D hD hSplit

end Divisor
