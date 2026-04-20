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
  * `∑_{P ∈ E.points} β(P) = D.degE`, and
  * the `β`-weighted group sum on `E.points` vanishes.

  The witness is `β := betaConstructive E D` (QB1). The four properties
  are the QB1 lemmas `betaConstructive_support`, `betaConstructive_covers`
  plus the QB2 derived theorems `betaConstructive_sum_eq_degE` and
  `betaConstructive_group_sum_zero`.

  This module keeps downstream code unchanged: it re-exposes the exact
  signature that `Divisor/Axioms.lean` used to state as an axiom.
-/
import Divisor.Defs
import Divisor.BetaConstructive

namespace Divisor

variable (E : ECSetup)

/-- **Principal divisor of a nonzero `D ∈ F_q[E]`**
    (Silverman Ch III, Prop 3.4 + Cor 3.5, specialized).

    For a nonzero `D = a(x) - b(x)·y` (with `(a, b) ≠ (0, 0)`), there is
    a multiplicity function `β : ZMod E.q × ZMod E.q → ℕ` such that:
    * `β`'s support is contained in `D`'s affine zeros on `E`,
    * every `E`-rational affine `D`-zero is in `β`'s support,
    * `∑_{P ∈ E.points} β(P) = D.degE`, and
    * the `β`-weighted group sum on `E.points` is `0`
      (the Abel-theorem content).

    Previously an axiom; now derived from the constructive
    `betaConstructive E D` (QB1) together with the narrow
    `CoordRingElt.divisor_degree_eq` and
    `CoordRingElt.divisor_group_sum_zero` axioms (QB2). -/
theorem CoordRingElt.has_principal_divisor
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) = D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) = 0 := by
  refine ⟨betaConstructive E D, ?_, ?_, ?_, ?_⟩
  · exact fun P hP => betaConstructive_support E D P hP
  · exact fun P hP hZ => betaConstructive_covers E D hD P hP hZ
  · exact betaConstructive_sum_eq_degE E D hD
  · exact betaConstructive_group_sum_zero E D hD

end Divisor
