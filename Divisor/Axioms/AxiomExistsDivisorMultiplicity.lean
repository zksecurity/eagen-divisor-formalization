/-
  Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean

  Existential "true divisor multiplicity" axiom.

  History:
  * v1 (retired): asserted the β-weighted group sum on `betaConstructive E D`
    is zero under polynomial-splitting. False on F_5 — the constructive β
    Nat-divides twin-sheet root multiplicities, losing the per-sheet split
    that the group sum is sensitive to.
  * v2 (the previous form of this axiom): replaced v1's β by an existential,
    but still gated the deeper clauses (accounting + group-sum-zero) on
    `normPoly_splits_over_Fq E D` alone — i.e. only on `normPoly E D`'s
    splitting AS A POLYNOMIAL IN `X`. Also unsound: when an x-root α of
    `normPoly E D` corresponds to no F_q-rational `(α, y)` on `E` (the
    fiber `α³ + Aα + B` not being a QR in F_q), the F_q-only sum cannot
    pick up its multiplicity, so accounting `Σ β = natDeg` is forced
    false.  Concrete failure: `E : y² = x³ + 1 / F_5`, `D = X − 1`;
    `normPoly E D = (X−1)²` splits and has natDeg 2, but `2 = 1+1` is
    not a square in F_5, so no F_5-points have x = 1 and `Σ β = 0 ≠ 2`.
  * v3 (current): gates the accounting and group-sum-zero clauses on a
    *stronger* hypothesis `splitsOnE E D` that adds the missing
    fiber-rationality condition.

  Reference:
  Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Corollary III.3.5, p. 63 (Abel's theorem) + II §1 (local orders).

  Phase-1 plan (now realised): this existence statement is no longer
  asserted as an axiom but proved as a theorem with witness
  `ordAt E D`, derived from the narrower principal-divisor bridge
  axiom `ordAt_divisor_isPrincipal`. The theorem
  `Divisor.exists_divisor_multiplicity_proved` lives in
  `Divisor/OrdP/LocalRing.lean`; this file re-exports it under the
  legacy name `CoordRingElt.exists_divisor_multiplicity` so that
  downstream `betaTrue` / `betaCanonical` consumers continue to work
  unchanged. Importing `Divisor.OrdP.LocalRing` here is safe because
  `splitsOnE` was extracted into `Divisor.SplitsOnE` to break the
  prior import cycle.
-/
import Divisor.Defs
import Divisor.BetaConstructive
import Divisor.SplitsOnE
import Divisor.OrdP.LocalRing

namespace Divisor

variable (E : ECSetup)

/-- **Existence of true divisor multiplicity** (Silverman AEC III Cor
    3.5 + II §1, specialised to `D = a(x) - b(x)·y ∈ F_q[E]^×`).

    For a nonzero `D`, there is a multiplicity function
    `β : ZMod E.q × ZMod E.q → ℕ` such that:
    * `β` is supported on `D`'s affine zeros on `E`;
    * `β` covers every `E`-rational `D`-zero;
    * `Σ β ≤ D.degE` (unconditionally — degree of N(D));
    * under `splitsOnE E D` (full polynomial-splitting AND fiber-
      rationality of every root over F_q),
        `Σ β = (normPoly E D).natDegree` (pole-at-∞ accounting), and
    * under `splitsOnE E D`,
        the β-weighted group sum on `E.points` is `O` (Abel's theorem).

    Proved via `exists_divisor_multiplicity_proved` (witness
    `ordAt E D`); the only remaining axiom in the dependency closure
    of this statement is `ordAt_divisor_isPrincipal` (the narrower
    principal-divisor bridge for `divisorOfD E D`). -/
theorem CoordRingElt.exists_divisor_multiplicity
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (splitsOnE E D →
        (∑ P ∈ E.points, β P) = (normPoly E D).natDegree) ∧
      (splitsOnE E D →
        ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0) :=
  exists_divisor_multiplicity_proved E D hD

/-! ## `betaTrue`: a fixed canonical witness from the existence axiom -/

/-- Canonical "true divisor multiplicity" for `D = a − by ∈ F_q[E]^×`,
    obtained by `Classical.choose` of `exists_divisor_multiplicity`. -/
noncomputable def betaTrue (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ZMod E.q × ZMod E.q → ℕ :=
  Classical.choose (CoordRingElt.exists_divisor_multiplicity E D hD)

theorem betaTrue_support (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∀ P, betaTrue E D hD P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0 :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).1

theorem betaTrue_covers (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → betaTrue E D hD P ≠ 0 :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.1

theorem betaTrue_sum_le_degE (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (∑ P ∈ E.points, betaTrue E D hD P) ≤ D.degE :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.2.1

theorem betaTrue_account (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D) :
    (∑ P ∈ E.points, betaTrue E D hD P) = (normPoly E D).natDegree :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.2.2.1 hSplitOnE

theorem betaTrue_group_sum_zero (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaTrue E D hD P)
                  (ECPoint.affine E P.1 P.2)) = 0 :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.2.2.2 hSplitOnE

/-! ## `betaCanonical`: totalised `betaTrue` -/

/-- Totalised true divisor multiplicity. -/
noncomputable def betaCanonical (E : ECSetup) (D : CoordRingElt E.q) :
    ZMod E.q × ZMod E.q → ℕ :=
  if hD : ¬ (D.a = 0 ∧ D.b = 0) then betaTrue E D hD else fun _ => 0

theorem betaCanonical_eq_betaTrue (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    betaCanonical E D = betaTrue E D hD := by
  unfold betaCanonical
  rw [dif_pos hD]

theorem betaCanonical_eq_zero (E : ECSetup)
    (D : CoordRingElt E.q) (hD : D.a = 0 ∧ D.b = 0) :
    betaCanonical E D = fun _ => 0 := by
  unfold betaCanonical
  rw [dif_neg]
  exact fun h => h hD

theorem betaCanonical_support (E : ECSetup) (D : CoordRingElt E.q) :
    ∀ P, betaCanonical E D P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0 := by
  intro P hP
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD] at hP
    exact betaTrue_support E D hD P hP
  · push_neg at hD
    rw [betaCanonical_eq_zero E D hD] at hP
    exact absurd rfl hP

theorem betaCanonical_covers (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → betaCanonical E D P ≠ 0 := by
  rw [betaCanonical_eq_betaTrue E D hD]
  exact betaTrue_covers E D hD

theorem betaCanonical_sum_le_degE (E : ECSetup) (D : CoordRingElt E.q) :
    (∑ P ∈ E.points, betaCanonical E D P) ≤ D.degE := by
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD]
    exact betaTrue_sum_le_degE E D hD
  · push_neg at hD
    rw [betaCanonical_eq_zero E D hD]
    simp

theorem betaCanonical_account (E : ECSetup)
    (D : CoordRingElt E.q)
    (hSplitOnE : splitsOnE E D) :
    (∑ P ∈ E.points, betaCanonical E D P) = (normPoly E D).natDegree := by
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD]
    exact betaTrue_account E D hD hSplitOnE
  · push_neg at hD
    -- D = 0: normPoly = 0, both sides are 0.
    rw [betaCanonical_eq_zero E D hD]
    have hZero : normPoly E D = 0 := by
      rw [normPoly_eq, hD.1, hD.2]; ring
    rw [hZero, Polynomial.natDegree_zero]
    simp

theorem betaCanonical_group_sum_zero (E : ECSetup)
    (D : CoordRingElt E.q)
    (hSplitOnE : splitsOnE E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaCanonical E D P)
                  (ECPoint.affine E P.1 P.2)) = 0 := by
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD]
    exact betaTrue_group_sum_zero E D hD hSplitOnE
  · push_neg at hD
    rw [betaCanonical_eq_zero E D hD]
    apply Finset.sum_eq_zero
    intro P _
    exact ECPoint.nsmul_zero E _

end Divisor
