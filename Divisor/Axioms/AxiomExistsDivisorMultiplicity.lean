/-
  Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean

  Existential "true divisor multiplicity" axiom.

  Replaces the (unsound) `CoordRingElt.divisor_group_sum_zero` axiom,
  which had asserted the *β-weighted* group sum on
  `betaConstructive E D` to be zero.  That assertion is provably false:
  on `E : y² = x³ + 1 / F_5` with `D = (x²+1) - (1+2x)·y`, normPoly
  splits over F_5 (so the splitting hypothesis holds), `Σ β = natDeg
  N(D) = 5`, yet the β-weighted group sum is `(0,1) ≠ O`.  The cause:
  `betaConstructive` distributes twin-sheet root-multiplicity evenly
  by `rootMult / 2` (Nat division), losing the per-sheet split that
  the group sum is sensitive to.  The TRUE divisor of D on E uses
  the actual local orders ord_P(D), which here are 1, 3, 1 at
  (0,1), (2,2), (2,3) respectively, and the group sum 1·(0,1) +
  3·(2,2) + 1·(2,3) = O as Abel's theorem requires.

  This axiom asserts the existence of a multiplicity function with
  the four divisor properties: support, coverage, the unconditional
  total-degree bound, and (under the splitting hypothesis) the
  pole-at-∞ accounting identity together with Abel's theorem
  group-sum-zero.  Such a function exists classically — it is the
  point-by-point order ord_P(D) of the rational function D on the
  smooth elliptic curve E (Silverman, AEC, II §1 + III Cor 3.5).

  Reference:
  Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Corollary III.3.5, p. 63 (Abel's theorem) + II §1 (local orders).

  Phase-1 plan: this axiom is intended to be discharged by
  mechanising ord_P from uniformizers and deriving the existential
  via `principal_divisor_iff` applied to `div(D)`.
-/
import Divisor.Defs
import Divisor.BetaConstructive

namespace Divisor

variable (E : ECSetup)

/-- **Existence of true divisor multiplicity** (Silverman AEC III Cor
    3.5 + II §1, specialised to `D = a(x) - b(x)·y ∈ F_q[E]^×`).

    For a nonzero `D`, there is a multiplicity function
    `β : ZMod E.q × ZMod E.q → ℕ` such that:
    * `β` is supported on `D`'s affine zeros on `E`;
    * `β` covers every `E`-rational `D`-zero;
    * `Σ β ≤ D.degE` (unconditionally — degree of N(D));
    * under `normPoly_splits_over_Fq E D`,
        `Σ β = (normPoly E D).natDegree` (pole-at-∞ accounting), and
    * under `normPoly_splits_over_Fq E D`,
        the β-weighted group sum on `E.points` is `O` (Abel's theorem).

    The classical witness is `β = fun P => (ord_P D).toNat` for
    affine F_q-rational P (Silverman II §1.1, local discrete
    valuation at a smooth point).  Under splitting every geometric
    zero of D is F_q-rational, so this β picks up the full
    `Σ_{P ∈ E(F̄_q)} ord_P(D)·(P)` of Cor 3.5 and Abel's theorem
    descends. -/
axiom CoordRingElt.exists_divisor_multiplicity
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (normPoly_splits_over_Fq E D →
        (∑ P ∈ E.points, β P) = (normPoly E D).natDegree) ∧
      (normPoly_splits_over_Fq E D →
        ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0)

/-! ## `betaTrue`: a fixed canonical witness from the existence axiom

    Defined as `Classical.choose` of the existence axiom, so the choice
    is deterministic across uses (one call to `Classical.choose` per
    `(D, hD)` pair). All downstream theorems that need a specific
    "true divisor multiplicity" function thread through `betaTrue`,
    avoiding the need to parameterise every consumer over an arbitrary
    β_fun. -/

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
    (hSplit : normPoly_splits_over_Fq E D) :
    (∑ P ∈ E.points, betaTrue E D hD P) = (normPoly E D).natDegree :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.2.2.1 hSplit

theorem betaTrue_group_sum_zero (E : ECSetup)
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaTrue E D hD P)
                  (ECPoint.affine E P.1 P.2)) = 0 :=
  (Classical.choose_spec (CoordRingElt.exists_divisor_multiplicity E D hD)).2.2.2.2 hSplit

/-! ## `betaCanonical`: totalised `betaTrue`

    Returns 0 when `D` is the zero rational function (the case
    `D.a = 0 ∧ D.b = 0`). Provides a total β suitable for use in
    theorem statements that don't carry `hD` as a separate hypothesis. -/

/-- Totalised true divisor multiplicity. Equals `betaTrue E D hD`
    when `D` is nonzero, and the constant zero function when
    `D.a = 0 ∧ D.b = 0`. -/
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
    (hSplit : normPoly_splits_over_Fq E D) :
    (∑ P ∈ E.points, betaCanonical E D P) = (normPoly E D).natDegree := by
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD]
    exact betaTrue_account E D hD hSplit
  · push_neg at hD
    -- D = 0: normPoly = 0, both sides are 0.
    rw [betaCanonical_eq_zero E D hD]
    have hZero : normPoly E D = 0 := by
      rw [normPoly_eq, hD.1, hD.2]; ring
    rw [hZero, Polynomial.natDegree_zero]
    simp

theorem betaCanonical_group_sum_zero (E : ECSetup)
    (D : CoordRingElt E.q)
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaCanonical E D P)
                  (ECPoint.affine E P.1 P.2)) = 0 := by
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [betaCanonical_eq_betaTrue E D hD]
    exact betaTrue_group_sum_zero E D hD hSplit
  · push_neg at hD
    rw [betaCanonical_eq_zero E D hD]
    -- All summands are nsmul 0 = 0.
    apply Finset.sum_eq_zero
    intro P _
    exact ECPoint.nsmul_zero E _

end Divisor
