/-
  Divisor/OrdP/LocalRing.lean

  Algebraic API for `ordAt` (order of vanishing of `D = a − b·y` at
  affine F_q-rational points).

  The lemmas here are the obligations to discharge in Phase 1.2 of
  the soundness-restoration plan.  Aristotle is expected to fill the
  `sorry`s with proofs grounded in the corresponding textbook
  statements (Silverman AEC II §1, Stichtenoth §I.4 + III.1).

  Main API:

  * `ordAt_pos_iff_zero`: `0 < ordAt E D P ↔ D.eval P.1 P.2 = 0`
    (when `P ∈ E.points` and `D ≠ 0`).
  * `ordAt_eq_zero_offE`: `P ∉ E.points → ordAt E D P = 0`.
  * `sum_ordAt_le_degE`: `Σ_{P ∈ E.points} ordAt E D P ≤ D.degE`.
  * `sum_ordAt_eq_natDegree_under_split`: under
    `normPoly_splits_over_Fq`, the sum equals `(normPoly E D).natDegree`.
  * `ordAt_group_sum_zero_under_split`: under splitting + `D ≠ 0`,
    the `ordAt`-weighted group sum on `E.points` vanishes (Abel /
    `principal_divisor_iff`).

  Once all four lemmas are proven, `betaTrue` (the existential β from
  `AxiomExistsDivisorMultiplicity.lean`) can be discharged to a
  `theorem` with witness `ordAt E D`, eliminating the
  `exists_divisor_multiplicity` axiom.
-/
import Divisor.OrdP.Uniformizer
import Divisor.Axioms.AxiomPrincipalDivisorIff
import Divisor.Axioms.AxiomExistsDivisorMultiplicity

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Support: ord_P > 0 ↔ D vanishes at P -/

/-- **Support property**: when `D ≠ 0`, `ordAt E D P > 0` iff `P` is
    an affine F_q-rational point at which `D` vanishes.

    PROVIDED SOLUTION sketch:
    * `(→)` direction: if `ordAt > 0` at non-2-torsion, the constant
      Taylor coefficient is `D.eval P.1 P.2`, so `> 0` order means
      this is 0.  At 2-torsion same argument.
    * `(←)` direction: if `D.eval P.1 P.2 = 0`, the constant
      coefficient vanishes, so `ordAt ≥ 1`. -/
theorem ordAt_pos_iff_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    0 < ordAt E D P ↔ D.eval P.1 P.2 = 0 := by
  sorry

/-- Off `E`, ord is 0 by convention. -/
theorem ordAt_eq_zero_offE
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∉ E.points) :
    ordAt E D P = 0 := by
  sorry

/-! ## Sum bound -/

/-- **Sum bound**: `Σ_{P ∈ E.points} ordAt E D P ≤ D.degE`.

    PROVIDED SOLUTION sketch:
    Each `P ∈ E.points` with `D.eval P = 0` contributes `ordAt`,
    others contribute 0. The total contribution is bounded by the
    sum of root multiplicities of `normPoly E D` (which has
    `natDegree ≤ D.degE`). The factor of 2 from `normPoly`'s
    sheets-as-products cancels with the `÷2` for twin sheets only
    when both contribute, so the total is at most `D.degE`.  -/
theorem sum_ordAt_le_degE
    (D : CoordRingElt E.q) :
    (∑ P ∈ E.points, ordAt E D P) ≤ D.degE := by
  sorry

/-! ## Pole-at-∞ accounting under splitting -/

/-- **Accounting under splitting**: under `normPoly_splits_over_Fq E D`,
    the sum of orders equals `natDegree (normPoly E D)`. This is the
    "every geometric zero is F_q-rational" content of splitting.

    PROVIDED SOLUTION sketch: factor `normPoly E D` over its splitting
    field; the splitting hypothesis says all roots are F_q-rational.
    Each x-coordinate root corresponds to either (i) a pair of sheets
    (twin), with combined order = root multiplicity, or (ii) a single
    sheet (lone, including 2-torsion). Sum agrees by construction. -/
theorem sum_ordAt_eq_natDegree_under_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    (∑ P ∈ E.points, ordAt E D P) = (normPoly E D).natDegree := by
  sorry

/-! ## Group-sum identity (Abel's theorem) -/

/-- **Group-sum-zero**: under splitting, the `ordAt`-weighted group
    sum on `E.points` vanishes.

    PROVIDED SOLUTION sketch:
    Build the divisor `divD : ECPoint E → ℤ` from `ordAt` (with the
    pole at ∞ contributing `−degE`).  By `principal_divisor_iff.mp`
    applied to `IsPrincipal E divD` (which holds because `D` *is* a
    rational function on E with this divisor), the group sum
    `Σ [n_P] · P` vanishes. The `(∞)` term contributes `[−degE]·O = O`,
    so the remaining F_q-affine sum is also zero. -/
theorem ordAt_group_sum_zero_under_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (ordAt E D P)
                    (ECPoint.affine E P.1 P.2)) = 0 := by
  sorry

/-! ## Discharge `exists_divisor_multiplicity` -/

/-- **Goal of Phase 1**: the existential `β` axiom is discharged with
    witness `ordAt E D`.  Once this theorem is proven, the file
    `AxiomExistsDivisorMultiplicity.lean` can be retired (its `axiom`
    becomes a `theorem` with this proof).  -/
theorem exists_divisor_multiplicity_proved
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (normPoly_splits_over_Fq E D →
        (∑ P ∈ E.points, β P) = (normPoly E D).natDegree) ∧
      (normPoly_splits_over_Fq E D →
        ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0) := by
  refine ⟨ordAt E D, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    refine ⟨?_, ?_⟩
    · by_contra hOff
      exact hP (ordAt_eq_zero_offE E D hOff)
    · by_contra hNZ
      apply hP
      have : ¬ 0 < ordAt E D P := by
        rw [ordAt_pos_iff_zero E D hD P (by_contra fun hOff => hP (ordAt_eq_zero_offE E D hOff))]
        exact hNZ
      omega
  · intro P hP hZ
    rw [← Nat.pos_iff_ne_zero, ordAt_pos_iff_zero E D hD P hP]
    exact hZ
  · exact sum_ordAt_le_degE E D
  · exact sum_ordAt_eq_natDegree_under_split E D hD
  · exact ordAt_group_sum_zero_under_split E D hD

end Divisor
