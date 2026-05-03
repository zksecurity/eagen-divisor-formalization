/-
  Divisor/HDenomNZBound.lean

  Bound on the count of "bad A₀" where the DAtA₂Scaled factor of
  denomScaledPoly vanishes mod curveEqPoly. This is the first piece
  of the hDenomNZ discharge plan documented at
  `docs/hDenomNZ-discharge-plan.md`.

  Key result: `badA₂Mod_card_mul_card_sub_two_le`. For
  `A₀ ∈ badA₂Mod` (i.e. `DAtA₂Scaled D A₀ %ₘ curveEqPoly E = 0`) and
  any nonvertical `A₁ ∈ E.points`, the chord-third evaluation
  `D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0`. This injects
  `badA₂Mod × (nonvertical A₁)` into the set bounded by
  `DAtA₂_zero_pairs_card_le`.
-/
import Divisor.ClearedPolyForm
import Divisor.ClearedPolyFormBounds

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-- Set of `A₀ ∈ E.points` where the `DAtA₂Scaled` factor of
`denomScaledPoly` vanishes mod the curve equation polynomial. For such
`A₀`, the discharge of `hDenomNZ` via simple per-factor degree bounds
fails (the natDegree of `DAtA₂Scaled` can exceed the curve equation's
natDegree of 2). -/
noncomputable def badA₂Mod (D : CoordRingElt E.q) :
    Finset (ZMod E.q × ZMod E.q) :=
  E.points.filter
    (fun A₀ => (DAtA₂Scaled (E := E) D A₀) %ₘ curveEqPoly E = 0)

/-- For `A₀ ∈ badA₂Mod`, the chord-third evaluation
`D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁)` vanishes for every
nonvertical `A₁ ∈ E.points`. -/
theorem D_eval_chord_third_zero_of_badA₂Mod
    (D : CoordRingElt E.q)
    {A₀ : ZMod E.q × ZMod E.q} (hA₀ : A₀ ∈ badA₂Mod E D)
    {A₁ : ZMod E.q × ZMod E.q} (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0 := by
  classical
  -- Extract the mod-zero hypothesis.
  rw [badA₂Mod, Finset.mem_filter] at hA₀
  obtain ⟨_, hmod⟩ := hA₀
  -- bivEval at A₁ ∈ E.points = 0 since the polynomial is in (curveEqPoly).
  have hbiv : bivEval (DAtA₂Scaled (E := E) D A₀) A₁ = 0 := by
    rw [bivEval_eq_modByMonic_on_E E _ hA₁, hmod]
    unfold bivEval; simp
  -- Use the explicit form on the non-vertical cone.
  rw [bivEval_DAtA₂Scaled_eq E D A₀ A₁ hNV] at hbiv
  -- Extract D.eval(chord_third) = 0 by killing the (A₁.1 - A₀.1)^D.degE prefactor.
  have hpow_ne : (A₁.1 - A₀.1) ^ D.degE ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hNV))
  exact (mul_eq_zero.mp hbiv).resolve_left hpow_ne

/-- The cardinality bound: `|badA₂Mod| · (|E.points| − 2) ≤ (D.degE + 2) · |E.points|`.

Proof: every `(A₀, A₁)` with `A₀ ∈ badA₂Mod`, `A₁ ∈ E.points`,
`A₀.1 ≠ A₁.1` injects into the set of `(A₀, A₁) ∈ E.points × E.points`
where `D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0`, which is bounded
by `DAtA₂_zero_pairs_card_le`. The non-vertical fiber over each `A₀` has
size at least `|E.points| − 2` (since the vertical fiber has at most 2
points by `card_points_with_fst_eq_le`). -/
theorem badA₂Mod_card_mul_card_sub_two_le
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (badA₂Mod E D).card * (E.points.card - 2)
      ≤ (D.degE + 2) * E.points.card := by
  classical
  -- Define the joint set bounded by DAtA₂_zero_pairs_card_le.
  set S : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0) with hSdef
  have hS_bound : S.card ≤ (D.degE + 2) * E.points.card :=
    DAtA₂_zero_pairs_card_le E D hD
  -- Define the injected set: pairs (A₀, A₁) with A₀ ∈ badA₂Mod, A₁ ∈ E.points, A₀.1 ≠ A₁.1.
  set T : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (badA₂Mod E D ×ˢ E.points).filter (fun p => p.1.1 ≠ p.2.1) with hTdef
  -- T ⊆ S.
  have hT_sub_S : T ⊆ S := by
    intro p hp
    simp only [hTdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hA₀_bad, hA₁_pts⟩, hNV⟩ := hp
    have hA₀_pts : p.1 ∈ E.points := by
      rw [badA₂Mod, Finset.mem_filter] at hA₀_bad
      exact hA₀_bad.1
    simp only [hSdef, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hA₀_pts, hA₁_pts⟩, ?_⟩
    exact D_eval_chord_third_zero_of_badA₂Mod E D hA₀_bad hA₁_pts hNV
  have hT_le_S : T.card ≤ S.card := Finset.card_le_card hT_sub_S
  -- Now T.card = |badA₂Mod| × (|E.points fibers with A₀.1 ≠ A₁.1|).
  -- For each fixed A₀ ∈ badA₂Mod, the fiber count {A₁ ∈ E.points : A₀.1 ≠ A₁.1}
  -- ≥ |E.points| - 2 (by card_points_with_fst_eq_le).
  have hT_card_ge :
      (badA₂Mod E D).card * (E.points.card - 2) ≤ T.card := by
    -- Use Finset.card_filter_pi or direct: T.card = Σ A₀ ∈ badA₂Mod of fiber-count.
    rw [hTdef]
    -- T = (badA₂Mod ×ˢ E.points).filter (fun p => p.1.1 ≠ p.2.1).
    -- Express as biUnion of fibers.
    have hcard_eq : ((badA₂Mod E D ×ˢ E.points).filter (fun p => p.1.1 ≠ p.2.1)).card
        = ∑ A₀ ∈ badA₂Mod E D, (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro A₀ _
      rw [Finset.card_filter]
    rw [hcard_eq]
    -- Each fiber has ≥ |E.points| - 2 elements.
    have hfiber : ∀ A₀ : ZMod E.q × ZMod E.q,
        E.points.card - 2 ≤ (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card := by
      intro A₀
      have hVertCard := card_points_with_fst_eq_le E A₀.1
      have hCompl : (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
          (E.points.filter (fun A₁ => ¬A₁.1 = A₀.1)).card =
          E.points.card :=
        Finset.card_filter_add_card_filter_not (s := E.points)
          (p := fun A₁ => A₁.1 = A₀.1)
      have hEq : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1) =
          E.points.filter (fun A₁ => ¬A₁.1 = A₀.1) := by
        ext x; simp [ne_comm]
      rw [hEq]; omega
    calc (badA₂Mod E D).card * (E.points.card - 2)
        = ∑ _ ∈ badA₂Mod E D, (E.points.card - 2) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ A₀ ∈ badA₂Mod E D,
            (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card :=
          Finset.sum_le_sum (fun A₀ _ => hfiber A₀)
  exact hT_card_ge.trans (hT_le_S.trans hS_bound)

/-! ### Witness-form discharge of `hDenomNZ`

The existing theorem `denomScaledPoly_modCurve_ne_zero` discharges
`hDenomNZ` when there is a witness `A₁` for which the verifier's
denominator is defined. The version here packages this for
hypothesis-discharge use: if the count of "totally bad" `A₀` (every
`A₁ ∈ E.points` makes the verifier's denominator vanish) is small,
then for "most" `A₀` the witness exists and `hDenomNZ` holds. -/

/-- **Discharge tool for `hDenomNZ` via witness existence.**

For each `A₀ ∈ E.points` satisfying the standard preconditions,
`hDenomNZ A₀ _ _ _` reduces to "there exists `A₁ ∈ E.points` with
`A₀.1 ≠ A₁.1` and `logDerivCheckFnDefined E D P B A₀ A₁`". The witness
existence in turn follows whenever the count of "bad" `A₁` is strictly
less than `|E.points| - 2`.

This packages `denomScaledPoly_modCurve_ne_zero` so callers can
discharge `hDenomNZ` from a "bad fiber count" upper bound rather than
from a per-`A₀` polynomial-non-vanishing argument. -/
theorem hDenomNZ_of_witness_exists
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q)
    (hWitness : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
                  logDerivCheckFnDefined E D P B A₀ A₁) :
    denomScaledPoly (E := E) D P k B A₀ %ₘ curveEqPoly E ≠ 0 :=
  denomScaledPoly_modCurve_ne_zero E D P k B A₀ hWitness

end Divisor

