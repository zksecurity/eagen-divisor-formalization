/-
  Divisor/HDenomNZBound.lean

  Bound on the count of "bad A₀" where the DAtA₂Scaled factor of
  denomScaledPoly vanishes mod curveEqPoly. This is the first piece
  of the hDenomNZ discharge.

  Key result: `badA₂Mod_card_mul_card_sub_two_le`. For
  `A₀ ∈ badA₂Mod` (i.e. `DAtA₂Scaled D A₀ %ₘ curveEqPoly E = 0`) and
  any nonvertical `A₁ ∈ E.points`, the chord-third evaluation
  `D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0`. This injects
  `badA₂Mod × (nonvertical A₁)` into the set bounded by
  `DAtA₂_zero_pairs_card_le`.
-/
import Divisor.DivisorPrincipal

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

/-! ### `badDenomA0`: the full bad-denominator A₀ set

Generalises `badA₂Mod` from a single `D(A₂)` factor to the full
`denomScaledPoly`. By the contrapositive of
`denomScaledPoly_modCurve_ne_zero`, for `A₀ ∈ badDenomA0` every
non-vertical `A₁ ∈ E.points` makes the verifier check undefined — so
no defined witness exists at this `A₀`. The cardinality bound below
(`badDenomA0_card_mul_card_sub_two_le`) together with degree and
distinctR-image bounds gives the count-out argument for
`goodA0_exists`. -/

/-- Set of `A₀ ∈ E.points` where the *full* `denomScaledPoly` reduces
to zero modulo the curve equation polynomial. By
`not_logDerivCheckFnDefined_of_mem_badDenomA0`, this is exactly the
set of `A₀`'s for which every non-vertical `A₁ ∈ E.points` satisfies
`¬ logDerivCheckFnDefined E D P B A₀ A₁`. These `A₀`'s are unusable
for the all-zero extractor. -/
noncomputable def badDenomA0
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    Finset (ZMod E.q × ZMod E.q) :=
  E.points.filter
    (fun A₀ => denomScaledPoly (E := E) D P k B A₀ %ₘ curveEqPoly E = 0)

/-- For `A₀ ∈ badDenomA0`, the verifier's denominator is undefined at
every non-vertical `A₁ ∈ E.points`. Contrapositive of
`denomScaledPoly_modCurve_ne_zero` via `bivEval_denomScaledPoly_eq`. -/
theorem not_logDerivCheckFnDefined_of_mem_badDenomA0
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    {A₀ : ZMod E.q × ZMod E.q} (hA₀ : A₀ ∈ badDenomA0 E D P k B)
    {A₁ : ZMod E.q × ZMod E.q} (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    ¬ logDerivCheckFnDefined E D P B A₀ A₁ := by
  classical
  rw [badDenomA0, Finset.mem_filter] at hA₀
  obtain ⟨_, hmod⟩ := hA₀
  intro hDef
  -- bivEval at A₁ ∈ E.points = 0 since the polynomial is in (curveEqPoly).
  have hbiv : bivEval (denomScaledPoly (E := E) D P k B A₀) A₁ = 0 := by
    rw [bivEval_eq_modByMonic_on_E E _ hA₁, hmod]
    unfold bivEval; simp
  rw [bivEval_denomScaledPoly_eq E D P k B A₀ A₁ hNV] at hbiv
  -- (A₁.1 - A₀.1)^N nonzero, so logDerivCheckFnDenom = 0, contradicting hDef.
  have hpow_ne : (A₁.1 - A₀.1) ^ (D.degE + k + 7) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hNV))
  have hDenomZero : logDerivCheckFnDenom E D P B A₀ A₁ = 0 :=
    (mul_eq_zero.mp hbiv).resolve_left hpow_ne
  exact hDef hDenomZero

/-- The cardinality bound:
`|badDenomA0| · (|E.points| − 2) ≤ (3·d + 9·k + 71) · |E.points|`.

Proof: every `(A₀, A₁)` with `A₀ ∈ badDenomA0`, `A₁ ∈ E.points`,
`A₀.1 ≠ A₁.1` injects into the undefined-pair set on `E × E`, bounded
by `logDerivCheckFn_undefined_set_bound_tight`. The non-vertical fiber
over each `A₀` has size at least `|E.points| − 2`. -/
theorem badDenomA0_card_mul_card_sub_two_le
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) :
    (badDenomA0 E D P k B).card * (E.points.card - 2)
      ≤ (3 * D.degE + 9 * k + 71) * E.points.card := by
  classical
  -- Joint set bounded by logDerivCheckFn_undefined_set_bound_tight.
  set S : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hSdef
  have hS_bound : S.card ≤ (3 * D.degE + 9 * k + 71) * E.points.card :=
    logDerivCheckFn_undefined_set_bound_tight E D P k B hD
  -- Injected set: pairs (A₀, A₁) with A₀ ∈ badDenomA0, A₁ ∈ E.points, A₀.1 ≠ A₁.1.
  set T : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (badDenomA0 E D P k B ×ˢ E.points).filter (fun p => p.1.1 ≠ p.2.1) with hTdef
  -- T ⊆ S.
  have hT_sub_S : T ⊆ S := by
    intro p hp
    simp only [hTdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hA₀_bad, hA₁_pts⟩, hNV⟩ := hp
    have hA₀_pts : p.1 ∈ E.points := by
      rw [badDenomA0, Finset.mem_filter] at hA₀_bad
      exact hA₀_bad.1
    simp only [hSdef, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hA₀_pts, hA₁_pts⟩, ?_⟩
    exact not_logDerivCheckFnDefined_of_mem_badDenomA0 E D P k B hA₀_bad hA₁_pts hNV
  have hT_le_S : T.card ≤ S.card := Finset.card_le_card hT_sub_S
  -- For each fixed A₀ ∈ badDenomA0, the fiber count {A₁ ∈ E.points : A₀.1 ≠ A₁.1}
  -- ≥ |E.points| - 2 (by card_points_with_fst_eq_le).
  have hT_card_ge :
      (badDenomA0 E D P k B).card * (E.points.card - 2) ≤ T.card := by
    rw [hTdef]
    have hcard_eq :
        ((badDenomA0 E D P k B ×ˢ E.points).filter
            (fun p => p.1.1 ≠ p.2.1)).card
          = ∑ A₀ ∈ badDenomA0 E D P k B,
              (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro A₀ _
      rw [Finset.card_filter]
    rw [hcard_eq]
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
    calc (badDenomA0 E D P k B).card * (E.points.card - 2)
        = ∑ _ ∈ badDenomA0 E D P k B, (E.points.card - 2) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ A₀ ∈ badDenomA0 E D P k B,
            (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card :=
          Finset.sum_le_sum (fun A₀ _ => hfiber A₀)
  exact hT_card_ge.trans (hT_le_S.trans hS_bound)

/-! ### Linear bound on `badDenomA0` under the standard `hLargeQ` -/

/-- Under the standard `hLargeQ` regime
`|E.points| ≥ 31·d + 31·k + 141`, the multiplicative
`|badDenomA0|·(|E|−2) ≤ (3d+9k+71)·|E|` collapses to the linear bound

  `|badDenomA0| ≤ |E.points| − 11·d − 11·k − 20`.

Algebraic verification: substituting `n = 31d + 31k + 141 + m` (with
`m ≥ 0`) and expanding yields a polynomial in `m, d, k` with all
non-negative coefficients (see comments in proof). -/
theorem badDenomA0_card_le_linear
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (hLargeQ : E.points.card ≥ 31 * D.degE + 31 * k + 141) :
    (badDenomA0 E D P k B).card ≤ E.points.card - 11 * D.degE - 11 * k - 20 := by
  classical
  set bad := (badDenomA0 E D P k B).card with hbaddef
  set n := E.points.card with hndef
  have hMul : bad * (n - 2) ≤ (3 * D.degE + 9 * k + 71) * n :=
    badDenomA0_card_mul_card_sub_two_le E D hD P k B
  -- Cast to ℤ for clean polynomial reasoning.
  have hLargeZ : (n : ℤ) ≥ 31 * D.degE + 31 * k + 141 := by exact_mod_cast hLargeQ
  have hMulZ : (bad : ℤ) * ((n : ℤ) - 2) ≤ (3 * D.degE + 9 * k + 71) * n := by
    have hge : 2 ≤ n := by omega
    have h := hMul
    have hsub : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
      omega
    have := h
    -- Cast both sides.
    have : (bad * (n - 2) : ℕ) ≤ ((3 * D.degE + 9 * k + 71) * n : ℕ) := h
    exact_mod_cast this
  -- Goal in ℤ: bad ≤ n - 11d - 11k - 20.
  -- By contradiction: if bad ≥ n - 11d - 11k - 19, then
  -- bad * (n-2) ≥ (n - 11d - 11k - 19)(n-2) > (3d+9k+71)n at n ≥ 31d+31k+141.
  have hd_nn : (0 : ℤ) ≤ D.degE := by exact_mod_cast Nat.zero_le _
  have hk_nn : (0 : ℤ) ≤ k := by exact_mod_cast Nat.zero_le _
  have hn_ge : (n : ℤ) - (31 * D.degE + 31 * k + 141) ≥ 0 := by linarith
  -- Key polynomial inequality:
  -- (n - 11d - 11k - 20)(n-2) - (3d+9k+71)n ≥ (algebraic non-neg expression)
  -- Equivalent: at n = 31d + 31k + 141 + m, polynomial is ≥ 0.
  -- Use nlinarith with sq_nonneg hint for (n - 31d - 31k - 141).
  have hPoly :
      ((n : ℤ) - 11 * D.degE - 11 * k - 20) * ((n : ℤ) - 2)
        ≥ (3 * D.degE + 9 * k + 71) * n := by
    nlinarith [hLargeZ, hd_nn, hk_nn, hn_ge,
      mul_nonneg hd_nn hk_nn,
      mul_nonneg hd_nn hn_ge,
      mul_nonneg hk_nn hn_ge,
      mul_nonneg hn_ge hn_ge,
      mul_nonneg hd_nn hd_nn, mul_nonneg hk_nn hk_nn,
      sq_nonneg ((n : ℤ) - 31 * D.degE - 31 * k - 141)]
  -- Conclude bad ≤ n - 11d - 11k - 20 in ℤ.
  have hBoundZ : (bad : ℤ) ≤ (n : ℤ) - 11 * D.degE - 11 * k - 20 := by
    have hn2pos : (0 : ℤ) < (n : ℤ) - 2 := by linarith
    -- bad * (n-2) ≤ (3d+9k+71)n ≤ (n - 11d - 11k - 20)(n-2)
    have : (bad : ℤ) * ((n : ℤ) - 2) ≤ ((n : ℤ) - 11 * D.degE - 11 * k - 20) * ((n : ℤ) - 2) :=
      le_trans hMulZ hPoly
    exact le_of_mul_le_mul_right this hn2pos
  -- Cast back to ℕ.
  have hPos_ℕ : 11 * D.degE + 11 * k + 20 ≤ n := by
    have : (11 * D.degE + 11 * k + 20 : ℤ) ≤ n := by linarith
    exact_mod_cast this
  omega

/-- Variant of `badDenomA0_card_le_linear` with the bound stated in terms
of an external `k_stmt ≥ k_param`. Used when the consumer's resultantX
bound is in terms of `stmt.k` (statement-level) but the bad set is
parameterised by `baseImageCount ≤ stmt.k`. -/
theorem badDenomA0_card_le_linear_relax
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (k_stmt : ℕ) (hk_le : k ≤ k_stmt)
    (hLargeQ : E.points.card ≥ 31 * D.degE + 31 * k_stmt + 141) :
    (badDenomA0 E D P k B).card
      ≤ E.points.card - 11 * D.degE - 11 * k_stmt - 20 := by
  classical
  set bad := (badDenomA0 E D P k B).card with hbaddef
  set n := E.points.card with hndef
  have hMul : bad * (n - 2) ≤ (3 * D.degE + 9 * k + 71) * n :=
    badDenomA0_card_mul_card_sub_two_le E D hD P k B
  have hMul_relax : bad * (n - 2) ≤ (3 * D.degE + 9 * k_stmt + 71) * n := by
    refine hMul.trans ?_
    apply Nat.mul_le_mul_right
    omega
  have hLargeZ : (n : ℤ) ≥ 31 * D.degE + 31 * k_stmt + 141 := by exact_mod_cast hLargeQ
  have hge : 2 ≤ n := by omega
  have hMulZ : (bad : ℤ) * ((n : ℤ) - 2) ≤ (3 * D.degE + 9 * k_stmt + 71) * n := by
    have h := hMul_relax
    have : (bad * (n - 2) : ℕ) ≤ ((3 * D.degE + 9 * k_stmt + 71) * n : ℕ) := h
    exact_mod_cast this
  have hd_nn : (0 : ℤ) ≤ D.degE := by exact_mod_cast Nat.zero_le _
  have hk_nn : (0 : ℤ) ≤ k_stmt := by exact_mod_cast Nat.zero_le _
  have hn_ge : (n : ℤ) - (31 * D.degE + 31 * k_stmt + 141) ≥ 0 := by linarith
  have hPoly :
      ((n : ℤ) - 11 * D.degE - 11 * k_stmt - 20) * ((n : ℤ) - 2)
        ≥ (3 * D.degE + 9 * k_stmt + 71) * n := by
    nlinarith [hLargeZ, hd_nn, hk_nn, hn_ge,
      mul_nonneg hd_nn hk_nn,
      mul_nonneg hd_nn hn_ge,
      mul_nonneg hk_nn hn_ge,
      mul_nonneg hn_ge hn_ge,
      mul_nonneg hd_nn hd_nn, mul_nonneg hk_nn hk_nn,
      sq_nonneg ((n : ℤ) - 31 * D.degE - 31 * k_stmt - 141)]
  have hBoundZ : (bad : ℤ) ≤ (n : ℤ) - 11 * D.degE - 11 * k_stmt - 20 := by
    have hn2pos : (0 : ℤ) < (n : ℤ) - 2 := by linarith
    have : (bad : ℤ) * ((n : ℤ) - 2) ≤
        ((n : ℤ) - 11 * D.degE - 11 * k_stmt - 20) * ((n : ℤ) - 2) :=
      le_trans hMulZ hPoly
    exact le_of_mul_le_mul_right this hn2pos
  have hPos_ℕ : 11 * D.degE + 11 * k_stmt + 20 ≤ n := by
    have : (11 * D.degE + 11 * k_stmt + 20 : ℤ) ≤ n := by linarith
    exact_mod_cast this
  omega

/-! ### Existence of a "good" `A₀`

A counting lemma that, under a sufficient large-`q` condition, produces
an `A₀ ∈ E.points` that avoids:

* the `D`-zero set `zerosFinset E D`,
* an external "exclude" Finset (used at the call site for the
  `distinctR`-image), and
* `badDenomA0` (where the verifier's denominator polynomial vanishes
  mod the curve equation).

This is the count-out lemma needed to discharge the per-`A₀`
`hDenomNZ` hypothesis in the all-zero extractor: for the chosen good
`A₀`, `denomScaledPoly … A₀ %ₘ curveEqPoly E ≠ 0`. -/

/-- Existence of an `A₀ ∈ E.points` outside `zerosFinset`, an
external `extra` set, and `badDenomA0`.

The size hypothesis uses the multiplied form
`badDenomA0.card · (|E| − 2) ≤ (3d + 9k + 71)·|E|` directly, avoiding
the loose `n/(n−2)` factor. -/
theorem exists_A0_outside_bad
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (extra : Finset (ZMod E.q × ZMod E.q))
    (hExtra : extra.card ≤ k + 1)
    (hSize :
      (D.degE + (k + 1)) * (E.points.card - 2)
        + (3 * D.degE + 9 * k + 71) * E.points.card
        < E.points.card * (E.points.card - 2)) :
    ∃ A₀ ∈ E.points,
      A₀ ∉ zerosFinset E D ∧
      A₀ ∉ extra ∧
      A₀ ∉ badDenomA0 E D P k B := by
  classical
  have hn_ge : 3 ≤ E.points.card := by
    -- hSize forces (n - 2) > 0, hence n ≥ 3.
    by_contra hLt
    push_neg at hLt
    interval_cases E.points.card <;> simp_all
  -- Bound for the bad union.
  set bad : Finset (ZMod E.q × ZMod E.q) :=
    zerosFinset E D ∪ extra ∪ badDenomA0 E D P k B with hbaddef
  have hZeros_le : (zerosFinset E D).card ≤ D.degE := by
    have h := numZeros_le_degE E D hD
    -- numZeros = (zeros D E.points).card; zerosFinset = zeros D E.points (defeq).
    exact h
  have hBad_le_mul :
      bad.card * (E.points.card - 2)
        ≤ (D.degE + (k + 1)) * (E.points.card - 2)
            + (3 * D.degE + 9 * k + 71) * E.points.card := by
    have hcu1 : ((zerosFinset E D ∪ extra) ∪ badDenomA0 E D P k B).card
        ≤ (zerosFinset E D ∪ extra).card + (badDenomA0 E D P k B).card :=
      Finset.card_union_le _ _
    have hcu2 : (zerosFinset E D ∪ extra).card
        ≤ (zerosFinset E D).card + extra.card :=
      Finset.card_union_le _ _
    have hbad_card_le : bad.card
        ≤ ((zerosFinset E D).card + extra.card) + (badDenomA0 E D P k B).card := by
      simp only [hbaddef]
      exact hcu1.trans (Nat.add_le_add_right hcu2 _)
    have hMul : bad.card * (E.points.card - 2)
        ≤ (((zerosFinset E D).card + extra.card) + (badDenomA0 E D P k B).card)
            * (E.points.card - 2) :=
      Nat.mul_le_mul_right _ hbad_card_le
    have hZE_le : (zerosFinset E D).card + extra.card ≤ D.degE + (k + 1) :=
      Nat.add_le_add hZeros_le hExtra
    have hLeft : ((zerosFinset E D).card + extra.card) * (E.points.card - 2)
        ≤ (D.degE + (k + 1)) * (E.points.card - 2) :=
      Nat.mul_le_mul_right _ hZE_le
    have hRight : (badDenomA0 E D P k B).card * (E.points.card - 2)
        ≤ (3 * D.degE + 9 * k + 71) * E.points.card :=
      badDenomA0_card_mul_card_sub_two_le E D hD P k B
    calc bad.card * (E.points.card - 2)
        ≤ _ := hMul
      _ = ((zerosFinset E D).card + extra.card) * (E.points.card - 2)
          + (badDenomA0 E D P k B).card * (E.points.card - 2) := by ring
      _ ≤ (D.degE + (k + 1)) * (E.points.card - 2)
          + (3 * D.degE + 9 * k + 71) * E.points.card :=
          Nat.add_le_add hLeft hRight
  -- bad.card * (n - 2) < n * (n - 2), so bad.card < n.
  have hStrict : bad.card * (E.points.card - 2)
      < E.points.card * (E.points.card - 2) := lt_of_le_of_lt hBad_le_mul hSize
  have hPos : 0 < E.points.card - 2 := by omega
  have hbad_lt : bad.card < E.points.card := by
    have hStrict' :
        (E.points.card - 2) * bad.card < (E.points.card - 2) * E.points.card := by
      rw [Nat.mul_comm (E.points.card - 2) bad.card,
          Nat.mul_comm (E.points.card - 2) E.points.card]
      exact hStrict
    exact Nat.lt_of_mul_lt_mul_left hStrict'
  -- E.points has more elements than bad, so complement is nonempty.
  have hsdiff_card : 0 < (E.points \ bad).card := by
    have h := Finset.le_card_sdiff bad E.points
    omega
  obtain ⟨A₀, hA₀_mem⟩ := Finset.card_pos.mp hsdiff_card
  have ⟨hA₀_pts, hA₀_not_bad⟩ := Finset.mem_sdiff.mp hA₀_mem
  refine ⟨A₀, hA₀_pts, ?_, ?_, ?_⟩
  · intro hZ; apply hA₀_not_bad
    simp only [hbaddef, Finset.mem_union]; left; left; exact hZ
  · intro hE; apply hA₀_not_bad
    simp only [hbaddef, Finset.mem_union]; left; right; exact hE
  · intro hB; apply hA₀_not_bad
    simp only [hbaddef, Finset.mem_union]; right; exact hB

end Divisor
