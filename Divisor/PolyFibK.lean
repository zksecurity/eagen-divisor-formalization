/-
  Divisor/PolyFibK.lean

  Slope-μ projection polynomial and its connection to `polyG`.

  The non-vanishing criterion for the log-derivative check
  (`log_deriv_nonvanishing_criterion`, T5 in the axiom elimination
  plan) is a statement about the denominator-cleared polynomial
  `polyG E Q β R m`. Fixing a slope `λ` and projecting points to the
  μ-coordinate `zLambda λ pt = pt.2 - λ · pt.1`, one has the identity
  `polyG E Q β R m A₀ A₁ =
     (-(A₁.1 - A₀.1))^(d+M-1) ·
       (polyFibK λ Q β R m).eval (zLambda λ A₀)`
  on the non-vertical cone (`A₀.1 ≠ A₁.1`, with `λ = slopeOf A₀ A₁`).
  This is the "Phase A2" connection lemma in the plan.

  The "Phase A4" generic-λ distinctness lemma bounds the number of
  slopes `λ` for which `zLambda λ` fails to separate two given
  distinct points. Each non-vertical pair of points gives at most one
  such bad slope; vertical pairs give none. Total: ≤ `binom(n, 2)`
  bad slopes, where `n` is the size of the combined point set.
-/
import Divisor.Defs
import Divisor.LogDeriv

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Slope-μ projection -/

/-- Project a point `pt` onto the μ-coordinate orthogonal to the
    direction `(1, λ)`: lines of slope `λ` are level sets of
    `zLambda λ`. -/
def zLambda (lam : ZMod E.q) (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  pt.2 - lam * pt.1

/-! ## Connection between `ellP` and `zLambda`

`ellP E P A₀ A₁` is the bilinear form whose vanishing detects whether
`P` lies on the chord through `A₀` and `A₁`. On the non-vertical cone,
factoring `(A₁.1 - A₀.1)` out yields a difference of `zLambda` values
at the chord's slope `λ`:
  `ellP E P A₀ A₁ = -(A₁.1 - A₀.1) · (μ - zLambda λ P)`,
where `μ = zLambda λ A₀` is the chord's intercept.
-/

/-- Express `ellP` as `-(A₁.1 - A₀.1) · (X - C (zLambda λ P)).eval μ`
    on the non-vertical cone. The `(X - C α)` form will combine
    cleanly with `polyFibK`'s product structure. -/
theorem ellP_eq_neg_scaled_eval (P A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1) :
    ellP E P A₀ A₁ =
      -(A₁.1 - A₀.1) *
        ((X - C (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) P)).eval
          (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)) := by
  simp only [ellP, zLambda, slopeOf, eval_sub, eval_X, eval_C]
  have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  field_simp
  ring

/-! ## The projection polynomial `polyFibK` -/

/-- Slope-μ projection polynomial. The first sum collects β-residues
    at the projected zero set; the second collects m-residues at the
    projected target set. Both grouped to a single polynomial in
    `μ : ZMod E.q`. -/
noncomputable def polyFibK
    {d M : ℕ}
    (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    (ZMod E.q)[X] :=
  (Finset.univ.sum (fun k : Fin d =>
    C (β k) *
    ((Finset.univ.erase k).prod (fun k' => X - C (zLambda E lam (Q k')))) *
    (Finset.univ.prod (fun j : Fin M => X - C (zLambda E lam (R j)))))) +
  (Finset.univ.sum (fun j : Fin M =>
    C (m j) *
    (Finset.univ.prod (fun k : Fin d => X - C (zLambda E lam (Q k)))) *
    ((Finset.univ.erase j).prod (fun j' => X - C (zLambda E lam (R j'))))))

/-! ## Connection lemma -/

/-- Single-term identity for `polyG`'s first sum (assumes `k : Fin d`,
    so `d ≥ 1`). -/
private theorem polyG_firstSum_term_eq
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (k : Fin d) :
    β k *
      ((Finset.univ.erase k).prod (fun k' => ellP E (Q k') A₀ A₁)) *
      Finset.univ.prod (fun j : Fin M => ellP E (R j) A₀ A₁)
      =
    (-(A₁.1 - A₀.1))^(d + M - 1) *
      (C (β k) *
       ((Finset.univ.erase k).prod (fun k' =>
         X - C (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (Q k')))) *
       Finset.univ.prod (fun j : Fin M =>
         X - C (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (R j)))).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) := by
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set mu := zLambda E lam A₀
  simp_rw [ellP_eq_neg_scaled_eval E _ _ _ hNV]
  simp only [eval_mul, eval_C, Polynomial.eval_prod, eval_sub, eval_X,
    Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin]
  -- d ≥ 1 since k : Fin d, so d + M - 1 = d - 1 + M.
  have hd_pos : 1 ≤ d := by have := k.isLt; omega
  rw [show d + M - 1 = d - 1 + M from by omega]
  ring

/-- Single-term identity for `polyG`'s second sum (assumes `j : Fin M`,
    so `M ≥ 1`). -/
private theorem polyG_secondSum_term_eq
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (j : Fin M) :
    m j *
      Finset.univ.prod (fun k : Fin d => ellP E (Q k) A₀ A₁) *
      ((Finset.univ.erase j).prod (fun j' => ellP E (R j') A₀ A₁))
      =
    (-(A₁.1 - A₀.1))^(d + M - 1) *
      (C (m j) *
       Finset.univ.prod (fun k : Fin d =>
         X - C (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (Q k))) *
       ((Finset.univ.erase j).prod (fun j' =>
         X - C (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (R j'))))).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) := by
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set mu := zLambda E lam A₀
  simp_rw [ellP_eq_neg_scaled_eval E _ _ _ hNV]
  simp only [eval_mul, eval_C, Polynomial.eval_prod, eval_sub, eval_X,
    Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]
  -- M ≥ 1 since j : Fin M, so d + M - 1 = d + (M - 1).
  have hM_pos : 1 ≤ M := by have := j.isLt; omega
  rw [show d + M - 1 = d + (M - 1) from by omega]
  ring

/-- **Connection lemma (Phase A2).** On the non-vertical cone,
    `polyG E Q β R m A₀ A₁` factors as
    `(-(A₁.1-A₀.1))^(d+M-1) · polyFibK λ Q β R m .eval μ`,
    where `λ` is the chord's slope and `μ = zLambda λ A₀`. -/
theorem polyG_eq_polyFibK_eval
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    polyG E Q β R m A₀ A₁ =
      (-(A₁.1 - A₀.1))^(d + M - 1) *
      (polyFibK E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q β R m).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) := by
  unfold polyG polyFibK
  rw [eval_add, eval_finset_sum, eval_finset_sum, mul_add]
  congr 1
  · -- First sum: pull (-(c))^(d+M-1) out via per-term identity.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact polyG_firstSum_term_eq E Q β R A₀ A₁ hNV k
  · -- Second sum: symmetric.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact polyG_secondSum_term_eq E Q R m A₀ A₁ hNV j

/-! ## Generic-λ distinctness (Phase A4)

For a Finset of points `S`, the set of slopes `λ` for which
`zLambda λ` fails to separate two distinct points of `S` is bounded.
Each non-vertical pair `(P₁, P₂)` with `P₁.1 ≠ P₂.1` contributes one
bad slope `(P₁.2 - P₂.2) / (P₁.1 - P₂.1)`; vertical pairs (same
x-coordinate) contribute none, since `P₁.1 = P₂.1` forces
`P₁.2 = P₂.2` from any `zLambda` collision, contradicting `P₁ ≠ P₂`.

Total: bad-slope count ≤ `(distinctPairs S).card = S.card · (S.card - 1)`.
-/

/-- For a distinct pair `(P₁, P₂)` of points: the unique slope `λ` for
    which `zLambda λ P₁ = zLambda λ P₂` is `(P₁.2 - P₂.2)/(P₁.1 - P₂.1)`,
    when this is well-defined (i.e., on non-vertical pairs). For
    vertical or equal pairs, the value is irrelevant; we use the same
    formula with the convention `0⁻¹ = 0`. -/
noncomputable def pairBadLambda (P₁ P₂ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (P₁.2 - P₂.2) * (P₁.1 - P₂.1)⁻¹

/-- **Generic-λ distinctness (Phase A4).**
    The set of slopes `λ` for which `zLambda λ` is not injective on
    `S` has cardinality at most `S.card · (S.card - 1)`, the number of
    ordered distinct pairs in `S`. -/
theorem badLambdaSet_card_le (S : Finset (ZMod E.q × ZMod E.q)) :
    ((Finset.univ : Finset (ZMod E.q)).filter (fun lam =>
      ∃ P₁ ∈ S, ∃ P₂ ∈ S, P₁ ≠ P₂ ∧ zLambda E lam P₁ = zLambda E lam P₂)).card
      ≤ S.card * (S.card - 1) := by
  classical
  set bad := (Finset.univ : Finset (ZMod E.q)).filter (fun lam =>
      ∃ P₁ ∈ S, ∃ P₂ ∈ S, P₁ ≠ P₂ ∧ zLambda E lam P₁ = zLambda E lam P₂)
    with hbad_def
  -- Each bad λ comes from at least one distinct pair in S.
  -- Map every bad λ to its witness pair via pairBadLambda.
  have hSub : bad ⊆ (distinctPairs S).image (fun pair =>
      pairBadLambda E pair.1 pair.2) := by
    intro lam hlam
    simp only [hbad_def, Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    obtain ⟨P₁, hP₁, P₂, hP₂, hne, hzeq⟩ := hlam
    -- From hne + hzeq: P₁.1 ≠ P₂.1 (else P₁.2 = P₂.2, ⇒ P₁ = P₂).
    have hx_ne : P₁.1 ≠ P₂.1 := by
      intro hx
      apply hne
      apply Prod.ext hx
      have h := hzeq
      simp only [zLambda, hx] at h
      linear_combination h
    have hx_diff : P₁.1 - P₂.1 ≠ 0 := sub_ne_zero.mpr hx_ne
    -- Solve for lam.
    have hkey : lam = pairBadLambda E P₁ P₂ := by
      have heq : P₁.2 - P₂.2 = lam * (P₁.1 - P₂.1) := by
        have h := hzeq
        simp only [zLambda] at h
        linear_combination h
      simp only [pairBadLambda]
      rw [heq, mul_assoc, mul_inv_cancel₀ hx_diff, mul_one]
    rw [Finset.mem_image]
    refine ⟨(P₁, P₂), ?_, ?_⟩
    · simp only [distinctPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hP₁, hP₂⟩, hne⟩
    · exact hkey.symm
  calc bad.card
      ≤ ((distinctPairs S).image (fun pair =>
          pairBadLambda E pair.1 pair.2)).card := Finset.card_le_card hSub
    _ ≤ (distinctPairs S).card := Finset.card_image_le
    _ = S.card * S.card - S.card := card_distinctPairs S
    _ ≤ S.card * (S.card - 1) := by
        rcases Nat.eq_zero_or_pos S.card with h | _
        · simp [h]
        · have : S.card * (S.card - 1) = S.card * S.card - S.card := by
            rw [Nat.mul_sub_one]
          omega

end Divisor
