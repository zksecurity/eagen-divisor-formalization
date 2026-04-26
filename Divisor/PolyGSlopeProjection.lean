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
import Divisor.SlopeDist
import Divisor.BassaMonic
import Divisor.PartialFraction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

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

/-! ## Per-slope μ-count (Phase A3)

For a given slope `λ`, the set of intercepts `μ` realized by chords on
`E` with slope `λ` (i.e., `μ` such that the line `y = λx + μ` meets
`E` in ≥ 2 affine points) has cardinality bounded below by the total
validPairs count, divided pigeonhole-wise over all slopes.

Combined with A4 (distinctness), we obtain a slope `λ ∈ F_q` that:
(i) does not make `zLambda E λ` collide two points in a given set `S`,
(ii) realizes ≥ `N` distinct intercepts via chords on `E`.

This is the "Phase A3 alternative" path from the plan: existence of
ONE good slope (pigeonhole on the total), not "most slopes".
-/

/-- The set of intercepts `μ` that realize a chord on `E` with slope
    `λ`: those for which the affine line `y = λx + μ` hits `E` in at
    least 2 points. -/
noncomputable def goodIntercepts (lam : ZMod E.q) : Finset (ZMod E.q) :=
  (Finset.univ : Finset (ZMod E.q)).filter
    (fun mu => 2 ≤ (pointsOnLine E lam mu).card)

/-- If `(A₀, A₁)` is a pair of distinct non-vertical points on `E`
    with slope `λ`, the intercept `A₀.2 - λ · A₀.1` is in
    `goodIntercepts E λ`. -/
lemma interceptOf_fst_mem_goodIntercepts
    {lam : ZMod E.q}
    {p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)}
    (hp : p ∈ pairsWithSlope E lam) :
    interceptOf E lam p.1 ∈ goodIntercepts E lam := by
  simp only [pairsWithSlope, distinctPairs, Finset.mem_filter,
             Finset.mem_product] at hp
  obtain ⟨⟨⟨h1, h2⟩, hne⟩, hxne, hslope⟩ := hp
  set mu := interceptOf E lam p.1
  have hp1 : p.1 ∈ pointsOnLine E lam mu := mem_pointsOnLine_self E h1
  have hp2 : p.2 ∈ pointsOnLine E lam mu := by
    simp only [pointsOnLine, Finset.mem_filter]
    refine ⟨h2, ?_⟩
    simp only [mu, interceptOf]
    have hxne_diff : p.2.1 - p.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
    have heq : p.2.2 - p.1.2 = lam * (p.2.1 - p.1.1) := by
      have hs : (p.2.2 - p.1.2) * (p.2.1 - p.1.1)⁻¹ = lam := hslope
      calc p.2.2 - p.1.2
          = (p.2.2 - p.1.2) * ((p.2.1 - p.1.1)⁻¹ * (p.2.1 - p.1.1)) := by
              rw [inv_mul_cancel₀ hxne_diff, mul_one]
        _ = (p.2.2 - p.1.2) * (p.2.1 - p.1.1)⁻¹ * (p.2.1 - p.1.1) := by ring
        _ = lam * (p.2.1 - p.1.1) := by rw [hs]
    linear_combination heq
  simp only [goodIntercepts, Finset.mem_filter, Finset.mem_univ, true_and]
  have hPair : ({p.1, p.2} : Finset _).card ≤ (pointsOnLine E lam mu).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp1
    · exact hp2
  have hPair_card : ({p.1, p.2} : Finset _).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  omega

/-- Per-slope bound: `|pairsWithSlope lam| ≤ 6 · |goodIntercepts lam|`.

    For a given λ, each ordered distinct non-vertical pair on E with
    slope λ maps via `interceptOf E lam` (on the first coordinate) to
    an element of `goodIntercepts lam`. Each fiber has size at most
    6 because the fiber is a subset of the distinct ordered pairs on
    the line, which has ≤ 3 affine points (Bezout). -/
theorem pairsWithSlope_card_le_six_mul_goodIntercepts (lam : ZMod E.q) :
    (pairsWithSlope E lam).card ≤ 6 * (goodIntercepts E lam).card := by
  classical
  let f : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) → ZMod E.q :=
    fun p => interceptOf E lam p.1
  have himg_sub : (pairsWithSlope E lam).image f ⊆ goodIntercepts E lam := by
    intro mu hmu
    rw [Finset.mem_image] at hmu
    obtain ⟨p, hp, heq⟩ := hmu
    show mu ∈ goodIntercepts E lam
    rw [← heq]
    exact interceptOf_fst_mem_goodIntercepts E hp
  have hfiber : ∀ mu ∈ (pairsWithSlope E lam).image f,
      ((pairsWithSlope E lam).filter (fun p => f p = mu)).card ≤ 6 := by
    intro mu _
    have hsub : (pairsWithSlope E lam).filter (fun p => f p = mu) ⊆
                distinctPairs (pointsOnLine E lam mu) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      -- hp2 : f p = mu, i.e., interceptOf E lam p.1 = mu
      change interceptOf E lam p.1 = mu at hp2
      simp only [pairsWithSlope, distinctPairs, Finset.mem_filter,
                 Finset.mem_product] at hp1
      obtain ⟨⟨⟨h1, h2⟩, hne⟩, hxne, hslope⟩ := hp1
      unfold distinctPairs
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, hne⟩
      · rw [← hp2]; exact mem_pointsOnLine_self E h1
      · rw [← hp2]
        simp only [pointsOnLine, Finset.mem_filter]
        refine ⟨h2, ?_⟩
        simp only [interceptOf]
        have hxne_diff : p.2.1 - p.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
        have heq : p.2.2 - p.1.2 = lam * (p.2.1 - p.1.1) := by
          have hs : (p.2.2 - p.1.2) * (p.2.1 - p.1.1)⁻¹ = lam := hslope
          calc p.2.2 - p.1.2
              = (p.2.2 - p.1.2) * ((p.2.1 - p.1.1)⁻¹ * (p.2.1 - p.1.1)) := by
                  rw [inv_mul_cancel₀ hxne_diff, mul_one]
            _ = (p.2.2 - p.1.2) * (p.2.1 - p.1.1)⁻¹ * (p.2.1 - p.1.1) := by ring
            _ = lam * (p.2.1 - p.1.1) := by rw [hs]
        linear_combination heq
    have hcard := Finset.card_le_card hsub
    have hle3 : (pointsOnLine E lam mu).card ≤ 3 := line_meets_cubic_le_three E lam mu
    rw [card_distinctPairs] at hcard
    have hbound : (pointsOnLine E lam mu).card * (pointsOnLine E lam mu).card
          - (pointsOnLine E lam mu).card ≤ 6 := by
      set n := (pointsOnLine E lam mu).card
      interval_cases n <;> omega
    omega
  calc (pairsWithSlope E lam).card
      ≤ 6 * ((pairsWithSlope E lam).image f).card :=
        Finset.card_le_mul_card_image _ _ hfiber
    _ ≤ 6 * (goodIntercepts E lam).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg_sub)

/-- Summing `pairsWithSlope` over all slopes gives back `validPairs`. -/
lemma validPairs_card_eq_sum_pairsWithSlope :
    (validPairs E).card = ∑ lam : ZMod E.q, (pairsWithSlope E lam).card := by
  classical
  have hmaps : ∀ p ∈ validPairs E,
      slopeOf p.1.1 p.1.2 p.2.1 p.2.2 ∈ (Finset.univ : Finset (ZMod E.q)) :=
    fun _ _ => Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  ext p
  simp only [pairsWithSlope, validPairs, distinctPairs, Finset.mem_filter,
             Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, hne⟩, hxne, _hPnegP⟩, hslope⟩
    exact ⟨⟨⟨h1, h2⟩, hne⟩, hxne, hslope⟩
  · rintro ⟨⟨⟨h1, h2⟩, hne⟩, hxne, hslope⟩
    refine ⟨⟨⟨⟨h1, h2⟩, hne⟩, hxne, ?_⟩, hslope⟩
    intro heq
    apply hxne
    have : p.1.1 = (p.2.1, -p.2.2).1 := by rw [heq]
    exact this

/-- Aggregate bound: `|validPairs E| ≤ 6 · ∑_λ |goodIntercepts λ|`. -/
theorem validPairs_le_six_sum_goodIntercepts :
    (validPairs E).card ≤ 6 * ∑ lam : ZMod E.q, (goodIntercepts E lam).card := by
  rw [validPairs_card_eq_sum_pairsWithSlope E, Finset.mul_sum]
  exact Finset.sum_le_sum
    (fun lam _ => pairsWithSlope_card_le_six_mul_goodIntercepts E lam)

/-- **existence lemma.** Given a "reference point set" `S`
    (in the T5 application: `S = range Q ∪ range R`) and a required
    lower bound `N` on realized chord-intercepts (in T5: `N = d + M`),
    there exists a slope `λ ∈ F_q` such that:
    (i) `zLambda E λ` is injective on `S` (no projection collisions
        among points of `S`), and
    (ii) at least `N` distinct intercepts `μ` are realized as chord
        intercepts of non-vertical pairs on `E` with slope `λ`.

    This follows from pigeonhole: the total number of non-vertical
    distinct ordered pairs on `E` is bounded below by `6 · E.q · (N +
    S.card(S.card-1))`, and each slope carries ≤ 6 · |goodIntercepts|
    such pairs. After excluding the ≤ `S.card(S.card-1)` bad slopes
    from A4, a slope with ≥ `N` good intercepts remains. -/
theorem exists_good_lambda
    (S : Finset (ZMod E.q × ZMod E.q))
    (N : ℕ)
    (hQuant : 6 * E.q * (N + S.card * (S.card - 1)) + 1 ≤ (validPairs E).card) :
    ∃ lam : ZMod E.q,
      Set.InjOn (zLambda E lam) S ∧ N ≤ (goodIntercepts E lam).card := by
  classical
  -- A4 bad set: slopes collapsing two points of S under zLambda.
  set bad := (Finset.univ : Finset (ZMod E.q)).filter (fun lam =>
    ∃ P₁ ∈ S, ∃ P₂ ∈ S, P₁ ≠ P₂ ∧ zLambda E lam P₁ = zLambda E lam P₂)
  have hbad_le : bad.card ≤ S.card * (S.card - 1) := badLambdaSet_card_le E S
  have hsum_ineq := validPairs_le_six_sum_goodIntercepts E
  by_contra habsurd
  push_neg at habsurd
  -- bad = {lam : ¬ InjOn}
  have hbad_iff : ∀ lam : ZMod E.q, lam ∉ bad ↔ Set.InjOn (zLambda E lam) S := by
    intro lam
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Set.InjOn]
    constructor
    · intro h P₁ hP₁ P₂ hP₂ hz
      by_contra hne
      exact h ⟨P₁, hP₁, P₂, hP₂, hne, hz⟩
    · intro h ⟨P₁, hP₁, P₂, hP₂, hne, hz⟩
      exact hne (h hP₁ hP₂ hz)
  -- For each lam ∉ bad: |goodIntercepts lam| + 1 ≤ N.
  have hbound_notbad : ∀ lam ∈ Finset.univ \ bad,
      (goodIntercepts E lam).card + 1 ≤ N := by
    intro lam hlam
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hlam
    exact habsurd lam ((hbad_iff lam).mp hlam)
  have hcard_univ : (Finset.univ : Finset (ZMod E.q)).card = E.q := by
    rw [Finset.card_univ, ZMod.card E.q]
  set c := (Finset.univ \ bad : Finset (ZMod E.q)).card with hc_def
  have hc_le_q : c ≤ E.q := by
    rw [hc_def]; exact (Finset.card_le_univ _).trans (le_of_eq hcard_univ)
  -- Bound ∑_bad via pointwise ≤ E.q.
  have hsum_bad :
      ∑ lam ∈ bad, (goodIntercepts E lam).card ≤ bad.card * E.q := by
    calc ∑ lam ∈ bad, (goodIntercepts E lam).card
        ≤ ∑ _ ∈ bad, E.q := by
          apply Finset.sum_le_sum
          intro lam _
          exact ((goodIntercepts E lam).card_le_univ).trans (le_of_eq hcard_univ)
      _ = bad.card * E.q := by rw [Finset.sum_const, smul_eq_mul]
  -- Bound ∑_notbad + c ≤ N · c.
  have hsum_notbad_shifted :
      (∑ lam ∈ Finset.univ \ bad, (goodIntercepts E lam).card) + c ≤ N * c := by
    have hsum_add : ∑ lam ∈ Finset.univ \ bad, ((goodIntercepts E lam).card + 1)
        ≤ ∑ _ ∈ Finset.univ \ bad, N := Finset.sum_le_sum hbound_notbad
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul, Nat.mul_one, Nat.mul_comm] at hsum_add
    exact hsum_add
  -- Split ∑ over all slopes into bad + notbad parts.
  have hsum_split : ∑ lam : ZMod E.q, (goodIntercepts E lam).card =
      (∑ lam ∈ bad, (goodIntercepts E lam).card) +
      (∑ lam ∈ Finset.univ \ bad, (goodIntercepts E lam).card) := by
    have : (∑ lam : ZMod E.q, (goodIntercepts E lam).card) =
        ∑ lam ∈ (Finset.univ : Finset (ZMod E.q)), (goodIntercepts E lam).card := rfl
    rw [this, ← Finset.sum_sdiff (Finset.subset_univ bad)]
    ring
  -- Deriving key inequalities for omega.
  set T := ∑ lam : ZMod E.q, (goodIntercepts E lam).card
  set Tbad := ∑ lam ∈ bad, (goodIntercepts E lam).card
  set Tnb := ∑ lam ∈ Finset.univ \ bad, (goodIntercepts E lam).card
  -- From hQuant + hsum_ineq: 6 · E.q · (N + b) + 1 ≤ 6 · T.
  -- Divide by 6 (nat): E.q · (N + b) + 1 ≤ T.
  have hA : E.q * (N + S.card * (S.card - 1)) + 1 ≤ T := by
    have h1 : 6 * E.q * (N + S.card * (S.card - 1)) + 1 ≤ 6 * T :=
      hQuant.trans hsum_ineq
    have h2 : 6 * (E.q * (N + S.card * (S.card - 1))) + 1 ≤ 6 * T := by
      rw [← Nat.mul_assoc]; exact h1
    omega
  -- From hsum_split + hsum_bad + hbad_le: Tnb ≥ E.q * N + 1.
  have hB : E.q * N + 1 ≤ Tnb := by
    have h1 : Tbad ≤ S.card * (S.card - 1) * E.q := by
      calc Tbad ≤ bad.card * E.q := hsum_bad
        _ ≤ S.card * (S.card - 1) * E.q := Nat.mul_le_mul_right _ hbad_le
    have h3 : E.q * (N + S.card * (S.card - 1)) =
              E.q * N + E.q * (S.card * (S.card - 1)) := by ring
    have h4 : E.q * (S.card * (S.card - 1)) =
              S.card * (S.card - 1) * E.q := by ring
    omega
  -- From hsum_notbad_shifted + hc_le_q: Tnb + c ≤ N * E.q.
  have hC : Tnb + c ≤ N * E.q :=
    hsum_notbad_shifted.trans (Nat.mul_le_mul_left N hc_le_q)
  -- Final contradiction: E.q * N + 1 ≤ Tnb, Tnb + c ≤ N * E.q, so 1 + c ≤ 0.
  have hmul : E.q * N = N * E.q := Nat.mul_comm _ _
  omega

/-! ## polyFibK degree and root-count arguments -/

/-- Each linear factor `X - C α` has natDegree ≤ 1 (uniformly). -/
private lemma XsubC_natDegree_le_one {R : Type*} [CommRing R] (a : R) :
    (X - C a).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le Polynomial.natDegree_X_le ?_
  rw [Polynomial.natDegree_C]
  exact Nat.zero_le _

/-- A product of `s.card` linear factors `(X - C α_i)` has natDegree ≤ `s.card`.
    Helper for `polyFibK_natDegree_le`. -/
private lemma prod_XsubC_natDegree_le {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (g : ι → R[X])
    (hg : ∀ i ∈ s, (g i).natDegree ≤ 1) :
    (∏ i ∈ s, g i).natDegree ≤ s.card := by
  refine (Polynomial.natDegree_prod_le s g).trans ?_
  calc ∑ i ∈ s, (g i).natDegree
      ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum hg
    _ = s.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]

/-- `polyFibK` has degree at most `d + M - 1`. -/
theorem polyFibK_natDegree_le {d M : ℕ} (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    (polyFibK E lam Q β R m).natDegree ≤ d + M - 1 := by
  unfold polyFibK
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · -- First sum: each term has degree ≤ (d-1) + M ≤ d + M - 1 (when d ≥ 1).
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro k _
    have hd_pos : 1 ≤ d := by have := k.isLt; omega
    have h_βerase :
        (C (β k) * ∏ k' ∈ Finset.univ.erase k,
          (X - C (zLambda E lam (Q k')))).natDegree ≤ d - 1 := by
      refine natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      refine (prod_XsubC_natDegree_le _ _ (fun _ _ =>
        XsubC_natDegree_le_one _)).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
    have h_univR :
        (∏ j : Fin M, (X - C (zLambda E lam (R j)))).natDegree ≤ M := by
      refine (prod_XsubC_natDegree_le _ _ (fun _ _ =>
        XsubC_natDegree_le_one _)).trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    refine natDegree_mul_le.trans ?_
    calc _ ≤ (d - 1) + M := Nat.add_le_add h_βerase h_univR
      _ ≤ d + M - 1 := by omega
  · -- Second sum: each term has degree ≤ d + (M-1) ≤ d + M - 1 (when M ≥ 1).
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro j _
    have hM_pos : 1 ≤ M := by have := j.isLt; omega
    have h_mkuniv :
        (C (m j) * ∏ k : Fin d,
          (X - C (zLambda E lam (Q k)))).natDegree ≤ d := by
      refine natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      refine (prod_XsubC_natDegree_le _ _ (fun _ _ =>
        XsubC_natDegree_le_one _)).trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have h_erase :
        (∏ j' ∈ Finset.univ.erase j,
          (X - C (zLambda E lam (R j')))).natDegree ≤ M - 1 := by
      refine (prod_XsubC_natDegree_le _ _ (fun _ _ =>
        XsubC_natDegree_le_one _)).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
    refine natDegree_mul_le.trans ?_
    calc _ ≤ d + (M - 1) := Nat.add_le_add h_mkuniv h_erase
      _ ≤ d + M - 1 := by omega

/-- If `polyG ≡ 0` on non-vertical pairs of `E.points × E.points` and
    `lam` has enough good intercepts, then `polyFibK lam ≡ 0` as a
    polynomial in `(ZMod E.q)[X]`.

    Weaker hypothesis than "polyG ≡ 0 on all of F_q² × F_q²": the proof
    only invokes `polyG = 0` at pairs on a chord with slope `lam`, which
    are always on E by construction of `goodIntercepts`. -/
theorem polyFibK_eq_zero_of_polyG_zero {d M : ℕ}
    (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hGood : d + M ≤ (goodIntercepts E lam).card)
    (hfZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E Q β R m A₀ A₁ = 0) :
    polyFibK E lam Q β R m = 0 := by
  classical
  by_cases hdM : d + M = 0
  · -- d = M = 0: polyFibK = 0 trivially.
    have hd : d = 0 := by omega
    have hM : M = 0 := by omega
    subst hd
    subst hM
    unfold polyFibK
    simp
  have hdM_pos : 1 ≤ d + M := Nat.one_le_iff_ne_zero.mpr hdM
  by_contra hne
  -- Each mu ∈ goodIntercepts is a root of polyFibK.
  have hRoots : ∀ mu ∈ goodIntercepts E lam,
      (polyFibK E lam Q β R m).eval mu = 0 := by
    intro mu hmu
    simp only [goodIntercepts, Finset.mem_filter, Finset.mem_univ, true_and] at hmu
    have h_onept_lt : 1 < (pointsOnLine E lam mu).card := hmu
    obtain ⟨A₀, hA₀, A₁, hA₁, hne_A⟩ := Finset.one_lt_card.mp h_onept_lt
    simp only [pointsOnLine, Finset.mem_filter] at hA₀ hA₁
    have hNV : A₀.1 ≠ A₁.1 := by
      intro hx
      apply hne_A
      apply Prod.ext hx
      rw [hA₀.2, hA₁.2, hx]
    have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
    have hslope : slopeOf A₀.1 A₀.2 A₁.1 A₁.2 = lam := by
      simp only [slopeOf]
      rw [hA₀.2, hA₁.2]
      have : lam * A₁.1 + mu - (lam * A₀.1 + mu) = lam * (A₁.1 - A₀.1) := by ring
      rw [this, mul_assoc, mul_inv_cancel₀ hxne, mul_one]
    have hmu_eq : zLambda E lam A₀ = mu := by
      simp only [zLambda]
      rw [hA₀.2]; ring
    have hPolyGZero := hfZero A₀ A₁ hA₀.1 hA₁.1 hNV
    rw [polyG_eq_polyFibK_eval E Q β R m A₀ A₁ hNV, hslope, hmu_eq] at hPolyGZero
    have hpow_ne : (-(A₁.1 - A₀.1))^(d + M - 1) ≠ 0 := by
      apply pow_ne_zero
      rw [neg_ne_zero]
      exact hxne
    exact (mul_eq_zero.mp hPolyGZero).resolve_left hpow_ne
  -- goodIntercepts ⊆ polyFibK.roots.toFinset.
  have h_sub : goodIntercepts E lam ⊆ (polyFibK E lam Q β R m).roots.toFinset := by
    intro mu hmu
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact hRoots mu hmu
  have h_le : (goodIntercepts E lam).card ≤ d + M - 1 :=
    calc (goodIntercepts E lam).card
        ≤ (polyFibK E lam Q β R m).roots.toFinset.card :=
          Finset.card_le_card h_sub
      _ ≤ Multiset.card (polyFibK E lam Q β R m).roots :=
          (polyFibK E lam Q β R m).roots.toFinset_card_le
      _ ≤ (polyFibK E lam Q β R m).natDegree :=
          (polyFibK E lam Q β R m).card_roots'
      _ ≤ d + M - 1 := polyFibK_natDegree_le E lam Q β R m
  omega

/-! ## σ extraction helpers -/

/-- Evaluation of `polyFibK` at `τ(Q k)` isolates only the k-th first-sum
    term (second-sum vanishes entirely; other first-sum terms vanish via
    a shared `(X - τ(Q k))` factor in `erase k'`). -/
private lemma polyFibK_eval_tauQ_eq {d M : ℕ} (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (k : Fin d) :
    (polyFibK E lam Q β R m).eval (zLambda E lam (Q k)) =
      β k *
        (∏ k' ∈ Finset.univ.erase k,
          (zLambda E lam (Q k) - zLambda E lam (Q k'))) *
        (∏ j : Fin M,
          (zLambda E lam (Q k) - zLambda E lam (R j))) := by
  unfold polyFibK
  simp only [eval_add, eval_finset_sum, eval_mul, eval_C,
             Polynomial.eval_prod, eval_sub, eval_X]
  -- First sum: only k-th term survives.
  have hFirstSum :
      ∑ k' : Fin d, β k' *
          (∏ k'' ∈ Finset.univ.erase k',
            (zLambda E lam (Q k) - zLambda E lam (Q k''))) *
          (∏ j : Fin M,
            (zLambda E lam (Q k) - zLambda E lam (R j))) =
      β k *
          (∏ k'' ∈ Finset.univ.erase k,
            (zLambda E lam (Q k) - zLambda E lam (Q k''))) *
          (∏ j : Fin M,
            (zLambda E lam (Q k) - zLambda E lam (R j))) := by
    rw [Finset.sum_eq_single k]
    · intro k' _ hne
      have hkmem : k ∈ Finset.univ.erase k' :=
        Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero hkmem (by ring)]
      ring
    · intro h; exact absurd (Finset.mem_univ k) h
  -- Second sum: all terms vanish (common factor `(τ Q k - τ Q k) = 0`).
  have hSecondSum :
      ∑ j : Fin M, m j *
          (∏ k' : Fin d,
            (zLambda E lam (Q k) - zLambda E lam (Q k'))) *
          (∏ j' ∈ Finset.univ.erase j,
            (zLambda E lam (Q k) - zLambda E lam (R j'))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hkmem : k ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
    rw [Finset.prod_eq_zero hkmem (by ring)]
    ring
  rw [hFirstSum, hSecondSum, add_zero]

/-- Evaluation of `polyFibK` at `τ(R j)` isolates only the j-th second-sum
    term (first-sum vanishes entirely; other second-sum terms vanish via
    a shared `(X - τ(R j))` factor in `erase j'`). -/
private lemma polyFibK_eval_tauR_eq {d M : ℕ} (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (j : Fin M) :
    (polyFibK E lam Q β R m).eval (zLambda E lam (R j)) =
      m j *
        (∏ k : Fin d,
          (zLambda E lam (R j) - zLambda E lam (Q k))) *
        (∏ j' ∈ Finset.univ.erase j,
          (zLambda E lam (R j) - zLambda E lam (R j'))) := by
  unfold polyFibK
  simp only [eval_add, eval_finset_sum, eval_mul, eval_C,
             Polynomial.eval_prod, eval_sub, eval_X]
  -- First sum: all terms vanish (Π_j has factor (τ R j - τ R j) = 0).
  have hFirstSum :
      ∑ k : Fin d, β k *
          (∏ k'' ∈ Finset.univ.erase k,
            (zLambda E lam (R j) - zLambda E lam (Q k''))) *
          (∏ j' : Fin M,
            (zLambda E lam (R j) - zLambda E lam (R j'))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hjmem : j ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ _
    have hprod_zero :
        (∏ j' : Fin M, (zLambda E lam (R j) - zLambda E lam (R j'))) = 0 :=
      Finset.prod_eq_zero hjmem (by ring)
    rw [hprod_zero]; ring
  -- Second sum: only j-th term survives.
  have hSecondSum :
      ∑ j' : Fin M, m j' *
          (∏ k : Fin d,
            (zLambda E lam (R j) - zLambda E lam (Q k))) *
          (∏ j'' ∈ Finset.univ.erase j',
            (zLambda E lam (R j) - zLambda E lam (R j''))) =
      m j *
          (∏ k : Fin d,
            (zLambda E lam (R j) - zLambda E lam (Q k))) *
          (∏ j'' ∈ Finset.univ.erase j,
            (zLambda E lam (R j) - zLambda E lam (R j''))) := by
    rw [Finset.sum_eq_single j]
    · intro j' _ hne
      have hjmem : j ∈ Finset.univ.erase j' :=
        Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero hjmem (by ring)]
      ring
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hFirstSum, hSecondSum, zero_add]

/-! ## Factorization identity `polyFibK = B · (Σ over k)` -/

/-- Under the matching `σ : Fin d ↪ Fin M` with `Q k = R (σ k)` and
    `m j = 0` for `j ∉ range σ`, the polynomial `polyFibK` factors as a
    product of the full R-product `∏ j (X - C (τ R j))` with a single sum
    over `Fin d` in simple-pole form. -/
private lemma polyFibK_factor_of_sigma {d M : ℕ} (lam : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (σ : Fin d ↪ Fin M) (hQR : ∀ k, Q k = R (σ k))
    (hMNonrange : ∀ j, j ∉ Set.range σ → m j = 0) :
    polyFibK E lam Q β R m =
      (∏ j : Fin M, (X - C (zLambda E lam (R j)))) *
      (∑ k : Fin d, C (β k + m (σ k)) *
        ∏ k' ∈ Finset.univ.erase k, (X - C (zLambda E lam (Q k')))) := by
  classical
  unfold polyFibK
  set τ := zLambda E lam
  -- Step A: Reindex second sum via σ (using m_j = 0 off range σ).
  have hA :
      (∑ j : Fin M, C (m j) *
        (∏ k : Fin d, (X - C (τ (Q k)))) *
        (∏ j' ∈ Finset.univ.erase j, (X - C (τ (R j')))))
      = ∑ k : Fin d, C (m (σ k)) *
          (∏ k' : Fin d, (X - C (τ (Q k')))) *
          (∏ j' ∈ Finset.univ.erase (σ k), (X - C (τ (R j')))) := by
    have hSub :
        (∑ j : Fin M, C (m j) * (∏ k : Fin d, (X - C (τ (Q k)))) *
          (∏ j' ∈ Finset.univ.erase j, (X - C (τ (R j')))))
        = ∑ j ∈ (Finset.univ : Finset (Fin d)).image σ, C (m j) *
            (∏ k : Fin d, (X - C (τ (Q k)))) *
            (∏ j' ∈ Finset.univ.erase j, (X - C (τ (R j')))) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hnotin
      have hnotrange : j ∉ Set.range σ := by
        intro ⟨k, hk⟩
        apply hnotin
        rw [Finset.mem_image]
        exact ⟨k, Finset.mem_univ _, hk⟩
      rw [hMNonrange j hnotrange, map_zero, zero_mul, zero_mul]
    rw [hSub, Finset.sum_image (fun _ _ _ _ heq => σ.injective heq)]
  rw [hA]
  -- Step B: For each k, rewrite second-sum-k-term using Q k = R (σ k) to get the
  --         `Π_{k' ≠ k} · Π_j` shape matching first-sum-k-term.
  have hB : ∀ k : Fin d,
      C (m (σ k)) *
        (∏ k' : Fin d, (X - C (τ (Q k')))) *
        (∏ j' ∈ Finset.univ.erase (σ k), (X - C (τ (R j')))) =
      C (m (σ k)) *
        (∏ k' ∈ Finset.univ.erase k, (X - C (τ (Q k')))) *
        (∏ j : Fin M, (X - C (τ (R j)))) := by
    intro k
    have hQk : Q k = R (σ k) := hQR k
    rw [show (∏ k' : Fin d, (X - C (τ (Q k')))) =
            (X - C (τ (Q k))) * (∏ k' ∈ Finset.univ.erase k, (X - C (τ (Q k'))))
          from (Finset.mul_prod_erase Finset.univ
                (fun k' => X - C (τ (Q k'))) (Finset.mem_univ k)).symm]
    rw [hQk]
    rw [show (∏ j : Fin M, (X - C (τ (R j)))) =
            (X - C (τ (R (σ k)))) *
              (∏ j' ∈ Finset.univ.erase (σ k), (X - C (τ (R j'))))
          from (Finset.mul_prod_erase (Finset.univ : Finset (Fin M))
                (fun j => X - C (τ (R j))) (Finset.mem_univ (σ k))).symm]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hB k)]
  -- Step C: Combine first sum + second sum into single sum over k with coefficient
  --         `(β k + m σ k)`, then factor `Π_j (X - C (τ R j))` out.
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show C (β k + m (σ k)) = C (β k) + C (m (σ k)) from map_add _ _ _]
  ring

/-! ## Main theorem: `log_deriv_nonvanishing_criterion` -/

/-- **Non-vanishing criterion (T5).** If `polyG ≡ 0` on non-vertical
    pairs of `E.points × E.points` with `Q`, `R` distinct, `β` nonzero,
    and `q` large enough (quantified by `hQuant`), then there exists
    an injection `σ : Fin d ↪ Fin M` matching
    `Q k = R (σ k)`, `β k + m (σ k) = 0`, and `m j = 0` for `j ∉ range σ`.

    The hypothesis was weakened (compared to an earlier `∀ A₀ A₁ : F_q²,
    polyG = 0` formulation): the proof only uses `polyG = 0` at pairs
    of distinct non-vertical points on `E`, which is the form naturally
    derivable from the log-derivative bridge. -/
theorem log_deriv_nonvanishing_criterion {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hQuant : 6 * E.q * (d + M + (d + M) * (d + M - 1)) + 1 ≤
              (validPairs E).card)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hfZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E Q beta R m A₀ A₁ = 0) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0) := by
  classical
  -- Step 1: Set up S = range Q ∪ range R and extract good λ via A3.
  set S : Finset (ZMod E.q × ZMod E.q) :=
    ((Finset.univ : Finset (Fin d)).image Q) ∪
    ((Finset.univ : Finset (Fin M)).image R)
  have hS_card_le : S.card ≤ d + M := by
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add
      (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))
      (Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin]))
  have hQuantS : 6 * E.q * ((d + M) + S.card * (S.card - 1)) + 1 ≤
                  (validPairs E).card := by
    refine le_trans ?_ hQuant
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul hS_card_le (Nat.sub_le_sub_right hS_card_le 1)
  obtain ⟨lam, hInjS, hGood⟩ := exists_good_lambda E S (d + M) hQuantS
  have hQmem : ∀ k, Q k ∈ S := fun k => Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have hRmem : ∀ j, R j ∈ S := fun j => Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  set τ := zLambda E lam
  -- Step 2: polyFibK = 0 (as a polynomial in F_q[X]).
  have hPolyZero : polyFibK E lam Q beta R m = 0 :=
    polyFibK_eq_zero_of_polyG_zero E lam Q beta R m hGood hfZero
  -- Step 3: For each k, ∃ j with R j = Q k. Build σ via Classical.choose.
  have hSigmaExists : ∀ k : Fin d, ∃ j : Fin M, R j = Q k := by
    intro k
    have hEval : (polyFibK E lam Q beta R m).eval (τ (Q k)) = 0 := by
      rw [hPolyZero]; simp
    rw [polyFibK_eval_tauQ_eq] at hEval
    have hβk : beta k ≠ 0 := hBetaNz k
    have hProdQ :
        (∏ k' ∈ Finset.univ.erase k, (τ (Q k) - τ (Q k'))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k' hk'
      rw [sub_ne_zero]
      intro heq
      have hk'_ne := (Finset.mem_erase.mp hk').1
      exact hk'_ne (hDistinctQ (hInjS (hQmem k') (hQmem k) heq.symm))
    have hProdR : (∏ j : Fin M, (τ (Q k) - τ (R j))) = 0 := by
      rcases mul_eq_zero.mp hEval with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hβk
        · exact absurd h hProdQ
      · exact h
    rw [Finset.prod_eq_zero_iff] at hProdR
    obtain ⟨j, _, hzero⟩ := hProdR
    have hτeq : τ (Q k) = τ (R j) := sub_eq_zero.mp hzero
    exact ⟨j, hInjS (hRmem j) (hQmem k) hτeq.symm⟩
  let sigma_fun : Fin d → Fin M := fun k => Classical.choose (hSigmaExists k)
  have hσ_def : ∀ k, R (sigma_fun k) = Q k :=
    fun k => Classical.choose_spec (hSigmaExists k)
  have hσ_inj : Function.Injective sigma_fun := by
    intro k₁ k₂ heq
    have h1 := hσ_def k₁
    have h2 := hσ_def k₂
    rw [heq] at h1
    exact hDistinctQ (h1.symm.trans h2)
  let σ : Fin d ↪ Fin M := ⟨sigma_fun, hσ_inj⟩
  -- Step 4: m j = 0 for j ∉ range σ (via eval at τ(R j)).
  have hM_offrange : ∀ j, j ∉ Set.range σ → m j = 0 := by
    intro j hj
    have hEval : (polyFibK E lam Q beta R m).eval (τ (R j)) = 0 := by
      rw [hPolyZero]; simp
    rw [polyFibK_eval_tauR_eq] at hEval
    have hProdR :
        (∏ j' ∈ Finset.univ.erase j, (τ (R j) - τ (R j'))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j' hj'
      rw [sub_ne_zero]
      intro heq
      have hj'_ne := (Finset.mem_erase.mp hj').1
      exact hj'_ne (hDistinctR (hInjS (hRmem j') (hRmem j) heq.symm))
    have hProdQ : (∏ k : Fin d, (τ (R j) - τ (Q k))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k _
      rw [sub_ne_zero]
      intro heq
      have hRQ : R j = Q k := hInjS (hRmem j) (hQmem k) heq
      have hjeq : j = sigma_fun k :=
        hDistinctR (hRQ.trans (hσ_def k).symm)
      exact hj ⟨k, hjeq.symm⟩
    rcases mul_eq_zero.mp hEval with h | h
    · exact (mul_eq_zero.mp h).resolve_right hProdQ
    · exact absurd h hProdR
  -- Step 5: Factor polyFibK = B · SumF and apply simple_pole_fraction_zero.
  have hFactor := polyFibK_factor_of_sigma E lam Q beta R m σ
    (fun k => (hσ_def k).symm) hM_offrange
  rw [hPolyZero] at hFactor
  set B := ∏ j : Fin M, (X - C (τ (R j))) with hB_def
  set SumF := ∑ k : Fin d, C (beta k + m (σ k)) *
      ∏ k' ∈ Finset.univ.erase k, (X - C (τ (Q k')))
  -- B is nonzero (product of nonzero linear factors in an integral domain).
  have hB_ne : B ≠ 0 := by
    rw [hB_def]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => Polynomial.X_sub_C_ne_zero _)
  have hSumF_zero : SumF = 0 := by
    have : B * SumF = 0 := hFactor.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hB_ne
    · exact h
  -- Step 6: Apply simple_pole_fraction_zero on Finset.univ : Finset (Fin d).
  have hBetaMsigma : ∀ k : Fin d, beta k + m (σ k) = 0 := by
    intro k
    have hInjUniv :
        Set.InjOn (fun k' => τ (Q k')) (Finset.univ : Finset (Fin d)) := by
      intro a _ b _ heq
      exact hDistinctQ (hInjS (hQmem a) (hQmem b) heq)
    exact simple_pole_fraction_zero (Finset.univ : Finset (Fin d))
      (fun k' => τ (Q k')) (fun k' => beta k' + m (σ k')) hInjUniv
      hSumF_zero k (Finset.mem_univ _)
  refine ⟨σ, fun k => (hσ_def k).symm, hBetaMsigma, hM_offrange⟩

end Divisor
