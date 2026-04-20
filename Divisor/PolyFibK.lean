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
    rw [Finset.card_insert_of_not_mem (by simp [hne]), Finset.card_singleton]
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

/-- **Phase A3 existence lemma.** Given a "reference point set" `S`
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

end Divisor
