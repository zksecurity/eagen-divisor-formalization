/-
  Divisor/SigmaMatching.lean

  σ-matching from polyGFull vanishing: T5-replacement path that
  closes the `hAllZero` branch of `ma_extractable` without the
  quadratic `|validPairs|` threshold of the original T5.

  Path: view `polyG` as a 4-variate polynomial (`polyGFull`) and
  apply the Lang–Weil (DKL+Bezout) contrapositive to obtain
  identical vanishing on `E × E`; then extract the σ-matching
  permutation from the equality of factored norm forms.
-/
import Divisor.ClearedFullPoly

open Polynomial Finset

namespace Divisor

local notation:max "Xm" i => (MvPolynomial.X i : FourVarPoly _)
local notation:max "Cm" c => (MvPolynomial.C c : FourVarPoly _)

variable (E : ECSetup)

/-! ## T5 replacement scaffolding

    To eliminate the quadratic `6·q·((d+k+1)+(d+k+1)·(d+k))` summand in
    `ma_extractable`'s bound, we need to close the `hAllZero` branch
    (where `logDerivCheckFn ≡ 0` on non-vertical E×E) without T5's
    `exists_good_lambda` step (whose quadratic threshold on
    `|validPairs|` is the source of the quadratic summand).

    Path: view `polyG` as a 4-variate polynomial (`polyGFull`) and
    apply the Lang-Weil contrapositive. If `polyG` vanishes pointwise
    on all but a small subset of E × E, then by `bivariate_poly_zeros
    _on_ExE_le`, `polyGFull` has no nonzero witness on E × E — a
    stronger statement than pointwise vanishing on non-vertical pairs.
    From there the paper-aligned residue-matching argument
    (`sections/ip.tex:552-634`) extracts the σ-matching directly.

    This section provides the 4-variate polyG scaffold. -/

/-- 4-variate lift of `polyG`. Each `ellP (P)` becomes `lineEvalNumAtFull P`. -/
noncomputable def polyGFull
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    FourVarPoly E.q :=
  (∑ k : Fin d,
    (MvPolynomial.C (beta k) : FourVarPoly E.q) *
    (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k')) *
    (∏ j : Fin M, lineEvalNumAtFull E (R j))) +
  (∑ j : Fin M,
    (MvPolynomial.C (m j) : FourVarPoly E.q) *
    (∏ k : Fin d, lineEvalNumAtFull E (Q k)) *
    (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j')))

/-- Compat: `polyGFull` at `(A₀, A₁)` agrees with `polyG Q beta R m A₀ A₁`. -/
theorem bivEval₂_polyGFull_eq_polyG
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = polyG E Q beta R m A₀ A₁ := by
  simp only [polyGFull, polyG, bivEval₂_add, bivEval₂_sum, bivEval₂_mul,
    bivEval₂_prod, bivEval₂_C, bivEval₂_lineEvalNumAtFull, ellP]

private theorem lineEvalNumAtFull_bi_x_degree_le (pt : ZMod E.q × ZMod E.q) :
    bi_x_degree_le E (lineEvalNumAtFull E pt) 1 1 := by
  unfold lineEvalNumAtFull
  apply bi_x_degree_le.sub
  · have h1 : bi_x_degree_le E (embedScalarFull E pt.2 - varA₀y E) 0 0 :=
      bi_x_degree_le.sub (by unfold embedScalarFull; exact bi_x_degree_le.C _)
        (by unfold varA₀y; exact bi_x_degree_le.Y₀)
    have h2 : bi_x_degree_le E (lamDenFull E) 1 1 := by
      unfold lamDenFull varA₁x varA₀x
      exact bi_x_degree_le.sub (bi_x_degree_le.mono bi_x_degree_le.X₁ (by omega) (by omega))
        (bi_x_degree_le.mono bi_x_degree_le.X₀ (by omega) (by omega))
    simpa using bi_x_degree_le.mul h1 h2
  · have h1 : bi_x_degree_le E (embedScalarFull E pt.1 - varA₀x E) 1 0 :=
      bi_x_degree_le.sub
        (bi_x_degree_le.mono (by unfold embedScalarFull; exact bi_x_degree_le.C _)
          (by omega) (by omega))
        (by unfold varA₀x; exact bi_x_degree_le.mono bi_x_degree_le.X₀ (by omega) (by omega))
    have h2 : bi_x_degree_le E (lamNumFull E) 0 0 := by
      unfold lamNumFull varA₁y varA₀y
      exact bi_x_degree_le.sub bi_x_degree_le.Y₁ bi_x_degree_le.Y₀
    exact bi_x_degree_le.mono (bi_x_degree_le.mul h1 h2) (by omega) (by omega)

private theorem bi_x_degree_le_prod_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → FourVarPoly E.q)
    (hf : ∀ i ∈ s, bi_x_degree_le E (f i) 1 1) :
    bi_x_degree_le E (∏ i ∈ s, f i) s.card s.card := by
  induction s using Finset.induction_on with
  | empty => simp; exact ⟨(MvPolynomial.degreeOf_one _).le, (MvPolynomial.degreeOf_one _).le⟩
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has]
    have hmul := bi_x_degree_le.mul (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hmul using 1 <;> omega

/-- `polyGFull` has bi-x-degree `(d + M - 1, d + M - 1)`.

    Proof: each `lineEvalNumAtFull` has bi-x-degree `(1, 1)`. A product
    of `d + M − 1` such (in each summand of either sum) gives `(d + M −
    1, d + M − 1)`. Summing over `d + M` summands preserves the bound. -/
theorem polyGFull_bi_x_degree_le
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    bi_x_degree_le E (polyGFull E Q beta R m) (d + M) (d + M) := by
  unfold polyGFull
  apply bi_x_degree_le.add
  · apply bi_x_degree_le.sum
    intro k _
    have hC : bi_x_degree_le E (MvPolynomial.C (beta k) : FourVarPoly E.q) 0 0 :=
      bi_x_degree_le.C _
    have hErase : bi_x_degree_le E
        (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k'))
        ((Finset.univ (α := Fin d)).erase k).card
        ((Finset.univ (α := Fin d)).erase k).card :=
      bi_x_degree_le_prod_finset E _ _ (fun i _ => lineEvalNumAtFull_bi_x_degree_le E (Q i))
    have hProd : bi_x_degree_le E
        (∏ j : Fin M, lineEvalNumAtFull E (R j)) (M * 1) (M * 1) :=
      bi_x_degree_le.prod_fin _ (fun j => lineEvalNumAtFull_bi_x_degree_le E (R j))
    have hEraseCard : ((Finset.univ (α := Fin d)).erase k).card ≤ d :=
      le_trans Finset.card_erase_le (by simp)
    have hMul := bi_x_degree_le.mul (bi_x_degree_le.mul hC hErase) hProd
    apply bi_x_degree_le.mono hMul <;> omega
  · apply bi_x_degree_le.sum
    intro j _
    have hC : bi_x_degree_le E (MvPolynomial.C (m j) : FourVarPoly E.q) 0 0 :=
      bi_x_degree_le.C _
    have hProd : bi_x_degree_le E
        (∏ k : Fin d, lineEvalNumAtFull E (Q k)) (d * 1) (d * 1) :=
      bi_x_degree_le.prod_fin _ (fun k => lineEvalNumAtFull_bi_x_degree_le E (Q k))
    have hErase : bi_x_degree_le E
        (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j'))
        ((Finset.univ (α := Fin M)).erase j).card
        ((Finset.univ (α := Fin M)).erase j).card :=
      bi_x_degree_le_prod_finset E _ _ (fun i _ => lineEvalNumAtFull_bi_x_degree_le E (R i))
    have hEraseCard : ((Finset.univ (α := Fin M)).erase j).card ≤ M :=
      le_trans Finset.card_erase_le (by simp)
    have hMul := bi_x_degree_le.mul (bi_x_degree_le.mul hC hProd) hErase
    apply bi_x_degree_le.mono hMul <;> omega

/-- **Total-degree bound for `lineEvalNumAtFull`.** Bilinear of total
    degree 2 in `(X 0, Y 0, X 1, Y 1)`. -/
private theorem lineEvalNumAtFull_total_degree_le' (P : ZMod E.q × ZMod E.q) :
    total_degree_le E (lineEvalNumAtFull E P) 2 := by
  unfold lineEvalNumAtFull
  refine total_degree_le.sub ?_ ?_
  · have h1 : total_degree_le E (embedScalarFull E P.2 - varA₀y E) 1 := by
      unfold embedScalarFull varA₀y
      exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
        (total_degree_le.X _)
    have h2 : total_degree_le E (lamDenFull E) 1 := by
      unfold lamDenFull varA₁x varA₀x
      exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)
    exact total_degree_le.mul h1 h2
  · have h1 : total_degree_le E (embedScalarFull E P.1 - varA₀x E) 1 := by
      unfold embedScalarFull varA₀x
      exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
        (total_degree_le.X _)
    have h2 : total_degree_le E (lamNumFull E) 1 := by
      unfold lamNumFull varA₁y varA₀y
      exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)
    exact total_degree_le.mul h1 h2

/-- **Total-degree bound for `polyGFull`.** Each summand has at most
    `(d-1)+M` factors of degree-2 `lineEvalNumAtFull` (or symmetrically
    `d+(M-1)`), giving total degree `2·(d+M-1)`. We state the looser
    `≤ 2·(d+M)` to avoid Nat-subtraction edge cases. -/
private theorem polyGFull_total_degree_le'
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    total_degree_le E (polyGFull E Q beta R m) (2 * (d + M)) := by
  classical
  unfold polyGFull
  refine total_degree_le.add ?_ ?_
  · refine total_degree_le.sum _ _ ?_
    intro k _
    have hβ : total_degree_le E (MvPolynomial.C (beta k) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    have hQErase : total_degree_le E
        (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k'))
        (((Finset.univ (α := Fin d)).erase k).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k' _
      exact lineEvalNumAtFull_total_degree_le' E (Q k')
    have hR : total_degree_le E
        (∏ j : Fin M, lineEvalNumAtFull E (R j))
        ((Finset.univ (α := Fin M)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j _
      exact lineEvalNumAtFull_total_degree_le' E (R j)
    have hMul := total_degree_le.mul (total_degree_le.mul hβ hQErase) hR
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin d)).erase k).card ≤ d := by
      simp
    have hMC : (Finset.univ (α := Fin M)).card = M := by simp
    rw [hMC]
    set ce := ((Finset.univ (α := Fin d)).erase k).card with hce
    have hCE : ce * 2 ≤ d * 2 := Nat.mul_le_mul_right 2 hEC
    omega
  · refine total_degree_le.sum _ _ ?_
    intro j _
    have hm : total_degree_le E (MvPolynomial.C (m j) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    have hQ : total_degree_le E
        (∏ k : Fin d, lineEvalNumAtFull E (Q k))
        ((Finset.univ (α := Fin d)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k _
      exact lineEvalNumAtFull_total_degree_le' E (Q k)
    have hRErase : total_degree_le E
        (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j'))
        (((Finset.univ (α := Fin M)).erase j).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j' _
      exact lineEvalNumAtFull_total_degree_le' E (R j')
    have hMul := total_degree_le.mul (total_degree_le.mul hm hQ) hRErase
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin M)).erase j).card ≤ M := by
      simp
    have hDC : (Finset.univ (α := Fin d)).card = d := by simp
    rw [hDC]
    set ce := ((Finset.univ (α := Fin M)).erase j).card with hce
    have hCE : ce * 2 ≤ M * 2 := Nat.mul_le_mul_right 2 hEC
    omega

/-- **Tight total-degree bound for `polyGFull`.** Each summand has
    exactly `(d−1)+M` or `d+(M−1)` degree-2 factors, giving total
    degree `≤ 2·(d+M−1)` (using Nat subtraction, which is 0 when
    `d+M=0`). This is 2 less than the loose bound
    `polyGFull_total_degree_le'`. -/
theorem polyGFull_total_degree_le_tight
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    total_degree_le E (polyGFull E Q beta R m) (2 * (d + M - 1)) := by
  classical
  unfold polyGFull
  refine total_degree_le.add ?_ ?_
  · refine total_degree_le.sum _ _ ?_
    intro k _
    have hβ : total_degree_le E (MvPolynomial.C (beta k) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    have hQErase : total_degree_le E
        (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k'))
        (((Finset.univ (α := Fin d)).erase k).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k' _; exact lineEvalNumAtFull_total_degree_le' E (Q k')
    have hR : total_degree_le E
        (∏ j : Fin M, lineEvalNumAtFull E (R j))
        ((Finset.univ (α := Fin M)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j _; exact lineEvalNumAtFull_total_degree_le' E (R j)
    have hMul := total_degree_le.mul (total_degree_le.mul hβ hQErase) hR
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin d)).erase k).card = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k)]; simp
    have hMC : (Finset.univ (α := Fin M)).card = M := by simp
    have hd1 : 1 ≤ d := by have := k.isLt; omega
    rw [hEC, hMC]; omega
  · refine total_degree_le.sum _ _ ?_
    intro j _
    have hm : total_degree_le E (MvPolynomial.C (m j) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    have hQ : total_degree_le E
        (∏ k : Fin d, lineEvalNumAtFull E (Q k))
        ((Finset.univ (α := Fin d)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k _; exact lineEvalNumAtFull_total_degree_le' E (Q k)
    have hRErase : total_degree_le E
        (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j'))
        (((Finset.univ (α := Fin M)).erase j).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j' _; exact lineEvalNumAtFull_total_degree_le' E (R j')
    have hMul := total_degree_le.mul (total_degree_le.mul hm hQ) hRErase
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin M)).erase j).card = M - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; simp
    have hDC : (Finset.univ (α := Fin d)).card = d := by simp
    have hM1 : 1 ≤ M := by have := j.isLt; omega
    rw [hEC, hDC]; omega

/-- **Paper Step 2** (`thm:ma`, ip.tex `\ref{step:szbiv}`): cleared
    polynomial `polyGFull` vanishes identically on `E × E`.

    Lean realisation of "apply SZ-on-(E×E) (paper's `lem:log-derivative`
    machinery, i.e. `thm:variety-bound` + Bezout) contrapositively to
    the cleared polynomial `G`": if `polyG` vanishes on every defined
    non-vertical pair of `E.points × E.points` and the threshold
    `|E|² − 2|E| > 18·(d + M)·E.q` holds (derived from `hLargeQ` via
    Hasse), then `polyGFull` has no nonzero witness on `E × E`.

    Proof uses the `bivariate_poly_zeros_on_ExE_le` theorem
    on `polyGFull` of total degree `≤ 2·(d+M)`: were it nonzero
    somewhere on `E × E`, its zero set would have cardinality
    `≤ 9·2·(d+M)·q = 18·(d+M)·q`, contradicting the non-vertical-pair
    count `|E|² − 2|E|` it must contain. -/
theorem polyGFull_vanishes_on_ExE_of_polyG_zero (hHW : E.HasseBound)
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hPolyGZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card * E.points.card - 2 * E.points.card
                  > 18 * (d + M) * E.q) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨A₀, A₁, hA₀, hA₁, hNZ⟩ := h
  have hDeg := polyGFull_total_degree_le' E Q beta R m
  have hLW := bivariate_poly_zeros_on_ExE_le E hHW (polyGFull E Q beta R m)
    (2 * (d + M)) hDeg ⟨A₀, A₁, hA₀, hA₁, hNZ⟩
  have hNVsub : (E.points ×ˢ E.points).filter
      (fun p : _ × _ => p.1.1 ≠ p.2.1) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (polyGFull E Q beta R m) p.1 p.2 = 0) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [bivEval₂_polyGFull_eq_polyG]
    exact hPolyGZero _ _ hp.1.1 hp.1.2 hp.2
  have hCardProd : (E.points ×ˢ E.points).card = E.points.card * E.points.card :=
    Finset.card_product _ _
  have hNVcard : ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 ≠ p.2.1)).card
    + ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 = p.2.1)).card
    = (E.points ×ˢ E.points).card := by
    have h := @Finset.card_filter_add_card_filter_not
      _ (E.points ×ˢ E.points)
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 = p.2.1)
      _ _
    linarith
  have hVertBd := card_vertical_pairs_le E
  have hZeroCard := Finset.card_le_card hNVsub
  have hNVge : E.points.card * E.points.card - 2 * E.points.card
    ≤ ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) => p.1.1 ≠ p.2.1)).card := by
    rw [hCardProd] at hNVcard; omega
  have hChain : E.points.card * E.points.card - 2 * E.points.card
    ≤ 9 * (2 * (d + M)) * E.q := le_trans hNVge (le_trans hZeroCard hLW)
  have hRw : 9 * (2 * (d + M)) * E.q = 18 * (d + M) * E.q := by ring
  rw [hRw] at hChain
  exact absurd hChain (Nat.not_le.mpr hELarge)

/-! ### Sub-lemmas for `sigma_matching_core`

    The proof decomposes into five steps:
    1. `ellP_self_eq_zero`: `ellP E P P A₁ = 0` (P = A₀).
    2. `polyG_only_Rj_term`: When `ellP(R_{j₀})=0` and all other factors ≠ 0,
       `polyG` reduces to the `j₀`-th second-sum term.
    3. `polyG_only_Qk_term`: When `ellP(Q_{k₀})=0` and all other factors ≠ 0,
       `polyG` reduces to the `k₀`-th first-sum term.
    4. `exists_avoiding_A1`: For `P ∈ E.points` and finite `T`, find
       `A₁ ∈ E.points` with `A₁ ≠ P` and `ellP(P', P, A₁) ≠ 0` for `P' ∈ T`.
    5. Combine to build `σ` and verify the three properties. -/

/-- `ellP E P P A₁ = 0` — the line numerator through `(A₀, A₁)`
    evaluated at `P = A₀` always vanishes. -/
private lemma ellP_self_eq_zero (P A₁ : ZMod E.q × ZMod E.q) :
    ellP E P P A₁ = 0 := by
  simp [ellP]

/-- When `A₀ = Q k₀ ∈ E.points`, `polyG(Q k₀, A₁)` reduces to the
    `k₀`-th first-sum term with the full `∏_j ellP(R_j)` factor.
    All other terms vanish because they contain `ellP(Q_{k₀}, Q_{k₀}, A₁) = 0`
    as a factor. -/
private lemma polyG_at_self_Q
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (k₀ : Fin d) (A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q beta R m (Q k₀) A₁ =
      beta k₀ *
        (∏ k' ∈ Finset.univ.erase k₀, ellP E (Q k') (Q k₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (Q k₀) A₁) := by
  unfold polyG
  have hFirstSum : ∀ k' : Fin d, k' ≠ k₀ →
      beta k' *
        (∏ k'' ∈ Finset.univ.erase k', ellP E (Q k'') (Q k₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (Q k₀) A₁) = 0 := by
    intro k' hne
    have hk₀mem : k₀ ∈ Finset.univ.erase k' :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hk₀mem (ellP_self_eq_zero E _ _)]
    ring
  have hSecondSum : ∀ j : Fin M,
      m j *
        (∏ k : Fin d, ellP E (Q k) (Q k₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (Q k₀) A₁) = 0 := by
    intro j
    have hk₀mem : k₀ ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
    rw [Finset.prod_eq_zero hk₀mem (ellP_self_eq_zero E _ _)]
    ring
  rw [Finset.sum_eq_zero (fun j _ => hSecondSum j), add_zero]
  exact Finset.sum_eq_single k₀
    (fun k' _ hne => hFirstSum k' hne)
    (fun h => absurd (Finset.mem_univ k₀) h)

/-- When `A₀ = R j₀ ∈ E.points`, `polyG(R j₀, A₁)` reduces to the
    `j₀`-th second-sum term. All first-sum terms vanish (each has
    `∏_j ellP(R_j)` including `ellP(R_{j₀}) = 0`), and all
    second-sum terms with `j ≠ j₀` vanish (they contain
    `ellP(R_{j₀})` in their `∏_{j'≠j}` product). -/
private lemma polyG_at_self_R
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (j₀ : Fin M) (A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q beta R m (R j₀) A₁ =
      m j₀ *
        (∏ k : Fin d, ellP E (Q k) (R j₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j₀, ellP E (R j') (R j₀) A₁) := by
  unfold polyG
  have hFirstSum : ∀ k : Fin d,
      beta k *
        (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') (R j₀) A₁) *
        (∏ j : Fin M, ellP E (R j) (R j₀) A₁) = 0 := by
    intro k
    have hj₀mem : j₀ ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ _
    rw [Finset.prod_eq_zero hj₀mem (ellP_self_eq_zero E _ _)]
    ring
  have hSecondSum : ∀ j : Fin M, j ≠ j₀ →
      m j *
        (∏ k : Fin d, ellP E (Q k) (R j₀) A₁) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (R j₀) A₁) = 0 := by
    intro j hne
    have hj₀mem : j₀ ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hj₀mem (ellP_self_eq_zero E _ _)]
    ring
  rw [Finset.sum_eq_zero (fun k _ => hFirstSum k), zero_add]
  exact Finset.sum_eq_single j₀
    (fun j _ hne => hSecondSum j hne)
    (fun h => absurd (Finset.mem_univ j₀) h)

/-- For `P ∈ E.points` and a finite set `T` of "bad" points, if
    `|E| > 2|T| + 1`, there exists `A₁ ∈ E.points`, `A₁ ≠ P`,
    such that `ellP(P', P, A₁) ≠ 0` for every `P' ∈ T`.

    Geometrically: each `P' ∈ T` determines a line through `P`;
    by Bezout, that line meets `E` in ≤ 3 points, at most 2 besides `P`.
    So the set of "bad" `A₁` values has size ≤ `2|T|`.
    With `|E| > 2|T| + 1`, a "good" `A₁ ≠ P` exists. -/
private lemma exists_avoiding_A1
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points)
    (T : Finset (ZMod E.q × ZMod E.q))
    (hPnotT : P ∉ T)
    (hSize : E.points.card > 2 * T.card + 1) :
    ∃ A₁ ∈ E.points, A₁ ≠ P ∧
      ∀ P' ∈ T, ellP E P' P A₁ ≠ 0 := by
  classical
  -- For each P' ∈ T (with P' ≠ P since P ∉ T), the set of A₁ ∈ E.points
  -- where ellP E P' P A₁ = 0 has card ≤ 3 by Bezout (linear_form_zeros_le_three).
  -- P is always one of those zeros, so at most 2 other bad A₁ per P'.
  -- Define bad = {P} ∪ ⋃_{P' ∈ T} {A₁ ∈ E.points | A₁ ≠ P ∧ ellP = 0}
  -- |bad| ≤ 1 + 2|T| = 2|T| + 1 < |E|.
  set badPerP' := fun (P' : ZMod E.q × ZMod E.q) =>
    (E.points.filter (fun A₁ => ellP E P' P A₁ = 0)).erase P
  -- Each badPerP' has card ≤ 2 (when P' ≠ P)
  have hBadCard : ∀ P' ∈ T, (badPerP' P').card ≤ 2 := by
    intro P' hP'T
    have hP'neP : P' ≠ P := fun h => hPnotT (h ▸ hP'T)
    -- ellP E P' P A₁ = (P'.2 - P.2)*A₁.1 + (-(P'.1 - P.1))*A₁.2 +
    --   ((P'.1 - P.1)*P.2 - (P'.2 - P.2)*P.1)
    -- The linear form has coefficients a = P'.2 - P.2, b = -(P'.1 - P.1)
    -- At least one is nonzero since P' ≠ P.
    have hab : (P'.2 - P.2) ≠ 0 ∨ (-(P'.1 - P.1)) ≠ 0 := by
      by_contra h
      push_neg at h
      have h1 : P'.2 = P.2 := by linear_combination h.1
      have h2 : P'.1 = P.1 := by linear_combination -h.2
      exact hP'neP (Prod.ext h2 h1)
    have hFilterSub : E.points.filter (fun A₁ => ellP E P' P A₁ = 0) ⊆
        E.points.filter (fun A₁ =>
          (P'.2 - P.2) * A₁.1 + (-(P'.1 - P.1)) * A₁.2 +
          ((P'.1 - P.1) * P.2 - (P'.2 - P.2) * P.1) = 0) := by
      intro A₁ hA₁
      simp only [Finset.mem_filter] at hA₁ ⊢
      refine ⟨hA₁.1, ?_⟩
      simp only [ellP] at hA₁
      linear_combination hA₁.2
    have hCard3 : (E.points.filter (fun A₁ =>
        ellP E P' P A₁ = 0)).card ≤ 3 := by
      calc (E.points.filter (fun A₁ => ellP E P' P A₁ = 0)).card
          ≤ (E.points.filter (fun A₁ =>
              (P'.2 - P.2) * A₁.1 + (-(P'.1 - P.1)) * A₁.2 +
              ((P'.1 - P.1) * P.2 - (P'.2 - P.2) * P.1) = 0)).card :=
            Finset.card_le_card hFilterSub
        _ ≤ 3 := linear_form_zeros_le_three E _ _ _ (by tauto)
    calc (badPerP' P').card
        = (E.points.filter (fun A₁ => ellP E P' P A₁ = 0)).card - 1 := by
          exact Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hP, by simp [ellP]⟩)
      _ ≤ 2 := by omega
  -- bad = {P} ∪ ⋃_{P' ∈ T} badPerP'
  set bad := ({P} : Finset _) ∪ T.biUnion badPerP'
  have hBadSub : bad ⊆ E.points := by
    intro x hx
    simp only [bad, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] at hx
    rcases hx with rfl | ⟨P', _, hx⟩
    · exact hP
    · exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1
  have hBadCard_total : bad.card ≤ 2 * T.card + 1 := by
    calc bad.card ≤ ({P} : Finset _).card + (T.biUnion badPerP').card :=
          Finset.card_union_le _ _
      _ ≤ 1 + ∑ P' ∈ T, (badPerP' P').card := by
          simp only [Finset.card_singleton]
          linarith [Finset.card_biUnion_le (s := T) (t := badPerP')]
      _ ≤ 1 + ∑ _ ∈ T, 2 :=
          Nat.add_le_add_left (Finset.sum_le_sum hBadCard) _
      _ = 2 * T.card + 1 := by simp [Finset.sum_const]; ring
  -- E.points \ bad is nonempty
  have hGoodNonempty : (E.points \ bad).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hSub
    have := Finset.card_le_card hSub
    omega
  obtain ⟨A₁, hA₁⟩ := hGoodNonempty.exists_mem
  rw [Finset.mem_sdiff] at hA₁
  refine ⟨A₁, hA₁.1, ?_, ?_⟩
  · intro heq
    exact hA₁.2 (Finset.mem_union_left _ (Finset.mem_singleton.mpr heq))
  · intro P' hP'T hEllP
    apply hA₁.2
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨P', hP'T, Finset.mem_erase.mpr
      ⟨fun heq => hA₁.2 (Finset.mem_union_left _ (Finset.mem_singleton.mpr heq)),
       Finset.mem_filter.mpr ⟨hA₁.1, hEllP⟩⟩⟩

/-- The 4-variate lift of the "residual" polynomial
    `G = ∑_k c_k · ∏_{j≠σ(k)} lineEvalNumAtFull(R_j)`,
    which arises after simplifying `polyG` under the σ-matching. -/
private noncomputable def residualFull
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M) : FourVarPoly E.q :=
  ∑ k : Fin d,
    (MvPolynomial.C (c k) : FourVarPoly E.q) *
    (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
      lineEvalNumAtFull E (R j))

private lemma residualFull_bi_x_degree_le
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M) :
    bi_x_degree_le E (residualFull E R c σ) (M - 1) (M - 1) := by
  unfold residualFull
  apply bi_x_degree_le.sum
  intro k _
  have hC : bi_x_degree_le E (MvPolynomial.C (c k) : FourVarPoly E.q) 0 0 :=
    bi_x_degree_le.C _
  have hProd : bi_x_degree_le E
      (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k), lineEvalNumAtFull E (R j))
      ((Finset.univ : Finset (Fin M)).erase (σ k)).card
      ((Finset.univ : Finset (Fin M)).erase (σ k)).card :=
    bi_x_degree_le_prod_finset E _ _ (fun i _ => lineEvalNumAtFull_bi_x_degree_le E (R i))
  have hEraseCard : ((Finset.univ : Finset (Fin M)).erase (σ k)).card ≤ M - 1 := by
    rcases M with _ | M
    · exact Fin.elim0 (σ k)
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hMul := bi_x_degree_le.mul hC hProd
  apply bi_x_degree_le.mono hMul <;> omega

private lemma residualFull_total_degree_le
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M) :
    total_degree_le E (residualFull E R c σ) (2 * (M - 1)) := by
  unfold residualFull
  apply total_degree_le.sum
  intro k _
  have hC : total_degree_le E (MvPolynomial.C (c k) : FourVarPoly E.q) 0 :=
    total_degree_le.C _
  have hProd : total_degree_le E
      (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k), lineEvalNumAtFull E (R j))
      (((Finset.univ : Finset (Fin M)).erase (σ k)).card * 2) :=
    total_degree_le.prod_const _ _ (fun i _ => lineEvalNumAtFull_total_degree_le' E (R i))
  have hEraseCard : ((Finset.univ : Finset (Fin M)).erase (σ k)).card ≤ M - 1 := by
    rcases M with _ | M
    · exact Fin.elim0 (σ k)
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hMul := total_degree_le.mul hC hProd
  exact hMul.mono (by omega)

private lemma bivEval₂_residualFull_eq
    {d M : ℕ}
    (R : Fin M → ZMod E.q × ZMod E.q)
    (c : Fin d → ZMod E.q)
    (σ : Fin d ↪ Fin M)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval₂ (residualFull E R c σ) A₀ A₁ =
    ∑ k : Fin d, c k *
      ∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
        ellP E (R j) A₀ A₁ := by
  simp only [residualFull, bivEval₂_sum, bivEval₂_mul,
    bivEval₂_prod, bivEval₂_C, bivEval₂_lineEvalNumAtFull, ellP]

/-- Algebraic identity: `polyG = (∏_k ellP(Q_k)) · residualFull` under σ-matching. -/
private lemma polyG_factorization
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (σ : Fin d ↪ Fin M)
    (hQR : ∀ k, Q k = R (σ k))
    (hMoff : ∀ j, j ∉ Set.range σ → m j = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q beta R m A₀ A₁ =
      (∏ k : Fin d, ellP E (Q k) A₀ A₁) *
      (∑ k : Fin d, (beta k + m (σ k)) *
        ∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k), ellP E (R j) A₀ A₁) := by
  classical
  set F := fun j => ∏ j' ∈ (Finset.univ : Finset (Fin M)).erase j, ellP E (R j') A₀ A₁
  set prodQ := ∏ k : Fin d, ellP E (Q k) A₀ A₁
  set prodR := ∏ j : Fin M, ellP E (R j) A₀ A₁
  have hKey : ∀ k : Fin d,
      (∏ k' ∈ (Finset.univ : Finset (Fin d)).erase k, ellP E (Q k') A₀ A₁) * prodR =
      prodQ * F (σ k) := by
    intro k
    have h1 : prodQ = ellP E (Q k) A₀ A₁ *
      ∏ k' ∈ Finset.univ.erase k, ellP E (Q k') A₀ A₁ :=
      (Finset.mul_prod_erase _ (fun k => ellP E (Q k) A₀ A₁) (Finset.mem_univ k)).symm
    have h2 : prodR = ellP E (R (σ k)) A₀ A₁ * F (σ k) :=
      (Finset.mul_prod_erase _ (fun j => ellP E (R j) A₀ A₁) (Finset.mem_univ (σ k))).symm
    rw [hQR k] at h1; rw [h1, h2]; ring
  have hSecond :
      (∑ j : Fin M, m j * prodQ * F j) =
      ∑ k : Fin d, m (σ k) * prodQ * F (σ k) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ Set.range σ)]
    have hOff : ∑ j ∈ Finset.univ.filter (fun j => j ∉ Set.range σ),
        m j * prodQ * F j = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [Finset.mem_filter] at hj; rw [hMoff j hj.2]; ring)
    rw [hOff, add_zero]
    rw [← Finset.sum_image (f := fun j => m j * prodQ * F j) (g := σ) (s := Finset.univ)]
    · congr 1; ext j; simp [Finset.mem_image, Set.mem_range]
    · intro k₁ _ k₂ _ h; exact σ.injective h
  have hFirst :
      (∑ k : Fin d, beta k *
        (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') A₀ A₁) * prodR) =
      ∑ k : Fin d, beta k * prodQ * F (σ k) := by
    congr 1; ext k; rw [mul_assoc, hKey k]; ring
  unfold polyG
  rw [hFirst, hSecond, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1; ext k; ring

/-- After establishing `Q k = R (σ k)` and `m j = 0` for `j ∉ range σ`,
    the simplified `polyG` factors as
    `(∏_k ellP(Q_k)) · G` where `G = residual c σ R` and `c k = β k + m(σ k)`.
    This lemma shows that `G = 0` on all of `E × E` by applying the
    bivariate polynomial zeros axiom contrapositively. -/
private lemma residual_vanishes_on_ExE (hHW : E.HasseBound)
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (σ : Fin d ↪ Fin M)
    (hQR : ∀ k, Q k = R (σ k))
    (hMoff : ∀ j, j ∉ Set.range σ → m j = 0)
    (hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2)
    (_hQonE : ∀ k, Q k ∈ E.points)
    (hELarge_dkl : E.points.card * E.points.card - 2 * E.points.card
                     > 18 * (d + M) * E.q) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) A₀ A₁ = 0 := by
  classical
  by_contra hNontriv
  push_neg at hNontriv
  obtain ⟨A₀, A₁, hA₀, hA₁, hNZ⟩ := hNontriv
  -- Step 1: Apply the new axiom to residualFull.
  have hTD := residualFull_total_degree_le E R (fun k => beta k + m (σ k)) σ
  have hLW := bivariate_poly_zeros_on_ExE_le E hHW
    (residualFull E R (fun k => beta k + m (σ k)) σ)
    (2 * (M - 1)) hTD ⟨A₀, A₁, hA₀, hA₁, hNZ⟩
  -- Step 2: polyG = prod_Q * residualFull. So wherever prod_Q ≠ 0 on E×E,
  --   residualFull = 0.
  have hPolyGFact := polyG_factorization E Q beta R m σ hQR hMoff
  have hResZeroWhenProdNZ : ∀ a₀ a₁ : ZMod E.q × ZMod E.q,
      a₀ ∈ E.points → a₁ ∈ E.points →
      (∏ k : Fin d, ellP E (Q k) a₀ a₁) ≠ 0 →
      bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) a₀ a₁ = 0 := by
    intro a0 a1 ha0 ha1 hProdNZ
    have h0 := hPolyGAll a0 a1 ha0 ha1
    rw [hPolyGFact a0 a1] at h0
    rw [bivEval₂_residualFull_eq]
    exact (mul_eq_zero.mp h0).resolve_left hProdNZ
  -- Step 3: {residualFull ≠ 0 on E×E} ⊆ {∏ ellP(Q_k) = 0 on E×E}
  --   ⊆ ⋃_k {ellP(Q_k) = 0 on E×E}
  have hZerosInclusion : (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨hp.1, ?_⟩
    by_contra hAllNZ
    push_neg at hAllNZ
    have hProdNZ : (∏ k : Fin d, ellP E (Q k) p.1 p.2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => hAllNZ k)
    exact hp.2 (hResZeroWhenProdNZ p.1 p.2 hp.1.1 hp.1.2 hProdNZ)
  -- Step 4: For each k, the zero set of ellP(Q_k) on E×E has card ≤ 18*q.
  --   We need nonzero witnesses; these exist since |E| ≥ 7 and Q_k ∈ E.
  have hEllPZeros : ∀ k : Fin d,
      ((E.points ×ˢ E.points).filter
        (fun p => ellP E (Q k) p.1 p.2 = 0)).card ≤ 18 * E.q := by
    intro k
    -- Find a nonzero witness for ellP(Q_k): take A₀' ≠ Q_k on E,
    -- then A₁' avoiding collinearity.
    have hd_pos : 0 < d := Fin.pos k
    have hcard : E.points.card ≥ 7 := by omega
    -- There exists A₀' ∈ E.points with A₀' ≠ Q_k
    have hExA₀ : ∃ A₀' ∈ E.points, A₀' ≠ Q k := by
      by_contra h; push_neg at h
      have : E.points ⊆ {Q k} := by
        intro x hx; exact Finset.mem_singleton.mpr (h x hx)
      have : E.points.card ≤ 1 := (Finset.card_le_card this).trans (by simp)
      omega
    obtain ⟨A₀', hA₀', hA₀'ne⟩ := hExA₀
    have hA₀'notT : A₀' ∉ ({Q k} : Finset _) := by
      simp [Finset.mem_singleton]; exact hA₀'ne
    have hSizeOK : E.points.card > 2 * ({Q k} : Finset _).card + 1 := by
      simp; omega
    obtain ⟨A₁', hA₁'mem, _, hA₁'good⟩ := exists_avoiding_A1 E A₀' hA₀'
      ({Q k}) hA₀'notT hSizeOK
    have hWitness : ellP E (Q k) A₀' A₁' ≠ 0 := hA₁'good (Q k) (Finset.mem_singleton.mpr rfl)
    -- Apply LW with total degree 2 and nonzero witness
    have hTD_ell := lineEvalNumAtFull_total_degree_le' E (Q k)
    have hLW_ell := bivariate_poly_zeros_on_ExE_le E hHW
      (lineEvalNumAtFull E (Q k)) 2 hTD_ell
      ⟨A₀', A₁', hA₀', hA₁'mem, by rwa [bivEval₂_lineEvalNumAtFull]⟩
    -- zeros ≤ 9 * 2 * q = 18 * q
    have hSetEq : (E.points ×ˢ E.points).filter
        (fun p => ellP E (Q k) p.1 p.2 = 0) =
      (E.points ×ˢ E.points).filter
        (fun p => bivEval₂ (lineEvalNumAtFull E (Q k)) p.1 p.2 = 0) := by
      exact Finset.filter_congr fun p _ => by
        rw [bivEval₂_lineEvalNumAtFull]; exact Iff.rfl
    rw [hSetEq]
    calc _ ≤ 9 * 2 * E.q := hLW_ell
      _ = 18 * E.q := by ring
  -- Step 5: Counting contradiction.
  -- nonzeros of residualFull ≥ |E|² - 18*(M-1)*q
  -- nonzeros ⊆ ⋃_k {ellP(Q_k) = 0}, card ≤ ∑_k 18*q = 18*d*q
  have hCardExE : (E.points ×ˢ E.points).card = E.points.card * E.points.card :=
    Finset.card_product _ _
  -- Count of nonzeros
  have hNonzeroCard : ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0)).card
    ≥ E.points.card * E.points.card - 18 * (M - 1) * E.q := by
    have h1 := @Finset.card_filter_add_card_filter_not
      _ (E.points ×ˢ E.points)
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 = 0)
      _ _
    rw [hCardExE] at h1
    -- zeros ≤ 18*(M-1)*q
    have hZerosLe : ((E.points ×ˢ E.points).filter
        (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 = 0)).card
      ≤ 18 * (M - 1) * E.q := by
      calc _ ≤ 9 * (2 * (M - 1)) * E.q := hLW
        _ = 18 * (M - 1) * E.q := by ring
    -- filter ≠ 0 = filter (not (= 0))
    have hFilterConvert : (E.points ×ˢ E.points).filter
        (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0)
      = (E.points ×ˢ E.points).filter
        (fun p => ¬ (bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 = 0)) := by
      rfl
    rw [hFilterConvert]; omega
  -- Union bound on ⋃_k ellP zeros
  have hUnionBound : ((E.points ×ˢ E.points).filter
      (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0)).card
    ≤ 18 * d * E.q := by
    have hSub : (E.points ×ˢ E.points).filter
        (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0) ⊆
      Finset.univ.biUnion (fun k : Fin d =>
        (E.points ×ˢ E.points).filter (fun p => ellP E (Q k) p.1 p.2 = 0)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
      obtain ⟨hprod, ⟨k, hk⟩⟩ := hp
      exact ⟨k, Finset.mem_univ k, hprod, hk⟩
    calc ((E.points ×ˢ E.points).filter _).card
      ≤ (Finset.univ.biUnion _).card := Finset.card_le_card hSub
      _ ≤ ∑ k ∈ Finset.univ, ((E.points ×ˢ E.points).filter
          (fun p => ellP E (Q k) p.1 p.2 = 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.univ, (18 * E.q) := Finset.sum_le_sum (fun k _ => hEllPZeros k)
      _ = 18 * d * E.q := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- Chain: nonzeros ≤ union bound
  have hChain : E.points.card * E.points.card - 18 * (M - 1) * E.q ≤ 18 * d * E.q :=
    le_trans hNonzeroCard (le_trans (Finset.card_le_card hZerosInclusion) hUnionBound)
  -- From hELarge_dkl: N*N - 2*N > 18*(d+M)*q, so N*N > 18*(d+M)*q + 2*N ≥ 18*(d+M)*q.
  -- Since 18*(d+M)*q = 18*d*q + 18*M*q ≥ 18*d*q + 18*(M-1)*q (as M ≥ M-1):
  --   N*N > 18*d*q + 18*(M-1)*q.
  -- So N*N - 18*(M-1)*q > 18*d*q (exact Nat subtraction is fine).
  -- This contradicts hChain.
  -- Step: N*N > 18*(d+M)*q from hELarge_dkl
  have hNN : E.points.card * E.points.card > 18 * (d + M) * E.q := by omega
  -- Step: 18*(d+M)*q = 18*d*q + 18*M*q
  -- And 18*M*q ≥ 18*(M-1)*q (trivially, since M ≥ M-1 in ℕ)
  -- So N*N > 18*d*q + 18*(M-1)*q
  have h1 : 18 * (d + M) * E.q = 18 * d * E.q + 18 * M * E.q := by ring
  have h2 : 18 * M * E.q ≥ 18 * (M - 1) * E.q := by
    apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
  -- So N*N > 18*d*q + 18*(M-1)*q
  have h3 : E.points.card * E.points.card > 18 * d * E.q + 18 * (M - 1) * E.q := by omega
  -- hChain says N*N - 18*(M-1)*q ≤ 18*d*q. Since N*N > 18*(M-1)*q + 18*d*q, this is a contradiction.
  omega

set_option linter.all false in
example : True := trivial -- separator marker
/-
Old body of `residual_vanishes_on_ExE` (kept commented for reference; uses
the old `bivariate_poly_zeros_on_ExE_le` axiom signature with `bi_x_degree_le`):

  by_contra hNontriv
  push_neg at hNontriv
  obtain ⟨A₀, A₁, hA₀, hA₁, hNZ⟩ := hNontriv
  -- From the algebraic identity and polyG = 0:
  -- (∏_k ellP(Q_k)) * residualFull = polyG = 0 on E×E
  -- At the nonzero witness (A₀, A₁): residualFull ≠ 0, so ∏ ellP(Q_k) = 0.
  have hPolyGFact := polyG_factorization E Q beta R m σ hQR hMoff
  -- For all (A₀, A₁) ∈ E×E with ∏ ellP ≠ 0, residualFull = 0.
  have hResZeroWhenProdNZ : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      (∏ k : Fin d, ellP E (Q k) A₀ A₁) ≠ 0 →
      bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) A₀ A₁ = 0 := by
    intro a0 a1 ha0 ha1 hProdNZ
    have h0 := hPolyGAll a0 a1 ha0 ha1
    rw [hPolyGFact a0 a1] at h0
    have h1 := bivEval₂_residualFull_eq E R (fun k => beta k + m (σ k)) σ a0 a1
    rw [h1]
    rcases mul_eq_zero.mp h0 with hProd0 | hRes0
    · exact absurd hProd0 hProdNZ
    · exact hRes0
  -- Lang-Weil on residualFull: zeros ≤ 4*(M-1)*|E|
  have hBideg := residualFull_bi_x_degree_le E R (fun k => beta k + m (σ k)) σ
  have hLW := bivariate_poly_zeros_on_ExE_le E hHW
    (residualFull E R (fun k => beta k + m (σ k)) σ) (M - 1) (M - 1)
    hBideg ⟨A₀, A₁, hA₀, hA₁, hNZ⟩
  -- {residualFull ≠ 0 on E×E} ⊆ {∏ ellP(Q_k) = 0 on E×E}
  -- ⊆ ⋃_k {ellP(Q_k) = 0 on E×E}
  -- Bound each {ellP(Q_k) = 0}: for fixed A₀, at most 3 bad A₁ (by Bezout).
  -- Plus A₀ = Q_k gives |E| pairs. Total per k: ≤ 4|E|.
  -- ⋃: ≤ 4d|E|.
  -- nonzeros = |E|² - zeros ≥ |E|² - 4(M-1)|E| (from LW).
  -- But nonzeros ≤ 4d|E| (from inclusion).
  -- |E|² - 4(M-1)|E| ≤ 4d|E|, so |E| ≤ 4(d+M-1) < |E|. Contradiction.
  -- Count {residualFull ≠ 0 on E×E}
  have hCardExE : (E.points ×ˢ E.points).card = E.points.card * E.points.card :=
    Finset.card_product _ _
  have hZerosInclusion : (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨hp.1, ?_⟩
    by_contra hAllNZ
    push_neg at hAllNZ
    have hProdNZ : (∏ k : Fin d, ellP E (Q k) p.1 p.2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => hAllNZ k)
    exact hp.2 (hResZeroWhenProdNZ p.1 p.2 hp.1.1 hp.1.2 hProdNZ)
  -- Count {ellP(Q_k) = 0 on E×E} for each k, using Bezout:
  -- For each k, #{(A₀,A₁) | ellP(Q_k) = 0} ≤ 4|E|
  -- This follows from: for each A₀, #{A₁ | ellP = 0} ≤ 3 (when A₀ ≠ Q_k)
  -- and for A₀ = Q_k: all |E| values of A₁ work.
  have hEllPZeroCount : ∀ k : Fin d,
      ((E.points ×ˢ E.points).filter
        (fun p => ellP E (Q k) p.1 p.2 = 0)).card ≤ 4 * E.points.card := by
    intro k
    -- #{(A₀,A₁) ∈ E×E | ellP(Q_k,A₀,A₁)=0}
    -- = Σ_{A₀ ∈ E} #{A₁ ∈ E | ellP(Q_k,A₀,A₁)=0}
    -- For each A₀ ≠ Q_k: ellP is a nonzero linear form in A₁, so ≤ 3 zeros.
    -- For A₀ = Q_k (if on E): all |E| values of A₁ work.
    -- Total ≤ |E| + 3*(|E|-1) ≤ 4|E|.
    -- We use a simpler bound: for every A₀, ≤ |E| values of A₁. So ≤ |E|*|E|.
    -- But we need 4|E|, not |E|².
    -- Actually, use: #{pairs} = Σ_{A₀} |fiber(A₀)| ≤ |E| * max_fiber
    -- But max_fiber ≤ |E| gives |E|². Need per-A₀ bound.
    -- Use the bivariate_poly_zeros_on_ExE_le axiom on lineEvalNumAtFull(Q_k).
    -- lineEvalNumAtFull(Q_k) has bi_x_degree (1,1). If it has a nonzero witness
    -- on E×E, then zeros ≤ 2*(1+1)*|E| = 4*|E|.
    -- If no nonzero witness: all of E×E are zeros, so card = |E|².
    -- But we need ≤ 4|E|, which requires |E|² ≤ 4|E|, i.e., |E| ≤ 4.
    -- This fails for large E. So we need the nonzero witness.
    -- A nonzero witness exists when d ≥ 1 (which is true since k : Fin d).
    -- For any Q_k, take A₀ ∈ E with A₀ ≠ Q_k (need |E| ≥ 2, true since |E| > 4*(d+M)+2 ≥ 6).
    -- Then the linear form ellP(Q_k, A₀, ·) in A₁ is nonzero.
    -- By linear_form_zeros_le_three, ≤ 3 zeros on E. Since |E| ≥ 4, ∃ A₁ nonzero.
    by_cases hWitness : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ ellP E (Q k) A₀ A₁ ≠ 0
    · -- Has nonzero witness: use Lang-Weil
      have hBi : bi_x_degree_le E (lineEvalNumAtFull E (Q k)) 1 1 :=
        lineEvalNumAtFull_bi_x_degree_le E (Q k)
      have hNZW : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
          bivEval₂ (lineEvalNumAtFull E (Q k)) A₀ A₁ ≠ 0 := by
        obtain ⟨a0, a1, ha0, ha1, hne⟩ := hWitness
        exact ⟨a0, a1, ha0, ha1, by rwa [bivEval₂_lineEvalNumAtFull]⟩
      have hLW_k := bivariate_poly_zeros_on_ExE_le E hHW (lineEvalNumAtFull E (Q k)) 1 1 hBi hNZW
      have hFilterEq : (E.points ×ˢ E.points).filter (fun p => ellP E (Q k) p.1 p.2 = 0) =
          (E.points ×ˢ E.points).filter
            (fun p => bivEval₂ (lineEvalNumAtFull E (Q k)) p.1 p.2 = 0) := by
        congr 1; ext p; simp [bivEval₂_lineEvalNumAtFull, ellP]
      rw [hFilterEq]; linarith
    · -- No nonzero witness: ellP = 0 everywhere on E×E.
      -- This is impossible when |E| ≥ 5:
      -- There exist A₀, A₁ ∈ E with ellP(Q_k, A₀, A₁) ≠ 0.
      push_neg at hWitness
      exfalso
      -- |E| ≥ 2, so ∃ A₀ ∈ E.
      have hE2 : 2 ≤ E.points.card := by linarith
      -- Pick any A₀ ∈ E. If A₀ = Q_k, pick another.
      have hNE : E.points.Nonempty := Finset.card_pos.mp (by linarith)
      obtain ⟨A₀, hA₀⟩ := hNE
      -- ellP(Q_k, A₀, A₁) for fixed A₀ is a linear form in A₁
      -- If A₀ ≠ Q_k, the form is nonzero and has ≤ 3 zeros on E.
      -- Since |E| ≥ 4, there exists A₁ with ellP ≠ 0. Contradiction.
      have hAllZero := hWitness A₀
      -- For any A₁ ∈ E: ellP(Q_k, A₀, A₁) = 0.
      -- In particular, this is a linear form in A₁.
      -- The coefficients are (Q_k.2 - A₀.2, -(Q_k.1 - A₀.1)).
      -- By linear_form_zeros_le_three, if the form is nonzero, ≤ 3 zeros.
      -- But ALL of E are zeros, so the form must be zero, meaning Q_k = A₀.
      -- So Q_k = A₀ for every A₀ ∈ E, which is impossible if |E| ≥ 2.
      -- More carefully: pick A₀ ∈ E and A₀' ∈ E with A₀ ≠ A₀'.
      -- Both satisfy Q_k = A₀ and Q_k = A₀', giving A₀ = A₀'. Contradiction.
      -- So the form must be zero for all A₀ ∈ E, meaning Q_k = A₀ for all A₀.
      -- But there are ≥ 2 distinct A₀'s.
      -- Actually, the argument is simpler: for A₀ = Q_k, ellP = 0 for all A₁.
      -- For A₀ ≠ Q_k, ellP is a nonzero linear form. If |E| ≥ 4, it can't
      -- vanish on all of E. But it does (by hWitness). So A₀ ≠ Q_k can't hold.
      -- So ALL A₀ ∈ E must equal Q_k, but |E| ≥ 2, contradiction.
      have : ∀ A₀ ∈ E.points, A₀ = Q k := by
        intro A₀' hA₀'
        by_contra hne
        -- ellP(Q_k, A₀', ·) is a nonzero linear form
        -- It's: (Q k).2 - A₀'.2) * A₁.1 + (-(Q k).1 + A₀'.1) * A₁.2 + ...
        -- Nonzero since Q_k ≠ A₀'
        have hab : ((Q k).2 - A₀'.2) ≠ 0 ∨ (-((Q k).1 - A₀'.1)) ≠ 0 := by
          by_contra h; push_neg at h
          apply hne
          have h1 : A₀'.1 = (Q k).1 := by
            have := h.2; simp only [neg_eq_zero, sub_eq_zero] at this; exact this.symm
          have h2 : A₀'.2 = (Q k).2 := by
            have := h.1; rw [sub_eq_zero] at this; exact this.symm
          exact Prod.ext h1 h2
        -- By linear_form_zeros_le_three: ≤ 3 zeros on E
        have hLin : (E.points.filter (fun A₁ =>
            ((Q k).2 - A₀'.2) * A₁.1 + (-((Q k).1 - A₀'.1)) * A₁.2 +
            (((Q k).1 - A₀'.1) * A₀'.2 - ((Q k).2 - A₀'.2) * A₀'.1) = 0)).card ≤ 3 :=
          linear_form_zeros_le_three E _ _ _ (by tauto)
        -- But all of E has ellP = 0, so the filter is all of E
        have hAllE : E.points.filter (fun A₁ =>
            ((Q k).2 - A₀'.2) * A₁.1 + (-((Q k).1 - A₀'.1)) * A₁.2 +
            (((Q k).1 - A₀'.1) * A₀'.2 - ((Q k).2 - A₀'.2) * A₀'.1) = 0) = E.points := by
          apply Finset.filter_true_of_mem
          intro A₁ hA₁
          have := hWitness A₀' A₁ hA₀' hA₁
          unfold ellP at this; ring_nf; ring_nf at this; convert this using 1; ring
        rw [hAllE] at hLin
        have : 0 < d := Fin.pos k
        linarith
      -- All of E = {Q k}, but |E| ≥ 2, so ∃ two distinct elements
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < E.points.card)
      exact hab ((this a ha).trans (this b hb).symm)
  -- Union bound
  have hUnionBound :
      ((E.points ×ˢ E.points).filter
        (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0)).card ≤
      4 * d * E.points.card := by
    calc ((E.points ×ˢ E.points).filter
          (fun p => ∃ k : Fin d, ellP E (Q k) p.1 p.2 = 0)).card
        ≤ (Finset.univ.biUnion (fun k : Fin d =>
            (E.points ×ˢ E.points).filter (fun p => ellP E (Q k) p.1 p.2 = 0))).card := by
          apply Finset.card_le_card; intro p hp
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
            Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨⟨h1, h2⟩, k, hk⟩ := hp
          exact ⟨k, ⟨h1, h2⟩, hk⟩
      _ ≤ ∑ k : Fin d, ((E.points ×ˢ E.points).filter
            (fun p => ellP E (Q k) p.1 p.2 = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin d, (4 * E.points.card) :=
          Finset.sum_le_sum (fun k _ => hEllPZeroCount k)
      _ = d * (4 * E.points.card) := by simp [Finset.sum_const]
      _ = 4 * d * E.points.card := by ring
  -- Counting
  have hNonzerosCard :
      ((E.points ×ˢ E.points).filter
        (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0)).card ≤
      4 * d * E.points.card :=
    le_trans (Finset.card_le_card hZerosInclusion) hUnionBound
  -- Zeros of residualFull + nonzeros = |E×E|
  have hSplit : ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 = 0)).card +
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 ≠ 0)).card =
    (E.points ×ˢ E.points).card := by
    have h := Finset.card_filter_add_card_filter_not
      (fun p : _ × _ => bivEval₂ (residualFull E R (fun k => beta k + m (σ k)) σ) p.1 p.2 = 0)
      (s := E.points ×ˢ E.points)
    simp only [ne_eq] at h ⊢
    linarith
  have hNatBound : 2 * (M - 1 + (M - 1)) + 4 * d ≤ 4 * (d + M) := by omega
  nlinarith [hCardExE, hLW, hNonzerosCard, hSplit, hELarge, hNatBound]
-/

/-- **Core σ-matching extraction from polyG ≡ 0 on E × E.**

    Mechanizes paper Steps 3–6 via direct polynomial evaluation.

    **Proof outline:**
    1. For `j₀ : Fin M` with `R j₀ ∉ range Q`: set `A₀ = R j₀`
       (if `R j₀ ∈ E`); `polyG` reduces to
       `m j₀ · (∏_k ellP Q_k) · (∏_{j'≠j₀} ellP R_{j'})`, which is 0;
       picking `A₁` avoiding collinearity with other S-points shows `m j₀ = 0`.
    2. For each `k : Fin d`: assume `Q k ∉ range R`; set `A₀ = Q k`;
       `polyG` reduces to `β_k · (∏_{k'≠k} ellP Q_{k'}) · (∏_j ellP R_j)`;
       picking `A₁` avoiding other S-points gives `β_k = 0`,
       contradicting `hBetaNz`.
    3. Construct `σ : Fin d ↪ Fin M` with `Q k = R (σ k)`.
    4. After simplification, `polyG = (∏_k ellP Q_k) · G`;
       show `G = 0` on `E × E` via the bivariate zeros axiom.
    5. Evaluate `G` at collinear triples: `c_k = β_k + m(σ k) = 0`. -/
private lemma sigma_matching_core (hHW : E.HasseBound)
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hQonE : ∀ k, Q k ∈ E.points)
    (hRonE : ∀ j, R j ∈ E.points)
    (hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2)
    (hELarge_dkl : E.points.card * E.points.card - 2 * E.points.card
                     > 18 * (d + M) * E.q) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0) := by
  classical
  -- == Step 2: Every Q k is in range R ==
  have hSigmaExists : ∀ k : Fin d, ∃ j : Fin M, R j = Q k := by
    intro k
    by_contra h
    push_neg at h
    -- polyG(Q k, A₁) = beta k * (∏_{k'≠k} ellP(Q_{k'})) * (∏_j ellP(R_j))
    -- by polyG_at_self_Q. Since Q k ≠ R j for all j, we pick A₁ avoiding
    -- collinearity with all other S-points.
    set T1 := (Finset.univ.image (fun k' => Q k') |>.erase (Q k)) ∪
                   Finset.univ.image R with hT1_def
    have hTcard : T1.card ≤ d + M := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : ((Finset.univ.image (fun k' => Q k')).erase (Q k)).card ≤ d :=
        Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
      have h3 : (Finset.univ.image R).card ≤ M :=
        Finset.card_image_le.trans (by simp)
      linarith
    have hSizeOK : E.points.card > 2 * T1.card + 1 := by
      linarith
    have hQk_notT : Q k ∉ T1 := by
      simp only [T1, Finset.mem_union, Finset.mem_erase, Finset.mem_image]
      push_neg
      exact ⟨fun habs => absurd rfl habs, fun j _ => h j⟩
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (Q k) (hQonE k)
      ((Finset.univ.image (fun k' => Q k') |>.erase (Q k)) ∪ Finset.univ.image R)
      hQk_notT hSizeOK
    have hPolyG0 := hPolyGAll (Q k) A₁ (hQonE k) hA₁mem
    rw [polyG_at_self_Q E Q beta R m k A₁] at hPolyG0
    -- beta k * (∏_{k'≠k} ellP(Q_{k'})) * (∏_j ellP(R_j)) = 0
    -- All factors nonzero by A₁good, so beta k = 0, contradiction.
    have hProdQ : (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k' hk'
      apply hA₁good
      rw [Finset.mem_union]
      left
      rw [Finset.mem_erase]
      exact ⟨fun heq => (Finset.mem_erase.mp hk').1 (hDistinctQ heq),
             Finset.mem_image.mpr ⟨k', Finset.mem_univ _, rfl⟩⟩
    have hProdR : (∏ j : Fin M, ellP E (R j) (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j _
      apply hA₁good
      rw [Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact absurd (by
      rcases mul_eq_zero.mp hPolyG0 with h1 | h1
      · exact (mul_eq_zero.mp h1).resolve_right hProdQ
      · exact absurd h1 hProdR) (hBetaNz k)
  -- == Step 3: Build σ ==
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
  -- == Step 4: m j = 0 for j ∉ range σ ==
  have hM_offrange : ∀ j, j ∉ Set.range σ → m j = 0 := by
    intro j hj
    -- R j ∉ {Q k} since j ∉ range σ. Set A₀ = R j.
    have hRjNotQ : ∀ k, R j ≠ Q k := by
      intro k heq
      exact hj ⟨k, hDistinctR ((hσ_def k).trans heq.symm)⟩
    set T2 := Finset.univ.image Q ∪ (Finset.univ.image R |>.erase (R j)) with hT2_def
    have hTcard2 : T2.card ≤ d + M := by
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : (Finset.univ.image Q).card ≤ d :=
        Finset.card_image_le.trans (by simp)
      have h3 : ((Finset.univ.image R).erase (R j)).card ≤ M :=
        Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
      omega
    have hSizeOK2 : E.points.card > 2 * T2.card + 1 := by linarith
    have hRj_notT : R j ∉ T2 := by
      simp only [T2, Finset.mem_union, Finset.mem_image, Finset.mem_erase]
      intro h
      rcases h with ⟨k, _, hQk⟩ | ⟨hne, _⟩
      · exact hRjNotQ k hQk.symm
      · exact hne rfl
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (R j) (hRonE j)
      (Finset.univ.image Q ∪ (Finset.univ.image R |>.erase (R j)))
      hRj_notT hSizeOK2
    have hPolyG0 := hPolyGAll (R j) A₁ (hRonE j) hA₁mem
    rw [polyG_at_self_R E Q beta R m j A₁] at hPolyG0
    have hProdQ2 : (∏ k : Fin d, ellP E (Q k) (R j) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro k _
      apply hA₁good
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    have hProdR2 : (∏ j' ∈ Finset.univ.erase j, ellP E (R j') (R j) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j' hj'
      apply hA₁good
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => (Finset.mem_erase.mp hj').1 (hDistinctR heq),
         Finset.mem_image.mpr ⟨j', Finset.mem_univ _, rfl⟩⟩)
    rcases mul_eq_zero.mp hPolyG0 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_right hProdQ2
    · exact absurd h1 hProdR2
  -- == Step 5: beta k + m (σ k) = 0 ==
  have hBetaMsigma : ∀ k : Fin d, beta k + m (σ k) = 0 := by
    intro k
    -- Use residual_vanishes_on_ExE to get G = 0 on E×E,
    -- then evaluate at A₀ = R(σ k) = Q k with a good A₁.
    have hResVan := residual_vanishes_on_ExE E hHW Q beta R m σ
      (fun k' => (hσ_def k').symm) hM_offrange hPolyGAll hELarge hQonE hELarge_dkl
    -- G(Q k, A₁) = (beta k + m(σ k)) * ∏_{j≠σ(k)} ellP(R j, Q k, A₁)
    -- for all A₁ ∈ E. The product structure means:
    -- when ellP(R(σ k)) = 0 (automatic since R(σ k) = Q k = A₀),
    -- only the k-th term survives (others have ellP(R(σ k)) in their product).
    have hTcard3 : ((Finset.univ.image R).erase (R (σ k))).card ≤ M := by
      exact Finset.card_erase_le.trans (Finset.card_image_le.trans (by simp))
    have hSizeOK3 : E.points.card > 2 * ((Finset.univ.image R).erase (R (σ k))).card + 1 := by
      linarith
    have hQk_notT3 : Q k ∉ (Finset.univ.image R).erase (R (σ k)) := by
      simp only [Finset.mem_erase, Finset.mem_image]
      intro ⟨_, j, _, hRjQk⟩
      have : R (σ k) = R j := (hσ_def k).trans hRjQk.symm
      have : σ k = j := hDistinctR this
      simp_all
    obtain ⟨A₁, hA₁mem, hA₁ne, hA₁good⟩ := exists_avoiding_A1 E (Q k) (hQonE k)
      ((Finset.univ.image R).erase (R (σ k)))
      hQk_notT3 hSizeOK3
    have hResVal := hResVan (Q k) A₁ (hQonE k) hA₁mem
    rw [bivEval₂_residualFull_eq] at hResVal
    -- At A₀ = Q k = R(σ k): for k' ≠ k, the product ∏_{j≠σ(k')}
    -- includes j = σ(k) (since σ k ≠ σ k'), and
    -- ellP(R(σ k), Q k, A₁) = ellP(Q k, Q k, A₁) = 0.
    -- So only the k-th term survives.
    have hOtherTerms : ∀ k' : Fin d, k' ≠ k →
        (beta k' + m (σ k')) *
          ∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k'),
            ellP E (R j) (Q k) A₁ = 0 := by
      intro k' hne
      have hσkmem : σ k ∈ Finset.univ.erase (σ k') := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hne (by exact (σ.injective h).symm), Finset.mem_univ _⟩
      have : ellP E (R (σ k)) (Q k) A₁ = 0 := by
        change ellP E (R (sigma_fun k)) (Q k) A₁ = 0
        rw [hσ_def k]; exact ellP_self_eq_zero E (Q k) A₁
      rw [Finset.prod_eq_zero hσkmem this]
      ring
    rw [Finset.sum_eq_single k
      (fun k' _ hne => hOtherTerms k' hne)
      (fun h => absurd (Finset.mem_univ k) h)] at hResVal
    -- Now hResVal : (beta k + m(σ k)) * ∏_{j≠σ(k)} ellP(R j, Q k, A₁) = 0
    -- with the product nonzero.
    have hProdNz : (∏ j ∈ (Finset.univ : Finset (Fin M)).erase (σ k),
        ellP E (R j) (Q k) A₁) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro j hj
      apply hA₁good
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      intro heq
      have := (Finset.mem_erase.mp hj).1
      apply this
      exact hDistinctR heq
    exact (mul_eq_zero.mp hResVal).resolve_right hProdNz
  refine ⟨σ, fun k => (hσ_def k).symm, hBetaMsigma, hM_offrange⟩

/-- **Paper Step 3** (`thm:ma`, ip.tex `\ref{step:sigma}`): permutation
    `σ` matches multisets `{Q_α} ↔ {-P, B_j}` with multiplicities
    (≡ paper's residue identity `eq:residue-identity`).

    Lean realisation of "equate the two factored norm forms
    `∏_α (t - L(Q_α))^{n_α}` and `(t - L(-P)) · ∏_j (t - L(B_j))^{m_j}`
    and take multisets of roots with multiplicities". Given `polyGFull`
    vanishing pointwise on `E × E` (= Step 2's conclusion) plus
    `hELarge : |E| > 4·(d+M) + 2`, produce the σ-matching output.
    Internally consolidated via `sigma_matching_core`. -/
theorem sigma_matching_from_polyGFull_vanishing (hHW : E.HasseBound)
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hQonE : ∀ k, Q k ∈ E.points)
    (hRonE : ∀ j, R j ∈ E.points)
    (hVanishing : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (polyGFull E Q beta R m) A₀ A₁ = 0)
    (hELarge : E.points.card > 4 * (d + M) + 2)
    (hELarge_dkl : E.points.card * E.points.card - 2 * E.points.card
                     > 18 * (d + M) * E.q) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0) := by
  classical
  have hPolyGAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      polyG E Q beta R m A₀ A₁ = 0 := by
    intro A₀ A₁ h₀ h₁
    rw [← bivEval₂_polyGFull_eq_polyG E Q beta R m A₀ A₁]
    exact hVanishing A₀ A₁ h₀ h₁
  exact sigma_matching_core E hHW Q beta R m hDistinctQ hDistinctR hBetaNz hQonE hRonE hPolyGAll
    hELarge hELarge_dkl

end Divisor
