/-
  Divisor/TightBound.lean — Paper-tight bound via polyGFull
-/
import Divisor.ClearedFullPoly
import Divisor.TraceProof

open Polynomial Finset Classical

namespace Divisor

variable {E : ECSetup}

/-! ### Step 1: Chord avoids D-zeros (Bezout argument) -/

theorem chord_avoids_D_zeros_of_denom_defined
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hDenom : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 := by
  contrapose! hDenom;
  obtain ⟨ Q, hQ₁, hQ₂ ⟩ := hDenom; simp_all +decide [ logDerivCheckFnDenom ] ;
  have h_card : (E.points.filter (fun p => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval p.1 p.2 = 0)).card ≤ 3 := by
    have := @linear_form_zeros_le_three E;
    convert this ( A₀.2 - A₁.2 ) ( A₁.1 - A₀.1 ) ( A₁.2 * A₀.1 - A₀.2 * A₁.1 ) _ using 1 <;> simp +decide [ lineThrough ];
    · congr! 2;
      ext; simp +decide [ slopeOf, Line.eval ] ; ring;
      grind +extAll;
    · exact Or.inr ( sub_ne_zero_of_ne <| Ne.symm hNV );
  contrapose! h_card; simp_all +decide [ Finset.subset_iff ] ;
  refine' lt_of_lt_of_le _ ( Finset.card_mono <| show { A₀, A₁, ( slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1, slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * ( slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1 ) + ( A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1 ) ), Q } ⊆ Finset.filter ( fun p => ( lineThrough A₀.1 A₀.2 A₁.1 A₁.2 ).eval p.1 p.2 = 0 ) E.points from _ );
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ * ];
    · intro h; simp_all +decide [ zerosFinset ] ;
      unfold zeros at hQ₁; aesop;
    · constructor;
      · grind +suggestions;
      · rintro rfl; simp_all +decide [ zerosFinset ] ;
        unfold zeros at hQ₁; aesop;
    · refine' ⟨ _, _, _ ⟩;
      · grind;
      · grind +suggestions;
      · rintro rfl; simp_all +decide [ zerosFinset ] ;
        unfold zeros at hQ₁; simp_all +decide [ Finset.mem_filter ] ;
  · simp_all +decide [ Finset.subset_iff ];
    refine' ⟨ _, _, _, _ ⟩;
    · unfold lineThrough; simp +decide [ sub_eq_iff_eq_add ] ;
      unfold Line.eval; simp +decide [ sub_eq_iff_eq_add ] ;
    · unfold lineThrough; simp +decide [ sub_eq_iff_eq_add ] ;
      unfold Line.eval slopeOf; simp +decide [ sub_eq_iff_eq_add ] ;
      field_simp;
      rw [ sub_div', ← add_div, eq_div_iff ] <;> ring ; simp +decide [ sub_eq_iff_eq_add, hNV ];
      · exact Ne.symm hNV;
      · exact sub_ne_zero_of_ne <| Ne.symm hNV;
    · refine' ⟨ _, _ ⟩;
      · exact E.hComplete _ _ ( chord_third_point_on_E E A₀ A₁ hA₀ hA₁ hNV );
      · unfold lineThrough; simp +decide [ slopeOf ] ; ring;
        unfold Line.eval; ring;
    · exact Finset.mem_filter.mp hQ₁ |>.1

/-! ### Step 2: logDerivCheckFn = 0 ← polyG = 0 -/

theorem logDerivCheckFn_zero_of_polyG_zero
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hPolyG : polyG E (zerosAt E D)
      (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  revert hDef hPolyG A₀ A₁ hA₀ hA₁ hNV;
  intros A₀ A₁ hA₀ hA₁ hNV hDef hPolyG
  have hQline : ∀ Q ∈ zerosFinset E D, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 := by
    exact?;
  have hRline : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (P.1) (-P.2) ≠ 0 ∧ ∀ j : Fin k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0 := by
    unfold logDerivCheckFnDefined at hDef;
    unfold logDerivCheckFnDenom at hDef; simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_zero ] ;
  have hPaperResidue : paperResidueDivided E (zerosAt E D) (fun k' => (multAt E (betaConstructive E D) D k')) (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) A₀ A₁ = 0 := by
    have := polyG_eq_zero_iff_paperResidue E ( zerosAt E D ) ( fun k' => ( multAt E ( betaConstructive E D ) D k' : ZMod E.q ) ) ( Fin.cons ( P.1, -P.2 ) B ) ( Fin.cons ( -1 ) fun j => -m j ) A₀ A₁;
    simp_all +decide [ Fin.forall_fin_succ ];
    exact this fun k => hQline _ _ <| by simp +decide [ zerosAt ] ;
  convert congr_arg ( fun x : ZMod E.q => -x ) hPaperResidue using 1;
  · unfold logDerivCheckFn paperResidueDivided;
    simp +decide [ Fin.sum_univ_succ, Fin.cons ];
    rw [ chord_sum_eq_residue_sum_fin ];
    all_goals norm_num [ logDerivCheckFnDefined ] at *;
    any_goals tauto;
    · unfold multAt; ring;
    · exact fun h => hDef <| by unfold logDerivCheckFnDenom; simp +decide [ h ] ;
    · exact fun h => hDef <| by unfold logDerivCheckFnDenom; simp +decide [ h ] ;
    · exact fun h => hDef <| by unfold logDerivCheckFnDenom; aesop;
    · unfold logDerivCheckFnDenom at hDef; aesop;
  · norm_num

/-! ### Step 3: Bad pair → polyGFull = 0 -/

theorem bad_pair_implies_polyGFull_zero
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNVx : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    bivEval₂ (polyGFull E (zerosAt E D)
      (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
      A₀ A₁ = 0 := by
  rw [bivEval₂_polyGFull_eq_polyG]
  exact polyG_zero_at_defined_fincons D hDnz hSplit hAccount P B m A₀ A₁
    hA₀ hA₁ hNVx hDef
    (chord_avoids_D_zeros_of_denom_defined D P B A₀ A₁ hA₀ hA₁ hNVx hDef)
    hCheck

/-! ### Step 4: polyGFull ≠ 0 at the hNV witness -/

theorem polyGFull_nonzero_at_witness
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNVx : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    bivEval₂ (polyGFull E (zerosAt E D)
      (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
      A₀ A₁ ≠ 0 := by
  intro hContra
  rw [bivEval₂_polyGFull_eq_polyG] at hContra
  exact hCheck (logDerivCheckFn_zero_of_polyG_zero D hDnz hSplit hAccount
    P B m A₀ A₁ hA₀ hA₁ hNVx hDef hContra)

/-! ### Step 5: zerosCard ≤ degE -/

private lemma zerosCard_le_degE' (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    zerosCard E D ≤ D.degE := by
  have hβcov := betaConstructive_covers E D hDnz
  have hβpos : ∀ k' : Fin (zerosCard E D),
      1 ≤ multAt E (betaConstructive E D) D k' :=
    fun k' => multAt_pos E (betaConstructive E D) D hβcov k'
  calc zerosCard E D
      = ∑ _ : Fin (zerosCard E D), 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    _ ≤ ∑ k' : Fin (zerosCard E D), multAt E (betaConstructive E D) D k' :=
        Finset.sum_le_sum (fun k' _ => hβpos k')
    _ = ∑ P ∈ E.points, betaConstructive E D P :=
        sum_multAt_eq_sum_βfun E (betaConstructive E D) D
          (betaConstructive_support E D)
    _ ≤ D.degE := betaConstructive_sum_le_degE E D

/-! ### Step 6: Tight core bound -/

private lemma hDnz_from_hNV
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ¬ (D.a = 0 ∧ D.b = 0) := by
  obtain ⟨A₀, A₁, _, _, _, hDef, _⟩ := hNV
  intro ⟨ha, hb⟩
  apply hDef
  show logDerivCheckFnDenom E D P B A₀ A₁ = 0
  unfold logDerivCheckFnDenom CoordRingElt.eval
  simp only [ha, hb, Polynomial.eval_zero, zero_mul, mul_zero, sub_zero]

theorem log_deriv_sz_paper_core_tight
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          A₀ne_A₁x_cleared_pair E D P B m p)).card
      ≤ 18 * (D.degE + k) * E.q := by
  classical
  have hDnz := hDnz_from_hNV D P B m hNV
  set polyGF := polyGFull E (zerosAt E D)
    (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
  -- bad ⊆ {polyGFull = 0 on E × E}
  have hBadSub : (E.points ×ˢ E.points).filter
      (fun p => A₀ne_A₁x_cleared_pair E D P B m p) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ polyGF p.1 p.2 = 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    obtain ⟨hNVx, hDenom, hCheck⟩ := hp.2
    have hprod := Finset.mem_product.mp hp.1
    exact bad_pair_implies_polyGFull_zero D hDnz hSplit hAccount P B m
      p.1 p.2 hprod.1 hprod.2 hNVx hDenom hCheck
  -- nonzero witness
  obtain ⟨wA₀, wA₁, hwA₀, hwA₁, hwNV, hwDef, hwCheck⟩ := hNV
  have hWitness : ∃ a₀ a₁, a₀ ∈ E.points ∧ a₁ ∈ E.points ∧
      bivEval₂ polyGF a₀ a₁ ≠ 0 :=
    ⟨wA₀, wA₁, hwA₀, hwA₁,
      polyGFull_nonzero_at_witness D hDnz hSplit hAccount P B m
        wA₀ wA₁ hwA₀ hwA₁ hwNV hwDef hwCheck⟩
  -- degree bound
  set d := zerosCard E D
  set M := k + 1
  have hTD := polyGFull_total_degree_le_tight E (zerosAt E D)
    (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
  have hdM1 : d + M - 1 = d + k := by omega
  rw [hdM1] at hTD
  have hDKL := bivariate_poly_zeros_on_ExE_le E polyGF
    (2 * (d + k)) hTD hWitness
  have hZC : d ≤ D.degE := zerosCard_le_degE' D hDnz
  calc ((E.points ×ˢ E.points).filter
        (fun p => A₀ne_A₁x_cleared_pair E D P B m p)).card
      ≤ ((E.points ×ˢ E.points).filter
          (fun p => bivEval₂ polyGF p.1 p.2 = 0)).card :=
        Finset.card_le_card hBadSub
    _ ≤ 9 * (2 * (d + k)) * E.q := hDKL
    _ = 18 * (d + k) * E.q := by ring
    _ ≤ 18 * (D.degE + k) * E.q := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega

/-! ### Paper-tight outer bound -/

/-- **Paper `event_NotEq` bound** (`thm:ma`, ip.tex): given a witness
    `(A₀, A₁) ∈ E.points²` where the log-derivative check is defined
    and nonzero (i.e. `f ≢ 0` in the paper's notation), bound the
    cardinality of the accepting challenge set by

      `18·(d + k)·|F_q| + (6·d + 9·k + 71)·|E.points|`.

    Realised via `lem:log-derivative` (SZ-on-(E×E) applied to the
    cleared log-deriv polynomial) plus the Hasse bound. -/
theorem log_deriv_sz_paper_tight
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (eventNotEq E D P B (fun i => m i)).card
      ≤ 18 * (D.degE + k) * E.q +
        (6 * D.degE + 9 * k + 71) * E.points.card := by
  classical
  have hDnz := hDnz_from_hNV D P B m hNV
  -- Split: defined-bad + undefined
  have hSub : eventNotEq E D P B (fun i => m i) ⊆
      (E.points ×ˢ E.points).filter
        (fun p => A₀ne_A₁x_cleared_pair E D P B m p) ∪
      (E.points ×ˢ E.points).filter
        (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) := by
    intro p hp
    simp only [eventNotEq, Finset.mem_filter] at hp
    obtain ⟨hVP, hCheck⟩ := hp
    have hDP : p ∈ distinctPairs E.points := (Finset.mem_filter.mp hVP).1
    have hEE : p ∈ E.points ×ˢ E.points := (Finset.mem_filter.mp hDP).1
    have hNeq : p.1.1 ≠ p.2.1 := ((Finset.mem_filter.mp hVP).2).1
    by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hEE, hNeq, hDef, hCheck⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hEE, hDef⟩))
  have hCoreBound := log_deriv_sz_paper_core_tight D P B m hDeg
    hSplit hAccount hNV
  have hUndefBound := logDerivCheckFn_undefined_set_bound_tight E D P k B hDnz
  calc (eventNotEq E D P B (fun i => m i)).card
      ≤ ((E.points ×ˢ E.points).filter
          (fun p => A₀ne_A₁x_cleared_pair E D P B m p)).card +
        ((E.points ×ˢ E.points).filter
          (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card :=
        le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
    _ ≤ 18 * (D.degE + k) * E.q +
          (6 * D.degE + 9 * k + 71) * E.points.card :=
        Nat.add_le_add hCoreBound hUndefBound

end Divisor