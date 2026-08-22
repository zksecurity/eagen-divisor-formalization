/-
  Divisor/TightBound.lean — Paper-tight bound via polyGFull
-/
import Divisor.ClearedFullPoly
import Divisor.SigmaMatching
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
  contrapose! h_card; simp_all +decide ;
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
    · unfold lineThrough; simp +decide ;
      unfold Line.eval; simp +decide ;
    · unfold lineThrough; simp +decide ;
      unfold Line.eval slopeOf; simp +decide [ sub_eq_iff_eq_add ] ;
      field_simp;
      ring;
    · refine' ⟨ _, _ ⟩;
      · exact E.hComplete _ _ ( chord_third_point_on_E E A₀ A₁ hA₀ hA₁ hNV );
      · unfold lineThrough; simp +decide [ slopeOf ] ; ring;
        unfold Line.eval; ring;
    · exact Finset.mem_filter.mp hQ₁ |>.1

/-! ### Step 2: logDerivCheckFn = 0 ← polyG = 0 -/

theorem logDerivCheckFn_zero_of_polyG_zero
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hPolyG : polyG E (zerosAt E D)
      (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  -- Extract individual nonzero conditions from `hDef` (mirror of
  -- `polyG_zero_at_defined_fincons` in TraceProof.lean).
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLamDef
  set L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2 with hLDef
  set x₂ := lam ^ 2 - A₀.1 - A₁.1 with hx₂Def
  set y₂ := lam * x₂ + (A₀.2 - lam * A₀.1) with hy₂Def
  have hProdNZ := hDef
  have hBlineProd : (univ : Finset (Fin k)).prod (fun j => L.eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hProdNZ
  have h7 : L.eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have hLeftOf7 := left_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have h6 : 3 * x₂ ^ 2 + E.curveA - 2 * lam * y₂ ≠ 0 :=
    right_ne_zero_of_mul hLeftOf7
  have hLeftOf6 := left_ne_zero_of_mul hLeftOf7
  have h5 : 3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf6
  have hLeftOf5 := left_ne_zero_of_mul hLeftOf6
  have h4 : 3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf5
  have hLeftOf4 := left_ne_zero_of_mul hLeftOf5
  have h3 : D.eval x₂ y₂ ≠ 0 := right_ne_zero_of_mul hLeftOf4
  have hLeftOf3 := left_ne_zero_of_mul hLeftOf4
  have h2 : D.eval A₁.1 A₁.2 ≠ 0 := right_ne_zero_of_mul hLeftOf3
  have h1 : D.eval A₀.1 A₀.2 ≠ 0 := left_ne_zero_of_mul hLeftOf3
  have hDen : ∀ pt : ZMod E.q × ZMod E.q,
      pt = A₀ ∨ pt = A₁ ∨ pt = (x₂, y₂)
      → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0 := by
    rintro pt (rfl | rfl | rfl) <;> assumption
  have hBline : ∀ j : Fin k, L.eval (B j).1 (B j).2 ≠ 0 := by
    intro j hj; exact hBlineProd (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  -- Chord avoids D-zeros.
  have hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 :=
    chord_avoids_D_zeros_of_denom_defined D P B A₀ A₁ hA₀ hA₁ hNV hDef
  -- The β properties.
  have hβsup := betaTrue_support E D hDnz
  have hβcov := betaTrue_covers E D hDnz
  have hAccount := betaTrue_account E D hDnz hSplit
  -- Lemma 6 with β = betaTrue.
  have hLemma6 := chord_sum_eq_residue_sum_fin E D (betaTrue E D hDnz) A₀ A₁
    hA₀ hA₁ hNV hDnz hSplit hβsup hβcov hAccount (fun _ => rfl)
    h1 h2 h3 hQline hDen
  -- multAt = β at zerosAt.
  have hLemma6' :
      logDerivTerm E D E.curveA lam A₀
        + logDerivTerm E D E.curveA lam A₁
        + logDerivTerm E D E.curveA lam (x₂, y₂)
      = -∑ k' : Fin (zerosCard E D),
          ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
              (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ := by
    convert hLemma6 using 2
    exact Finset.sum_congr rfl fun k' _ => by
      rw [show multAt E (betaTrue E D hDnz) D k'
            = betaTrue E D hDnz (zerosAt E D k') from rfl]
  -- Bridge polyG = 0 → paperResidueDivided = 0.
  have hQlineFin : ∀ k' : Fin (zerosCard E D),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
        (zerosAt E D k').1 (zerosAt E D k').2 ≠ 0 :=
    hQline_fin_of_finset E D A₀ A₁ hQline
  have hRlineFin : ∀ j : Fin (k + 1),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
        ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j).1
        ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j).2 ≠ 0 := by
    intro j
    rcases Fin.eq_zero_or_eq_succ j with h | ⟨i, rfl⟩
    · subst h; simpa using h7
    · simpa using hBline i
  have hPolyGEq := polyG_eq_zero_iff_paperResidue E (zerosAt E D)
    (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) A₀ A₁
    hNV hQlineFin hRlineFin
  have hPaperResidue := hPolyGEq.mp hPolyG
  -- Now match logDerivCheckFn against -paperResidueDivided.
  show logDerivCheckFn E D P k B m A₀ A₁ = 0
  simp only [logDerivCheckFn]
  simp only [paperResidueDivided] at hPaperResidue
  rw [hLemma6']
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hPaperResidue
  linear_combination -hPaperResidue

/-! ### Step 3: Bad pair → polyGFull = 0 -/

theorem bad_pair_implies_polyGFull_zero
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNVx : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    bivEval₂ (polyGFull E (zerosAt E D)
      (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
      A₀ A₁ = 0 := by
  rw [bivEval₂_polyGFull_eq_polyG]
  exact polyG_zero_at_defined_fincons D hDnz (betaTrue E D hDnz)
    (betaTrue_support E D hDnz) (betaTrue_covers E D hDnz)
    hSplit (betaTrue_account E D hDnz hSplit) (fun _ => rfl) P B m A₀ A₁
    hA₀ hA₁ hNVx hDef
    (chord_avoids_D_zeros_of_denom_defined D P B A₀ A₁ hA₀ hA₁ hNVx hDef)
    hCheck

/-! ### Step 4: polyGFull ≠ 0 at the hNV witness -/

theorem polyGFull_nonzero_at_witness
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNVx : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    bivEval₂ (polyGFull E (zerosAt E D)
      (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
      A₀ A₁ ≠ 0 := by
  intro hContra
  rw [bivEval₂_polyGFull_eq_polyG] at hContra
  exact hCheck (logDerivCheckFn_zero_of_polyG_zero D hDnz hSplit
    P B m A₀ A₁ hA₀ hA₁ hNVx hDef hContra)

/-! ### Step 5: zerosCard ≤ degE -/

private lemma zerosCard_le_degE' (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    zerosCard E D ≤ D.degE := by
  have hβcov := betaTrue_covers E D hDnz
  have hβpos : ∀ k' : Fin (zerosCard E D),
      1 ≤ multAt E (betaTrue E D hDnz) D k' :=
    fun k' => multAt_pos E (betaTrue E D hDnz) D hβcov k'
  calc zerosCard E D
      = ∑ _ : Fin (zerosCard E D), 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    _ ≤ ∑ k' : Fin (zerosCard E D), multAt E (betaTrue E D hDnz) D k' :=
        Finset.sum_le_sum (fun k' _ => hβpos k')
    _ = ∑ P ∈ E.points, betaTrue E D hDnz P :=
        sum_multAt_eq_sum_βfun E (betaTrue E D hDnz) D
          (betaTrue_support E D hDnz)
    _ ≤ D.degE := betaTrue_sum_le_degE E D hDnz

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
    (hSplit : splitsOnE E D)
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
    (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
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
    exact bad_pair_implies_polyGFull_zero D hDnz hSplit P B m
      p.1 p.2 hprod.1 hprod.2 hNVx hDenom hCheck
  -- nonzero witness
  obtain ⟨wA₀, wA₁, hwA₀, hwA₁, hwNV, hwDef, hwCheck⟩ := hNV
  have hWitness : ∃ a₀ a₁, a₀ ∈ E.points ∧ a₁ ∈ E.points ∧
      bivEval₂ polyGF a₀ a₁ ≠ 0 :=
    ⟨wA₀, wA₁, hwA₀, hwA₁,
      polyGFull_nonzero_at_witness D hDnz hSplit P B m
        wA₀ wA₁ hwA₀ hwA₁ hwNV hwDef hwCheck⟩
  -- degree bound
  set d := zerosCard E D
  set M := k + 1
  have hTD := polyGFull_total_degree_le_tight E (zerosAt E D)
    (fun k' => ((multAt E (betaTrue E D hDnz) D k' : ℕ) : ZMod E.q))
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

      `18·(d + k)·|F_q| + (3·d + 9·k + 71)·|E.points|`.

    Realised via `lem:log-derivative` (SZ-on-(E×E) applied to the
    cleared log-deriv polynomial) plus the Hasse bound. -/
theorem log_deriv_sz_paper_tight
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hSplit : splitsOnE E D)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (eventNotEq E D P B (fun i => m i)).card
      ≤ 18 * (D.degE + k) * E.q +
        (3 * D.degE + 9 * k + 71) * E.points.card := by
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
    hSplit hNV
  have hUndefBound := logDerivCheckFn_undefined_set_bound_tight E D P k B hDnz
  calc (eventNotEq E D P B (fun i => m i)).card
      ≤ ((E.points ×ˢ E.points).filter
          (fun p => A₀ne_A₁x_cleared_pair E D P B m p)).card +
        ((E.points ×ˢ E.points).filter
          (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card :=
        le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
    _ ≤ 18 * (D.degE + k) * E.q +
          (3 * D.degE + 9 * k + 71) * E.points.card :=
        Nat.add_le_add hCoreBound hUndefBound

end Divisor
