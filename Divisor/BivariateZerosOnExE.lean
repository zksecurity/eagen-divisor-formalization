/-
  Divisor/BivariateZerosOnExE.lean

  Bound on `|{(A₀, A₁) ∈ E × E : f(A₀, A₁) = 0}|` for a 4-variate `f`
  of total degree ≤ D, derived from `Divisor.hasse_weil` plus
  elementary fiber counting. Same `≤ 9·D·q` bound as the
  classical DKL'14 + Hartshorne (Bezout) corollary.
-/
import Divisor.FourVarPoly
import Divisor.Axioms.AxiomHasseWeil
import Divisor.CurveEvalZerosHelper
import Mathlib

namespace Divisor.BivariateZerosOnExE

open MvPolynomial Finset

variable (E : ECSetup)

/-! ## Helper lemmas -/

/-- Each x ∈ ZMod q has at most 2 curve points, so `|E| ≤ 2q`. -/
lemma points_card_le_two_mul_q : E.points.card ≤ 2 * E.q := by
  have h_card : ∀ x ∈ Finset.univ, (Finset.filter (fun y => y^2 = x^3 + E.curveA * x + E.curveB) (Finset.univ : Finset (ZMod E.q))).card ≤ 2 := by
    intro x hx
    refine' le_trans ( Finset.card_le_card _ ) _
    exact ( Polynomial.roots ( Polynomial.X ^ 2 - Polynomial.C ( x ^ 3 + E.curveA * x + E.curveB ) ) |> Multiset.toFinset )
    · norm_num [ Finset.subset_iff ]
      exact fun y hy => ⟨ ne_of_apply_ne ( fun p => p.coeff 2 ) <| by norm_num [ Polynomial.coeff_eq_zero_of_natDegree_lt ], sub_eq_zero.mpr hy ⟩
    · exact le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] ) )
  have h_card : E.points ⊆ Finset.biUnion (Finset.univ : Finset (ZMod E.q)) (fun x => Finset.image (fun y => (x, y)) (Finset.filter (fun y => y^2 = x^3 + E.curveA * x + E.curveB) (Finset.univ : Finset (ZMod E.q)))) := by
    intro p hp; have := E.hOnCurve p hp; aesop
  refine le_trans ( Finset.card_le_card h_card ) ?_
  refine' le_trans ( Finset.card_biUnion_le ) _
  exact le_trans ( Finset.sum_le_sum fun _ _ => by rw [ Finset.card_image_of_injective ] ; aesop_cat ) ( by simpa [ mul_comm ] using Finset.sum_le_sum ‹∀ x ∈ Finset.univ, Finset.card { y : ZMod E.q | y ^ 2 = x ^ 3 + E.curveA * x + E.curveB } ≤ 2› )

/-- A degree-0 MvPolynomial is a constant. -/
lemma totalDegree_zero_eq_C {q : ℕ} [Fact (Nat.Prime q)]
    (f : FourVarPoly q) (h : f.totalDegree ≤ 0) :
    ∃ c : ZMod q, f = C c := by
  grind +suggestions

/-
Integer arithmetic: m^2 ≤ 4*q and q ≥ 5 implies 2*m ≤ q + 3 for integer m.
-/
lemma hasse_int_bound (q : ℕ) (m : ℤ) (hq : q ≥ 5) (hm : m ^ 2 ≤ 4 * (q : ℤ)) :
    2 * m ≤ (q : ℤ) + 3 := by
  nlinarith

/-- Specialise a 4-variate polynomial at the first pair of coordinates. -/
noncomputable def specialize_first (f : FourVarPoly E.q)
    (A₀ : ZMod E.q × ZMod E.q) : MvPolynomial (Fin 2) (ZMod E.q) :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 4 => match i with
      | ⟨0, _⟩ => MvPolynomial.C A₀.1
      | ⟨1, _⟩ => MvPolynomial.C A₀.2
      | ⟨2, _⟩ => MvPolynomial.X 0
      | ⟨3, _⟩ => MvPolynomial.X 1) f

/-- Specialise a 4-variate polynomial at the second pair of coordinates. -/
noncomputable def specialize_second (f : FourVarPoly E.q)
    (A₁ : ZMod E.q × ZMod E.q) : MvPolynomial (Fin 2) (ZMod E.q) :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 4 => match i with
      | ⟨0, _⟩ => MvPolynomial.X 0
      | ⟨1, _⟩ => MvPolynomial.X 1
      | ⟨2, _⟩ => MvPolynomial.C A₁.1
      | ⟨3, _⟩ => MvPolynomial.C A₁.2) f

lemma specialize_first_eval (f : FourVarPoly E.q) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then A₁.1 else A₁.2)
      (specialize_first E f A₀) = bivEval₂ f A₀ A₁ := by
  erw [ MvPolynomial.eval_eval₂ ]
  congr
  · ext; simp +decide [ MvPolynomial.eval_C ]
  · ext i; fin_cases i <;> simp +decide [ bivEval₂Fun ]

lemma specialize_second_eval (f : FourVarPoly E.q) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then A₀.1 else A₀.2)
      (specialize_second E f A₁) = bivEval₂ f A₀ A₁ := by
  erw [ MvPolynomial.eval_eval₂ ];
  congr;
  · exact RingHom.ext fun x => by simp +decide ;
  · funext s; fin_cases s <;> simp +decide [ bivEval₂Fun ] ;

lemma specialize_first_totalDegree (f : FourVarPoly E.q) (A₀ : ZMod E.q × ZMod E.q) (D : ℕ)
    (hDeg : total_degree_le E f D) :
    (specialize_first E f A₀).totalDegree ≤ D := by
  have h_total_degree_le : ∀ m ∈ f.support, (m 0) + (m 1) + (m 2) + (m 3) ≤ D := by
    intro m hm; have := hDeg; simp_all +decide [ total_degree_le ]
    have h_deg : m.sum (fun i n => n) ≤ D := by
      exact le_trans ( Finset.le_sup ( f := fun m => m.sum fun i n => n ) ( Finsupp.mem_support_iff.mpr hm ) ) hDeg
    convert h_deg using 1 ; simp +decide [ Finsupp.sum_fintype, Fin.sum_univ_four ]
  rw [ show specialize_first E f A₀ = ∑ m ∈ f.support, f.coeff m • ( MvPolynomial.C A₀.1 ^ m 0 * MvPolynomial.C A₀.2 ^ m 1 * MvPolynomial.X 0 ^ m 2 * MvPolynomial.X 1 ^ m 3 ) from ?_ ]
  · simp +decide [ MvPolynomial.totalDegree ]
    intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_smul ]
    refine Finset.sum_eq_zero fun m hm => ?_ ; simp_all +decide [ mul_assoc ]
    rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ]
    refine' lt_of_le_of_lt _ hb
    refine' le_trans _ ( h_total_degree_le m hm )
    refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _
    refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_pow _ _ ) ( MvPolynomial.totalDegree_mul _ _ ) ) _ ; norm_num
    refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_pow _ _ ) ( MvPolynomial.totalDegree_mul _ _ ) ) _ ; norm_num
  · unfold specialize_first; simp +decide [ MvPolynomial.eval₂_eq' ]
    exact Finset.sum_congr rfl fun _ _ => by rw [ Fin.prod_univ_four ] ; simp +decide [ mul_assoc, Algebra.smul_def ]

/-- The (0,1) ↔ (2,3) coordinate swap, used to derive the second-coordinate
    bound from the first via `specialize_first_totalDegree`. -/
private noncomputable def swapσ : Fin 4 → Fin 4 :=
  fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1

lemma specialize_second_totalDegree (f : FourVarPoly E.q) (A₁ : ZMod E.q × ZMod E.q) (D : ℕ)
    (hDeg : total_degree_le E f D) :
    (specialize_second E f A₁).totalDegree ≤ D := by
  have hRen : total_degree_le E (MvPolynomial.rename swapσ f) D := by
    unfold total_degree_le at hDeg ⊢
    exact (MvPolynomial.totalDegree_rename_le swapσ f).trans hDeg
  have hEq : specialize_second E f A₁ =
      specialize_first E (MvPolynomial.rename swapσ f) A₁ := by
    unfold specialize_first specialize_second
    rw [MvPolynomial.eval₂_rename]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hEq]
  exact specialize_first_totalDegree E (MvPolynomial.rename swapσ f) A₁ D hRen

/-- Bivariate Bezout-style bound on E.

    A polynomial of total degree ≤ d not vanishing identically on E has
    at most `3·d` zeros on `E(F_q)`. Proved via reduction modulo
    `Y² = X³ + AX + B` to canonical form `α(X) + β(X)·Y` and the
    norm-polynomial root count from `CurveEvalZerosHelper`. -/
lemma curve_eval_zeros_le
    (g : MvPolynomial (Fin 2) (ZMod E.q)) (d : ℕ)
    (hDeg : g.totalDegree ≤ d)
    (hNZ : ∃ P ∈ E.points, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g ≠ 0) :
    (E.points.filter (fun P =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g = 0)).card ≤ 3 * d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; exact le_trans (CurveEvalZeros.curve_eval_zeros_le_zero E g hDeg hNZ) (by norm_num)
  · exact CurveEvalZeros.curve_eval_zeros_le_pos E g d (by omega) hDeg hNZ

/-- Fibre count bound for fixed first coordinate. -/
lemma fiber_count_le (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (A₀ : ZMod E.q × ZMod E.q) (_hA₀ : A₀ ∈ E.points)
    (hFiberNZ : ∃ A₁ ∈ E.points, bivEval₂ f A₀ A₁ ≠ 0) :
    (E.points.filter (fun A₁ => bivEval₂ f A₀ A₁ = 0)).card ≤ 3 * D := by
  have h := curve_eval_zeros_le E (specialize_first E f A₀) D
    (specialize_first_totalDegree E f A₀ D hDeg)
    (hFiberNZ.imp fun x hx => ⟨hx.1, by simpa only [specialize_first_eval] using hx.2⟩)
  convert h using 2
  exact Finset.filter_congr fun x _ => by rw [specialize_first_eval]

/-- Fibre count bound for fixed second coordinate. -/
lemma fiber_count_le_second (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (A₁ : ZMod E.q × ZMod E.q) (_hA₁ : A₁ ∈ E.points)
    (hFiberNZ : ∃ A₀ ∈ E.points, bivEval₂ f A₀ A₁ ≠ 0) :
    (E.points.filter (fun A₀ => bivEval₂ f A₀ A₁ = 0)).card ≤ 3 * D := by
  have h := curve_eval_zeros_le E (specialize_second E f A₁) D
    (specialize_second_totalDegree E f A₁ D hDeg)
    (hFiberNZ.imp fun x hx => ⟨hx.1, by simpa only [specialize_second_eval] using hx.2⟩)
  convert h using 2
  exact Finset.filter_congr fun x _ => by rw [specialize_second_eval]

/-- From the Hasse bound (as a hypothesis):
`2 * |E.points| ≤ 3 * E.q + 3`. -/
lemma hasse_points_bound_of (hHW : E.HasseBound) :
    2 * E.points.card ≤ 3 * E.q + 3 := by
  have hw : ((E.numPoints : ℤ) - E.q - 1) ^ 2 ≤ 4 * E.q := hHW
  have hnum := E.hNumPoints
  have hqge := E.hq_ge
  set m := (E.numPoints : ℤ) - E.q - 1 with hm_def
  have hm_sq : m ^ 2 ≤ 4 * (E.q : ℤ) := hw
  have h2m : 2 * m ≤ (E.q : ℤ) + 3 := hasse_int_bound E.q m hqge hm_sq
  omega

/-- From Hasse-Weil: 2 * |E.points| ≤ 3 * E.q + 3. -/
lemma hasse_points_bound : 2 * E.points.card ≤ 3 * E.q + 3 :=
  hasse_points_bound_of E (hasse_bound E)

/-- From the Hasse bound (as a hypothesis): `q ≤ 2 * |E.points| + 3`.
The lower-side dual of `hasse_points_bound_of`. Apply
`hasse_int_bound` to `m = q − numAffine`. -/
lemma hasse_points_bound_lb_of (hHW : E.HasseBound) :
    E.q ≤ 2 * E.points.card + 3 := by
  have hw : ((E.numPoints : ℤ) - E.q - 1) ^ 2 ≤ 4 * E.q := hHW
  have hnum := E.hNumPoints
  have hqge := E.hq_ge
  -- Use m' = q + 1 - numPoints (so m'² = (numPoints - q - 1)² ≤ 4q).
  set m' := (E.q : ℤ) + 1 - E.numPoints with hm'_def
  have hm'_sq : m' ^ 2 ≤ 4 * (E.q : ℤ) := by
    have h := hw
    -- (numPoints - q - 1)² = (q + 1 - numPoints)² = m'²
    have : ((E.numPoints : ℤ) - E.q - 1) ^ 2 = m' ^ 2 := by ring
    linarith [this ▸ h]
  have h2m' : 2 * m' ≤ (E.q : ℤ) + 3 := hasse_int_bound E.q m' hqge hm'_sq
  omega

/-- From Hasse-Weil: `q − 3 ≤ 2 * |E.points|`. -/
lemma hasse_points_bound_lb : E.q ≤ 2 * E.points.card + 3 :=
  hasse_points_bound_lb_of E (hasse_bound E)

lemma arith_bound (D q n : ℕ) (hD : D ≥ 1) (hn : 2 * n ≤ 3 * q + 3) :
    6 * D * n ≤ 9 * D * q + 9 * D * D := by
  nlinarith

/-- For D = 0 and constant nonzero f, the filter is empty. -/
lemma filter_empty_of_D_zero
    (f : FourVarPoly E.q) (hDeg : total_degree_le E f 0)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ZMod E.q, f = C c := totalDegree_zero_eq_C f hDeg
  simp_all +decide [ bivEval₂_C ]

/-- Case when |E.points| ≤ 3D: trivial product bound. -/
lemma main_bound_small_points
    (f : FourVarPoly E.q) (D : ℕ) (_hD : D ≥ 1)
    (hSmall : E.points.card ≤ 3 * D) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q := by
  refine' le_trans ( Finset.card_filter_le _ _ ) _;
  rw [ Finset.card_product ];
  nlinarith [ points_card_le_two_mul_q E ]

/-- Case when |E.points| > 3D: fiber decomposition + bad fiber bound. -/
lemma main_bound_large_points (hHW : E.HasseBound)
    (f : FourVarPoly E.q) (D : ℕ) (hD : D ≥ 1)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0)
    (hLarge : E.points.card > 3 * D) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q := by
  revert f D hD hDeg hNonzero hLarge;
  intro f D hD hDeg hNonzero hLarge
  set bad := E.points.filter (fun A₀ => ∀ A₁ ∈ E.points, bivEval₂ f A₀ A₁ = 0) with hbad_def
  have hbad_card : bad.card ≤ 3 * D := by
    have := @fiber_count_le_second E f D hDeg;
    obtain ⟨ A₀, A₁, hA₀, hA₁, h ⟩ := hNonzero;
    exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( this A₁ hA₁ ⟨ A₀, hA₀, h ⟩ );
  have hgood_card : ∀ A₀ ∈ E.points \ bad, (E.points.filter (fun A₁ => bivEval₂ f A₀ A₁ = 0)).card ≤ 3 * D := by
    simp +zetaDelta at *;
    exact fun a b ha hb => fiber_count_le E f D hDeg ( a, b ) ha <| by obtain ⟨ x, y, hx, hy ⟩ := hb ha; exact ⟨ ( x, y ), hx, hy ⟩ ;
  have htotal_card : ((E.points ×ˢ E.points).filter (fun p => bivEval₂ f p.1 p.2 = 0)).card ≤ bad.card * E.points.card + (E.points.card - bad.card) * 3 * D := by
    have htotal_card : ((E.points ×ˢ E.points).filter (fun p => bivEval₂ f p.1 p.2 = 0)).card ≤ ∑ A₀ ∈ E.points, (E.points.filter (fun A₁ => bivEval₂ f A₀ A₁ = 0)).card := by
      rw [ Finset.card_filter ];
      rw [ Finset.sum_product ] ; aesop;
    have htotal_card : ∑ A₀ ∈ E.points, (E.points.filter (fun A₁ => bivEval₂ f A₀ A₁ = 0)).card ≤ ∑ A₀ ∈ bad, E.points.card + ∑ A₀ ∈ E.points \ bad, 3 * D := by
      rw [ ← Finset.sum_sdiff ( Finset.filter_subset ( fun A₀ => ∀ A₁ ∈ E.points, bivEval₂ f A₀ A₁ = 0 ) E.points ) ];
      rw [ add_comm ];
      exact add_le_add ( Finset.sum_le_sum fun x hx => Finset.card_filter_le _ _ ) ( Finset.sum_le_sum hgood_card );
    simp_all +decide [ mul_assoc, Finset.card_sdiff ];
    exact le_trans ‹_› ( htotal_card.trans ( by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ) );
  have := hasse_points_bound_of E hHW;
  nlinarith only [ this, htotal_card, hbad_card, hLarge, Nat.sub_add_cancel ( show #bad ≤ #E.points from Finset.card_le_card <| Finset.filter_subset _ _ ), arith_bound D E.q #E.points hD this ]

/-! ## Main theorem -/

theorem bivariate_poly_zeros_on_ExE_le_thm (hHW : E.HasseBound)
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp [filter_empty_of_D_zero E f hDeg hNonzero]
  · by_cases h : E.points.card ≤ 3 * D
    · exact main_bound_small_points E f D hD h
    · exact main_bound_large_points E hHW f D hD hDeg hNonzero (by omega)

end Divisor.BivariateZerosOnExE

namespace Divisor

variable (E : ECSetup)

/-- **Bound on `|{(A₀, A₁) ∈ E × E : f(A₀, A₁) = 0}|`.**

    For a 4-variate polynomial `f ∈ F_q[X₀, Y₀, X₁, Y₁]` of total
    degree at most `D` that is **not identically zero on `E × E`**
    (witnessed by the existence of a point where it evaluates
    non-zero), the set of `F_q`-point pairs `(A₀, A₁) ∈ E × E` at
    which `f(A₀, A₁) = 0` has cardinality at most `9 · D · q`.

    Discharged by `BivariateZerosOnExE.bivariate_poly_zeros_on_ExE_le_thm`
    above (reduce mod `Y² = X³+AX+B` → `α(X) + β(X)·Y` → univariate
    norm-polynomial root count + the Hasse hypothesis's `2·|E| ≤ 3q+3`).
    Axiom-free: the Hasse point-count bound enters only through the
    explicit `hHW` hypothesis; use `bivariate_poly_zeros_on_ExE_le_hasse`
    to discharge it via the axiom. -/
theorem bivariate_poly_zeros_on_ExE_le (hHW : E.HasseBound)
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q :=
  BivariateZerosOnExE.bivariate_poly_zeros_on_ExE_le_thm E hHW f D hDeg hNonzero

/-- `bivariate_poly_zeros_on_ExE_le` with the Hasse hypothesis
discharged by the axiom (`hasse_weil_textbook`). -/
theorem bivariate_poly_zeros_on_ExE_le_hasse
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q :=
  bivariate_poly_zeros_on_ExE_le E (hasse_bound E) f D hDeg hNonzero

end Divisor
