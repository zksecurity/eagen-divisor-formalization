/-
  Divisor/CurveEvalZerosHelper.lean

  Helper lemmas for bounding the number of zeros of a bivariate
  polynomial on an elliptic curve E(F_q).
-/
import Divisor.DefsPre
import Mathlib

namespace Divisor.CurveEvalZeros

open Polynomial Finset MvPolynomial Divisor

variable (E : ECSetup)

/-! ## Curve polynomial -/

noncomputable def curvePoly : Polynomial (ZMod E.q) :=
  Polynomial.X ^ 3 + Polynomial.C E.curveA * Polynomial.X + Polynomial.C E.curveB

@[simp]
lemma curvePoly_eval (x : ZMod E.q) :
    (curvePoly E).eval x = x ^ 3 + E.curveA * x + E.curveB := by
  simp [curvePoly]

/-! ## Reduction modulo the curve equation -/

noncomputable def alphaPoly (g : MvPolynomial (Fin 2) (ZMod E.q)) : Polynomial (ZMod E.q) :=
  ∑ m ∈ g.support.filter (fun m => Even (m 1)),
    Polynomial.C (g.coeff m) * Polynomial.X ^ (m 0) * curvePoly E ^ (m 1 / 2)

noncomputable def betaPoly (g : MvPolynomial (Fin 2) (ZMod E.q)) : Polynomial (ZMod E.q) :=
  ∑ m ∈ g.support.filter (fun m => ¬Even (m 1)),
    Polynomial.C (g.coeff m) * Polynomial.X ^ (m 0) * curvePoly E ^ ((m 1 - 1) / 2)

/-! ## Key properties -/

/-
On E, y^(2k) = (y²)^k = c(x)^k and y^(2k+1) = y·c(x)^k, so
    g(x,y) = Σ_{even} coeff·x^a·c(x)^(b/2) + y·Σ_{odd} coeff·x^a·c(x)^((b-1)/2)
           = α(x) + β(x)·y.
-/
lemma eval_eq_alpha_beta (g : MvPolynomial (Fin 2) (ZMod E.q))
    (x y : ZMod E.q) (hy : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) g =
    (alphaPoly E g).eval x + (betaPoly E g).eval x * y := by
  simp +decide [ MvPolynomial.eval_eq', alphaPoly, betaPoly ];
  simp +decide [ Polynomial.eval_finset_sum, Finset.sum_filter ];
  rw [ Finset.sum_mul _ _ _ ];
  rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rcases Nat.even_or_odd' ( i 1 ) with ⟨ k, hk | hk ⟩ <;> simp +decide [ hk, pow_add, pow_mul, hy ] ; ring;
  · norm_num [ Nat.even_iff, Nat.odd_iff, Nat.mul_mod ];
  · ring

/-
If g doesn't vanish identically on E, then α ≠ 0 or β ≠ 0.
-/
lemma not_both_zero (g : MvPolynomial (Fin 2) (ZMod E.q))
    (hNZ : ∃ P ∈ E.points, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g ≠ 0) :
    alphaPoly E g ≠ 0 ∨ betaPoly E g ≠ 0 := by
  contrapose! hNZ;
  exact fun p hp => by simpa [ hNZ ] using eval_eq_alpha_beta E g p.1 p.2 ( E.hOnCurve p hp ) ;

/-
Degree bound: max(2·natDegree α, 3+2·natDegree β) ≤ 3d when d ≥ 1 and totalDegree g ≤ d.
-/
lemma degE_bound (g : MvPolynomial (Fin 2) (ZMod E.q)) (d : ℕ) (hd : d ≥ 1)
    (hDeg : g.totalDegree ≤ d) :
    max (2 * (alphaPoly E g).natDegree) (3 + 2 * (betaPoly E g).natDegree) ≤ 3 * d := by
  refine' max_le _ _;
  · -- Each summand in alphaPoly has degree at most 3d/2.
    have h_alpha_deg : ∀ m ∈ g.support.filter (fun m => Even (m 1)), Polynomial.natDegree (Polynomial.C (g.coeff m) * Polynomial.X ^ (m 0) * curvePoly E ^ (m 1 / 2)) ≤ 3 * d / 2 := by
      intro m hm
      have h_m_deg : m 0 + m 1 ≤ d := by
        simp_all +decide [ MvPolynomial.totalDegree ];
        simpa [ Finsupp.sum_fintype ] using hDeg m hm.1;
      refine' le_trans ( Polynomial.natDegree_mul_le .. ) _;
      refine' le_trans ( add_le_add ( Polynomial.natDegree_C_mul_X_pow_le _ _ ) ( Polynomial.natDegree_pow_le ) ) _;
      erw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
      · grind;
      · by_cases h : E.curveA = 0 <;> simp +decide [ h ];
    refine' le_trans ( Nat.mul_le_mul_left 2 ( Polynomial.natDegree_sum_le _ _ |> le_trans <| Finset.sup_le _ ) ) _;
    exacts [ 3 * d / 2, h_alpha_deg, by linarith [ Nat.div_mul_le_self ( 3 * d ) 2 ] ];
  · -- For the beta bound: 3 + 2*(3*d-3)/2 ≤ 3 + (3*d-3) = 3*d.
    have h_beta_bound : ∀ m ∈ g.support.filter (fun m => ¬Even (m 1)), (m 0 + 3 * ((m 1 - 1) / 2)) ≤ (3 * d - 3) / 2 := by
      intro m hm
      have h_m_deg : m 0 + m 1 ≤ d := by
        simp_all +decide [ MvPolynomial.totalDegree ];
        simpa [ Finsupp.sum_fintype ] using hDeg m hm.1;
      grind;
    -- Apply the bound on the degree of each term in the sum to conclude the bound on the degree of the sum.
    have h_beta_deg_sum : (betaPoly E g).natDegree ≤ (3 * d - 3) / 2 := by
      refine' le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le _ );
      intro m hm; specialize h_beta_bound m hm; by_cases h : MvPolynomial.coeff m g = 0 <;> simp_all +decide ;
      refine' le_trans ( Polynomial.natDegree_mul_le .. ) _ ; simp_all +decide [ Polynomial.natDegree_mul' ];
      erw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
      · linarith;
      · by_cases h : E.curveA = 0 <;> simp +decide [ h ];
    omega

/-! ## Zero counting -/

/-
Number of zeros of a non-trivial CoordRingElt on E ≤ degE.
    Proved via norm polynomial root counting.
    D.eval x y = D.a.eval x - D.b.eval x * y.
    On E, the norm N(x) = D.a(x)² - D.b(x)²·c(x) satisfies:
    • Every zero of D on E has N(x) = 0.
    • N ≠ 0 (since degE ≠ 0 implies one of a, b is nonzero, and
      the leading terms of a² and b²·c can't cancel by degree parity).
    • deg N ≤ degE.
    Use multiplicity: at each common root of a and b,
    (X-x₀)² | N, while the point contributes ≤ 2 zeros.
    At roots of N with b(x₀) ≠ 0, y is unique, contributing ≤ 1 zero.
    So Σ n(x) ≤ Σ rootMultiplicity(x, N) = N.roots.card ≤ deg N ≤ degE.
-/
lemma zeros_card_le_degE (D : CoordRingElt E.q) (hDnz : ¬(D.a = 0 ∧ D.b = 0)) :
    (E.points.filter (fun p => D.eval p.1 p.2 = 0)).card ≤ D.degE := by
  revert hDnz;
  intro hDnz
  set N := D.a^2 - D.b^2 * curvePoly E with hN_def
  have hN_nonzero : N ≠ 0 := by
    by_cases hD_a_zero : D.a = 0 <;> by_cases hD_b_zero : D.b = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · exact ne_of_apply_ne ( fun p => p.coeff 3 ) ( by norm_num [ curvePoly ] );
    · intro h_eq
      have h_deg : 2 * D.a.natDegree = 3 + 2 * D.b.natDegree := by
        apply_fun Polynomial.natDegree at h_eq;
        rw [ Polynomial.natDegree_mul' ] at h_eq <;> simp_all +decide [ Polynomial.natDegree_pow ];
        · unfold curvePoly; erw [ Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num; ring;
          by_cases h : E.curveA = 0 <;> simp +decide [ h ];
        · exact ne_of_apply_ne ( fun p => p.coeff 3 ) ( by simp +decide [ curvePoly ] );
      omega
  have hN_deg : N.natDegree ≤ D.degE := by
    refine' le_trans ( Polynomial.natDegree_sub_le _ _ ) _;
    refine' max_le _ _;
    · simp +decide [ CoordRingElt.degE ];
    · refine' le_trans ( Polynomial.natDegree_mul_le .. ) _ ; norm_num [ curvePoly ];
      rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases h : E.curveA = 0 <;> simp +decide [ h ];
      · exact le_max_of_le_right ( by linarith );
      · exact le_max_of_le_right ( by linarith );
  -- For each x₀ with N(x₀) = 0:
  -- - If D.b(x₀) ≠ 0: y = D.a(x₀)/D.b(x₀) is unique, at most 1 zero on E above x₀.
  -- - If D.b(x₀) = 0: then D.a(x₀)² = 0, so D.a(x₀) = 0. All ≤ 2 points on E above x₀ are zeros.
  -- AND: (X-x₀)|D.a and (X-x₀)|D.b, so (X-x₀)²|D.a² and (X-x₀)²|D.b²·c, hence (X-x₀)²|N.
  -- So rootMultiplicity(x₀, N) ≥ 2.
  have h_root_multiplicity : ∀ x₀ : ZMod E.q, N.eval x₀ = 0 → (Finset.filter (fun p => p.1 = x₀ ∧ D.eval p.1 p.2 = 0) E.points).card ≤ (Polynomial.rootMultiplicity x₀ N) := by
    intro x₀ hx₀
    by_cases hD_b_x₀ : D.b.eval x₀ = 0;
    · have h_root_multiplicity_ge_two : (Polynomial.rootMultiplicity x₀ N) ≥ 2 := by
        have h_root_multiplicity_ge_two : (Polynomial.X - Polynomial.C x₀)^2 ∣ N := by
          have h_root_multiplicity_ge_two : (Polynomial.X - Polynomial.C x₀) ∣ D.a ∧ (Polynomial.X - Polynomial.C x₀) ∣ D.b := by
            simp_all +decide [ Polynomial.dvd_iff_isRoot ];
          exact dvd_sub ( pow_dvd_pow_of_dvd h_root_multiplicity_ge_two.1 2 ) ( dvd_mul_of_dvd_left ( pow_dvd_pow_of_dvd h_root_multiplicity_ge_two.2 2 ) _ );
        exact (Polynomial.le_rootMultiplicity_iff hN_nonzero).mpr h_root_multiplicity_ge_two;
      refine' le_trans _ h_root_multiplicity_ge_two;
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun y => ( x₀, y ) ) ( Finset.filter ( fun y => y ^ 2 = x₀ ^ 3 + E.curveA * x₀ + E.curveB ) ( Finset.univ : Finset ( ZMod E.q ) ) );
      · simp +contextual [ Finset.subset_iff ];
        exact fun a b hab ha hb => by simpa [ ha ] using E.hOnCurve ( a, b ) hab;
      · refine' le_trans ( Finset.card_image_le ) _;
        haveI := Fact.mk E.hq_prime; exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun y => y ^ 2 = x₀ ^ 3 + E.curveA * x₀ + E.curveB ) Finset.univ ⊆ ( Polynomial.roots ( Polynomial.X ^ 2 - Polynomial.C ( x₀ ^ 3 + E.curveA * x₀ + E.curveB ) ) |> Multiset.toFinset ) from fun y hy => Multiset.mem_toFinset.mpr <| Polynomial.mem_roots ( show Polynomial.X ^ 2 - Polynomial.C ( x₀ ^ 3 + E.curveA * x₀ + E.curveB ) ≠ 0 from Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) |>.2 <| by aesop ) ) <| le_trans ( Multiset.toFinset_card_le _ ) <| le_trans ( Polynomial.card_roots' _ ) <| by erw [ Polynomial.natDegree_X_pow_sub_C ] ;
    · -- If D.b(x₀) ≠ 0, then y = D.a(x₀)/D.b(x₀) is unique, at most 1 zero on E above x₀.
      have h_unique_y : ∀ p ∈ E.points, p.1 = x₀ → D.eval p.1 p.2 = 0 → p.2 = D.a.eval x₀ / D.b.eval x₀ := by
        simp_all +decide [ sub_eq_iff_eq_add, CoordRingElt.eval ];
      refine' le_trans ( Finset.card_le_one.mpr _ ) _;
      · grind +qlia;
      · exact Nat.pos_of_ne_zero ( by aesop );
  -- Sum of zeros ≤ sum of rootMultiplicity over roots = N.roots.card ≤ N.natDegree ≤ D.degE.
  have h_sum_zeros : (Finset.filter (fun p => D.eval p.1 p.2 = 0) E.points).card ≤ Multiset.card (Polynomial.roots N) := by
    have h_sum_zeros : (Finset.filter (fun p => D.eval p.1 p.2 = 0) E.points).card ≤ Finset.sum (N.roots.toFinset) (fun x₀ => (Finset.filter (fun p => p.1 = x₀ ∧ D.eval p.1 p.2 = 0) E.points).card) := by
      have h_sum_multiplicity : (Finset.filter (fun p => D.eval p.1 p.2 = 0) E.points) ⊆ Finset.biUnion N.roots.toFinset (fun x₀ => Finset.filter (fun p => p.1 = x₀ ∧ D.eval p.1 p.2 = 0) E.points) := by
        intro p hp; simp_all +decide ;
        have := E.hOnCurve p hp.1; simp_all +decide [ CoordRingElt.eval ] ;
        rw [ ← this ] ; linear_combination' hp.2 * ( Polynomial.eval p.1 D.a + Polynomial.eval p.1 D.b * p.2 ) ;
      exact le_trans ( Finset.card_le_card h_sum_multiplicity ) ( Finset.card_biUnion_le );
    refine le_trans h_sum_zeros <| le_trans ( Finset.sum_le_sum fun x hx => h_root_multiplicity x <| by aesop ) ?_;
    rw [ ← Multiset.toFinset_sum_count_eq ];
    simp +decide;
  exact h_sum_zeros.trans ( le_trans ( Polynomial.card_roots' _ ) hN_deg )

/-! ## Main result -/

noncomputable def toCoordRingElt (g : MvPolynomial (Fin 2) (ZMod E.q)) : CoordRingElt E.q :=
  { a := alphaPoly E g, b := -(betaPoly E g) }

lemma toCoordRingElt_eval_eq (g : MvPolynomial (Fin 2) (ZMod E.q))
    (x y : ZMod E.q) (hy : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB) :
    (toCoordRingElt E g).eval x y =
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y) g := by
  simp only [toCoordRingElt, CoordRingElt.eval, Polynomial.eval_neg, neg_mul, sub_neg_eq_add]
  exact (eval_eq_alpha_beta E g x y hy).symm

lemma toCoordRingElt_not_zero (g : MvPolynomial (Fin 2) (ZMod E.q))
    (hNZ : ∃ P ∈ E.points, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g ≠ 0) :
    ¬((toCoordRingElt E g).a = 0 ∧ (toCoordRingElt E g).b = 0) := by
  simp only [toCoordRingElt, neg_eq_zero]
  intro ⟨ha, hb⟩
  have h := not_both_zero E g hNZ
  simp [ha, hb] at h

lemma toCoordRingElt_degE_le (g : MvPolynomial (Fin 2) (ZMod E.q)) (d : ℕ) (hd : d ≥ 1)
    (hDeg : g.totalDegree ≤ d) :
    (toCoordRingElt E g).degE ≤ 3 * d := by
  unfold CoordRingElt.degE toCoordRingElt
  simp only [Polynomial.natDegree_neg]
  exact degE_bound E g d hd hDeg

/-- Main: zeros of g on E ≤ 3d, for d ≥ 1. -/
lemma curve_eval_zeros_le_pos
    (g : MvPolynomial (Fin 2) (ZMod E.q)) (d : ℕ) (hd : d ≥ 1)
    (hDeg : g.totalDegree ≤ d)
    (hNZ : ∃ P ∈ E.points, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g ≠ 0) :
    (E.points.filter (fun P =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g = 0)).card ≤ 3 * d := by
  set D := toCoordRingElt E g
  have hDnz := toCoordRingElt_not_zero E g hNZ
  have hDeg_le := toCoordRingElt_degE_le E g d hd hDeg
  have hfilter : (E.points.filter (fun P =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g = 0)) =
      (E.points.filter (fun p => D.eval p.1 p.2 = 0)) := by
    ext P; simp only [Finset.mem_filter]
    constructor
    · intro ⟨hP, hg⟩
      refine ⟨hP, ?_⟩
      have := toCoordRingElt_eval_eq E g P.1 P.2 (E.hOnCurve P hP)
      rw [this]; exact hg
    · intro ⟨hP, hD_eval⟩
      refine ⟨hP, ?_⟩
      have := toCoordRingElt_eval_eq E g P.1 P.2 (E.hOnCurve P hP)
      rw [← this]; exact hD_eval
  rw [hfilter]
  exact le_trans (zeros_card_le_degE E D hDnz) hDeg_le

/-
For d = 0 with g nonvanishing on E, there are 0 zeros.
-/
lemma curve_eval_zeros_le_zero
    (g : MvPolynomial (Fin 2) (ZMod E.q))
    (hDeg : g.totalDegree ≤ 0)
    (hNZ : ∃ P ∈ E.points, MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g ≠ 0) :
    (E.points.filter (fun P =>
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then P.1 else P.2) g = 0)).card ≤ 0 := by
  -- Since g is a constant polynomial, write g = C c.
  obtain ⟨c, hc⟩ : ∃ c : ZMod E.q, g = MvPolynomial.C c := by
    use g.coeff 0; ext1 i; by_cases hi : i = 0 <;> simp_all +decide [ MvPolynomial.coeff_C ] ;
    rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ] ; aesop;
    exact hDeg.symm ▸ Finset.sum_pos ( fun x hx => Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hx ) ) ( by contrapose! hi; aesop );
  aesop

end Divisor.CurveEvalZeros
