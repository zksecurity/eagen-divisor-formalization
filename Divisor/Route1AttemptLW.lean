/-
  Divisor/Route1AttemptLW.lean

  Lang-Weil-led variant of `Route1Attempt.lean`. Same target theorem,
  same Lean statement; only the proof sketch leads with Lang-Weil 1954
  Theorem 1 instead of DKL'14 Claim 7.2.
-/
import Divisor.FourVarPoly
import Divisor.Axioms.AxiomHasseWeil
import Divisor.CurveEvalZerosHelper
import Mathlib

namespace Divisor.Route1LW

open MvPolynomial Finset

variable (E : ECSetup)

/-! ## Helper lemmas -/

/-- Each x ∈ ZMod q has at most 2 curve points. -/
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
    refine Finset.sum_eq_zero fun m hm => ?_ ; simp_all +decide [ MvPolynomial.coeff_C, MvPolynomial.coeff_X_pow, mul_assoc ]
    rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ]
    refine' lt_of_le_of_lt _ hb
    refine' le_trans _ ( h_total_degree_le m hm )
    refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _
    refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_pow _ _ ) ( MvPolynomial.totalDegree_mul _ _ ) ) _ ; norm_num
    refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_pow _ _ ) ( MvPolynomial.totalDegree_mul _ _ ) ) _ ; norm_num
  · unfold specialize_first; simp +decide [ MvPolynomial.eval₂_eq' ]
    exact Finset.sum_congr rfl fun _ _ => by rw [ Fin.prod_univ_four ] ; simp +decide [ mul_assoc, Algebra.smul_def ]

lemma specialize_second_totalDegree (f : FourVarPoly E.q) (A₁ : ZMod E.q × ZMod E.q) (D : ℕ)
    (hDeg : total_degree_le E f D) :
    (specialize_second E f A₁).totalDegree ≤ D := by
  by_contra hC;
  convert specialize_first_totalDegree _ _ _ _ using 1;
  rotate_left;
  exact ⟨ E.q, E.hq_prime, E.curveA, E.curveB, E.points, E.hOnCurve, E.hComplete, E.numPoints, E.hNumPoints, E.hq_ge ⟩;
  exact MvPolynomial.rename ( fun i => if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1 ) f;
  exact A₁;
  exact D;
  simp +decide [ total_degree_le ] at *;
  refine' ⟨ _, _ ⟩;
  · refine' le_trans _ hDeg;
    exact?;
  · convert hC using 1;
    unfold specialize_first specialize_second;
    rw [ MvPolynomial.eval₂_rename ];
    congr! 2;
    exact funext fun i => by fin_cases i <;> rfl;

/-- Bézout bound for zeros of a bivariate polynomial on E.
    A polynomial of total degree ≤ d with a nonzero point on E
    has at most 3d zeros on E(F_q).

PROVIDED SOLUTION

This is **Bezout's theorem for plane curves** specialised to the
Weierstrass cubic: a curve of degree `d` (the variety `g = 0`)
intersected with a curve of degree `3` (the elliptic curve E,
defined by `Y² = X³ + AX + B`) has at most `3·d` intersection points,
provided neither curve contains the other. The hypothesis `hNZ`
rules out `E ⊂ {g = 0}`.

**Concrete proof outline (without Bezout in Mathlib):**

1. Reduce `g` modulo the curve relation `Y² ≡ X³ + AX + B`. Repeated
   substitution sends `Y^j` to a polynomial in `(X, Y)` of bidegree
   `(3·⌊j/2⌋ + 0_or_3, j mod 2)`. After full reduction:
   `g ≡ α(X) + β(X)·Y` for some univariate `α, β ∈ F_q[X]` with
   `deg α, deg β ≤ ⌈3d/2⌉ ≤ 2d` (loose bound).

2. On `E(F_q)`, `g(P) = 0` iff `α(P.1) + β(P.1)·P.2 = 0`.

3. Count by `x`-coordinate. For each `x ∈ F_q`, define
   `n(x) := #{ P ∈ E.points : P.1 = x ∧ α(x) + β(x)·P.2 = 0 }`.
   - If `β(x) = 0`: contributes only when `α(x) = 0`, in which case
     all (≤ 2) lifts of `x` to E satisfy the equation. So `n(x) ≤ 2`
     when `α(x) = β(x) = 0`, else `n(x) = 0`.
   - If `β(x) ≠ 0`: `P.2 = -α(x)/β(x)` is forced; at most one lift
     of `x` to E has this `y`-coordinate. So `n(x) ≤ 1`.

4. Bound the totals:
   - `# bad x` (where `α(x) = β(x) = 0`) is at most
     `min(deg α, deg β) ≤ ⌈3d/2⌉` by univariate Schwartz–Zippel
     (`Polynomial.card_roots_le_degree`).
   - `# good x with α(x) + β(x)·y = 0 for some y on E`: x is a root
     of the univariate polynomial obtained by substituting
     `y = -α/β` and clearing denominators, namely
     `α(X)² - β(X)²·(X³ + A·X + B)`, of degree at most `3d + 3`.

5. Stitching: total ≤ `2·⌈3d/2⌉ + (3d + 3) ≤ 6d + 3` — too loose for
   the 3d bound. The cleaner argument uses Bezout directly: the
   intersection number on `P²` of degree-3 and degree-d curves is
   exactly `3d` (Hartshorne I.7.7).

If a `3d` bound proves intractable, a looser bound such as `12·d`
or `O(d)` also works for the downstream theorem (it would only
worsen the leading constant from `9 D q` to a larger multiple of
`D q` in `bivariate_poly_zeros_on_ExE_le_thm_lw` proportionally).
However, the existing scaffolding in this file relies on the exact
constant `3d`. A creative use of the project's divisor machinery in
`Divisor/Defs.lean` and `Divisor/DivisorPrincipal.lean` (where
divisors of `CoordRingElt` on `E` have a notion of degree) may
yield the clean `3d` bound.
-/
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
  convert h using 3
  ext; rw [specialize_first_eval]

/-
Fibre count bound for fixed second coordinate.
-/
lemma fiber_count_le_second (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (A₁ : ZMod E.q × ZMod E.q) (_hA₁ : A₁ ∈ E.points)
    (hFiberNZ : ∃ A₀ ∈ E.points, bivEval₂ f A₀ A₁ ≠ 0) :
    (E.points.filter (fun A₀ => bivEval₂ f A₀ A₁ = 0)).card ≤ 3 * D := by
  convert curve_eval_zeros_le _ _ _ _ using 1;
  rotate_left;
  exact E;
  exact specialize_second E f A₁;
  exact D;
  · exact?;
  · simp_all +decide [ specialize_second_eval ]

/-- From Hasse-Weil: 2 * E.points.card ≤ 3 * E.q + 3. -/
lemma hasse_points_bound : 2 * E.points.card ≤ 3 * E.q + 3 := by
  have hw := Divisor.hasse_weil E
  have hnum := E.hNumPoints
  have hqge := E.hq_ge
  -- Let m = numPoints - q - 1 (as integer)
  set m := (E.numPoints : ℤ) - E.q - 1 with hm_def
  -- From Hasse: m^2 ≤ 4q
  have hm_sq : m ^ 2 ≤ 4 * (E.q : ℤ) := hw
  -- Need: 2 * points.card ≤ 3*q + 3
  -- points.card = numPoints - 1 = q + 1 + m - 1 = q + m
  -- So need: 2*(q+m) ≤ 3q+3, i.e., 2m ≤ q+3
  have h2m : 2 * m ≤ (E.q : ℤ) + 3 := hasse_int_bound E.q m hqge hm_sq
  omega

lemma arith_bound (D q n : ℕ) (hD : D ≥ 1) (hn : 2 * n ≤ 3 * q + 3) :
    6 * D * n ≤ 9 * D * q + 9 * D * D := by
  nlinarith

/-
For D = 0 and constant nonzero f, the filter is empty.
-/
lemma filter_empty_of_D_zero
    (f : FourVarPoly E.q) (hDeg : total_degree_le E f 0)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card = 0 := by
  -- Since $f$ is a constant polynomial, we have $f = C c$ for some $c \in \mathbb{F}_q$.
  obtain ⟨c, hc⟩ : ∃ c : ZMod E.q, f = C c := by
    exact?;
  simp_all +decide [ bivEval₂_C ]

/-
Case when |E.points| ≤ 3D: use trivial bound.
-/
lemma main_bound_small_points
    (f : FourVarPoly E.q) (D : ℕ) (hD : D ≥ 1)
    (hSmall : E.points.card ≤ 3 * D) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q := by
  refine' le_trans ( Finset.card_filter_le _ _ ) _;
  rw [ Finset.card_product ];
  nlinarith [ points_card_le_two_mul_q E ]

/-
Case when |E.points| > 3D: use fiber decomposition + bad fiber bound.
-/
lemma main_bound_large_points
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
  -- For good A₀ (A₀ ∈ E.points \ bad): exists A₁ with f ≠ 0, so fiber.card ≤ 3D.
  have hgood_card : ∀ A₀ ∈ E.points \ bad, (E.points.filter (fun A₁ => bivEval₂ f A₀ A₁ = 0)).card ≤ 3 * D := by
    simp +zetaDelta at *;
    exact fun a b ha hb => fiber_count_le E f D hDeg ( a, b ) ha <| by obtain ⟨ x, y, hx, hy ⟩ := hb ha; exact ⟨ ( x, y ), hx, hy ⟩ ;
  -- Therefore, the total number of zeros is at most bad.card * E.points.card + (E.points.card - bad.card) * 3D.
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
  have := hasse_points_bound E;
  nlinarith only [ this, htotal_card, hbad_card, hLarge, Nat.sub_add_cancel ( show #bad ≤ #E.points from Finset.card_le_card <| Finset.filter_subset _ _ ), arith_bound D E.q #E.points hD this ]

/-! ## Main theorem -/

theorem bivariate_poly_zeros_on_ExE_le_thm_lw
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
    · exact main_bound_large_points E f D hD hDeg hNonzero (by omega)

end Divisor.Route1LW