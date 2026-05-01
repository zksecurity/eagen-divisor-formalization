/-
  Divisor/FrobDescentHelpers.lean

  Pure algebra helpers for the Frobenius descent argument in
  GeometricSoundness.lean. These are stated over a general field to avoid
  importing project axioms.
-/
import Mathlib

open Polynomial Finset BigOperators

namespace Divisor.FrobDescentHelpers

variable {F : Type*} [Field F]

/--
If a partial-fraction sum `sum_i c_i / (mu - alpha_i)` with pairwise-distinct
poles vanishes at at least as many points as there are poles, and none of those
points is a pole, then every coefficient is zero.

The proof clears denominators, uses polynomial root counting, and evaluates the
cleared numerator at each pole to isolate the corresponding coefficient.
-/
theorem partial_fraction_coeff_zero
    {n : ℕ}
    (α : Fin n → F)
    (c : Fin n → F)
    (hInj : Function.Injective α)
    (S : Finset F)
    (hDisjoint : ∀ μ ∈ S, ∀ i, μ ≠ α i)
    (hCard : n ≤ S.card)
    (hVanish : ∀ μ ∈ S, ∑ i : Fin n, c i * (μ - α i)⁻¹ = 0) :
    ∀ i : Fin n, c i = 0 := by
  set N : Polynomial F :=
    ∑ i, Polynomial.C (c i) *
      ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))
  have hN_zero : N = 0 := by
    refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _
    exact S
    · simp
      refine' lt_of_le_of_lt (Polynomial.degree_sum_le _ _) (Finset.sup_lt_iff _ |>.2 _)
      · exact WithBot.bot_lt_coe _
      · intro i hi
        by_cases hi0 : c i = 0 <;> simp_all +decide [Polynomial.degree_prod]
        exact lt_of_lt_of_le (Nat.pred_lt (ne_bot_of_gt (Fin.pos i))) hCard
    · intro μ hμ
      have h_eval :
          N.eval μ = (∏ j, (μ - α j)) * (∑ i, c i * (μ - α i)⁻¹) := by
        simp +decide [N, Polynomial.eval_finset_sum, Polynomial.eval_prod,
          Finset.mul_sum _ _ _]
        exact Finset.sum_congr rfl fun i hi => by
          rw [← Finset.prod_erase_mul _ _ hi, mul_left_comm, mul_assoc,
            mul_inv_cancel₀ (sub_ne_zero_of_ne (hDisjoint μ hμ i)), mul_one]
      aesop
  intro i
  have h_eval : N.eval (α i) =
      c i * ∏ j ∈ Finset.univ.erase i, (α i - α j) := by
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i] <;>
      simp +contextual [Polynomial.eval_prod]
    exact fun j hj => Or.inr <|
      Finset.prod_eq_zero
        (Finset.mem_erase_of_ne_of_mem (Ne.symm hj) <| Finset.mem_univ _)
        <| sub_self _
  simp_all +decide [Finset.prod_eq_zero_iff, sub_eq_zero, hInj.eq_iff]

/-! ## Slope choice -/

/-- In `ZMod p`, any finset of size smaller than the whole space misses an element. -/
theorem ZMod_exists_not_mem
    {p : ℕ} [NeZero p] [Fintype (ZMod p)]
    (S : Finset (ZMod p)) (h : S.card < Fintype.card (ZMod p)) :
    ∃ x : ZMod p, x ∉ S := by
  by_contra hall
  push_neg at hall
  have hle : Fintype.card (ZMod p) ≤ S.card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (fun x _ => Finset.mem_coe.mp (hall x))
  omega

set_option maxHeartbeats 800000 in
/--
Abstract slope-choice lemma. Given `n` points `(x_i, y_i)` in a field over
`F_p`, a distinguished point that is not Frobenius-fixed, and `n < p`, choose
a base-field slope whose linear projection separates the distinguished point
from every other point and remains non-Frobenius-fixed.
-/
theorem exists_good_slope_abstract
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    {K : Type*} [Field K] [Algebra (ZMod p) K] [CharP K p]
    {n : ℕ}
    (x y : Fin n → K)
    (i₀ : Fin n)
    (hDistinct : ∀ j, j ≠ i₀ → (x j ≠ x i₀ ∨ y j ≠ y i₀))
    (hNF : (x i₀) ^ p ≠ x i₀ ∨ (y i₀) ^ p ≠ y i₀)
    (hBound : n < p) :
    ∃ lam : ZMod p,
      (∀ j, j ≠ i₀ →
        y j - algebraMap (ZMod p) K lam * x j ≠
        y i₀ - algebraMap (ZMod p) K lam * x i₀) ∧
      (y i₀ - algebraMap (ZMod p) K lam * x i₀) ^ p ≠
        y i₀ - algebraMap (ZMod p) K lam * x i₀ := by
  by_contra! h
  have h_bad_slopes :
      ∀ j : Fin n, j ≠ i₀ → ∃ Sj : Finset (ZMod p), Sj.card ≤ 1 ∧
        ∀ lam : ZMod p, lam ∉ Sj →
          y j - (algebraMap (ZMod p) K) lam * x j ≠
            y i₀ - (algebraMap (ZMod p) K) lam * x i₀ := by
    intro j hj
    by_cases hx : x j = x i₀
    · exact ⟨∅, by simp +decide, by specialize hDistinct j hj; aesop⟩
    · have h_eq : ∀ lam₁ lam₂ : ZMod p,
          y j - (algebraMap (ZMod p) K) lam₁ * x j =
              y i₀ - (algebraMap (ZMod p) K) lam₁ * x i₀ →
          y j - (algebraMap (ZMod p) K) lam₂ * x j =
              y i₀ - (algebraMap (ZMod p) K) lam₂ * x i₀ →
          lam₁ = lam₂ := by
        intro lam₁ lam₂ h₁ h₂
        have h_eq : (algebraMap (ZMod p) K) (lam₁ - lam₂) * (x j - x i₀) = 0 := by
          grind
        simp_all +decide [sub_eq_iff_eq_add]
      by_cases h : ∃ lam : ZMod p,
          y j - (algebraMap (ZMod p) K) lam * x j =
            y i₀ - (algebraMap (ZMod p) K) lam * x i₀
      · exact ⟨{h.choose}, by simp +decide, fun lam hl => fun hlam =>
          hl <| Finset.mem_singleton.mpr <| h_eq _ _ hlam h.choose_spec⟩
      · exact ⟨∅, by simp +decide, fun lam hl => fun hlam => h ⟨lam, hlam⟩⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (ZMod p), S.card ≤ n - 1 ∧
      ∀ lam : ZMod p, lam ∉ S → ∀ j : Fin n, j ≠ i₀ →
        y j - (algebraMap (ZMod p) K) lam * x j ≠
          y i₀ - (algebraMap (ZMod p) K) lam * x i₀ := by
    choose! S hS₁ hS₂ using h_bad_slopes
    refine' ⟨Finset.biUnion (Finset.univ.erase i₀) S, _, _⟩ <;>
      simp_all +decide
    exact le_trans (Finset.card_biUnion_le)
      (le_trans (Finset.sum_le_sum fun j hj => hS₁ j (Finset.ne_of_mem_erase hj))
        (by simp +decide [Finset.card_erase_of_mem (Finset.mem_univ i₀)]))
  have h_bad_slope_nf : ∃ T : Finset (ZMod p), T.card ≤ 1 ∧
      ∀ lam : ZMod p, lam ∉ T →
        (y i₀ - (algebraMap (ZMod p) K) lam * x i₀) ^ p ≠
          y i₀ - (algebraMap (ZMod p) K) lam * x i₀ := by
    by_cases hxi₀ : x i₀ ^ p = x i₀
    · simp_all +decide [sub_pow_char]
      refine' ⟨∅, _, _⟩ <;> simp_all +decide [mul_pow]
      intro lam
      rw [show (algebraMap (ZMod p) K) lam ^ p =
          (algebraMap (ZMod p) K) lam from by rw [← map_pow, ZMod.pow_card]]
      simp +decide [hNF]
    · obtain ⟨lam₀, hlam₀⟩ : ∃ lam₀ : ZMod p,
          (y i₀ - (algebraMap (ZMod p) K) lam₀ * x i₀) ^ p =
            y i₀ - (algebraMap (ZMod p) K) lam₀ * x i₀ := by
        obtain ⟨lam₀, hlam₀⟩ : ∃ lam₀ : ZMod p, lam₀ ∉ S := by
          exact not_forall.mp fun h => by
            have := Finset.eq_univ_of_forall h
            rw [this] at hS
            norm_num at hS
            linarith [Nat.sub_add_cancel (show 1 ≤ n from Fin.pos i₀)]
        exact ⟨lam₀, h lam₀ fun j hj => hS.2 lam₀ hlam₀ j hj⟩
      refine' ⟨{lam₀}, _, _⟩ <;> simp +decide
      intro lam hlam hlam'
      have := hlam₀
      simp_all +decide [sub_eq_iff_eq_add]
      simp_all +decide [sub_pow_char, mul_pow]
      simp_all +decide [sub_eq_iff_eq_add]
      simp_all +decide
        [show (algebraMap (ZMod p) K) lam ^ p =
            (algebraMap (ZMod p) K) lam from by rw [← map_pow, ZMod.pow_card],
          show (algebraMap (ZMod p) K) lam₀ ^ p =
            (algebraMap (ZMod p) K) lam₀ from by rw [← map_pow, ZMod.pow_card]]
      exact hlam (by
        simpa [sub_eq_iff_eq_add, hxi₀] using
          (algebraMap (ZMod p) K).injective
            (mul_left_cancel₀ (sub_ne_zero_of_ne hxi₀) <| by linear_combination' this))
  obtain ⟨T, hT₁, hT₂⟩ := h_bad_slope_nf
  have h_total_bad_slopes : (S ∪ T).card ≤ n := by
    exact le_trans (Finset.card_union_le _ _)
      (by linarith [Nat.sub_add_cancel (show 1 ≤ n from Fin.pos i₀)])
  obtain ⟨lam, hlam⟩ : ∃ lam : ZMod p, lam ∉ S ∪ T := by
    exact not_forall.mp fun h => by
      have := Finset.eq_univ_of_forall h
      rw [this] at h_total_bad_slopes
      simp +decide [Finset.card_univ] at h_total_bad_slopes
      linarith
  exact hT₂ lam (Finset.notMem_mono (Finset.subset_union_right) hlam)
    (h lam fun j hj => hS.2 lam
      (Finset.notMem_mono (Finset.subset_union_left) hlam) j hj)

/-!
## Two-family partial fractions

The Frobenius descent branch produces a partial-fraction identity with
one family of poles from the geometric support and one auxiliary family
from rational protocol points.  The lemma below isolates the coefficient
of a pole that appears in only the first family.
-/

set_option maxHeartbeats 800000 in
/--
If a two-part partial-fraction sum vanishes at enough evaluation points,
and one pole `α i₀` is isolated from all other poles in both families,
then the corresponding coefficient `c i₀` is zero.

The proof clears all denominators, obtains a polynomial of degree
`< n + m`, shows it is zero by root counting, and evaluates it at the
isolated pole.
-/
theorem isolated_coeff_zero_of_pf_sum
    {n m : ℕ}
    (α : Fin n → F) (c : Fin n → F)
    (β : Fin m → F) (d : Fin m → F)
    (i₀ : Fin n)
    (hIsolatedα : ∀ j : Fin n, j ≠ i₀ → α j ≠ α i₀)
    (hIsolatedβ : ∀ j : Fin m, β j ≠ α i₀)
    (S : Finset F)
    (hCard : n + m ≤ S.card)
    (hDisjointα : ∀ μ ∈ S, ∀ i : Fin n, μ ≠ α i)
    (hDisjointβ : ∀ μ ∈ S, ∀ j : Fin m, μ ≠ β j)
    (hVanish : ∀ μ ∈ S,
      (∑ i, c i * (μ - α i)⁻¹) + (∑ j, d j * (μ - β j)⁻¹) = 0) :
    c i₀ = 0 := by
  set N : Polynomial F :=
    ∑ i, Polynomial.C (c i) *
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))) *
      (∏ j, (Polynomial.X - Polynomial.C (β j))) +
    ∑ i, Polynomial.C (d i) *
      (∏ j, (Polynomial.X - Polynomial.C (α j))) *
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (β j)))
  have hN_zero : N = 0 := by
    have hN_roots : ∀ μ ∈ S, N.eval μ = 0 := by
      intro μ hμ
      have hNμ : N.eval μ =
          (∏ i, (μ - α i)) * (∏ j, (μ - β j)) *
            ((∑ i, c i * (μ - α i)⁻¹) +
              ∑ j, d j * (μ - β j)⁻¹) := by
        simp +decide [N, Polynomial.eval_finset_sum, Polynomial.eval_prod,
          mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _]
        simp +decide [Finset.mul_sum _ _ _, mul_assoc, mul_left_comm,
          Finset.sum_mul]
        congr! 2
        · simp +decide [← mul_assoc,
            ← Finset.prod_erase_mul _ _ (Finset.mem_univ ‹_›)]
          grind +qlia
        · simp +decide [← mul_assoc,
            ← Finset.prod_erase_mul _ _ (Finset.mem_univ ‹_›)]
          grind +revert
      rw [hNμ, hVanish μ hμ, MulZeroClass.mul_zero]
    have hN_deg : N.degree < n + m := by
      refine' lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt _ _)
      · refine' lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
          (Finset.sup_lt_iff _ |>.2 _)
        · exact WithBot.bot_lt_coe _
        · intro i hi
          by_cases hi' : c i = 0 <;> simp +decide [hi', Polynomial.degree_prod]
          exact_mod_cast Nat.add_lt_add_right
            (Nat.pred_lt (ne_bot_of_gt (Fin.pos i))) m
      · refine' lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
          (Finset.sup_lt_iff _ |>.2 _)
        · exact WithBot.bot_lt_coe _
        · intro i hi
          by_cases hi' : d i = 0 <;> simp +decide [hi', Polynomial.degree_prod]
          exact_mod_cast Nat.add_lt_add_left
            (Nat.pred_lt (ne_bot_of_gt (Fin.pos i))) n
    refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _
    exact S
    · simpa using hN_deg.trans_le (mod_cast hCard)
    · aesop
  have hN_eval : N.eval (α i₀) =
      c i₀ * (∏ j ∈ Finset.erase Finset.univ i₀, (α i₀ - α j)) *
        (∏ j, (α i₀ - β j)) := by
    simp +zetaDelta at *
    rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_zero] <;>
      simp +contextual [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, *]
    exact fun j hj => Or.inl <| Or.inr ⟨i₀, Ne.symm hj, rfl⟩
  simp_all +decide [Finset.prod_eq_zero_iff, sub_eq_zero]
  grind

end Divisor.FrobDescentHelpers
