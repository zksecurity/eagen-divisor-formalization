/-
  Divisor/DensityBound.lean

  Helper lemmas for the density bound in the polyG trace formula proof.
-/
import Divisor.PolyGDensity
import Divisor.DivisorPrincipal

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## ellP antisymmetry -/

theorem ellP_swap (P A₀ A₁ : ZMod E.q × ZMod E.q) :
    ellP E P A₁ A₀ = -(ellP E P A₀ A₁) := by
  unfold ellP; ring

/-! ## lineThrough evaluation -/

theorem lineThrough_eval_fst_eq_zero (A₀ A₁ : ZMod E.q × ZMod E.q) :
    (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval A₀.1 A₀.2 = 0 := by
  unfold lineThrough Line.eval slopeOf; ring

/-! ## (-1)^n is nonzero in ZMod q for prime q ≥ 5 -/

private theorem neg_one_ne_zero_zmod : (-1 : ZMod E.q) ≠ 0 := by
  intro h
  have h1 : (1 : ZMod E.q) ≠ 0 := by
    rw [Ne, ZMod.one_eq_zero_iff]
    exact Nat.Prime.one_lt E.hq_prime |>.ne'
  apply h1
  have : (-1 : ZMod E.q) + 1 = 0 + 1 := congr_arg (· + 1) h
  simp at this

private theorem neg_one_pow_ne_zero (n : ℕ) :
    (-1 : ZMod E.q) ^ n ≠ 0 :=
  pow_ne_zero n (neg_one_ne_zero_zmod E)

/-! ## Product swap lemma -/

private theorem prod_ellP_swap {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    ∏ i ∈ s, ellP E (f i) A₁ A₀ =
    (-1 : ZMod E.q) ^ s.card * ∏ i ∈ s, ellP E (f i) A₀ A₁ := by
  have : ∀ i ∈ s, ellP E (f i) A₁ A₀ = -(ellP E (f i) A₀ A₁) :=
    fun i _ => ellP_swap E _ _ _
  rw [Finset.prod_congr rfl this, Finset.prod_neg]

/-! ## polyG swap -/

/-- Swapping A₀ ↔ A₁ in `polyG` multiplies by `(-1)^(d + K − 1)`. -/
theorem polyG_swap {d K : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin K → ZMod E.q × ZMod E.q) (m : Fin K → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q β R m A₁ A₀ =
    (-1 : ZMod E.q) ^ (d + K - 1) * polyG E Q β R m A₀ A₁ := by
  unfold polyG
  have h_erase_card : ∀ (n : ℕ) (k : Fin n),
      (Finset.univ.erase k : Finset (Fin n)).card = n - 1 := by
    intro n k
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  -- Rewrite the first sum
  have hS1 : ∀ k : Fin d, k ∈ Finset.univ →
      β k * (∏ k' ∈ Finset.univ.erase k, ellP E (Q k') A₁ A₀) *
        (∏ j : Fin K, ellP E (R j) A₁ A₀) =
      β k * ((-1 : ZMod E.q) ^ (d - 1) * ∏ k' ∈ Finset.univ.erase k, ellP E (Q k') A₀ A₁) *
        ((-1 : ZMod E.q) ^ K * ∏ j : Fin K, ellP E (R j) A₀ A₁) := by
    intro k _
    rw [prod_ellP_swap E (Finset.univ.erase k) Q A₀ A₁, h_erase_card d k,
        prod_ellP_swap E Finset.univ R A₀ A₁, Finset.card_univ, Fintype.card_fin]
  -- Rewrite the second sum
  have hS2 : ∀ j : Fin K, j ∈ Finset.univ →
      m j * (∏ k : Fin d, ellP E (Q k) A₁ A₀) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R j') A₁ A₀) =
      m j * ((-1 : ZMod E.q) ^ d * ∏ k : Fin d, ellP E (Q k) A₀ A₁) *
        ((-1 : ZMod E.q) ^ (K - 1) * ∏ j' ∈ Finset.univ.erase j, ellP E (R j') A₀ A₁) := by
    intro j _
    rw [prod_ellP_swap E Finset.univ Q A₀ A₁, Finset.card_univ, Fintype.card_fin,
        prod_ellP_swap E (Finset.univ.erase j) R A₀ A₁, h_erase_card K j]
  rw [Finset.sum_congr rfl hS1, Finset.sum_congr rfl hS2]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by intro h; exact (h ▸ k).elim0)
    have hsign : (-1 : ZMod E.q) ^ (d - 1) * (-1 : ZMod E.q) ^ K =
        (-1 : ZMod E.q) ^ (d + K - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [← hsign]; ring
  · apply Finset.sum_congr rfl; intro j _
    have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by intro h; exact (h ▸ j).elim0)
    have hsign : (-1 : ZMod E.q) ^ d * (-1 : ZMod E.q) ^ (K - 1) =
        (-1 : ZMod E.q) ^ (d + K - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [← hsign]; ring

/-- If `polyG` vanishes with swapped arguments, it vanishes with the original. -/
theorem polyG_swap_zero {d K : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin K → ZMod E.q × ZMod E.q) (m : Fin K → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (h : polyG E Q β R m A₁ A₀ = 0) :
    polyG E Q β R m A₀ A₁ = 0 := by
  rw [polyG_swap E] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_one_pow_ne_zero E _)

end Divisor
