/-
  Divisor/Defs.lean — Core definitions

  Group law on `ECPoint E` is supplied by mathlib's
  `WeierstrassCurve.Affine.Point` (see `DefsPre.lean`). This file adds:
  * `weightedSum` — `Finset`-indexed sum over `ECPoint E`, an
    abbreviation for `Finset.sum` (mathlib's `AddCommGroup` instance).
  * Derived group-law lemmas used downstream.
-/
import Divisor.DefsPre
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Polynomial WeierstrassCurve

namespace Divisor

variable (E : ECSetup)

/-! ## Group-sum on `ECPoint E` -/

/-- Group-sum of a family of `(coefficient, point)` weighted terms over
    a `Finset`. Inherits all the usual `Finset.sum` lemmas (insert,
    congr, subset, image, etc.) from mathlib. -/
noncomputable abbrev ECPoint.weightedSum (E : ECSetup) {α : Type*}
    (s : Finset α) (f : α → ECPoint E) : ECPoint E :=
  ∑ a ∈ s, f a

@[simp] theorem ECPoint.weightedSum_empty (E : ECSetup) {α : Type*}
    (f : α → ECPoint E) : ECPoint.weightedSum E (∅ : Finset α) f = 0 :=
  Finset.sum_empty

theorem ECPoint.weightedSum_insert (E : ECSetup) {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) (f : α → ECPoint E) :
    ECPoint.weightedSum E (insert a s) f = f a + ECPoint.weightedSum E s f :=
  Finset.sum_insert ha

theorem ECPoint.weightedSum_congr (E : ECSetup) {α : Type*}
    {s : Finset α} {f g : α → ECPoint E}
    (h : ∀ a ∈ s, f a = g a) :
    ECPoint.weightedSum E s f = ECPoint.weightedSum E s g :=
  Finset.sum_congr rfl h

/-- Adding zero-valued entries to a `weightedSum` doesn't change its
    value. Dual to `Finset.sum_subset` for additive sums. -/
theorem ECPoint.weightedSum_subset_of_zero_outside (E : ECSetup) {α : Type*}
    [DecidableEq α] {s t : Finset α} (h : s ⊆ t)
    {f : α → ECPoint E} (h0 : ∀ a ∈ t, a ∉ s → f a = 0) :
    ECPoint.weightedSum E t f = ECPoint.weightedSum E s f :=
  (Finset.sum_subset h h0).symm

theorem ECPoint.weightedSum_zero_of_forall_zero (E : ECSetup) {α : Type*}
    {s : Finset α} {f : α → ECPoint E}
    (h : ∀ a ∈ s, f a = 0) :
    ECPoint.weightedSum E s f = 0 :=
  Finset.sum_eq_zero h

/-- If `f` is zero except at one point `a` of `s`, the weighted sum
    equals `f a`. -/
theorem ECPoint.weightedSum_eq_single (E : ECSetup) {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ECPoint E} {a : α} (ha : a ∈ s)
    (hOther : ∀ b ∈ s, b ≠ a → f b = 0) :
    ECPoint.weightedSum E s f = f a :=
  Finset.sum_eq_single_of_mem a ha hOther

/-! ## Iterated group sum (alias for mathlib's `n • p`) -/

/-- Natural-number scalar multiple `nsmul n p = n • p` on `ECPoint E`. -/
noncomputable def ECPoint.nsmul (_E : ECSetup) {E : ECSetup} (n : ℕ)
    (p : ECPoint E) : ECPoint E := n • p

/-- Integer scalar multiple `zsmul n p = n • p` on `ECPoint E`. -/
noncomputable def ECPoint.zsmul (_E : ECSetup) {E : ECSetup} (n : ℤ)
    (p : ECPoint E) : ECPoint E := n • p

theorem ECPoint.nsmul_def (E : ECSetup) (n : ℕ) (p : ECPoint E) :
    ECPoint.nsmul E n p = n • p := rfl

theorem ECPoint.zsmul_def (E : ECSetup) (n : ℤ) (p : ECPoint E) :
    ECPoint.zsmul E n p = n • p := rfl

@[simp] theorem ECPoint.nsmul_zero (E : ECSetup) (p : ECPoint E) :
    ECPoint.nsmul E 0 p = 0 := zero_smul ℕ p

@[simp] theorem ECPoint.nsmul_succ (E : ECSetup) (n : ℕ) (p : ECPoint E) :
    ECPoint.nsmul E (n + 1) p = p + ECPoint.nsmul E n p := by
  show (n + 1) • p = p + n • p
  rw [add_smul, one_smul, add_comm]

@[simp] theorem ECPoint.zsmul_zero (E : ECSetup) (p : ECPoint E) :
    ECPoint.zsmul E 0 p = 0 := zero_smul ℤ p

@[simp] theorem ECPoint.zsmul_one (E : ECSetup) (p : ECPoint E) :
    ECPoint.zsmul E 1 p = p := one_smul ℤ p

@[simp] theorem ECPoint.zsmul_neg_one (E : ECSetup) (p : ECPoint E) :
    ECPoint.zsmul E (-1) p = -p := neg_one_zsmul p

theorem ECPoint.nsmul_infinity (E : ECSetup) (n : ℕ) :
    ECPoint.nsmul E n (0 : ECPoint E) = 0 := by
  induction n with
  | zero => exact ECPoint.nsmul_zero E _
  | succ n ih =>
      rw [ECPoint.nsmul_succ, ih, add_zero]

theorem ECPoint.zsmul_natCast (E : ECSetup) (n : ℕ) (p : ECPoint E) :
    ECPoint.zsmul E (n : ℤ) p = ECPoint.nsmul E n p := by
  show ((n : ℤ) • p : ECPoint E) = n • p
  simp

theorem ECPoint.zsmul_infinity (E : ECSetup) (n : ℤ) :
    ECPoint.zsmul E n (0 : ECPoint E) = 0 := by
  cases n with
  | ofNat m =>
      show ((m : ℤ) • (0 : ECPoint E)) = 0
      rw [show ((m : ℤ) • (0 : ECPoint E)) = ECPoint.zsmul E (m : ℤ) 0 from rfl,
          ECPoint.zsmul_natCast]
      exact ECPoint.nsmul_infinity E m
  | negSucc m =>
      show ((Int.negSucc m) • (0 : ECPoint E)) = 0
      rw [Int.negSucc_eq, neg_zsmul]
      have hm1 : ((m + 1 : ℤ) • (0 : ECPoint E)) = 0 := by
        rw [show ((m + 1 : ℤ) • (0 : ECPoint E)) = ECPoint.zsmul E (m + 1 : ℤ) 0 from rfl]
        have hcast : ECPoint.zsmul E (m + 1 : ℤ) (0 : ECPoint E) =
               ECPoint.zsmul E ((m + 1 : ℕ) : ℤ) 0 := by push_cast; rfl
        rw [hcast, ECPoint.zsmul_natCast]
        exact ECPoint.nsmul_infinity E (m + 1)
      rw [hm1, neg_zero]

/-! ## Derived group-law lemmas (kept for backward compatibility) -/

@[simp] theorem ECPoint.zero_def {E : ECSetup} : (0 : ECPoint E) = .zero := rfl

@[simp] theorem ECPoint.zero_add_curve (E : ECSetup) (p : ECPoint E) :
    (0 : ECPoint E) + p = p := zero_add p

@[simp] theorem ECPoint.add_zero_curve (E : ECSetup) (p : ECPoint E) :
    p + (0 : ECPoint E) = p := add_zero p

theorem ECPoint.add_comm_law (E : ECSetup) (p q : ECPoint E) :
    p + q = q + p := add_comm p q

theorem ECPoint.add_assoc_law (E : ECSetup) (p q r : ECPoint E) :
    (p + q) + r = p + (q + r) := add_assoc p q r

theorem ECPoint.neg_add_cancel_law (E : ECSetup) (p : ECPoint E) :
    -p + p = 0 := neg_add_cancel p

@[simp] theorem ECPoint.neg_neg (E : ECSetup) (p : ECPoint E) : -(-p) = p :=
  _root_.neg_neg p

@[simp] theorem ECPoint.neg_infinity {E : ECSetup} :
    -(0 : ECPoint E) = 0 := neg_zero

theorem ECPoint.neg_inj {E : ECSetup} {p₁ p₂ : ECPoint E} (h : -p₁ = -p₂) :
    p₁ = p₂ := neg_injective h

/-- For our setup (with `a₁ = a₃ = 0`), the curve's `negY` formula
collapses to plain `−y`. -/
theorem ECSetup.negY_eq_neg (E : ECSetup) (x y : ZMod E.q) :
    E.toW.toAffine.negY x y = -y := by
  show -y - E.toW.a₁ * x - E.toW.a₃ = -y
  rw [E.toW_a₁, E.toW_a₃]; ring

/-- The negation of `ECPoint.affine E x y` agrees with the
coordinate-level `(x, -y)` form. Holds whether or not `(x, y)` is
nonsingular: if it isn't, both sides equal infinity. -/
theorem ECPoint.affine_neg (E : ECSetup) (x y : ZMod E.q) :
    -(ECPoint.affine E x y : ECPoint E) = ECPoint.affine E x (-y) := by
  classical
  by_cases hns : E.toW.toAffine.Nonsingular x y
  · have hns' : E.toW.toAffine.Nonsingular x (-y) := by
      have := (WeierstrassCurve.Affine.nonsingular_neg
                (W' := E.toW.toAffine) x y).mpr hns
      rwa [E.negY_eq_neg] at this
    rw [ECPoint.affine_of_nonsingular E hns,
        ECPoint.affine_of_nonsingular E hns',
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨rfl, by rw [E.negY_eq_neg]⟩
  · have hns' : ¬ E.toW.toAffine.Nonsingular x (-y) := by
      intro h
      apply hns
      have hbi := (WeierstrassCurve.Affine.nonsingular_neg
                (W' := E.toW.toAffine) x (-y)).mpr h
      rw [E.negY_eq_neg] at hbi
      have hyy : -(-y) = y := _root_.neg_neg y
      rw [hyy] at hbi
      exact hbi
    have h0 : (ECPoint.affine E x y : ECPoint E) = 0 := by
      unfold ECPoint.affine; rw [dif_neg hns]
    have h0' : (ECPoint.affine E x (-y) : ECPoint E) = 0 := by
      unfold ECPoint.affine; rw [dif_neg hns']
    rw [h0, h0', neg_zero]

/-- The fiber sum at `x` over `(x, y)` and `(x, -y)` is zero in
`ECPoint E`, regardless of multiplicity. Uses `affine_neg` to fold
the pair into `n • P + n • (−P) = 0`. -/
theorem ECPoint.nsmul_affine_pair_eq_zero (E : ECSetup)
    (n : ℕ) (x y : ZMod E.q) :
    ECPoint.nsmul E n (ECPoint.affine E x y) +
    ECPoint.nsmul E n (ECPoint.affine E x (-y)) = 0 := by
  rw [← ECPoint.affine_neg E x y]
  rw [ECPoint.nsmul_def, ECPoint.nsmul_def, neg_nsmul]
  exact add_neg_cancel _

/-- Left cancellation. -/
theorem ECPoint.add_left_cancel (E : ECSetup) {p a b : ECPoint E}
    (h : p + a = p + b) : a = b :=
  _root_.add_left_cancel h

end Divisor
