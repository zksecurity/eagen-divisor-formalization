/-
  Divisor/Defs.lean — Core definitions

  The pure-type definitions live in `Divisor/DefsPre.lean`; this file
  re-exports them, pulls in the ECPoint group-law axioms, and declares
  the `Std.Commutative` / `Std.Associative` instances that `weightedSum`
  depends on. See `docs/bivariate-sz-paper-faithful.md` (Preconditions
  P1) for the axiom layout.
-/
import Divisor.DefsPre
import Divisor.Axioms.AxiomECPointAddComm
import Divisor.Axioms.AxiomECPointAddAssoc
import Divisor.Axioms.AxiomECPointNegAddCancel

open Finset Polynomial

namespace Divisor

variable (E : ECSetup)
variable {q : ℕ} [hq : Fact (Nat.Prime q)]

/-- Typeclass instances for `Finset.fold` over `ECPoint.add E`. -/
instance (E : ECSetup) : Std.Commutative (ECPoint.add E) :=
  ⟨ECPoint.add_comm E⟩

instance (E : ECSetup) : Std.Associative (ECPoint.add E) :=
  ⟨ECPoint.add_assoc E⟩

/-- Group-sum of a family of `(coefficient, point)` weighted terms over a
    `Finset`. Implemented via `Finset.fold` of `ECPoint.add E`; independence
    of iteration order is supplied by the `Std.Commutative` / `Std.Associative`
    instances above. -/
noncomputable def ECPoint.weightedSum (E : ECSetup) {α : Type*}
    (s : Finset α) (f : α → ECPoint E.q) : ECPoint E.q :=
  s.fold (ECPoint.add E) 0 f

@[simp] theorem ECPoint.weightedSum_empty (E : ECSetup) {α : Type*}
    (f : α → ECPoint E.q) : ECPoint.weightedSum E (∅ : Finset α) f = 0 := rfl

theorem ECPoint.weightedSum_insert (E : ECSetup) {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) (f : α → ECPoint E.q) :
    ECPoint.weightedSum E (insert a s) f =
      ECPoint.add E (f a) (ECPoint.weightedSum E s f) :=
  Finset.fold_insert ha

theorem ECPoint.weightedSum_congr (E : ECSetup) {α : Type*}
    {s : Finset α} {f g : α → ECPoint E.q}
    (h : ∀ a ∈ s, f a = g a) :
    ECPoint.weightedSum E s f = ECPoint.weightedSum E s g :=
  Finset.fold_congr (fun a ha => h a ha)

/-- Adding zero-valued entries to a `weightedSum` doesn't change its
    value. Dual to `Finset.sum_subset` for additive sums. -/
theorem ECPoint.weightedSum_subset_of_zero_outside (E : ECSetup) {α : Type*}
    [DecidableEq α] {s t : Finset α} (h : s ⊆ t)
    {f : α → ECPoint E.q} (h0 : ∀ a ∈ t, a ∉ s → f a = 0) :
    ECPoint.weightedSum E t f = ECPoint.weightedSum E s f := by
  revert s
  induction t using Finset.induction_on with
  | empty =>
      intro s hs _
      rw [Finset.subset_empty.mp hs]
  | @insert a t' ha ih =>
      intro s hs h0
      rw [ECPoint.weightedSum_insert E ha]
      by_cases hain : a ∈ s
      · have hs_erase_sub : s.erase a ⊆ t' := by
          intro x hx
          have hxs : x ∈ s := Finset.mem_of_mem_erase hx
          have hxt : x ∈ insert a t' := hs hxs
          have hxne : x ≠ a := Finset.ne_of_mem_erase hx
          exact (Finset.mem_insert.mp hxt).resolve_left hxne
        have hs_insert : s = insert a (s.erase a) := (Finset.insert_erase hain).symm
        have h0' : ∀ x ∈ t', x ∉ s.erase a → f x = 0 := by
          intro x hxt hxne
          by_cases hxs : x ∈ s
          · have hxeq : x = a := by
              by_contra hxa
              exact hxne (Finset.mem_erase.mpr ⟨hxa, hxs⟩)
            exact absurd (hxeq ▸ hxt) ha
          · exact h0 x (Finset.mem_insert_of_mem hxt) hxs
        have hrec : ECPoint.weightedSum E t' f = ECPoint.weightedSum E (s.erase a) f :=
          ih hs_erase_sub h0'
        rw [hs_insert, ECPoint.weightedSum_insert E (Finset.notMem_erase _ _), hrec]
      · rw [h0 a (Finset.mem_insert_self _ _) hain, ECPoint.zero_add_curve]
        have hs_t' : s ⊆ t' := by
          intro x hx
          have hxt : x ∈ insert a t' := hs hx
          have hxne : x ≠ a := fun heq => hain (heq ▸ hx)
          exact (Finset.mem_insert.mp hxt).resolve_left hxne
        have h0' : ∀ x ∈ t', x ∉ s → f x = 0 :=
          fun x hxt hxs => h0 x (Finset.mem_insert_of_mem hxt) hxs
        exact ih hs_t' h0'

theorem ECPoint.nsmul_infinity (E : ECSetup) (n : ℕ) :
    ECPoint.nsmul E n (ECPoint.infinity : ECPoint E.q) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show ECPoint.add E ECPoint.infinity (ECPoint.nsmul E n ECPoint.infinity) = 0
      rw [ih]
      rfl

theorem ECPoint.zsmul_infinity (E : ECSetup) (n : ℤ) :
    ECPoint.zsmul E n (ECPoint.infinity : ECPoint E.q) = 0 := by
  cases n with
  | ofNat m => exact ECPoint.nsmul_infinity E m
  | negSucc m =>
      show -(ECPoint.nsmul E (m + 1) ECPoint.infinity) = 0
      rw [ECPoint.nsmul_infinity]
      rfl

/-- `zsmul (n : ℕ)` equals `nsmul n`. -/
theorem ECPoint.zsmul_natCast (E : ECSetup) (n : ℕ) (p : ECPoint E.q) :
    ECPoint.zsmul E (n : ℤ) p = ECPoint.nsmul E n p := rfl

theorem ECPoint.weightedSum_zero_of_forall_zero (E : ECSetup) {α : Type*}
    [DecidableEq α] {s : Finset α} {f : α → ECPoint E.q}
    (h : ∀ a ∈ s, f a = 0) :
    ECPoint.weightedSum E s f = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ECPoint.weightedSum_empty E f
  | @insert b s' hbnmem ih =>
      rw [ECPoint.weightedSum_insert E hbnmem]
      rw [h b (Finset.mem_insert_self b s'), ECPoint.zero_add_curve]
      exact ih (fun a ha => h a (Finset.mem_insert_of_mem ha))

/-- If `f` is zero except at one point `a` of `s`, the weighted sum
    equals `f a`. -/
theorem ECPoint.weightedSum_eq_single (E : ECSetup) {α : Type*} [DecidableEq α]
    {s : Finset α} {f : α → ECPoint E.q} {a : α} (ha : a ∈ s)
    (hOther : ∀ b ∈ s, b ≠ a → f b = 0) :
    ECPoint.weightedSum E s f = f a := by
  induction s using Finset.induction_on with
  | empty => exact absurd ha (Finset.notMem_empty a)
  | @insert b s' hbnmem ih =>
      rw [ECPoint.weightedSum_insert E hbnmem]
      by_cases hab : b = a
      · subst hab
        have hs' : ECPoint.weightedSum E s' f = 0 := by
          apply ECPoint.weightedSum_zero_of_forall_zero E
          intro c hc
          have hc_insert : c ∈ insert b s' := Finset.mem_insert_of_mem hc
          have hne : c ≠ b := fun heq => hbnmem (heq ▸ hc)
          exact hOther c hc_insert hne
        rw [hs', ECPoint.add_zero_curve]
      · have hb_zero : f b = 0 := hOther b (Finset.mem_insert_self b s') hab
        rw [hb_zero, ECPoint.zero_add_curve]
        have ha_s' : a ∈ s' := by
          rw [Finset.mem_insert] at ha
          exact ha.resolve_left (Ne.symm hab)
        exact ih ha_s' (fun c hc hne => hOther c (Finset.mem_insert_of_mem hc) hne)

/-! ## Derived group-law lemmas -/

@[simp] theorem ECPoint.neg_neg (p : ECPoint q) : -(-p) = p := by
  cases p with
  | infinity => rfl
  | affine x y =>
      show (ECPoint.neg (ECPoint.neg (.affine x y))) = .affine x y
      simp [ECPoint.neg, _root_.neg_neg]

@[simp] theorem ECPoint.neg_infinity : (-(.infinity : ECPoint q)) = .infinity := rfl

theorem ECPoint.neg_inj {p₁ p₂ : ECPoint q} (h : -p₁ = -p₂) : p₁ = p₂ := by
  have := congrArg (fun r : ECPoint q => -r) h
  simpa using this

/-- Left cancellation for `ECPoint.add E`. Follows from `add_assoc` +
    `neg_add_cancel`. -/
theorem ECPoint.add_left_cancel (E : ECSetup) {p a b : ECPoint E.q}
    (h : ECPoint.add E p a = ECPoint.add E p b) : a = b := by
  have h1 : ECPoint.add E (-p) (ECPoint.add E p a)
          = ECPoint.add E (-p) (ECPoint.add E p b) := by rw [h]
  rw [← ECPoint.add_assoc, ← ECPoint.add_assoc,
      ECPoint.neg_add_cancel, ECPoint.zero_add_curve,
      ECPoint.zero_add_curve] at h1
  exact h1

/-- Relate `thirdPoint` to the group law: when the third point is affine,
    `thirdPoint E A₀ A₁ = -(A₀ + A₁)` in the `ECPoint E.q` group. -/
theorem thirdPoint_eq_neg_add (E : ECSetup) (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNotInf : thirdPoint E A₀ A₁ ≠ ECPoint.infinity) :
    thirdPoint E A₀ A₁
      = -(ECPoint.add E (.affine A₀.1 A₀.2) (.affine A₁.1 A₁.2)) := by
  rcases A₀ with ⟨x₀, y₀⟩
  rcases A₁ with ⟨x₁, y₁⟩
  simp only [Prod.fst, Prod.snd]
  show thirdPoint E (x₀, y₀) (x₁, y₁) = _
  have hadd : ECPoint.add E (.affine x₀ y₀) (.affine x₁ y₁)
      = match thirdPoint E (x₀, y₀) (x₁, y₁) with
        | .infinity => .infinity
        | .affine x₂ y₂ => .affine x₂ (-y₂) := rfl
  cases h : thirdPoint E (x₀, y₀) (x₁, y₁) with
  | infinity => exact absurd h hNotInf
  | affine x₂ y₂ =>
      rw [hadd, h]
      show (.affine x₂ y₂ : ECPoint E.q) = ECPoint.neg (.affine x₂ (-y₂))
      simp [ECPoint.neg]

end Divisor
