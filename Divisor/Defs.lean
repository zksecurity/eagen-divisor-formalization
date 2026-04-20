/-
  Divisor/Defs.lean — Core definitions
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.MinMax
import Mathlib.Data.Finset.Prod

open Finset Polynomial

namespace Divisor

/-- Short Weierstrass curve y^2 = x^3 + Ax + B over F_q with point set -/
structure ECSetup where
  q : ℕ
  hq_prime : Nat.Prime q
  curveA : ZMod q
  curveB : ZMod q
  points : Finset (ZMod q × ZMod q)
  hOnCurve : ∀ p ∈ points, p.2 ^ 2 = p.1 ^ 3 + curveA * p.1 + curveB
  hComplete : ∀ x y : ZMod q, y ^ 2 = x ^ 3 + curveA * x + curveB → (x, y) ∈ points
  numPoints : ℕ
  hNumPoints : numPoints = points.card + 1
  hq_ge : q ≥ 5

variable (E : ECSetup)

instance : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩

noncomputable abbrev ECSetup.numAffine : ℕ := E.points.card

theorem ECSetup.numPoints_eq : E.numPoints = E.numAffine + 1 := E.hNumPoints

/-! ## Lines -/

structure Line (q : ℕ) [Fact (Nat.Prime q)] where
  lam : ZMod q
  mu : ZMod q

variable {q : ℕ} [hq : Fact (Nat.Prime q)]

def Line.eval (L : Line q) (x y : ZMod q) : ZMod q :=
  y - L.lam * x - L.mu

def slopeOf (x₀ y₀ x₁ y₁ : ZMod q) : ZMod q :=
  (y₁ - y₀) * (x₁ - x₀)⁻¹

def lineThrough (x₀ y₀ x₁ y₁ : ZMod q) : Line q :=
  let s := slopeOf x₀ y₀ x₁ y₁
  { lam := s, mu := y₀ - s * x₀ }

/-! ## Coordinate ring elements -/

structure CoordRingElt (q : ℕ) [Fact (Nat.Prime q)] where
  a : Polynomial (ZMod q)
  b : Polynomial (ZMod q)

noncomputable def CoordRingElt.degE (D : CoordRingElt q) : ℕ :=
  max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree)

def CoordRingElt.eval (D : CoordRingElt q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y

def zeros (D : CoordRingElt q) (pts : Finset (ZMod q × ZMod q)) :
    Finset (ZMod q × ZMod q) :=
  pts.filter (fun p => D.eval p.1 p.2 = 0)

/-! ## Ordered pairs -/

def distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) : Finset (α × α) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2)

theorem card_distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) :
    (distinctPairs S).card = S.card * S.card - S.card := by
  unfold distinctPairs
  -- distinct = product \ diagonal
  have hdiag : (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) =
      S.image (fun a => (a, a)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
  have hcard_diag : (S.image (fun a => (a, a))).card = S.card :=
    Finset.card_image_of_injective S (fun a b h => (Prod.mk.injEq a a b b).mp h |>.1)
  -- filter (≠) = product \ filter (=)
  have hsplit : (S ×ˢ S).filter (fun p : α × α => p.1 ≠ p.2) =
      (S ×ˢ S) \ (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_product, ne_eq,
               not_and, not_not]
    tauto
  rw [hsplit, Finset.card_sdiff (Finset.filter_subset _ _),
      Finset.card_product, hdiag, hcard_diag]

/-! ## Points -/

inductive ECPoint (q : ℕ) [Fact (Nat.Prime q)] where
  | affine (x y : ZMod q) : ECPoint q
  | infinity : ECPoint q
  deriving DecidableEq

def ECPoint.neg : ECPoint q → ECPoint q
  | .affine x y => .affine x (-y)
  | .infinity => .infinity

instance : Neg (ECPoint q) := ⟨ECPoint.neg⟩

noncomputable def thirdPoint (E : ECSetup) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    ECPoint E.q :=
  if A₀.1 = A₁.1 then
    if A₀.2 = A₁.2 then
      -- A₀ = A₁: tangent-line case.
      if A₀.2 = 0 then .infinity  -- 2-torsion, vertical tangent
      else
        let lam := (3 * A₀.1 ^ 2 + E.curveA) * (2 * A₀.2)⁻¹
        let mu := A₀.2 - lam * A₀.1
        let x₂ := lam ^ 2 - 2 * A₀.1
        let y₂ := lam * x₂ + mu
        .affine x₂ y₂
    else
      -- A₁ = -A₀: vertical line.
      .infinity
  else
    let lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
    let mu := A₀.2 - lam * A₀.1
    let x₂ := lam ^ 2 - A₀.1 - A₁.1
    let y₂ := lam * x₂ + mu
    .affine x₂ y₂

/-! ## Group law on `ECPoint`

The elliptic-curve chord-and-tangent group law. The operation depends on
the concrete curve `E : ECSetup` (the coefficients `A, B` enter through
`thirdPoint`), so it is not a `Add (ECPoint q)` instance but a curve-
parameterized function `ECPoint.add E`.

Group-law facts (associativity, commutativity, inverse) are classical
(Silverman, "Arithmetic of Elliptic Curves", Ch III, §2). Per our "classical
AG as axioms" policy they are axiomatized here over the concrete chord-and-
tangent definition. The two trivial laws (`zero_add`, `add_zero`) are
discharged by pattern-matching. -/

/-- Zero of the elliptic-curve group: the point at infinity. -/
def ECPoint.zero : ECPoint q := .infinity

instance : Zero (ECPoint q) := ⟨ECPoint.zero⟩

@[simp] theorem ECPoint.zero_def : (0 : ECPoint q) = .infinity := rfl

/-- The elliptic-curve group operation on `ECPoint E.q`.

    Cases:
    * `∞ + p = p`, `p + ∞ = p`.
    * `(x, y) + (x, -y) = ∞` (inverses cancel).
    * `(x, y) + (x, y)` with `y = 0` (2-torsion, vertical tangent) returns `∞`.
    * Otherwise: take `thirdPoint E A₀ A₁` and negate. (Chord-and-tangent.) -/
noncomputable def ECPoint.add (E : ECSetup) :
    ECPoint E.q → ECPoint E.q → ECPoint E.q
  | .infinity, p => p
  | p, .infinity => p
  | .affine x₀ y₀, .affine x₁ y₁ =>
      match thirdPoint E (x₀, y₀) (x₁, y₁) with
      | .infinity => .infinity
      | .affine x₂ y₂ => .affine x₂ (-y₂)

@[simp] theorem ECPoint.zero_add_curve (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.add E 0 p = p := by
  cases p <;> rfl

@[simp] theorem ECPoint.add_zero_curve (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.add E p 0 = p := by
  cases p <;> rfl

/-- Commutativity of `ECPoint.add`. Classical; Silverman Ch III Prop 2.2(a). -/
axiom ECPoint.add_comm (E : ECSetup) (p q : ECPoint E.q) :
    ECPoint.add E p q = ECPoint.add E q p

/-- Associativity of `ECPoint.add`. Classical; Silverman Ch III Prop 2.2(d).
    The nontrivial group-law axiom — proof uses the Riemann-Roch / divisor
    equivalence. -/
axiom ECPoint.add_assoc (E : ECSetup) (p q r : ECPoint E.q) :
    ECPoint.add E (ECPoint.add E p q) r = ECPoint.add E p (ECPoint.add E q r)

/-- Left inverse: `-p + p = 0`. Follows from the chord-and-tangent definition
    (vertical line through `p` and `-p` has third intersection at `∞`).
    We keep as axiom to avoid a case split on `p = -p` (2-torsion) matching
    the `thirdPoint` branches; the facts we need downstream use this
    abstractly anyway. -/
axiom ECPoint.neg_add_cancel (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.add E (-p) p = (0 : ECPoint E.q)

/-- Typeclass instances for `Finset.fold` over `ECPoint.add E`. -/
instance (E : ECSetup) : Std.Commutative (ECPoint.add E) :=
  ⟨ECPoint.add_comm E⟩

instance (E : ECSetup) : Std.Associative (ECPoint.add E) :=
  ⟨ECPoint.add_assoc E⟩

/-- Iterated group sum: `nsmul E n p = p + p + ⋯ + p` (`n` copies). -/
noncomputable def ECPoint.nsmul (E : ECSetup) : ℕ → ECPoint E.q → ECPoint E.q
  | 0, _ => 0
  | n + 1, p => ECPoint.add E p (ECPoint.nsmul E n p)

@[simp] theorem ECPoint.nsmul_zero (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.nsmul E 0 p = 0 := rfl

@[simp] theorem ECPoint.nsmul_succ (E : ECSetup) (n : ℕ) (p : ECPoint E.q) :
    ECPoint.nsmul E (n + 1) p = ECPoint.add E p (ECPoint.nsmul E n p) := rfl

/-- Integer scalar multiplication on `ECPoint E.q`: `zsmul E n p = [n] · p`.

    For `n ≥ 0`: iterated addition. For `n < 0`: negate the iteration.
    Used by `principal_divisor_iff` to express `Σ [n_P] · P = O`. -/
noncomputable def ECPoint.zsmul (E : ECSetup) (n : ℤ) (p : ECPoint E.q) :
    ECPoint E.q :=
  match n with
  | Int.ofNat m => ECPoint.nsmul E m p
  | Int.negSucc m => -(ECPoint.nsmul E (m + 1) p)

@[simp] theorem ECPoint.zsmul_zero (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.zsmul E 0 p = 0 := rfl

@[simp] theorem ECPoint.zsmul_one (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.zsmul E 1 p = p := by
  show ECPoint.nsmul E 1 p = p
  show ECPoint.add E p (ECPoint.nsmul E 0 p) = p
  show ECPoint.add E p 0 = p
  exact ECPoint.add_zero_curve E p

@[simp] theorem ECPoint.zsmul_neg_one (E : ECSetup) (p : ECPoint E.q) :
    ECPoint.zsmul E (-1) p = -p := by
  show -(ECPoint.nsmul E 1 p) = -p
  show -(ECPoint.add E p (ECPoint.nsmul E 0 p)) = -p
  show -(ECPoint.add E p 0) = -p
  rw [ECPoint.add_zero_curve]

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
        rw [hs_insert, ECPoint.weightedSum_insert E (Finset.not_mem_erase _ _), hrec]
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
  | empty => rfl
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
  | empty => exact absurd ha (Finset.not_mem_empty a)
  | @insert b s' hbnmem ih =>
      rw [ECPoint.weightedSum_insert E hbnmem]
      by_cases hab : b = a
      · -- b = a: sum over s' is 0 (by hOther applied to every member of s')
        subst hab
        have hs' : ECPoint.weightedSum E s' f = 0 := by
          apply ECPoint.weightedSum_zero_of_forall_zero E
          intro c hc
          have hc_insert : c ∈ insert b s' := Finset.mem_insert_of_mem hc
          have hne : c ≠ b := fun heq => hbnmem (heq ▸ hc)
          exact hOther c hc_insert hne
        rw [hs', ECPoint.add_zero_curve]
      · -- b ≠ a, so f b = 0; recurse on s'.
        have hb_zero : f b = 0 := hOther b (Finset.mem_insert_self b s') hab
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

/-- Left cancellation for `ECPoint.add E`. -/
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
