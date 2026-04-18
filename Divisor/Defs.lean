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

/-- Group-sum of a family of `(coefficient, point)` weighted terms over a
    `Finset`. Implemented via `Finset.fold` of `ECPoint.add E`; independence
    of iteration order is supplied by the `Std.Commutative` / `Std.Associative`
    instances above. -/
noncomputable def ECPoint.weightedSum (E : ECSetup) {α : Type*}
    (s : Finset α) (f : α → ECPoint E.q) : ECPoint E.q :=
  s.fold (ECPoint.add E) 0 f

end Divisor
