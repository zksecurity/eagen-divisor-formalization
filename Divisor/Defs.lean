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
  if A₀.1 = A₁.1 then .infinity
  else
    let lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
    let mu := A₀.2 - lam * A₀.1
    let x₂ := lam ^ 2 - A₀.1 - A₁.1
    let y₂ := lam * x₂ + mu
    .affine x₂ y₂

end Divisor
