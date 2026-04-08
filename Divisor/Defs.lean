/-
  Divisor/Defs.lean

  Core definitions for the formalization of divisor-based
  zero-knowledge proofs on elliptic curves.

  Corresponds to the notation and setup in Section 1 of the paper.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.MinMax

open Finset Polynomial

namespace Divisor

/-! ## Elliptic curve setup

We work with a short Weierstrass curve y^2 = x^3 + A*x + B over F_q
where q is prime. We define a lightweight bundle capturing the finite
combinatorial data needed for the probability bounds.
-/

/-- An elliptic curve in short Weierstrass form over F_q = ZMod q,
    together with its set of rational points and cardinality data. -/
structure ECSetup where
  /-- The prime field size -/
  q : ℕ
  /-- q is prime -/
  hq_prime : Nat.Prime q
  /-- Curve coefficient A -/
  curveA : ZMod q
  /-- Curve coefficient B -/
  curveB : ZMod q
  /-- The set of affine rational points (x, y) on y^2 = x^3 + Ax + B -/
  points : Finset (ZMod q × ZMod q)
  /-- Every point in the set satisfies the curve equation -/
  hOnCurve : ∀ p ∈ points, p.2 ^ 2 = p.1 ^ 3 + curveA * p.1 + curveB
  /-- The point set is exactly the solution set -/
  hComplete : ∀ x y : ZMod q,
    y ^ 2 = x ^ 3 + curveA * x + curveB → (x, y) ∈ points
  /-- Number of rational points including the point at infinity O -/
  numPoints : ℕ
  /-- numPoints = #affine_points + 1 -/
  hNumPoints : numPoints = points.card + 1
  /-- q >= 5 so the field is large enough for short Weierstrass -/
  hq_ge : q ≥ 5

variable (E : ECSetup)

instance : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩

/-- Shorthand for the number of affine points -/
noncomputable abbrev ECSetup.numAffine : ℕ := E.points.card

theorem ECSetup.numPoints_eq : E.numPoints = E.numAffine + 1 := E.hNumPoints

/-! ## Lines -/

/-- A non-vertical line L(x,y) = y - lam * x - mu over F_q -/
structure Line (q : ℕ) [Fact (Nat.Prime q)] where
  lam : ZMod q
  mu : ZMod q

variable {q : ℕ} [hq : Fact (Nat.Prime q)]

/-- Evaluate L(x,y) = y - lam * x - mu -/
def Line.eval (L : Line q) (x y : ZMod q) : ZMod q :=
  y - L.lam * x - L.mu

/-- Slope of the line through two points with distinct x-coordinates -/
def slopeOf (x₀ y₀ x₁ y₁ : ZMod q) : ZMod q :=
  (y₁ - y₀) * (x₁ - x₀)⁻¹

/-- Construct the line through two affine points -/
def lineThrough (x₀ y₀ x₁ y₁ : ZMod q) : Line q :=
  let s := slopeOf x₀ y₀ x₁ y₁
  { lam := s, mu := y₀ - s * x₀ }

/-! ## Coordinate ring elements -/

/-- An element D = a(x) - b(x) * y of F_q[E] -/
structure CoordRingElt (q : ℕ) [Fact (Nat.Prime q)] where
  a : Polynomial (ZMod q)
  b : Polynomial (ZMod q)

/-- degE(D) = max(2 * deg(a), 3 + 2 * deg(b)) = pole multiplicity at O -/
noncomputable def CoordRingElt.degE (D : CoordRingElt q) : ℕ :=
  max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree)

/-- Evaluate D at an affine point: a(x) - b(x) * y -/
def CoordRingElt.eval (D : CoordRingElt q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y

/-- The set of affine zeros of D on E -/
def zeros (D : CoordRingElt q) (pts : Finset (ZMod q × ZMod q)) :
    Finset (ZMod q × ZMod q) :=
  pts.filter (fun p => D.eval p.1 p.2 = 0)

/-! ## Ordered pairs and probability -/

/-- Ordered pairs of distinct elements from a finset -/
def distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) : Finset (α × α) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2)

/-- The number of distinct ordered pairs -/
theorem card_distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) :
    (distinctPairs S).card = S.card * S.card - S.card := by
  sorry

/-! ## Group law (abstract interface)

We axiomatize the elliptic curve group law as an operation on affine
points plus the point at infinity. This avoids importing the full
Mathlib elliptic curve development while keeping the formalization
compatible with it.
-/

/-- A point on E: either affine (x,y) or the point at infinity O -/
inductive ECPoint (q : ℕ) [Fact (Nat.Prime q)] where
  | affine (x y : ZMod q) : ECPoint q
  | infinity : ECPoint q
  deriving DecidableEq

/-- Negation of a point -/
def ECPoint.neg : ECPoint q → ECPoint q
  | .affine x y => .affine x (-y)
  | .infinity => .infinity

instance : Neg (ECPoint q) := ⟨ECPoint.neg⟩

/-- The third intersection point A₂ = -(A₀ + A₁) -/
def thirdPoint (E : ECSetup) (A₀ A₁ : ZMod q × ZMod q) : ECPoint E.q :=
  -- When A₀, A₁ are distinct affine points with x₀ ≠ x₁,
  -- A₂ = -(A₀ + A₁) is the third point on E collinear with A₀, A₁.
  -- We represent this abstractly; the actual computation is axiomatized.
  sorry

end Divisor
