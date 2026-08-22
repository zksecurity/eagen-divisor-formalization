/-
  Divisor/DefsPre.lean — Core definitions

  The on-curve point group is mathlib's `WeierstrassCurve.Affine.Point`,
  which bundles the nonsingular hypothesis structurally. The local
  abbreviation `ECPoint E := (E.toW).toAffine.Point` reuses mathlib's
  full `AddCommGroup` instance — no chord-tangent axioms needed.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.MinMax
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.LinearCombination

open Finset Polynomial WeierstrassCurve

namespace Divisor

/-- Short Weierstrass curve `y² = x³ + Ax + B` over `F_q`, plus its
    affine point set as a `Finset`. The discriminant condition `hDisc`
    is `4A³ + 27B² ≠ 0`, equivalent to `Δ_W ≠ 0` (up to the unit `−16`).
    Bundling it here means every on-curve `(x, y)` is automatically a
    nonsingular point of the underlying `WeierstrassCurve`. -/
structure ECSetup where
  q : ℕ
  hq_prime : Nat.Prime q
  curveA : ZMod q
  curveB : ZMod q
  points : Finset (ZMod q × ZMod q)
  hOnCurve : ∀ p ∈ points, p.2 ^ 2 = p.1 ^ 3 + curveA * p.1 + curveB
  hComplete : ∀ x y : ZMod q, y ^ 2 = x ^ 3 + curveA * x + curveB → (x, y) ∈ points
  hDisc : 4 * curveA ^ 3 + 27 * curveB ^ 2 ≠ 0
  numPoints : ℕ
  hNumPoints : numPoints = points.card + 1
  hq_ge : q ≥ 5

variable (E : ECSetup)

instance : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩

noncomputable abbrev ECSetup.numAffine : ℕ := E.points.card

theorem ECSetup.numPoints_eq : E.numPoints = E.numAffine + 1 := E.hNumPoints

/-- The underlying mathlib Weierstrass curve, with `a₁ = a₂ = a₃ = 0`,
    `a₄ = curveA`, `a₆ = curveB`. -/
def ECSetup.toW (E : ECSetup) : WeierstrassCurve (ZMod E.q) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := E.curveA
  a₆ := E.curveB

@[simp] theorem ECSetup.toW_a₁ : E.toW.a₁ = 0 := rfl
@[simp] theorem ECSetup.toW_a₂ : E.toW.a₂ = 0 := rfl
@[simp] theorem ECSetup.toW_a₃ : E.toW.a₃ = 0 := rfl
@[simp] theorem ECSetup.toW_a₄ : E.toW.a₄ = E.curveA := rfl
@[simp] theorem ECSetup.toW_a₆ : E.toW.a₆ = E.curveB := rfl

/-- Affine equation in our short-Weierstrass conventions. -/
theorem ECSetup.equation_iff (E : ECSetup) (x y : ZMod E.q) :
    E.toW.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + E.curveA * x + E.curveB := by
  rw [Affine.equation_iff]
  simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₃,
             ECSetup.toW_a₄, ECSetup.toW_a₆]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Mathlib's discriminant `Δ` equals `−16(4A³ + 27B²)` for our short
    Weierstrass form. So `hDisc` (i.e. `4A³ + 27B² ≠ 0`) implies `Δ ≠ 0`
    when the characteristic is at least 5. -/
theorem ECSetup.toW_Δ_ne_zero (E : ECSetup) : E.toW.Δ ≠ 0 := by
  -- 16 ≠ 0 in ZMod E.q since q is prime ≥ 5 (so q ∤ 16 = 2^4).
  have h16 : (16 : ZMod E.q) ≠ 0 := by
    have hq5 : E.q ≥ 5 := E.hq_ge
    have hcast : (16 : ZMod E.q) = ((16 : ℕ) : ZMod E.q) := by norm_cast
    rw [hcast, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
    intro hdvd
    -- q ∣ 16 = 2^4, q prime, so q ∣ 2 hence q = 2; contradicts q ≥ 5.
    have hprime := E.hq_prime
    have h16_eq : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16_eq] at hdvd
    have hq_dvd_2 : E.q ∣ 2 := hprime.dvd_of_dvd_pow hdvd
    have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hq_dvd_2
    omega
  intro hΔ
  apply E.hDisc
  have hΔ_eq : E.toW.Δ = -16 * (4 * E.curveA ^ 3 + 27 * E.curveB ^ 2) := by
    show -E.toW.b₂ ^ 2 * E.toW.b₈ - 8 * E.toW.b₄ ^ 3
        - 27 * E.toW.b₆ ^ 2 + 9 * E.toW.b₂ * E.toW.b₄ * E.toW.b₆ = _
    show -(E.toW.a₁ ^ 2 + 4 * E.toW.a₂) ^ 2 *
          (E.toW.a₁ ^ 2 * E.toW.a₆ + 4 * E.toW.a₂ * E.toW.a₆
            - E.toW.a₁ * E.toW.a₃ * E.toW.a₄ + E.toW.a₂ * E.toW.a₃ ^ 2
            - E.toW.a₄ ^ 2)
        - 8 * (2 * E.toW.a₄ + E.toW.a₁ * E.toW.a₃) ^ 3
        - 27 * (E.toW.a₃ ^ 2 + 4 * E.toW.a₆) ^ 2
        + 9 * (E.toW.a₁ ^ 2 + 4 * E.toW.a₂) * (2 * E.toW.a₄ + E.toW.a₁ * E.toW.a₃)
            * (E.toW.a₃ ^ 2 + 4 * E.toW.a₆) = _
    rw [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₃,
        ECSetup.toW_a₄, ECSetup.toW_a₆]
    ring
  -- Conclude: the second factor must be zero.
  by_contra hDisc'
  have hZ : -16 * (4 * E.curveA ^ 3 + 27 * E.curveB ^ 2) = 0 := hΔ_eq ▸ hΔ
  -- Use the field instance on ZMod E.q.
  have : (4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 : ZMod E.q) = 0 := by
    have h16' : (-16 : ZMod E.q) ≠ 0 := by
      intro h
      apply h16
      have hh : (16 : ZMod E.q) = -(-16 : ZMod E.q) := by ring
      rw [hh, h]; ring
    -- divide both sides by -16.
    have := mul_left_cancel₀ h16' (by rw [hZ]; ring : (-16 : ZMod E.q) *
      (4 * E.curveA ^ 3 + 27 * E.curveB ^ 2) = (-16 : ZMod E.q) * 0)
    exact this
  exact hDisc' this

/-- An affine point `(x, y)` on the curve is automatically nonsingular
    in the mathlib sense, by the bundled discriminant hypothesis. -/
theorem ECSetup.equation_iff_nonsingular (E : ECSetup) {x y : ZMod E.q} :
    E.toW.toAffine.Equation x y ↔ E.toW.toAffine.Nonsingular x y :=
  Affine.equation_iff_nonsingular_of_Δ_ne_zero E.toW_Δ_ne_zero

instance ECSetup.nonsingularDecidable (E : ECSetup) (x y : ZMod E.q) :
    Decidable (E.toW.toAffine.Nonsingular x y) :=
  decidable_of_iff (y ^ 2 = x ^ 3 + E.curveA * x + E.curveB)
    ((E.equation_iff x y).symm.trans E.equation_iff_nonsingular)

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

noncomputable instance CoordRingElt.instSMul {q : ℕ} [Fact (Nat.Prime q)] :
    SMul (ZMod q) (CoordRingElt q) where
  smul c D := { a := c • D.a, b := c • D.b }

@[simp] theorem CoordRingElt.smul_a {q : ℕ} [Fact (Nat.Prime q)]
    (c : ZMod q) (D : CoordRingElt q) :
    (c • D).a = c • D.a := rfl

@[simp] theorem CoordRingElt.smul_b {q : ℕ} [Fact (Nat.Prime q)]
    (c : ZMod q) (D : CoordRingElt q) :
    (c • D).b = c • D.b := rfl

noncomputable def CoordRingElt.degE (D : CoordRingElt q) : ℕ :=
  max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree)

def CoordRingElt.eval (D : CoordRingElt q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y

@[simp] theorem CoordRingElt.eval_smul {q : ℕ} [Fact (Nat.Prime q)]
    (c : ZMod q) (D : CoordRingElt q) (x y : ZMod q) :
    (c • D).eval x y = c * D.eval x y := by
  unfold CoordRingElt.eval
  simp [mul_sub, mul_assoc]

def zeros (D : CoordRingElt q) (pts : Finset (ZMod q × ZMod q)) :
    Finset (ZMod q × ZMod q) :=
  pts.filter (fun p => D.eval p.1 p.2 = 0)

/-! ## Ordered pairs -/

def distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) : Finset (α × α) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2)

theorem card_distinctPairs {α : Type*} [DecidableEq α] (S : Finset α) :
    (distinctPairs S).card = S.card * S.card - S.card := by
  unfold distinctPairs
  have hdiag : (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) =
      S.image (fun a => (a, a)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
  have hcard_diag : (S.image (fun a => (a, a))).card = S.card :=
    Finset.card_image_of_injective S (fun a b h => (Prod.mk.injEq a a b b).mp h |>.1)
  have hsplit : (S ×ˢ S).filter (fun p : α × α => p.1 ≠ p.2) =
      (S ×ˢ S) \ (S ×ˢ S).filter (fun p : α × α => p.1 = p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_product, ne_eq,
               not_and]
    tauto
  rw [hsplit, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_product, hdiag, hcard_diag]

/-! ## Points -/

/-- The group of `F_q`-points on `E`, represented by mathlib's
    `WeierstrassCurve.Affine.Point`. Bundles the nonsingular condition
    structurally — off-curve `(x, y)` pairs are unrepresentable. -/
abbrev ECPoint (E : ECSetup) : Type := E.toW.toAffine.Point

namespace ECPoint

variable {E : ECSetup}

/-- The point at infinity. -/
abbrev infinity : ECPoint E := WeierstrassCurve.Affine.Point.zero

/-- Smart constructor for an affine point given on-curve evidence. -/
def affineOfEqn (E : ECSetup) {x y : ZMod E.q}
    (h : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB) : ECPoint E :=
  .some x y (E.equation_iff_nonsingular.mp ((E.equation_iff x y).mpr h))

/-- Smart constructor for an affine point given membership in `E.points`. -/
def affineOfMem (E : ECSetup) {p : ZMod E.q × ZMod E.q}
    (hp : p ∈ E.points) : ECPoint E :=
  affineOfEqn E (E.hOnCurve p hp)

/-- An affine point `(x, y)` from raw coordinates, junk-tolerant: returns
    the genuine affine point if `(x, y)` is on the curve, else falls back
    to `0` (the point at infinity). Convenient for total-function lambdas
    in `weightedSum` where off-curve coefficients are zero anyway, so
    the junk fallback is never observed. -/
def affine (E : ECSetup) (x y : ZMod E.q) : ECPoint E :=
  if h : E.toW.toAffine.Nonsingular x y then .some x y h else 0

/-- `ECPoint.affine E x y = .some x y h` whenever `(x, y)` is nonsingular. -/
theorem affine_of_nonsingular (E : ECSetup) {x y : ZMod E.q}
    (h : E.toW.toAffine.Nonsingular x y) :
    affine E x y = .some x y h := by
  unfold affine
  rw [dif_pos h]

/-- `ECPoint.affine E x y` agrees with the smart `affineOfMem` constructor
    on points of `E.points`. -/
theorem affine_eq_affineOfMem (E : ECSetup) {p : ZMod E.q × ZMod E.q}
    (hp : p ∈ E.points) :
    affine E p.1 p.2 = ECPoint.affineOfMem E hp := by
  rcases p with ⟨x, y⟩
  exact affine_of_nonsingular E
    (E.equation_iff_nonsingular.mp ((E.equation_iff x y).mpr (E.hOnCurve _ hp)))

/-- The finite set of affine `F_q`-points of `E`, represented as
    `ECPoint E` instead of raw coordinate pairs. -/
noncomputable def affinePoints (E : ECSetup) : Finset (ECPoint E) := by
  classical
  exact E.points.image (fun P => ECPoint.affine E P.1 P.2)

end ECPoint

namespace CoordRingElt

/-- Evaluate a coordinate-ring element at an `ECPoint`. The value at
    infinity is a harmless total-function default; callers that use this
    as affine evaluation should also require membership in
    `ECPoint.affinePoints E`. -/
def evalPoint (D : CoordRingElt E.q) : ECPoint E → ZMod E.q
  | 0 => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => D.eval x y

@[simp] theorem evalPoint_infinity (D : CoordRingElt E.q) :
    evalPoint E D (0 : ECPoint E) = 0 := rfl

@[simp] theorem evalPoint_some (D : CoordRingElt E.q)
    {x y : ZMod E.q} (h : E.toW.toAffine.Nonsingular x y) :
    evalPoint E D (.some x y h) = D.eval x y := rfl

/-- Pair-based evaluation and `ECPoint` evaluation agree on `E.points`. -/
theorem evalPoint_affine (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    evalPoint E D (ECPoint.affine E P.1 P.2) = D.eval P.1 P.2 := by
  have hns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  rw [ECPoint.affine_of_nonsingular E hns]
  rcases P with ⟨x, y⟩
  rfl

end CoordRingElt

/-- Third-intersection point of the chord/tangent line through `A₀`, `A₁`
    with the curve `E`. Operates on raw `ZMod q × ZMod q` pairs and
    returns either an `affine` point (when the third intersection is
    finite) or `infinity` (vertical line / 2-torsion case). The result
    is a junk-value coordinate pair — turned into a group element only
    via `thirdPoint_eq_neg_add` (which requires on-curve hypotheses).
    Defined here because downstream geometric lemmas reason about its
    coordinates directly. -/
noncomputable def thirdPoint (E : ECSetup) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    Option (ZMod E.q × ZMod E.q) :=
  if A₀.1 = A₁.1 then
    if A₀.2 = A₁.2 then
      if A₀.2 = 0 then none
      else
        let lam := (3 * A₀.1 ^ 2 + E.curveA) * (2 * A₀.2)⁻¹
        let mu := A₀.2 - lam * A₀.1
        let x₂ := lam ^ 2 - 2 * A₀.1
        let y₂ := lam * x₂ + mu
        some (x₂, y₂)
    else
      none
  else
    let lam := (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹
    let mu := A₀.2 - lam * A₀.1
    let x₂ := lam ^ 2 - A₀.1 - A₁.1
    let y₂ := lam * x₂ + mu
    some (x₂, y₂)

end Divisor
