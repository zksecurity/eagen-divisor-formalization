/-
  Divisor/CoordRingEltC/Bridge.lean

  Bridges from the computable `CoordRingEltC` layer to the existing
  `Polynomial`-valued `CoordRingElt`.  The forward direction
  (`toCoordRingElt`) is noncomputable, but it lets every operation
  on `CoordRingEltC` be related to its `CoordRingElt` counterpart.
-/
import Divisor.CoordRingEltC
import Divisor.IncrementalConstruction
import Divisor.OrdP.Uniformizer
import Divisor.CubicIntersection

open Polynomial

namespace Divisor

namespace CoordRingEltC

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Bridge: interpret a `CoordRingEltC` as a `CoordRingElt` via
    `CoeffPoly.toPolynomial` on both components. -/
noncomputable def toCoordRingElt (D : CoordRingEltC q) : CoordRingElt q :=
  ⟨D.a.toPolynomial, D.b.toPolynomial⟩

@[simp] theorem toCoordRingElt_a (D : CoordRingEltC q) :
    D.toCoordRingElt.a = D.a.toPolynomial := rfl

@[simp] theorem toCoordRingElt_b (D : CoordRingEltC q) :
    D.toCoordRingElt.b = D.b.toPolynomial := rfl

/-! ### `divLin` bridge -/

theorem divLin_toCoordRingElt (D : CoordRingEltC q) (x₀ : ZMod q) :
    (D.divLin x₀).toCoordRingElt = D.toCoordRingElt.divLin x₀ := by
  unfold CoordRingEltC.divLin CoordRingElt.divLin
  show (⟨(D.a.divXSubC x₀).toPolynomial, (D.b.divXSubC x₀).toPolynomial⟩ : CoordRingElt q)
    = ⟨D.a.toPolynomial /ₘ (Polynomial.X - Polynomial.C x₀),
        D.b.toPolynomial /ₘ (Polynomial.X - Polynomial.C x₀)⟩
  congr 1 <;> exact CoeffPoly.toPolynomial_divXSubC _ x₀

/-! ### `curveX` bridge -/

/-- `CoeffPoly` representation of `curveX E = X³ + A·X + B`. -/
def curveX_coeff (curveA curveB : ZMod q) : CoeffPoly q :=
  ⟨[curveB, curveA, 0, 1]⟩

/-- `toPolynomial` of `curveX_coeff` is `X^3 + C A * X + C B`. -/
theorem toPolynomial_curveX_coeff (curveA curveB : ZMod q) :
    (curveX_coeff curveA curveB).toPolynomial
      = Polynomial.X^3 + Polynomial.C curveA * Polynomial.X + Polynomial.C curveB := by
  apply Polynomial.ext
  intro n
  rw [CoeffPoly.toPolynomial_coeff]
  -- Compute both sides at each n.
  match n with
  | 0 =>
    show (curveX_coeff curveA curveB).coeff 0 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  | 1 =>
    show (curveX_coeff curveA curveB).coeff 1 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | 2 =>
    show (curveX_coeff curveA curveB).coeff 2 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | 3 =>
    show (curveX_coeff curveA curveB).coeff 3 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_X]
  | k + 4 =>
    show (curveX_coeff curveA curveB).coeff (k + 4) = _
    have h_left : (curveX_coeff curveA curveB).coeff (k + 4) = 0 := by
      simp [curveX_coeff, CoeffPoly.coeff]
    rw [h_left]
    have h_X3 : (Polynomial.X^3 : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_X_pow]; simp
    have h_AX : (Polynomial.C curveA * Polynomial.X : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]
      simp
    have h_B : (Polynomial.C curveB : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_C]; simp
    rw [Polynomial.coeff_add, Polynomial.coeff_add, h_X3, h_AX, h_B]
    ring

/-- `toPolynomial (curveX_coeff E.curveA E.curveB) = curveX E`. -/
theorem toPolynomial_curveX_coeff_eq_curveX (E : ECSetup) :
    (curveX_coeff E.curveA E.curveB).toPolynomial = curveX E := by
  rw [toPolynomial_curveX_coeff]
  rfl

/-! ### `mul` bridge -/

theorem mul_toCoordRingElt (E : ECSetup) (D₁ D₂ : CoordRingEltC E.q) :
    (CoordRingEltC.mul E.curveA E.curveB D₁ D₂).toCoordRingElt
      = mulCoordRingElt E D₁.toCoordRingElt D₂.toCoordRingElt := by
  unfold CoordRingEltC.mul mulCoordRingElt
  -- LHS: (⟨[curveB, curveA, 0, 1]⟩ : CoeffPoly).toPolynomial = curveX E.
  -- We restate the lhs using curveX_coeff so the curveX_coeff bridge fires.
  show (⟨D₁.a * D₂.a + D₁.b * D₂.b * curveX_coeff E.curveA E.curveB,
          D₁.a * D₂.b + D₂.a * D₁.b⟩ : CoordRingEltC E.q).toCoordRingElt
      = ⟨D₁.toCoordRingElt.a * D₂.toCoordRingElt.a
            + D₁.toCoordRingElt.b * D₂.toCoordRingElt.b * curveX E,
          D₁.toCoordRingElt.a * D₂.toCoordRingElt.b
            + D₂.toCoordRingElt.a * D₁.toCoordRingElt.b⟩
  unfold toCoordRingElt
  congr 1
  · rw [CoeffPoly.toPolynomial_add, CoeffPoly.toPolynomial_mul,
        CoeffPoly.toPolynomial_mul, CoeffPoly.toPolynomial_mul,
        toPolynomial_curveX_coeff_eq_curveX]
  · rw [CoeffPoly.toPolynomial_add, CoeffPoly.toPolynomial_mul,
        CoeffPoly.toPolynomial_mul]

end CoordRingEltC

end Divisor
