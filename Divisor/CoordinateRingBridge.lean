/-
  Divisor/CoordinateRingBridge.lean

  Bridge between the project's `CoordRingElt` (a pair of polynomials
  `(a, b)` representing the regular function `D = a(X) - b(X)·Y` on
  an elliptic curve `E`) and mathlib's affine `CoordinateRing` of `E`.

  This file is the foundation for the discharge of
  `CoordRingElt.divisorClass_isPrincipal_of_not_const_unit` (see
  `axioms/divisorClass_isPrincipal.md`). It supplies:

  * `CoordRingElt.toBivar` — the bivariate polynomial form
    `C D.a − C D.b · Y` in `(ZMod q)[X][Y]`.
  * `CoordRingElt.toCoordinateRing` — its image in
    `E.toW.toAffine.CoordinateRing` via `CoordinateRing.mk`.
  * `CoordRingElt.toBivar_evalEval` — the bivariate evaluation
    matches the project's scalar `D.eval x y`.
  * `CoordRingElt.toCoordinateRing_eq_smul_basis` — explicit basis
    decomposition `D = D.a · 1 + (−D.b) · Y` in the coordinate ring.
  * `CoordRingElt.toCoordinateRing_ne_zero` — nonzero coordinate-ring
    image whenever `(D.a, D.b) ≠ (0, 0)`, via mathlib's
    `smul_basis_eq_zero` rank-2 freeness.

  Subsequent files will add the XYIdeal-membership characterisation
  and the local-order ↔ recursive-`ordAt` compatibility theorem.
-/
import Divisor.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Polynomial Polynomial.Bivariate
open WeierstrassCurve WeierstrassCurve.Affine

namespace Divisor

namespace CoordRingElt

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Bivariate polynomial form of `D = a(X) − b(X)·Y` viewed as an
element of `(ZMod q)[X][Y]`. The outer variable is `Y`. -/
noncomputable def toBivar (D : CoordRingElt q) : (ZMod q)[X][Y] :=
  Polynomial.C D.a - Polynomial.C D.b * Polynomial.X

@[simp] theorem toBivar_eval_C (D : CoordRingElt q) (y : ZMod q) :
    D.toBivar.eval (Polynomial.C y) = D.a - D.b * Polynomial.C y := by
  unfold toBivar
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]

/-- The bivariate evaluation of `D.toBivar` at `(x, y)` matches the
project's scalar `D.eval x y`. -/
@[simp] theorem toBivar_evalEval (D : CoordRingElt q) (x y : ZMod q) :
    D.toBivar.evalEval x y = D.eval x y := by
  unfold Polynomial.evalEval CoordRingElt.eval
  rw [toBivar_eval_C, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]

end CoordRingElt

variable (E : ECSetup)

namespace CoordRingElt

/-- The class of `D = a(X) − b(X)·Y` in mathlib's affine coordinate
ring `E.toW.toAffine.CoordinateRing`. -/
noncomputable def toCoordinateRing (D : CoordRingElt E.q) :
    E.toW.toAffine.CoordinateRing :=
  CoordinateRing.mk E.toW.toAffine D.toBivar

/-- `D.toCoordinateRing` decomposes in the canonical `{1, Y}` basis
of `E.toW.toAffine.CoordinateRing` over `(ZMod E.q)[X]` as
`D.a · 1 + (-D.b) · Y`. -/
theorem toCoordinateRing_eq_smul_basis (D : CoordRingElt E.q) :
    D.toCoordinateRing E
      = D.a • (1 : E.toW.toAffine.CoordinateRing)
        + (-D.b) • CoordinateRing.mk E.toW.toAffine Polynomial.X := by
  unfold toCoordinateRing toBivar
  rw [map_sub, map_mul, CoordinateRing.smul, CoordinateRing.smul,
      Polynomial.C_neg, map_neg, mul_one, neg_mul, sub_eq_add_neg]

/-- `D.toCoordinateRing ≠ 0` whenever `D` has a nonzero polynomial
component. Proof: the basis decomposition
`D = D.a · 1 + (−D.b) · Y` is in mathlib's free rank-2 basis, so
`D = 0` would force both `D.a = 0` and `−D.b = 0` by
`smul_basis_eq_zero`. -/
theorem toCoordinateRing_ne_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    D.toCoordinateRing E ≠ 0 := by
  intro hZero
  rw [toCoordinateRing_eq_smul_basis] at hZero
  obtain ⟨ha, hb⟩ := CoordinateRing.smul_basis_eq_zero hZero
  exact hD ⟨ha, neg_eq_zero.mp hb⟩

end CoordRingElt

end Divisor
