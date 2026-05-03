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

/-- `D.toCoordinateRing E ∈ XYIdeal W' x (C y)` when `D.eval x y = 0`.

This is the forward direction of the membership characterisation
needed for the local-order ↔ recursive-`ordAt` compatibility step.
The backward direction (under the on-curve hypothesis) is
`toCoordinateRing_mem_XYIdeal_iff` below. -/
theorem toCoordinateRing_mem_XYIdeal_of_eval_zero
    (D : CoordRingElt E.q) {x y : ZMod E.q} (h : D.eval x y = 0) :
    D.toCoordinateRing E
      ∈ CoordinateRing.XYIdeal E.toW.toAffine x (Polynomial.C y) := by
  have h1 : D.toBivar.evalEval x y = 0 := by rw [toBivar_evalEval]; exact h
  have h2 : D.toBivar ∈
      (Ideal.span ({Polynomial.C (Polynomial.X - Polynomial.C x),
                    Polynomial.X - Polynomial.C (Polynomial.C y)}
                   : Set ((ZMod E.q)[X][Y]))) :=
    Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h1
  have h3 :=
    Ideal.mem_map_of_mem (CoordinateRing.mk E.toW.toAffine) h2
  rw [Ideal.map_span, Set.image_pair] at h3
  exact h3

/-- The on-curve curve-equation hypothesis as a bivariate evaluation
fact: for `(x, y) ∈ E.points`,
`(W'.polynomial.eval (C y)).eval x = 0`. -/
theorem polynomial_evalEval_eq_zero_of_mem_points
    {x y : ZMod E.q} (hP : (x, y) ∈ E.points) :
    (E.toW.toAffine.polynomial.eval (Polynomial.C y)).eval x = 0 := by
  have := (E.equation_iff x y).mpr (E.hOnCurve _ hP)
  rwa [WeierstrassCurve.Affine.Equation, Polynomial.evalEval] at this

/-- **`D.toCoordinateRing` membership in `XYIdeal` ↔ `D` vanishes at
`(x, y)`**, given `(x, y) ∈ E.points`.

This is the bridge between the project's vanishing condition
`D.eval x y = 0` and the algebraic-geometry membership in the
maximal-ideal `XYIdeal` of mathlib's affine coordinate ring. -/
theorem toCoordinateRing_mem_XYIdeal_iff
    (D : CoordRingElt E.q) {x y : ZMod E.q} (hP : (x, y) ∈ E.points) :
    D.toCoordinateRing E
        ∈ CoordinateRing.XYIdeal E.toW.toAffine x (Polynomial.C y) ↔
      D.eval x y = 0 := by
  classical
  refine ⟨?_, toCoordinateRing_mem_XYIdeal_of_eval_zero E D⟩
  intro hMem
  -- Lift the membership to a representation modulo `⟨W'.polynomial⟩`.
  unfold CoordinateRing.XYIdeal CoordinateRing.XClass
    CoordinateRing.YClass CoordRingElt.toCoordinateRing at hMem
  rw [Ideal.mem_span_pair] at hMem
  obtain ⟨α, β, hαβ⟩ := hMem
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective α
  obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective β
  -- `mk W' (a*C(X-Cx) + b*(X-C(Cy))) = mk W' D.toBivar`
  rw [← map_mul, ← map_mul, ← map_add, AdjoinRoot.mk_eq_mk] at hαβ
  -- `W'.polynomial ∣ (a*C(X-Cx) + b*(X-C(Cy))) - D.toBivar`
  obtain ⟨c, hc⟩ := hαβ
  -- `D.toBivar = (a*C(X-Cx) + b*(X-C(Cy))) - c * W'.polynomial`
  have hRewrite : D.toBivar
      = a * Polynomial.C (Polynomial.X - Polynomial.C x)
        + b * (Polynomial.X - Polynomial.C (Polynomial.C y))
        - c * E.toW.toAffine.polynomial := by
    linear_combination -hc
  -- Apply `evalEval x y` to both sides; the right factors all vanish.
  have h_eval := congr_arg (fun p => Polynomial.evalEval x y p) hRewrite
  have h_curveEval :
      Polynomial.evalEval x y E.toW.toAffine.polynomial = 0 := by
    have := polynomial_evalEval_eq_zero_of_mem_points E hP
    rwa [Polynomial.evalEval]
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_sub,
             Polynomial.evalEval_mul, Polynomial.evalEval_C,
             Polynomial.evalEval_X, Polynomial.eval_sub,
             Polynomial.eval_X, Polynomial.eval_C, sub_self,
             mul_zero, zero_add, h_curveEval, toBivar_evalEval] at h_eval
  exact h_eval
