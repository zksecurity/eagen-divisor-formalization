/-
  Divisor/GeomBase.lean

  Shared algebraic-closure definitions for the geometric soundness path.

  This file contains only the base-changed curve model, geometric
  evaluation, and finite geometric zero support. The local-order
  multiplicity API lives in `GeomLocalOrder`.
-/
import Divisor.BetaConstructive
import Divisor.FourVarPoly
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Algebraic-closure model -/

/-- The algebraic closure of the base field of `E`. -/
abbrev Fqbar : Type := AlgebraicClosure (ZMod E.q)

/-- Four-variable polynomials after base-change to `F_qbar`. -/
abbrev FourVarPolyBar : Type := MvPolynomial (Fin 4) (Fqbar E)

/-- Coefficient base-change for the existing four-variable polynomial ring. -/
noncomputable def baseChangeFourVar (f : FourVarPoly E.q) : FourVarPolyBar E :=
  MvPolynomial.map (algebraMap (ZMod E.q) (Fqbar E)) f

/-- Embed a base-field scalar into `F_qbar`. -/
noncomputable def fqToBar (x : ZMod E.q) : Fqbar E :=
  algebraMap (ZMod E.q) (Fqbar E) x

/-- The norm polynomial after coefficient base-change to `F_qbar`. -/
noncomputable def normPolyBar (D : CoordRingElt E.q) : Polynomial (Fqbar E) :=
  Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) (normPoly E D)

/-- An affine geometric point on the base-changed short Weierstrass curve. -/
structure GeomPoint where
  x : Fqbar E
  y : Fqbar E
  onCurve :
    y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB

namespace GeomPoint

/-- The other sheet in the affine fiber above the same `x` coordinate. -/
noncomputable def conjugate (Q : GeomPoint E) : GeomPoint E :=
  ⟨Q.x, -Q.y, by
    rw [show (-Q.y) ^ 2 = Q.y ^ 2 by ring]
    exact Q.onCurve⟩

@[simp] theorem conjugate_x (Q : GeomPoint E) :
    (Q.conjugate E).x = Q.x := rfl

@[simp] theorem conjugate_y (Q : GeomPoint E) :
    (Q.conjugate E).y = -Q.y := rfl

end GeomPoint

namespace CoordRingElt

/-- Evaluation of a coordinate-ring element at a geometric point. -/
noncomputable def geomEval (D : CoordRingElt E.q) (Q : GeomPoint E) : Fqbar E :=
  D.a.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x
    - D.b.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x * Q.y

end CoordRingElt

/-! ## Geometric zero support -/

/-- A geometric zero maps to a root of the base-changed norm polynomial. -/
theorem normPolyBar_eval_zero_of_geomEval_zero
    (D : CoordRingElt E.q) (Q : GeomPoint E)
    (hQ : D.geomEval E Q = 0) :
    (normPolyBar E D).eval Q.x = 0 := by
  unfold CoordRingElt.geomEval normPolyBar at *
  rw [normPoly_eq]
  simp_all +decide [sub_eq_iff_eq_add, Polynomial.eval_map]
  unfold curveX
  simp +decide [mul_pow, Q.onCurve]
  exact Or.inl rfl

private theorem geom_zero_set_finite'
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    Set.Finite {Q : GeomPoint E | D.geomEval E Q = 0} := by
  have hne : normPolyBar E D ≠ 0 := by
    unfold normPolyBar
    exact Polynomial.map_ne_zero (normPoly_ne_zero E D hDnz)
  have h_roots_finite : Set.Finite {x : Fqbar E | (normPolyBar E D).IsRoot x} := by
    convert ((normPolyBar E D).roots.toFinset |> Finset.finite_toSet) using 1
    ext x
    simp [Polynomial.mem_roots hne]
  have h_fiber_finite : ∀ x : Fqbar E,
      Set.Finite {y : Fqbar E |
        y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB} := by
    intro x
    set b := x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB
    have h_poly : ∀ y : Fqbar E, y ^ 2 = b →
        y ∈ (Polynomial.X ^ 2 - Polynomial.C b : Polynomial (Fqbar E)).roots.toFinset := by
      intro y hy
      simp only [Multiset.mem_toFinset]
      rw [Polynomial.mem_roots (by exact ne_of_apply_ne Polynomial.natDegree (by norm_num))]
      simp [Polynomial.IsRoot, sub_eq_zero]
      exact hy
    exact Set.Finite.subset (Multiset.finite_toSet _) h_poly
  have h_image_finite : Set.Finite
      (Set.image (fun Q : GeomPoint E => (Q.x, Q.y))
        {Q : GeomPoint E | D.geomEval E Q = 0}) := by
    apply Set.Finite.subset
      (h_roots_finite.biUnion fun x _ => (h_fiber_finite x).image fun y => (x, y))
    intro p hp
    simp only [Set.mem_image, Set.mem_setOf_eq] at hp
    obtain ⟨Q, hQ, hQp⟩ := hp
    rw [← hQp]
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq]
    exact
      ⟨Q.x, normPolyBar_eval_zero_of_geomEval_zero E D Q hQ,
        Q.y, Q.onCurve, rfl, rfl⟩
  exact h_image_finite.of_finite_image
    (fun Q1 _ Q2 _ h => by
      cases Q1
      cases Q2
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      rfl)

/--
Finite geometric zero support.

This is support-only; true local multiplicities are supplied by
`GeomLocalOrder`.
-/
theorem exists_geometric_zero_support
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ support : Finset (GeomPoint E),
      (∀ Q ∈ support, D.geomEval E Q = 0) ∧
      (∀ Q, D.geomEval E Q = 0 → Q ∈ support) := by
  have hfin := geom_zero_set_finite' E D hDnz
  exact ⟨hfin.toFinset,
    fun Q hQ => by rwa [Set.Finite.mem_toFinset] at hQ,
    fun Q hQ => by rwa [Set.Finite.mem_toFinset]⟩

end Divisor
