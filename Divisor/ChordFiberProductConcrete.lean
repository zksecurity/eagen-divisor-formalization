/-
  Divisor/ChordFiberProductConcrete.lean

  Production-level concrete candidate for the chord-fiber product,
  defined as the X-resultant of the chord cubic and the D-on-line
  polynomial in `(ZMod E.q)[Z][X]`. Re-reads as a polynomial in the
  chord-intercept variable `Z = μ`.

  This module contains the *axiom-free* concrete plumbing:
  the bivariate setup, the bar-level base-change, the resultant
  candidate `chord_fiber_product_concrete`, the four already-proved
  evaluation/factorisation helpers (`*_eval`,
  `*_eval_eq_prod_split`, `*_bar_eval`, `*_bar_eval_eq_prod`), and
  the now-proved non-vanishing theorem
  `chord_fiber_product_concrete_ne_zero`.  The three remaining
  sorry-bearing obligations against this candidate live in
  `Divisor/Sketch/ChordFiberProductConcrete.lean`.

  Imports are intentionally narrow:
  * `Divisor.Defs` — `CoordRingElt`, `ECSetup`, base-ring setup.
  * `Divisor.SlopeDist` — `intersectionPoly` and its degree bounds.
  * `Divisor.GeomBase` — `Fqbar`, `fqToBar`, `geomEval`, `GeomPoint`,
    `exists_geometric_zero_support`.
  * `Divisor.GeomLocalOrder` — `GeometricDivisorData` and friends, used by
    the non-vanishing proof.
  * Mathlib resultant API.

  In particular this file does **not** import `Divisor.Axioms` or
  any module that transitively imports
  `AxiomChordFiberProductEqNormZUnderSplit`. -/
import Divisor.Defs
import Divisor.SlopeDist
import Divisor.GeomBase
import Divisor.GeomLocalOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Bivariate setup

We work in `(ZMod E.q)[Z][X]` where:
* outer `Polynomial.X` (in `(ZMod E.q)[Z][X]`) = chord x-variable;
* inner `Polynomial.X` (in `(ZMod E.q)[Z]`) = chord intercept `Z = μ`.

The chord cubic over the inner `Z`-ring:
  `f(X, Z) = X³ − λ² X² + (A − 2λZ) X + (B − Z²)`

The D-on-line lift:
  `g(X, Z) = D.a(X) − D.b(X) (λX + Z)`

The candidate chord-fiber product is `Res_X(f, g) ∈ (ZMod E.q)[Z]`,
which reads as a polynomial in the chord-intercept `μ`. -/

/-- The chord cubic `X³ − λ² X² + (A − 2λZ) X + (B − Z²)` in the bivariate
ring `(ZMod E.q)[Z][X]`. The outer `X` is the chord x-variable; the inner
`Polynomial.X` is the chord intercept `Z`. -/
noncomputable def chordCubicBiv (lam : ZMod E.q) :
    Polynomial (Polynomial (ZMod E.q)) :=
  Polynomial.X ^ 3
    - Polynomial.C (Polynomial.C (lam ^ 2)) * Polynomial.X ^ 2
    + Polynomial.C (Polynomial.C E.curveA - Polynomial.C (2 * lam) * Polynomial.X)
        * Polynomial.X
    + Polynomial.C (Polynomial.C E.curveB - Polynomial.X ^ 2)

/-- The D-on-line polynomial `D.a(X) − D.b(X) · (λX + Z)` in
`(ZMod E.q)[Z][X]`. -/
noncomputable def DLineBiv (lam : ZMod E.q) (D : CoordRingElt E.q) :
    Polynomial (Polynomial (ZMod E.q)) :=
  D.a.map Polynomial.C
    - D.b.map Polynomial.C *
        (Polynomial.C (Polynomial.C lam) * Polynomial.X
          + Polynomial.C Polynomial.X)

/-- Coefficient base-change for the inner polynomial ring from `F_q` to
`F_qbar`. -/
private noncomputable abbrev toBarPolyHom :
    Polynomial (ZMod E.q) →+* Polynomial (Fqbar E) :=
  Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E))

/-- Base-changing a base-field polynomial whose coefficients were embedded
as constants, then specialising the inner variable, is ordinary base-change. -/
theorem eval₂_mapC_toBar_evalRingHom (μ x : Fqbar E)
    (p : Polynomial (ZMod E.q)) :
    Polynomial.eval₂ (Polynomial.evalRingHom μ) x
        ((p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
          (toBarPolyHom E)) =
      p.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) x := by
  rw [← Polynomial.eval_map]
  have hmap :
      ((p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
          (toBarPolyHom E)).map (Polynomial.evalRingHom μ) =
        p.map (algebraMap (ZMod E.q) (Fqbar E)) := by
    ext n
    simp [toBarPolyHom]
  rw [hmap]
  rw [Polynomial.eval_map]

/-- The bivariate chord cubic after coefficient base-change to
`F_qbar[Z][X]`. -/
noncomputable def chordCubicBivBar (lam : ZMod E.q) :
    Polynomial (Polynomial (Fqbar E)) :=
  (chordCubicBiv E lam).map (toBarPolyHom E)

/-- The bivariate D-on-line polynomial after coefficient base-change to
`F_qbar[Z][X]`. -/
noncomputable def DLineBivBar (lam : ZMod E.q) (D : CoordRingElt E.q) :
    Polynomial (Polynomial (Fqbar E)) :=
  (DLineBiv E lam D).map (toBarPolyHom E)

/-- The chord cubic over `F_qbar` after specialising the intercept
variable to `μ`. -/
noncomputable def chordCubicBar (lam : ZMod E.q) (μ : Fqbar E) :
    Polynomial (Fqbar E) :=
  (chordCubicBivBar E lam).map (Polynomial.evalRingHom μ)

/-- The D-on-line polynomial over `F_qbar` after specialising the
intercept variable to `μ`. -/
noncomputable def DLineBar (lam : ZMod E.q) (D : CoordRingElt E.q)
    (μ : Fqbar E) : Polynomial (Fqbar E) :=
  (DLineBivBar E lam D).map (Polynomial.evalRingHom μ)

/-- Evaluating the specialised bar-level D-on-line polynomial is the same
as evaluating `D` at the geometric point on the line `y = λx + μ`. -/
theorem DLineBar_eval_eq_geomEval (lam : ZMod E.q)
    (D : CoordRingElt E.q) (μ x : Fqbar E)
    (hOnE :
      (fqToBar E lam * x + μ) ^ 2 =
        x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB) :
    (DLineBar E lam D μ).eval x =
      D.geomEval E ⟨x, fqToBar E lam * x + μ, hOnE⟩ := by
  unfold DLineBar DLineBivBar DLineBiv toBarPolyHom
    CoordRingElt.geomEval fqToBar
  simp [Polynomial.eval_map, eval₂_mapC_toBar_evalRingHom]

/-- **Concrete chord-fiber-product candidate.** The X-resultant of the
chord cubic and the D-on-line lift, viewed as a polynomial in the
chord-intercept variable `μ`. -/
noncomputable def chord_fiber_product_concrete
    (lam : ZMod E.q) (D : CoordRingElt E.q) : Polynomial (ZMod E.q) :=
  Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)

/-! ## Map of bivariate polynomials under `evalRingHom μ` -/

/-- The composition `(evalRingHom μ) ∘ C` is the identity on the inner
ring. -/
private lemma evalRingHom_comp_C_eq_id (μ : ZMod E.q) :
    (Polynomial.evalRingHom μ).comp (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))
      = RingHom.id (ZMod E.q) := by
  ext r
  simp [Polynomial.coe_evalRingHom]

/-- `(p.map C).map (evalRingHom μ) = p` for any base-field polynomial `p`. -/
private lemma mapC_map_evalRingHom (μ : ZMod E.q) (p : Polynomial (ZMod E.q)) :
    (p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
        (Polynomial.evalRingHom μ) = p := by
  rw [Polynomial.map_map, evalRingHom_comp_C_eq_id, Polynomial.map_id]

/-- Specialising `chordCubicBiv` at `Z = μ` recovers the project's
`intersectionPoly`. -/
lemma chordCubicBiv_map_evalRingHom (lam μ : ZMod E.q) :
    (chordCubicBiv E lam).map (Polynomial.evalRingHom μ)
      = Divisor.intersectionPoly E lam μ := by
  unfold chordCubicBiv Divisor.intersectionPoly
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C]
  simp [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]

/-- Specialising `DLineBiv` at `Z = μ` recovers the rational
"D evaluated on the chord line `y = λx + μ`" polynomial. -/
lemma DLineBiv_map_evalRingHom (lam μ : ZMod E.q) (D : CoordRingElt E.q) :
    (DLineBiv E lam D).map (Polynomial.evalRingHom μ)
      = D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ) := by
  unfold DLineBiv
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
             Polynomial.map_C, Polynomial.map_X,
             mapC_map_evalRingHom, Polynomial.coe_evalRingHom,
             Polynomial.eval_C, Polynomial.eval_X]

/-- Pointwise specialisation: evaluating `chord_fiber_product_concrete`
at a base-field intercept `μ ∈ ZMod E.q` reduces to the resultant of the
chord cubic at `μ` (which is `intersectionPoly E lam μ`) against the
D-on-line polynomial at `μ`.

*Plumbing*: instance of `Polynomial.resultant_map_map` for the evaluation
hom `Polynomial.X ↦ μ`, plus normalisation of the bivariate `chordCubicBiv`
and `DLineBiv` under that homomorphism. The natDegrees are kept as the
*bivariate* natDegrees (rather than the post-specialisation natDegrees,
which would generally differ when the leading coefficient happens to vanish
at `μ`). -/
theorem chord_fiber_product_concrete_eval (lam μ : ZMod E.q)
    (D : CoordRingElt E.q) :
    (chord_fiber_product_concrete E lam D).eval μ
      = Polynomial.resultant (Divisor.intersectionPoly E lam μ)
          (D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ))
          (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree := by
  unfold chord_fiber_product_concrete
  rw [show ((Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)).eval μ
        = (Polynomial.evalRingHom μ)
            (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D))) by
        rw [Polynomial.coe_evalRingHom]]
  have hMap := Polynomial.resultant_map_map (φ := Polynomial.evalRingHom μ)
    (f := chordCubicBiv E lam) (g := DLineBiv E lam D)
    (m := (chordCubicBiv E lam).natDegree) (n := (DLineBiv E lam D).natDegree)
  rw [← hMap, chordCubicBiv_map_evalRingHom E lam μ,
      DLineBiv_map_evalRingHom E lam μ D]

/-- The chord cubic `intersectionPoly` is monic of degree 3. -/
private lemma intersectionPoly_natDegree (lam μ : ZMod E.q) :
    (Divisor.intersectionPoly E lam μ).natDegree = 3 := by
  refine le_antisymm (Divisor.natDegree_intersectionPoly_le E lam μ) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  show (Divisor.intersectionPoly E lam μ).coeff 3 ≠ 0
  unfold Divisor.intersectionPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
             Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
             Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

/-- The chord cubic `intersectionPoly` is monic. -/
private lemma intersectionPoly_leadingCoeff (lam μ : ZMod E.q) :
    (Divisor.intersectionPoly E lam μ).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, intersectionPoly_natDegree]
  unfold Divisor.intersectionPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
             Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
             Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

/-- The bivariate chord cubic also has natDegree 3. -/
private lemma chordCubicBiv_natDegree (lam : ZMod E.q) :
    (chordCubicBiv E lam).natDegree = 3 := by
  -- Same coefficient inspection over the inner ring `(ZMod E.q)[X]`.
  refine le_antisymm ?_ ?_
  · -- natDegree ≤ 3
    unfold chordCubicBiv
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact (Polynomial.natDegree_X_pow_le 3)
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (Polynomial.natDegree_X_pow_le 2 |>.trans (by omega))
      · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        exact Polynomial.natDegree_X_le.trans (by omega)
    · exact (Polynomial.natDegree_C _).le.trans (by omega)
  · -- natDegree ≥ 3 via coeff at 3 = 1
    refine Polynomial.le_natDegree_of_ne_zero ?_
    show (chordCubicBiv E lam).coeff 3 ≠ 0
    unfold chordCubicBiv
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
               Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
               Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num

/-- Specialising `DLineBiv` cannot raise the natDegree (mapping a polynomial
through a `RingHom` is degree-non-increasing). -/
private lemma DLine_specialized_natDegree_le (lam μ : ZMod E.q)
    (D : CoordRingElt E.q) :
    (D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ)).natDegree
      ≤ (DLineBiv E lam D).natDegree := by
  rw [← DLineBiv_map_evalRingHom E lam μ D]
  exact Polynomial.natDegree_map_le

/-- The coefficient of `X^3` in the base-changed/specialised chord cubic is
one. -/
private lemma chordCubicBar_coeff_three (lam : ZMod E.q) (μ : Fqbar E) :
    (chordCubicBar E lam μ).coeff 3 = 1 := by
  unfold chordCubicBar chordCubicBivBar chordCubicBiv toBarPolyHom
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  rw [show
      ((Polynomial.C ((algebraMap (ZMod E.q) (Fqbar E)) lam) ^ 2 *
          Polynomial.X ^ 2 : Polynomial (Fqbar E)).coeff 3) = 0 by
        rw [show 3 = 1 + 2 by norm_num]
        rw [Polynomial.coeff_mul_X_pow]
        rw [← Polynomial.C_pow]
        rw [Polynomial.coeff_C]
        norm_num]
  rw [show (((Polynomial.C μ : Polynomial (Fqbar E)) ^ 2).coeff 3) = 0 by
        rw [← Polynomial.C_pow]
        rw [Polynomial.coeff_C]
        norm_num]
  ring

/-- The base-changed/specialised chord cubic has natDegree 3. -/
private lemma chordCubicBar_natDegree (lam : ZMod E.q) (μ : Fqbar E) :
    (chordCubicBar E lam μ).natDegree = 3 := by
  refine le_antisymm ?_ ?_
  · calc
      (chordCubicBar E lam μ).natDegree
          ≤ (chordCubicBivBar E lam).natDegree := by
            unfold chordCubicBar
            exact Polynomial.natDegree_map_le
      _ ≤ (chordCubicBiv E lam).natDegree := by
            unfold chordCubicBivBar
            exact Polynomial.natDegree_map_le
      _ = 3 := chordCubicBiv_natDegree E lam
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [chordCubicBar_coeff_three]
    norm_num

/-- The base-changed/specialised chord cubic is monic. -/
private lemma chordCubicBar_leadingCoeff (lam : ZMod E.q) (μ : Fqbar E) :
    (chordCubicBar E lam μ).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, chordCubicBar_natDegree,
      chordCubicBar_coeff_three]

/-- Base-changing and specialising `DLineBiv` cannot raise the natDegree. -/
private lemma DLineBar_natDegree_le (lam : ZMod E.q) (D : CoordRingElt E.q)
    (μ : Fqbar E) :
    (DLineBar E lam D μ).natDegree ≤ (DLineBiv E lam D).natDegree := by
  calc
    (DLineBar E lam D μ).natDegree
        ≤ (DLineBivBar E lam D).natDegree := by
          unfold DLineBar
          exact Polynomial.natDegree_map_le
    _ ≤ (DLineBiv E lam D).natDegree := by
          unfold DLineBivBar
          exact Polynomial.natDegree_map_le

/-- Resultant-as-product: when the chord cubic at `μ` splits, the
specialised resultant equals the product of `D`-on-line evaluations at
each chord root.

*Plumbing*: direct call to mathlib's `Polynomial.resultant_eq_prod_eval`
on `intersectionPoly E lam μ` (monic of degree 3). -/
theorem chord_fiber_product_concrete_eval_eq_prod_split
    (lam μ : ZMod E.q) (D : CoordRingElt E.q)
    (hSplit : (Divisor.intersectionPoly E lam μ).Splits) :
    (chord_fiber_product_concrete E lam D).eval μ
      = ((Divisor.intersectionPoly E lam μ).roots.map
          (fun x => D.eval x (lam * x + μ))).prod := by
  rw [chord_fiber_product_concrete_eval E lam μ D]
  -- Align the chord cubic's natDegree with intersectionPoly's.
  rw [show (chordCubicBiv E lam).natDegree = (Divisor.intersectionPoly E lam μ).natDegree by
        rw [chordCubicBiv_natDegree, intersectionPoly_natDegree]]
  -- Apply mathlib's resultant_eq_prod_eval; the leading coefficient is 1.
  rw [Polynomial.resultant_eq_prod_eval _ _ _
        (DLine_specialized_natDegree_le E lam μ D) hSplit,
      intersectionPoly_leadingCoeff, one_pow, one_mul]
  -- The `g.eval x` simplifies to the chord-line evaluation.
  congr 1
  refine Multiset.map_congr rfl ?_
  intro x _
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, CoordRingElt.eval]

/-- Bar-level specialisation: evaluating the base-changed concrete
chord-fiber product at `μ : F_qbar` is the resultant of the base-changed
and specialised chord cubic against the specialised D-on-line polynomial. -/
theorem chord_fiber_product_concrete_bar_eval
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : Fqbar E) :
    Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D))
      =
        Polynomial.resultant (chordCubicBar E lam μ) (DLineBar E lam D μ)
          (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree := by
  unfold chord_fiber_product_concrete chordCubicBar DLineBar
    chordCubicBivBar DLineBivBar
  rw [show Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)
            (chordCubicBiv E lam).natDegree
            (DLineBiv E lam D).natDegree))
      =
        (Polynomial.evalRingHom μ)
          ((Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))
            (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)
              (chordCubicBiv E lam).natDegree
              (DLineBiv E lam D).natDegree)) by
      rw [Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]]
  rw [← Polynomial.resultant_map_map
    (φ := Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))
    (f := chordCubicBiv E lam) (g := DLineBiv E lam D)
    (m := (chordCubicBiv E lam).natDegree) (n := (DLineBiv E lam D).natDegree)]
  rw [← Polynomial.resultant_map_map
    (φ := Polynomial.evalRingHom μ)
    (f := (chordCubicBiv E lam).map (toBarPolyHom E))
    (g := (DLineBiv E lam D).map (toBarPolyHom E))
    (m := (chordCubicBiv E lam).natDegree) (n := (DLineBiv E lam D).natDegree)]

/-- Bar-level resultant-as-product. Same as
`chord_fiber_product_concrete_eval_eq_prod_split`, but over `Fqbar E`,
where the specialised chord cubic splits automatically. -/
theorem chord_fiber_product_concrete_bar_eval_eq_prod
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : Fqbar E) :
    Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D))
      =
        ((chordCubicBar E lam μ).roots.map
          fun x => (DLineBar E lam D μ).eval x).prod := by
  rw [chord_fiber_product_concrete_bar_eval E lam D μ]
  rw [show (chordCubicBiv E lam).natDegree = (chordCubicBar E lam μ).natDegree by
        rw [chordCubicBiv_natDegree, chordCubicBar_natDegree]]
  have hSplit : (chordCubicBar E lam μ).Splits := IsAlgClosed.splits _
  rw [Polynomial.resultant_eq_prod_eval _ _ _
        (DLineBar_natDegree_le E lam D μ) hSplit,
      chordCubicBar_leadingCoeff, one_pow, one_mul]

/-! ## Non-vanishing -/

/-- Explicit evaluation of `chordCubicBar` at a base point `x ∈ Fqbar`.
This local form is used by the non-vanishing proof below. -/
private lemma chordCubicBar_eval_eq_nonzero_aux
    (lam : ZMod E.q) (μ x : Fqbar E) :
    (chordCubicBar E lam μ).eval x =
      x ^ 3 - (fqToBar E lam) ^ 2 * x ^ 2
        + (fqToBar E E.curveA - 2 * fqToBar E lam * μ) * x
        + (fqToBar E E.curveB - μ ^ 2) := by
  unfold chordCubicBar chordCubicBivBar chordCubicBiv toBarPolyHom fqToBar
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
             Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
             Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
             Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
             Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
             Polynomial.eval_ofNat, Polynomial.map_ofNat, map_mul, map_pow,
             map_ofNat]

/-- A root `x` of `chordCubicBar lam μ` gives a point `(x, λ̄x + μ)` that
satisfies the curve equation `y² = x³ + Ax + B` over `Fqbar`. -/
private lemma chordCubicBar_root_onCurve_of_mem_roots
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hRoot : x ∈ (chordCubicBar E lam μ).roots) :
    (fqToBar E lam * x + μ) ^ 2 =
      x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB := by
  have hEval : (chordCubicBar E lam μ).eval x = 0 :=
    (Polynomial.mem_roots'.mp hRoot).2
  rw [chordCubicBar_eval_eq_nonzero_aux] at hEval
  linear_combination -hEval

/-- **Non-vanishing.** The candidate is nonzero whenever `D` is.

Proof: by contradiction. If the polynomial were zero, all bar evaluations
would be zero. Pick `μ ∈ Fqbar E` outside the finite set
`gd.support.image (zLambdaBar E lam)` (possible since `Fqbar E` is
algebraically closed, hence infinite). At this `μ`, `bar_eval_eq_prod`
expresses the evaluation as a product over chord roots; for the product
to be zero, some chord root `x` must satisfy `D̄(x, λ̄x + μ) = 0`. The
geometric point `Q := (x, λ̄x + μ)` then lies on `E` and is a `D`-zero,
hence in `gd.support`, hence `μ = zLambdaBar E lam Q` lies in the bad
set after all. -/
theorem chord_fiber_product_concrete_ne_zero
    (lam : ZMod E.q) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    chord_fiber_product_concrete E lam D ≠ 0 := by
  classical
  intro hZero
  obtain ⟨support, hSuppZero, hZeroSupp⟩ := exists_geometric_zero_support E D hD
  obtain ⟨gd, _hSuppEq⟩ :=
    exists_geometricDivisorData_of_support E D hD support hSuppZero hZeroSupp
  set badMu : Finset (Fqbar E) := gd.support.image (zLambdaBar E lam)
    with hBadMu_def
  obtain ⟨μ, hμ⟩ := Infinite.exists_notMem_finset badMu
  have hBarZero :
      (chord_fiber_product_concrete E lam D).map
        (algebraMap (ZMod E.q) (Fqbar E)) = 0 := by
    rw [hZero]
    exact Polynomial.map_zero _
  have hEvalZero :
      Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)) = 0 := by
    rw [hBarZero]
    simp
  rw [chord_fiber_product_concrete_bar_eval_eq_prod] at hEvalZero
  rw [Multiset.prod_eq_zero_iff, Multiset.mem_map] at hEvalZero
  obtain ⟨x, hx_root, hx_eq⟩ := hEvalZero
  have hOnE :
      (fqToBar E lam * x + μ) ^ 2 =
        x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB :=
    chordCubicBar_root_onCurve_of_mem_roots E lam μ x hx_root
  set Q : GeomPoint E := ⟨x, fqToBar E lam * x + μ, hOnE⟩ with hQ_def
  have hQzero : D.geomEval E Q = 0 := by
    rw [← DLineBar_eval_eq_geomEval E lam D μ x hOnE]
    exact hx_eq
  have hQ_mem : Q ∈ gd.support := gd.eval_zero_mem_support Q hQzero
  have hμ_eq : zLambdaBar E lam Q = μ := by
    show (fqToBar E lam * x + μ) - fqToBar E lam * x = μ
    ring
  exact hμ (Finset.mem_image.mpr ⟨Q, hQ_mem, hμ_eq⟩)

/-! ## Support-level root set -/

/-- **Support-level zero-locus bridge.** Over `Fqbar`, the base-changed
concrete chord-fiber product vanishes at `μ` exactly when some geometric
`D`-zero `Q ∈ gd.support` projects to `μ` under `zLambdaBar`.

This is the multiplicity-free precursor to the factored form: it pins down
the roots of the polynomial set-theoretically without yet counting how many
times each root appears. -/
theorem chord_fiber_product_concrete_bar_eval_eq_zero_iff_support
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (μ : Fqbar E) :
    Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)) = 0 ↔
      ∃ Q ∈ gd.support, zLambdaBar E lam Q = μ := by
  rw [chord_fiber_product_concrete_bar_eval_eq_prod,
      Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · -- Forward: a vanishing factor lifts to a `D`-zero in `gd.support`.
    rintro ⟨x, hx_root, hx_eq⟩
    have hOnE :=
      chordCubicBar_root_onCurve_of_mem_roots E lam μ x hx_root
    set Q : GeomPoint E := ⟨x, fqToBar E lam * x + μ, hOnE⟩
    have hQzero : D.geomEval E Q = 0 := by
      rw [← DLineBar_eval_eq_geomEval E lam D μ x hOnE]
      exact hx_eq
    refine ⟨Q, gd.eval_zero_mem_support Q hQzero, ?_⟩
    show (fqToBar E lam * x + μ) - fqToBar E lam * x = μ
    ring
  · -- Reverse: a support point `Q` with `zLambdaBar lam Q = μ` makes `Q.x`
    -- a chord cubic root with vanishing `D`-on-line factor.
    rintro ⟨Q, hQ_mem, hQ_proj⟩
    have hQy : Q.y = fqToBar E lam * Q.x + μ := by
      have hzL : Q.y - fqToBar E lam * Q.x = μ := hQ_proj
      linear_combination hzL
    have hRootEval : (chordCubicBar E lam μ).eval Q.x = 0 := by
      rw [chordCubicBar_eval_eq_nonzero_aux]
      have hQc := Q.onCurve
      linear_combination -hQc + (Q.y + fqToBar E lam * Q.x + μ) * hQy
    have hCubicNz : chordCubicBar E lam μ ≠ 0 := by
      intro h
      have h3 : (chordCubicBar E lam μ).natDegree = 3 := chordCubicBar_natDegree E lam μ
      rw [h, Polynomial.natDegree_zero] at h3
      exact absurd h3 (by decide)
    have hRootMem : Q.x ∈ (chordCubicBar E lam μ).roots :=
      (Polynomial.mem_roots'.mpr ⟨hCubicNz, hRootEval⟩)
    refine ⟨Q.x, hRootMem, ?_⟩
    have hQ_eq_lifted : Q = ⟨Q.x, fqToBar E lam * Q.x + μ,
        hQy ▸ Q.onCurve⟩ := by
      rcases Q with ⟨qx, qy, qc⟩
      simp only at hQy
      simp [hQy]
    rw [DLineBar_eval_eq_geomEval E lam D μ Q.x (hQy ▸ Q.onCurve)]
    rw [← hQ_eq_lifted]
    exact gd.support_eval_zero Q hQ_mem

/-- The root set of the base-changed concrete chord-fiber product is exactly
the image of the geometric `D`-zero support under `zLambdaBar`. -/
theorem chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).roots.toFinset =
      gd.support.image (zLambdaBar E lam) := by
  classical
  ext μ
  rw [Multiset.mem_toFinset]
  rw [Polynomial.mem_roots
    (Polynomial.map_ne_zero (chord_fiber_product_concrete_ne_zero E lam D hD))]
  change Polynomial.eval μ
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)) = 0 ↔
    μ ∈ gd.support.image (zLambdaBar E lam)
  rw [chord_fiber_product_concrete_bar_eval_eq_zero_iff_support E lam D hD gd μ]
  exact Iff.symm Finset.mem_image

end Divisor
