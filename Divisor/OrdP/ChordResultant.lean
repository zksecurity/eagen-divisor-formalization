/-
  Divisor/OrdP/ChordResultant.lean — plan.md Phase 3c: the norm is the
  chord-fiber resultant.

  Main result (`intNorm_chordD_eq`):

    `Algebra.intNorm F̄[Z] (ChordModel E lam) D̄
       = (chord_fiber_product_concrete E lam D).map (F_q → F̄)`

  via the embeddings chain over `K = Frac F̄[Z]`, `L = Frac (ChordModel)`
  and `K̄ = AlgebraicClosure K`:
  norm = ∏ embeddings (`Algebra.norm_eq_prod_embeddings`, separable by
  `ChordFraction`), embeddings ↔ roots of the minimal polynomial of the
  generator (`PowerBasis.liftEquiv'`, minpoly = the chord cubic), and
  the resultant as a product over those same roots
  (`resultant_eq_prod_eval` after two `resultant_map_map`s).
-/
import Divisor.OrdP.ChordFraction

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate nonZeroDivisors

namespace Divisor

variable (E : ECSetup) (lam : ZMod E.q)

attribute [local instance] FractionRing.liftAlgebra

/-! ## `D̄` as the D-line polynomial evaluated at the generator -/

/-- The double-`C` bivariate of a rational univariate evaluates at
`(z̄, x̄)` to the class of its base change. -/
private theorem eval₂_mapC_zHom (p : Polynomial (ZMod E.q)) :
    ((p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
        (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))).eval₂
      (zHom E lam) (xClassBar E) =
      CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C (p.map (algebraMap (ZMod E.q) (Fqbar E)))) := by
  -- commute the two coefficient maps
  have hswap : (p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
      (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E))) =
      (p.map (algebraMap (ZMod E.q) (Fqbar E))).map
        (Polynomial.C : Fqbar E →+* Polynomial (Fqbar E)) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext c
    simp
  rw [hswap, Polynomial.eval₂_map]
  have hcomp : (zHom E lam).comp (Polynomial.C : Fqbar E →+* Polynomial (Fqbar E)) =
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing := by
    ext c
    exact zHom_C E lam c
  rw [hcomp, ← Polynomial.aeval_def, aeval_xClassBar, AdjoinRoot.algebraMap_eq]
  rfl

/-- The chord line `λ̄·x̄ + z̄` is the `y`-coordinate. -/
private theorem lam_x_add_z :
    algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing (fqToBar E lam) *
        xClassBar E + zElt E lam =
      CoordinateRing.mk E.toWBar.toAffine Polynomial.X := by
  rw [algebraMap_bar_eq_mk, zElt_eq_mk]
  unfold xClassBar
  rw [← map_mul, ← Polynomial.C_mul]
  rw [← map_add]
  congr 1
  ring

/-- **`D̄` is the D-line polynomial evaluated at the chord generator**
(over `F̄[Z]`). -/
theorem chordD_eq_aeval (D : CoordRingElt E.q) :
    chordD E lam D =
      Polynomial.aeval (chordPowerBasis E lam).gen (DLineBivBar E lam D) := by
  -- the generator is `x̄` and `aeval` over `F̄[Z]` is `eval₂ zHom`
  have hgen : (chordPowerBasis E lam).gen =
      (chordToBar E lam (AdjoinRoot.root (chordCubicBivBar E lam)) :
        E.toWBar.toAffine.CoordinateRing) := by
    show ((AdjoinRoot.powerBasis' (chordCubicBivBar_monic E lam)).map
      (chordAlgEquiv E lam)).gen = _
    rw [PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen]
    rfl
  have haev : Polynomial.aeval (chordPowerBasis E lam).gen
      (DLineBivBar E lam D) =
      (DLineBivBar E lam D).eval₂ (zHom E lam) (xClassBar E) := by
    rw [Polynomial.aeval_def, hgen, chordToBar_root]
    rfl
  rw [haev]
  -- expand the D-line polynomial
  unfold DLineBivBar DLineBiv
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C]
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  rw [eval₂_mapC_zHom, eval₂_mapC_zHom]
  -- identify the line with the y-coordinate
  have hC : zHom E lam ((Polynomial.mapRingHom
      (algebraMap (ZMod E.q) (Fqbar E))) (Polynomial.C lam)) =
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing
        (fqToBar E lam) := by
    rw [show (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))
        (Polynomial.C lam) = Polynomial.C (fqToBar E lam) from by
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C]; rfl]
    exact zHom_C E lam _
  have hX : zHom E lam ((Polynomial.mapRingHom
      (algebraMap (ZMod E.q) (Fqbar E))) Polynomial.X) = zElt E lam := by
    rw [show (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))
        Polynomial.X = Polynomial.X from by
      rw [Polynomial.coe_mapRingHom, Polynomial.map_X]]
    exact zHom_X E lam
  rw [hC, hX, lam_x_add_z]
  -- assemble into `barD`
  unfold chordD barD geomAPoly geomBPoly
  rw [map_sub, map_mul]

/-! ## The embeddings product -/

/-- The algebraic closure of `K`. -/
noncomputable abbrev ChordKbar := AlgebraicClosure (ChordK E)

/-- The D-line polynomial over `K`. -/
noncomputable def dLineK (D : CoordRingElt E.q) : Polynomial (ChordK E) :=
  (DLineBivBar E lam D).map (algebraMap (Polynomial (Fqbar E)) (ChordK E))

theorem chordFracPowerBasis_gen :
    (chordFracPowerBasis E lam).gen = chordFracGen E lam := rfl

/-- `D̄` in `L` is the `K`-level D-line polynomial at the generator. -/
theorem chordD_L_eq_aeval (D : CoordRingElt E.q) :
    algebraMap (ChordModel E lam) (ChordL E lam) (chordD E lam D) =
      Polynomial.aeval (chordFracGen E lam) (dLineK E lam D) := by
  rw [chordD_eq_aeval]
  unfold dLineK
  rw [Polynomial.aeval_map_algebraMap]
  unfold chordFracGen
  rw [Polynomial.aeval_algebraMap_apply]

/-- The product over embeddings equals the product over the roots of
the minimal polynomial of the generator. -/
private theorem prod_embeddings (D : CoordRingElt E.q) :
    (∏ σ : ChordL E lam →ₐ[ChordK E] ChordKbar E,
      σ (algebraMap (ChordModel E lam) (ChordL E lam) (chordD E lam D))) =
    (((minpoly (ChordK E) (chordFracGen E lam)).map
        (algebraMap (ChordK E) (ChordKbar E))).roots.map
      (fun y => Polynomial.eval y
        ((dLineK E lam D).map
          (algebraMap (ChordK E) (ChordKbar E))))).prod := by
  classical
  have hsep : IsSeparable (ChordK E) (chordFracGen E lam) :=
    Algebra.IsSeparable.isSeparable _ _
  rw [Fintype.prod_equiv ((chordFracPowerBasis E lam).liftEquiv')
    _ (fun y => Polynomial.eval y.1
      ((dLineK E lam D).map (algebraMap (ChordK E) (ChordKbar E))))
    (fun σ => by
      rw [chordD_L_eq_aeval, ← Polynomial.aeval_algHom_apply,
        ← chordFracPowerBasis_gen, ← PowerBasis.liftEquiv'_apply_coe,
        Polynomial.aeval_def, Polynomial.eval_map])]
  rw [Finset.prod_mem_multiset _ _ (fun y => Polynomial.eval y
      ((dLineK E lam D).map (algebraMap (ChordK E) (ChordKbar E))))
      (fun x => rfl),
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    chordFracPowerBasis_gen, Polynomial.aroots_def,
    Multiset.dedup_eq_self.mpr
      (Polynomial.nodup_roots (Polynomial.Separable.map hsep))]

/-! ## The resultant chain (plan.md 3c) -/

/-- The bar-level D-line polynomial mapped into `K̄` factors through
`dLineK`. -/
private theorem dLine_map_map (D : CoordRingElt E.q) :
    (DLineBivBar E lam D).map
        ((algebraMap (ChordK E) (ChordKbar E)).comp
          (algebraMap (Polynomial (Fqbar E)) (ChordK E))) =
      (dLineK E lam D).map (algebraMap (ChordK E) (ChordKbar E)) := by
  unfold dLineK
  rw [Polynomial.map_map]

private theorem cubic_map_map :
    (chordCubicBivBar E lam).map
        ((algebraMap (ChordK E) (ChordKbar E)).comp
          (algebraMap (Polynomial (Fqbar E)) (ChordK E))) =
      (chordCubicK E lam).map (algebraMap (ChordK E) (ChordKbar E)) := by
  unfold chordCubicK
  rw [Polynomial.map_map]

private theorem cubicKbar_natDegree :
    ((chordCubicK E lam).map
      (algebraMap (ChordK E) (ChordKbar E))).natDegree = 3 := by
  rw [(chordCubicK_monic E lam).natDegree_map, chordCubicK_natDegree]

private theorem cubicKbar_leadingCoeff :
    ((chordCubicK E lam).map
      (algebraMap (ChordK E) (ChordKbar E))).leadingCoeff = 1 :=
  ((chordCubicK_monic E lam).map _)

/-- **The norm is the chord-fiber resultant** (plan.md 3c). -/
theorem intNorm_chordD_eq (D : CoordRingElt E.q) :
    Algebra.intNorm (Polynomial (Fqbar E)) (ChordModel E lam)
        (chordD E lam D) =
      (chord_fiber_product_concrete E lam D).map
        (algebraMap (ZMod E.q) (Fqbar E)) := by
  classical
  apply IsFractionRing.injective (Polynomial (Fqbar E)) (ChordK E)
  apply (algebraMap (ChordK E) (ChordKbar E)).injective
  -- Norm side: down to the embeddings product.
  rw [Algebra.algebraMap_intNorm_fractionRing,
    Algebra.norm_eq_prod_embeddings _ (ChordKbar E), prod_embeddings,
    minpoly_chordFracGen]
  -- Resultant side: map the resultant through the two homs.
  have hres1 : (chord_fiber_product_concrete E lam D).map
      (algebraMap (ZMod E.q) (Fqbar E)) =
      Polynomial.resultant (chordCubicBivBar E lam) (DLineBivBar E lam D)
        (chordCubicBiv E lam).natDegree (DLineBiv E lam D).natDegree := by
    unfold chord_fiber_product_concrete chordCubicBivBar DLineBivBar
    rw [show (Polynomial.resultant (chordCubicBiv E lam)
        (DLineBiv E lam D) (chordCubicBiv E lam).natDegree
        (DLineBiv E lam D).natDegree).map
          (algebraMap (ZMod E.q) (Fqbar E)) =
      (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E)))
        (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)
          (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree) from rfl]
    rw [← Polynomial.resultant_map_map]
  rw [hres1]
  rw [show (algebraMap (ChordK E) (ChordKbar E))
      ((algebraMap (Polynomial (Fqbar E)) (ChordK E))
        (Polynomial.resultant (chordCubicBivBar E lam)
          (DLineBivBar E lam D) (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree)) =
    ((algebraMap (ChordK E) (ChordKbar E)).comp
        (algebraMap (Polynomial (Fqbar E)) (ChordK E)))
      (Polynomial.resultant (chordCubicBivBar E lam)
        (DLineBivBar E lam D) (chordCubicBiv E lam).natDegree
        (DLineBiv E lam D).natDegree) from rfl]
  rw [← Polynomial.resultant_map_map, dLine_map_map, cubic_map_map]
  -- Product over the roots of the (split, monic) cubic over `K̄`.
  have hdegf : (chordCubicBiv E lam).natDegree =
      ((chordCubicK E lam).map
        (algebraMap (ChordK E) (ChordKbar E))).natDegree := by
    rw [cubicKbar_natDegree, chordCubicBiv_natDegree]
  rw [hdegf]
  have hdegg : ((dLineK E lam D).map
      (algebraMap (ChordK E) (ChordKbar E))).natDegree ≤
      (DLineBiv E lam D).natDegree := by
    refine Polynomial.natDegree_map_le.trans ?_
    unfold dLineK
    refine Polynomial.natDegree_map_le.trans ?_
    unfold DLineBivBar
    exact Polynomial.natDegree_map_le
  rw [Polynomial.resultant_eq_prod_eval _ _ _ hdegg (IsAlgClosed.splits _),
    cubicKbar_leadingCoeff, one_pow, one_mul]

end Divisor
