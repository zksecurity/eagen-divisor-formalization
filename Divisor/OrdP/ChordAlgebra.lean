/-
  Divisor/OrdP/ChordAlgebra.lean — the `F̄[Z]`-algebra
  structure on the base-changed coordinate ring, through the chord
  coordinate `z = y − λ̄·x`.

  The chord cubic `f̄(X, Z) = X³ − λ̄²X² + (Ā − 2λ̄Z)X + (B̄ − Z²)` is
  monic in `X` over `F̄[Z]` (`chordCubicBivBar`), and substituting
  `Z = y − λ̄x`, `X = x` in it recovers the curve equation. This file
  builds the resulting ring isomorphism

    `AdjoinRoot (chordCubicBivBar E lam) ≃+* R̄`

  (`chordEquiv`), and uses it to install, per `lam`, the `F̄[Z]`-algebra
  structure on the type synonym `ChordModel E lam` of `R̄`, together
  with the `Module.Finite` / `Module.Free` instances that the
  `relNorm` calculus and the norm-is-resultant computation consume. The power
  basis `{1, x̄, x̄²}` comes from `AdjoinRoot.powerBasis'` across the
  isomorphism.
-/
import Divisor.OrdP.GeomValuationBridge
import Divisor.ChordFiberProductConcrete

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Divisor

variable (E : ECSetup) (lam : ZMod E.q)

/-! ## The chord elements of `R̄` -/

/-- The affine coordinate `x` as an element of the base-changed
coordinate ring. -/
noncomputable def xClassBar : E.toWBar.toAffine.CoordinateRing :=
  CoordinateRing.mk E.toWBar.toAffine (Polynomial.C Polynomial.X)

/-- The chord coordinate `z = y − λ̄·x` as an element of the
base-changed coordinate ring. -/
noncomputable def zElt : E.toWBar.toAffine.CoordinateRing :=
  yClassZeroBar E - CoordinateRing.mk E.toWBar.toAffine
    (Polynomial.C (Polynomial.C (fqToBar E lam) * Polynomial.X))

/-- `zElt` as the class of an explicit bivariate polynomial. -/
theorem zElt_eq_mk :
    zElt E lam = CoordinateRing.mk E.toWBar.toAffine
      (Polynomial.X -
        Polynomial.C (Polynomial.C (fqToBar E lam) * Polynomial.X)) := by
  unfold zElt yClassZeroBar
  rw [map_sub]

/-- The scalar embedding `F̄ → R̄` is the class of a bivariate
constant. -/
theorem algebraMap_bar_eq_mk (c : Fqbar E) :
    algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing c =
      CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C (Polynomial.C c)) := by
  rw [IsScalarTower.algebraMap_apply (Fqbar E) ((Fqbar E)[X])
    E.toWBar.toAffine.CoordinateRing]
  rw [show algebraMap ((Fqbar E)[X]) E.toWBar.toAffine.CoordinateRing
      (algebraMap (Fqbar E) ((Fqbar E)[X]) c) =
      CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C (Polynomial.C c)) from ?_]
  rw [AdjoinRoot.algebraMap_eq]
  rfl

/-- The `F̄[Z] → R̄` structure map of the chord algebra: `Z ↦ z`. -/
noncomputable def zHom : Polynomial (Fqbar E) →+* E.toWBar.toAffine.CoordinateRing :=
  (Polynomial.aeval (zElt E lam)).toRingHom

@[simp] theorem zHom_C (c : Fqbar E) :
    zHom E lam (Polynomial.C c) =
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing c := by
  unfold zHom
  simp

@[simp] theorem zHom_X : zHom E lam Polynomial.X = zElt E lam := by
  unfold zHom
  simp

/-! ## The chord relation -/

/-- The base-changed chord cubic in fully explicit form over `F̄[Z]`. -/
theorem chordCubicBivBar_eq :
    chordCubicBivBar E lam =
      Polynomial.X ^ 3
        - Polynomial.C (Polynomial.C (fqToBar E lam)) ^ 2 * Polynomial.X ^ 2
        + Polynomial.C (Polynomial.C (fqToBar E E.curveA)
            - 2 * Polynomial.C (fqToBar E lam) * Polynomial.X) * Polynomial.X
        + Polynomial.C (Polynomial.C (fqToBar E E.curveB)
            - Polynomial.X ^ 2) := by
  show (chordCubicBiv E lam).map
      (Polynomial.mapRingHom (algebraMap (ZMod E.q) (Fqbar E))) = _
  unfold chordCubicBiv fqToBar
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_ofNat, Polynomial.coe_mapRingHom, map_pow, map_mul,
    map_ofNat]

/-- **The chord relation**: substituting `X = x̄`, `Z = z̄` in the chord
cubic yields zero in `R̄` — it is the curve equation in chord
coordinates. -/
theorem chordCubic_eval₂_zero :
    (chordCubicBivBar E lam).eval₂ (zHom E lam) (xClassBar E) = 0 := by
  rw [chordCubicBivBar_eq]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, map_sub, map_mul, map_pow, map_ofNat, zHom_C,
    zHom_X]
  -- Everything is an expression in `mk`-atoms.
  rw [zElt_eq_mk]
  simp only [algebraMap_bar_eq_mk]
  unfold xClassBar
  -- The right-hand side is `−(the curve relation)`.
  have hkey : CoordinateRing.mk E.toWBar.toAffine
      (Polynomial.X ^ 2 - Polynomial.C (curveXBar E)) = 0 := by
    rw [← toWBar_polynomial]
    exact AdjoinRoot.mk_self
  rw [show (0 : E.toWBar.toAffine.CoordinateRing) =
      -(CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.X ^ 2 - Polynomial.C (curveXBar E))) by rw [hkey, neg_zero]]
  rw [curveXBar_eq]
  simp only [map_add, map_sub, map_mul, map_pow]
  ring

/-! ## The abstract chord model and the isomorphism -/

/-- The abstract chord model `F̄[Z][X]/(chord cubic)`. -/
noncomputable abbrev ChordRing := AdjoinRoot (chordCubicBivBar E lam)

/-- The chord cubic is monic in the chord `X`-variable. -/
theorem chordCubicBivBar_monic : (chordCubicBivBar E lam).Monic :=
  (chordCubicBiv_monic E lam).map _

/-- The forward map `F̄[Z][X]/(f̄) → R̄`: `X ↦ x̄`, `Z ↦ z̄`. -/
noncomputable def chordToBar :
    ChordRing E lam →+* E.toWBar.toAffine.CoordinateRing :=
  AdjoinRoot.lift (zHom E lam) (xClassBar E) (chordCubic_eval₂_zero E lam)

@[simp] theorem chordToBar_root :
    chordToBar E lam (AdjoinRoot.root (chordCubicBivBar E lam)) =
      xClassBar E :=
  AdjoinRoot.lift_root _

@[simp] theorem chordToBar_of (s : Polynomial (Fqbar E)) :
    chordToBar E lam (AdjoinRoot.of _ s) = zHom E lam s :=
  AdjoinRoot.lift_of _

/-- `F̄`-constants in the chord model, through the base `F̄[Z]`. -/
theorem chord_ofC_eq (c : Fqbar E) :
    AdjoinRoot.of (chordCubicBivBar E lam) (Polynomial.C c) =
      algebraMap (Fqbar E) (ChordRing E lam) c := by
  rw [← AdjoinRoot.algebraMap_eq,
    IsScalarTower.algebraMap_apply (Fqbar E) (Polynomial (Fqbar E))
      (ChordRing E lam)]
  rfl

/-- `chordToBar` is `F̄`-linear on scalars. -/
theorem chordToBar_algebraMap (c : Fqbar E) :
    chordToBar E lam (algebraMap (Fqbar E) (ChordRing E lam) c) =
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing c := by
  rw [← chord_ofC_eq, chordToBar_of, zHom_C]

/-- Evaluating a univariate at `x̄` is the canonical `F̄[X]`-scalar map. -/
theorem aeval_xClassBar (r : (Fqbar E)[X]) :
    Polynomial.aeval (xClassBar E) r =
      algebraMap ((Fqbar E)[X]) E.toWBar.toAffine.CoordinateRing r := by
  have hhom : (Polynomial.aeval (xClassBar E)).toRingHom =
      algebraMap ((Fqbar E)[X]) E.toWBar.toAffine.CoordinateRing := by
    apply Polynomial.ringHom_ext
    · intro a
      show Polynomial.aeval (xClassBar E) (Polynomial.C a) = _
      rw [Polynomial.aeval_C, algebraMap_bar_eq_mk, AdjoinRoot.algebraMap_eq]
      rfl
    · show Polynomial.aeval (xClassBar E) Polynomial.X = _
      rw [Polynomial.aeval_X, AdjoinRoot.algebraMap_eq]
      rfl
  exact RingHom.congr_fun hhom r

/-- The `y`-coordinate in the chord model: `η = λ̄·ξ + ζ`. -/
noncomputable def etaElt : ChordRing E lam :=
  algebraMap (Fqbar E) (ChordRing E lam) (fqToBar E lam) *
      AdjoinRoot.root (chordCubicBivBar E lam) +
    AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X

/-- The base map `F̄[X] → ChordRing`: `X ↦ ξ`. -/
noncomputable def xHom : (Fqbar E)[X] →+* ChordRing E lam :=
  (Polynomial.aeval (AdjoinRoot.root (chordCubicBivBar E lam))).toRingHom

@[simp] theorem xHom_C (c : Fqbar E) :
    xHom E lam (Polynomial.C c) =
      algebraMap (Fqbar E) (ChordRing E lam) c := by
  unfold xHom
  simp

@[simp] theorem xHom_X :
    xHom E lam Polynomial.X = AdjoinRoot.root (chordCubicBivBar E lam) := by
  unfold xHom
  simp

/-- The chord-cubic relation at `(ξ, ζ)`, in expanded atom form. -/
theorem chord_root_relation :
    AdjoinRoot.root (chordCubicBivBar E lam) ^ 3 -
        algebraMap (Fqbar E) (ChordRing E lam) (fqToBar E lam) ^ 2 *
          AdjoinRoot.root (chordCubicBivBar E lam) ^ 2 +
        (algebraMap (Fqbar E) (ChordRing E lam) (fqToBar E E.curveA) -
          2 * algebraMap (Fqbar E) (ChordRing E lam) (fqToBar E lam) *
            AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X) *
          AdjoinRoot.root (chordCubicBivBar E lam) +
        (algebraMap (Fqbar E) (ChordRing E lam) (fqToBar E E.curveB) -
          AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X ^ 2) = 0 := by
  have hrel : (Polynomial.X ^ 3
      - Polynomial.C (Polynomial.C (fqToBar E lam)) ^ 2 * Polynomial.X ^ 2
      + Polynomial.C (Polynomial.C (fqToBar E E.curveA)
          - 2 * Polynomial.C (fqToBar E lam) * Polynomial.X) * Polynomial.X
      + Polynomial.C (Polynomial.C (fqToBar E E.curveB)
          - Polynomial.X ^ 2)).eval₂
        (AdjoinRoot.of (chordCubicBivBar E lam))
        (AdjoinRoot.root (chordCubicBivBar E lam)) = 0 := by
    rw [← chordCubicBivBar_eq]
    exact AdjoinRoot.eval₂_root _
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X] at hrel
  simp only [map_sub, map_mul, map_pow, map_ofNat, chord_ofC_eq] at hrel
  linear_combination hrel

/-- The Weierstrass relation holds at `(ξ, η)` in the chord model. -/
theorem weierstrass_eval₂_zero :
    (E.toWBar.toAffine.polynomial).eval₂ (xHom E lam) (etaElt E lam) = 0 := by
  rw [toWBar_polynomial, curveXBar_eq]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    map_add, map_mul, map_pow, xHom_C, xHom_X]
  unfold etaElt
  linear_combination -(chord_root_relation E lam)

/-- The reverse map `R̄ → F̄[Z][X]/(f̄)`: `x ↦ ξ`, `y ↦ η`. -/
noncomputable def barToChord :
    E.toWBar.toAffine.CoordinateRing →+* ChordRing E lam :=
  AdjoinRoot.lift (xHom E lam) (etaElt E lam) (weierstrass_eval₂_zero E lam)

@[simp] theorem barToChord_root :
    barToChord E lam (AdjoinRoot.root E.toWBar.toAffine.polynomial) =
      etaElt E lam :=
  AdjoinRoot.lift_root _

@[simp] theorem barToChord_of (r : (Fqbar E)[X]) :
    barToChord E lam (AdjoinRoot.of _ r) = xHom E lam r :=
  AdjoinRoot.lift_of _

/-! ## The compositions are the identity -/

/-- `barToChord` is `F̄`-linear on scalars. -/
theorem barToChord_algebraMap (c : Fqbar E) :
    barToChord E lam
        (algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing c) =
      algebraMap (Fqbar E) (ChordRing E lam) c := by
  rw [IsScalarTower.algebraMap_apply (Fqbar E) ((Fqbar E)[X])
    E.toWBar.toAffine.CoordinateRing, Polynomial.algebraMap_eq,
    AdjoinRoot.algebraMap_eq, barToChord_of, xHom_C]

private theorem chordToBar_comp_algebraMap :
    (chordToBar E lam).comp (algebraMap (Fqbar E) (ChordRing E lam)) =
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing :=
  RingHom.ext (chordToBar_algebraMap E lam)

private theorem barToChord_comp_algebraMap :
    (barToChord E lam).comp
        (algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing) =
      algebraMap (Fqbar E) (ChordRing E lam) :=
  RingHom.ext (barToChord_algebraMap E lam)

/-- `chordToBar ∘ barToChord` fixes the `F̄[X]`-scalars. -/
private theorem chordToBar_barToChord_of (r : (Fqbar E)[X]) :
    chordToBar E lam (barToChord E lam
      (algebraMap ((Fqbar E)[X]) E.toWBar.toAffine.CoordinateRing r)) =
      algebraMap ((Fqbar E)[X]) E.toWBar.toAffine.CoordinateRing r := by
  rw [AdjoinRoot.algebraMap_eq, barToChord_of]
  unfold xHom
  rw [show (Polynomial.aeval
      (AdjoinRoot.root (chordCubicBivBar E lam))).toRingHom r =
    r.eval₂ (algebraMap (Fqbar E) (ChordRing E lam))
      (AdjoinRoot.root (chordCubicBivBar E lam)) from rfl]
  rw [Polynomial.hom_eval₂ r (algebraMap (Fqbar E) (ChordRing E lam))
    (chordToBar E lam) (AdjoinRoot.root (chordCubicBivBar E lam))]
  rw [chordToBar_comp_algebraMap, chordToBar_root]
  rw [← Polynomial.aeval_def, aeval_xClassBar, AdjoinRoot.algebraMap_eq]

/-- `chordToBar` carries `η` back to the `y`-coordinate. -/
private theorem chordToBar_eta :
    chordToBar E lam (etaElt E lam) =
      AdjoinRoot.root E.toWBar.toAffine.polynomial := by
  unfold etaElt
  rw [map_add, map_mul, chordToBar_algebraMap, chordToBar_root,
    chordToBar_of, zHom_X, zElt_eq_mk, algebraMap_bar_eq_mk]
  unfold xClassBar
  rw [show AdjoinRoot.root E.toWBar.toAffine.polynomial =
    CoordinateRing.mk E.toWBar.toAffine Polynomial.X from rfl]
  rw [map_sub, ← map_mul, ← Polynomial.C_mul]
  ring

private theorem chordToBar_comp_barToChord :
    (chordToBar E lam).comp (barToChord E lam) =
      RingHom.id E.toWBar.toAffine.CoordinateRing := by
  ext
  case hAlg.h₁ x =>
    show chordToBar E lam (barToChord E lam
      (AdjoinRoot.of E.toWBar.toAffine.polynomial (Polynomial.C x))) =
      AdjoinRoot.of E.toWBar.toAffine.polynomial (Polynomial.C x)
    rw [show AdjoinRoot.of E.toWBar.toAffine.polynomial (Polynomial.C x) =
      CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C (Polynomial.C x)) from rfl,
      ← algebraMap_bar_eq_mk, barToChord_algebraMap, chordToBar_algebraMap]
  case h₂ =>
    show chordToBar E lam (barToChord E lam
      (AdjoinRoot.of E.toWBar.toAffine.polynomial Polynomial.X)) =
      AdjoinRoot.of E.toWBar.toAffine.polynomial Polynomial.X
    rw [barToChord_of, xHom_X, chordToBar_root]
    rfl
  case hRoot =>
    show chordToBar E lam (barToChord E lam
      (AdjoinRoot.root E.toWBar.toAffine.polynomial)) =
      AdjoinRoot.root E.toWBar.toAffine.polynomial
    rw [barToChord_root, chordToBar_eta]

/-- `barToChord` carries `z̄` to `ζ`. -/
private theorem barToChord_zElt :
    barToChord E lam (zElt E lam) =
      AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X := by
  rw [zElt_eq_mk]
  have hY : CoordinateRing.mk E.toWBar.toAffine Polynomial.X =
      AdjoinRoot.root E.toWBar.toAffine.polynomial := rfl
  rw [map_sub, hY]
  rw [show CoordinateRing.mk E.toWBar.toAffine
      (Polynomial.C (Polynomial.C (fqToBar E lam) * Polynomial.X)) =
    AdjoinRoot.of E.toWBar.toAffine.polynomial
      (Polynomial.C (fqToBar E lam) * Polynomial.X) from rfl]
  rw [map_sub, barToChord_root, barToChord_of]
  unfold etaElt xHom
  rw [show (Polynomial.aeval (AdjoinRoot.root
      (chordCubicBivBar E lam))).toRingHom
        (Polynomial.C (fqToBar E lam) * Polynomial.X) =
    Polynomial.aeval (AdjoinRoot.root (chordCubicBivBar E lam))
      (Polynomial.C (fqToBar E lam) * Polynomial.X) from rfl]
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  ring

/-- `barToChord ∘ chordToBar` fixes the `F̄[Z]`-scalars. -/
private theorem barToChord_chordToBar_of (s : Polynomial (Fqbar E)) :
    barToChord E lam (chordToBar E lam
      (algebraMap (Polynomial (Fqbar E)) (ChordRing E lam) s)) =
      algebraMap (Polynomial (Fqbar E)) (ChordRing E lam) s := by
  rw [AdjoinRoot.algebraMap_eq, chordToBar_of]
  unfold zHom
  rw [show (Polynomial.aeval (zElt E lam)).toRingHom s =
    s.eval₂ (algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing)
      (zElt E lam) from rfl]
  rw [Polynomial.hom_eval₂ s
    (algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing)
    (barToChord E lam) (zElt E lam)]
  rw [barToChord_comp_algebraMap, barToChord_zElt]
  -- `s.eval₂ (algebraMap F̄) ζ = of s`
  have hhom : ((AdjoinRoot.of (chordCubicBivBar E lam)).comp
      (Polynomial.C : Fqbar E →+* Polynomial (Fqbar E)) :
        Fqbar E →+* ChordRing E lam) =
      algebraMap (Fqbar E) (ChordRing E lam) := by
    ext c
    exact chord_ofC_eq E lam c
  calc s.eval₂ (algebraMap (Fqbar E) (ChordRing E lam))
        (AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X)
      = s.eval₂ ((AdjoinRoot.of (chordCubicBivBar E lam)).comp
          (Polynomial.C : Fqbar E →+* Polynomial (Fqbar E)))
          (AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X) := by
        rw [hhom]
    _ = AdjoinRoot.of (chordCubicBivBar E lam)
          (s.eval₂ Polynomial.C Polynomial.X) := by
        rw [← Polynomial.hom_eval₂]
    _ = AdjoinRoot.of (chordCubicBivBar E lam) s := by
        rw [Polynomial.eval₂_C_X]

private theorem barToChord_comp_chordToBar :
    (barToChord E lam).comp (chordToBar E lam) =
      RingHom.id (ChordRing E lam) := by
  ext
  case hAlg.h₁ x =>
    show barToChord E lam (chordToBar E lam
      (AdjoinRoot.of (chordCubicBivBar E lam) (Polynomial.C x))) =
      AdjoinRoot.of (chordCubicBivBar E lam) (Polynomial.C x)
    rw [chord_ofC_eq, chordToBar_algebraMap, barToChord_algebraMap,
      ← chord_ofC_eq]
  case h₂ =>
    show barToChord E lam (chordToBar E lam
      (AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X)) =
      AdjoinRoot.of (chordCubicBivBar E lam) Polynomial.X
    rw [chordToBar_of, zHom_X, barToChord_zElt]
  case hRoot =>
    show barToChord E lam (chordToBar E lam
      (AdjoinRoot.root (chordCubicBivBar E lam))) =
      AdjoinRoot.root (chordCubicBivBar E lam)
    rw [chordToBar_root]
    unfold xClassBar
    rw [show CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C Polynomial.X) =
      AdjoinRoot.of E.toWBar.toAffine.polynomial Polynomial.X from rfl]
    rw [barToChord_of, xHom_X]

/-- **The chord isomorphism** `F̄[Z][X]/(f̄) ≃+* R̄` (plan.md 3a). -/
noncomputable def chordEquiv :
    ChordRing E lam ≃+* E.toWBar.toAffine.CoordinateRing :=
  RingEquiv.ofRingHom (chordToBar E lam) (barToChord E lam)
    (chordToBar_comp_barToChord E lam) (barToChord_comp_chordToBar E lam)

/-! ## The chord model of `R̄` with its `F̄[Z]`-algebra structure -/

/-- Type synonym of the base-changed coordinate ring carrying the
`lam`-dependent `F̄[Z]`-algebra structure `Z ↦ y − λ̄·x`. Elements are
definitionally elements of `R̄`, so all ideal- and valuation-level
facts about `R̄` apply verbatim. -/
def ChordModel (_lam : ZMod E.q) : Type _ := E.toWBar.toAffine.CoordinateRing

noncomputable instance : CommRing (ChordModel E lam) :=
  inferInstanceAs (CommRing E.toWBar.toAffine.CoordinateRing)

instance : IsDomain (ChordModel E lam) :=
  inferInstanceAs (IsDomain E.toWBar.toAffine.CoordinateRing)

instance : IsDedekindDomain (ChordModel E lam) :=
  inferInstanceAs (IsDedekindDomain E.toWBar.toAffine.CoordinateRing)

noncomputable instance : Algebra (Polynomial (Fqbar E)) (ChordModel E lam) :=
  (zHom E lam).toAlgebra

theorem chordModel_algebraMap_eq :
    algebraMap (Polynomial (Fqbar E)) (ChordModel E lam) = zHom E lam := rfl

/-- The chord isomorphism as an `F̄[Z]`-algebra equivalence onto the
chord model. -/
noncomputable def chordAlgEquiv :
    ChordRing E lam ≃ₐ[Polynomial (Fqbar E)] ChordModel E lam :=
  { chordEquiv E lam with
    commutes' := fun s => by
      show chordToBar E lam (algebraMap (Polynomial (Fqbar E))
        (ChordRing E lam) s) = zHom E lam s
      rw [AdjoinRoot.algebraMap_eq]
      exact chordToBar_of E lam s }

/-- The power basis `{1, x̄, x̄²}` of the chord model over `F̄[Z]`. -/
noncomputable def chordPowerBasis :
    PowerBasis (Polynomial (Fqbar E)) (ChordModel E lam) :=
  (AdjoinRoot.powerBasis' (chordCubicBivBar_monic E lam)).map
    (chordAlgEquiv E lam)

instance : Module.Finite (Polynomial (Fqbar E)) (ChordModel E lam) :=
  Module.Finite.of_basis (chordPowerBasis E lam).basis

instance : Module.Free (Polynomial (Fqbar E)) (ChordModel E lam) :=
  Module.Free.of_basis (chordPowerBasis E lam).basis

/-- The chord cubic has `X`-degree 3 after base change. -/
theorem chordCubicBivBar_natDegree :
    (chordCubicBivBar E lam).natDegree = 3 := by
  unfold chordCubicBivBar
  rw [(chordCubicBiv_monic E lam).natDegree_map, chordCubicBiv_natDegree]

/-- The chord model has rank 3 over `F̄[Z]`. -/
theorem chordModel_finrank :
    Module.finrank (Polynomial (Fqbar E)) (ChordModel E lam) = 3 := by
  rw [Module.finrank_eq_card_basis (chordPowerBasis E lam).basis]
  show Fintype.card (Fin (chordPowerBasis E lam).dim) = 3
  rw [Fintype.card_fin]
  show (AdjoinRoot.powerBasis' (chordCubicBivBar_monic E lam)).dim = 3
  rw [AdjoinRoot.powerBasis'_dim, chordCubicBivBar_natDegree]

end Divisor
