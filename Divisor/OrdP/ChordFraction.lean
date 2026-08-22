/-
  Divisor/OrdP/ChordFraction.lean — plan.md Phase 3c, part 1: the
  fraction-field layer of the chord algebra.

  With `K := Frac F̄[Z]` and `L := Frac (ChordModel E lam)`:
  * `[L : K] = 3` (`IsFractionRing.finrank_eq` + the rank of the chord
    model), hence `FiniteDimensional K L`;
  * the power basis `{1, x̄, x̄²}` localizes to a `PowerBasis K L` with
    generator the image of `x̄` (`chordFracPowerBasis`);
  * the minimal polynomial of that generator is the chord cubic mapped
    into `K` (`minpoly_chordFracGen`);
  * `L/K` is separable: every element has minimal polynomial of degree
    `≤ 3 < q = char K`, so its derivative is nonzero
    (`instIsSeparableChordFrac`).
-/
import Divisor.OrdP.ChordNorm

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate nonZeroDivisors

namespace Divisor

variable (E : ECSetup) (lam : ZMod E.q)

attribute [local instance] FractionRing.liftAlgebra

/-! ## The two fraction fields -/

/-- Fraction field of the chord base `F̄[Z]`. -/
noncomputable abbrev ChordK := FractionRing (Polynomial (Fqbar E))

/-- Fraction field of the chord model. -/
noncomputable abbrev ChordL := FractionRing (ChordModel E lam)

/-- `[L : K] = 3`. -/
theorem chordFrac_finrank :
    Module.finrank (ChordK E) (ChordL E lam) = 3 := by
  rw [IsFractionRing.finrank_eq (Polynomial (Fqbar E)) (ChordK E)
    (ChordModel E lam) (ChordL E lam)]
  exact chordModel_finrank E lam

instance : FiniteDimensional (ChordK E) (ChordL E lam) :=
  FiniteDimensional.of_finrank_pos (by rw [chordFrac_finrank]; norm_num)

/-! ## The localized power basis -/

instance : IsIntegralClosure (ChordModel E lam) (Polynomial (Fqbar E))
    (ChordL E lam) :=
  IsIntegralClosure.of_isIntegrallyClosed _ _ _

instance : IsLocalization
    (Algebra.algebraMapSubmonoid (ChordModel E lam)
      (Polynomial (Fqbar E))⁰) (ChordL E lam) :=
  IsIntegralClosure.isLocalization (Polynomial (Fqbar E)) (ChordK E)
    (ChordL E lam) (ChordModel E lam)

/-- The image of the chord generator `x̄` in `L`. -/
noncomputable def chordFracGen : ChordL E lam :=
  algebraMap (ChordModel E lam) (ChordL E lam) (chordPowerBasis E lam).gen

/-- The `K`-basis of `L` obtained by localizing `{1, x̄, x̄²}`. -/
noncomputable def chordFracBasis :
    Module.Basis (Fin (chordPowerBasis E lam).dim) (ChordK E) (ChordL E lam) :=
  Module.Basis.localizationLocalization (ChordK E) (Polynomial (Fqbar E))⁰
    (ChordL E lam) (chordPowerBasis E lam).basis

/-- The localized basis is the powers of the localized generator. -/
theorem chordFracBasis_apply (i : Fin (chordPowerBasis E lam).dim) :
    chordFracBasis E lam i = chordFracGen E lam ^ (i : ℕ) := by
  unfold chordFracBasis chordFracGen
  rw [Module.Basis.localizationLocalization_apply,
    (chordPowerBasis E lam).basis_eq_pow, map_pow]

/-- **The power basis of `L` over `K`** with generator the image of
`x̄`. -/
noncomputable def chordFracPowerBasis :
    PowerBasis (ChordK E) (ChordL E lam) where
  gen := chordFracGen E lam
  dim := (chordPowerBasis E lam).dim
  basis := chordFracBasis E lam
  basis_eq_pow := chordFracBasis_apply E lam

theorem chordFracPowerBasis_dim : (chordFracPowerBasis E lam).dim = 3 := by
  show (chordPowerBasis E lam).dim = 3
  have h := chordModel_finrank E lam
  rw [Module.finrank_eq_card_basis (chordPowerBasis E lam).basis,
    Fintype.card_fin] at h
  exact h

/-! ## The minimal polynomial of the generator -/

/-- The chord cubic mapped into `K`. -/
noncomputable def chordCubicK : Polynomial (ChordK E) :=
  (chordCubicBivBar E lam).map
    (algebraMap (Polynomial (Fqbar E)) (ChordK E))

theorem chordCubicK_monic : (chordCubicK E lam).Monic :=
  (chordCubicBivBar_monic E lam).map _

theorem chordCubicK_natDegree : (chordCubicK E lam).natDegree = 3 := by
  unfold chordCubicK
  rw [(chordCubicBivBar_monic E lam).natDegree_map, chordCubicBivBar_natDegree]

/-- The chord relation survives into the chord model: the generator
satisfies the chord cubic with `F̄[Z]`-coefficients. -/
theorem aeval_chordGen :
    Polynomial.aeval (chordPowerBasis E lam).gen (chordCubicBivBar E lam) =
      (0 : ChordModel E lam) := by
  have hgen : (chordPowerBasis E lam).gen =
      chordAlgEquiv E lam (AdjoinRoot.root (chordCubicBivBar E lam)) := by
    show ((AdjoinRoot.powerBasis' (chordCubicBivBar_monic E lam)).map
      (chordAlgEquiv E lam)).gen = _
    rw [PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen]
  rw [hgen, Polynomial.aeval_algEquiv]
  show chordAlgEquiv E lam
    (Polynomial.aeval (AdjoinRoot.root (chordCubicBivBar E lam))
      (chordCubicBivBar E lam)) = 0
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

/-- The generator of `L` satisfies the chord cubic over `K`. -/
theorem aeval_chordFracGen :
    Polynomial.aeval (chordFracGen E lam) (chordCubicK E lam) =
      (0 : ChordL E lam) := by
  unfold chordCubicK chordFracGen
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply,
    aeval_chordGen, map_zero]

/-- **The minimal polynomial of the generator is the chord cubic.** -/
theorem minpoly_chordFracGen :
    minpoly (ChordK E) (chordFracGen E lam) = chordCubicK E lam := by
  have hdvd : minpoly (ChordK E) (chordFracGen E lam) ∣ chordCubicK E lam :=
    minpoly.dvd _ _ (aeval_chordFracGen E lam)
  have hdeg : (minpoly (ChordK E) (chordFracGen E lam)).natDegree = 3 := by
    have h := (chordFracPowerBasis E lam).natDegree_minpoly
    rw [chordFracPowerBasis_dim] at h
    exact h
  have hmonic : (minpoly (ChordK E) (chordFracGen E lam)).Monic :=
    minpoly.monic ((chordFracPowerBasis E lam).isIntegral_gen)
  obtain ⟨c, hc⟩ := hdvd
  have hcmonic : c.Monic := by
    have := chordCubicK_monic E lam
    rw [hc] at this
    exact hmonic.of_mul_monic_left this
  have hcdeg : c.natDegree = 0 := by
    have := chordCubicK_natDegree E lam
    rw [hc, Polynomial.natDegree_mul hmonic.ne_zero hcmonic.ne_zero,
      hdeg] at this
    omega
  rw [hc, Polynomial.eq_one_of_monic_natDegree_zero hcmonic hcdeg, mul_one]

/-! ## Separability -/

instance : CharP (ChordK E) E.q := by
  have h1 : CharP (Fqbar E) E.q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod E.q) (Fqbar E)).injective E.q
  have h2 : CharP (Polynomial (Fqbar E)) E.q := by
    exact charP_of_injective_ringHom Polynomial.C_injective E.q
  exact charP_of_injective_ringHom
    (IsFractionRing.injective (Polynomial (Fqbar E)) (ChordK E)) E.q

/-- Every monic irreducible over `K` of degree `< q` is separable. -/
private theorem separable_of_natDegree_lt {p : Polynomial (ChordK E)}
    (hirr : Irreducible p) (hmonic : p.Monic) (hdeg : p.natDegree < E.q) :
    p.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hzero
  have hpos : 0 < p.natDegree := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    exact hirr.not_isUnit (hmonic.natDegree_eq_zero.mp h ▸ isUnit_one)
  have hcoeff := Polynomial.coeff_derivative p (p.natDegree - 1)
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  have hlead : p.coeff (p.natDegree - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel hpos]
    exact hmonic.coeff_natDegree
  rw [hlead, one_mul] at hcoeff
  have hne : ((p.natDegree - 1 : ℕ) + 1 : ChordK E) ≠ 0 := by
    have : ((p.natDegree - 1 : ℕ) + 1 : ChordK E) =
        ((p.natDegree - 1 + 1 : ℕ) : ChordK E) := by push_cast; ring
    rw [this, Ne, CharP.cast_eq_zero_iff (ChordK E) E.q]
    intro hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  exact hne hcoeff.symm

instance : Algebra.IsSeparable (ChordK E) (ChordL E lam) := by
  constructor
  intro x
  have hint : IsIntegral (ChordK E) x := IsIntegral.of_finite _ _
  have hirr : Irreducible (minpoly (ChordK E) x) := minpoly.irreducible hint
  have hmonic : (minpoly (ChordK E) x).Monic := minpoly.monic hint
  have hdeg : (minpoly (ChordK E) x).natDegree ≤ 3 := by
    have h : (minpoly (ChordK E) x).natDegree ≤
        Module.finrank (ChordK E) (ChordL E lam) := minpoly.natDegree_le x
    rwa [chordFrac_finrank] at h
  have hq : 5 ≤ E.q := E.hq_ge
  exact separable_of_natDegree_lt E hirr hmonic (by omega)

end Divisor
