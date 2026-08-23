/-
  Divisor/OrdP/ChordNorm.lean — the relNorm-calculus lower bound for
  the chord-fiber product.

  For each chord intercept `z₀`, the fiber of geometric zeros of `D`
  above `z₀` contributes its summed multiplicity to the `(Z − z₀)`-adic
  order of the relative norm of `D̄` along the chord algebra
  `F̄[Z] → ChordModel E lam`:

    `(Z − z₀)^{Σ_{Q ↦ z₀} gd.mult Q} ∣ intNorm F̄[Z] (ChordModel) D̄`.

  Chain: the geometric valuation bridge gives `D̄ ∈ m_Q^{mult Q}` at
  every geometric zero
  (`intValuation_le_pow_iff_mem`); distinct points give distinct
  maximal ideals, so the fiber product `∏ m_Q^{mult Q}` divides
  `span {D̄}`; `relNorm` is monotone and multiplicative with
  `relNorm (span {r}) = span {intNorm r}`; and `relNorm m_Q` lands in
  the maximal ideal `(Z − z₀)` because `z̄ − z₀` vanishes at `Q`.
-/
import Divisor.OrdP.ChordAlgebra
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Divisor

variable (E : ECSetup) (lam : ZMod E.q)

/-! ## Elements and point ideals of the chord model -/

/-- `D̄` as an element of the chord model. -/
noncomputable def chordD (D : CoordRingElt E.q) : ChordModel E lam :=
  barD E (geomAPoly E D) (geomBPoly E D)

/-- The point ideal at a geometric point, as an ideal of the chord
model. -/
noncomputable def chordPointIdeal (Q : GeomPoint E) :
    Ideal (ChordModel E lam) :=
  (geomPointPrime E Q).asIdeal

/-- `chordToBar` is injective (it is an isomorphism). -/
theorem chordToBar_injective : Function.Injective (chordToBar E lam) := by
  intro a b hab
  apply (chordEquiv E lam).injective
  simpa [chordEquiv, RingEquiv.ofRingHom_apply] using hab

/-- The chord structure map `F̄[Z] → R̄` is injective. -/
theorem zHom_injective : Function.Injective (zHom E lam) := by
  have hof : Function.Injective (AdjoinRoot.of (chordCubicBivBar E lam)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by
      rw [Polynomial.degree_eq_natDegree (chordCubicBivBar_monic E lam).ne_zero,
        chordCubicBivBar_natDegree]
      norm_num)
  intro a b hab
  apply hof
  apply chordToBar_injective E lam
  rw [chordToBar_of, chordToBar_of, hab]

/-- Torsion-freeness of the chord model over `F̄[Z]`. -/
instance : Module.IsTorsionFree (Polynomial (Fqbar E)) (ChordModel E lam) :=
  (Module.isTorsionFree_iff_algebraMap_injective).mpr (zHom_injective E lam)

/-! ## Membership at the fiber points -/

/-- `D̄` lies in the `mult Q`-th power of the point ideal at every
geometric point (P3.pre in membership form). -/
theorem chordD_mem_pow (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) :
    chordD E lam D ∈ chordPointIdeal E lam Q ^ gd.mult Q := by
  have hval := geomPointPrime_intValuation_toBar E D hD Q
  rw [gd.mult_eq_geomLocalOrder]
  exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
    (geomPointPrime E Q) _ (geomLocalOrder E D Q)).mp (le_of_eq hval)

/-- Distinct geometric points give distinct point ideals. -/
theorem chordPointIdeal_injective {Q Q' : GeomPoint E} (h : Q ≠ Q') :
    chordPointIdeal E lam Q ≠ chordPointIdeal E lam Q' := by
  intro heq
  apply h
  have heq' : CoordinateRing.XYIdeal E.toWBar.toAffine Q.x
      (Polynomial.C Q.y) =
      CoordinateRing.XYIdeal E.toWBar.toAffine Q'.x (Polynomial.C Q'.y) := heq
  obtain ⟨hx, hy⟩ :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff
      (Q.equation E)).mp heq'
  cases Q
  cases Q'
  simp only at hx hy
  subst hx
  subst hy
  rfl

/-- The fiber product of point-ideal powers divides `span {D̄}`. -/
theorem prod_chordPointIdeal_pow_dvd (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (gd : GeometricDivisorData E D)
    (z₀ : Fqbar E) [DecidableEq (Fqbar E)] :
    (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
        chordPointIdeal E lam Q ^ gd.mult Q) ∣
      Ideal.span {chordD E lam D} := by
  apply Finset.prod_dvd_of_coprime
  · intro Q hQ Q' hQ' hne
    exact ((Ideal.isCoprime_iff_sup_eq).mpr
      ((geomPointPrime_isMaximal E Q).coprime_of_ne
        (geomPointPrime_isMaximal E Q')
        (chordPointIdeal_injective E lam hne))).pow
  · intro Q _
    rw [Ideal.dvd_span_singleton]
    exact chordD_mem_pow E lam D hD gd Q

/-! ## The relNorm of a point ideal -/

/-- `z̄ − z₀` vanishes at every geometric point of the fiber above
`z₀`, so `Z − z₀` lies in the contraction of the point ideal. -/
theorem X_sub_C_mem_comap (Q : GeomPoint E) {z₀ : Fqbar E}
    (hz : zLambdaBar E lam Q = z₀) :
    (Polynomial.X - Polynomial.C z₀ : Polynomial (Fqbar E)) ∈
      Ideal.comap (algebraMap (Polynomial (Fqbar E)) (ChordModel E lam))
        (chordPointIdeal E lam Q) := by
  show zHom E lam (Polynomial.X - Polynomial.C z₀) ∈
    (geomPointPrime E Q).asIdeal
  rw [map_sub, zHom_X, zHom_C]
  have hform : zElt E lam -
      algebraMap (Fqbar E) E.toWBar.toAffine.CoordinateRing z₀ =
      barD E (-(Polynomial.C z₀) -
          Polynomial.C (fqToBar E lam) * Polynomial.X) (-1) := by
    unfold barD zElt yClassZeroBar
    rw [algebraMap_bar_eq_mk]
    simp only [map_sub, map_mul, map_neg, map_one]
    ring
  rw [hform, barD_mem_XYIdeal_iff]
  unfold barEval zLambdaBar at *
  simp only [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one]
  unfold fqToBar at *
  linear_combination hz

/-- The relative norm of a point ideal above `z₀` lands in
`(Z − z₀)`. -/
theorem relNorm_chordPointIdeal_le (Q : GeomPoint E) {z₀ : Fqbar E}
    (hz : zLambdaBar E lam Q = z₀) :
    Ideal.relNorm (Polynomial (Fqbar E)) (chordPointIdeal E lam Q) ≤
      Ideal.span {Polynomial.X - Polynomial.C z₀} := by
  refine le_trans (Ideal.relNorm_le_comap _ _) (le_of_eq ?_)
  have hmax : (Ideal.span {Polynomial.X - Polynomial.C z₀} :
      Ideal (Polynomial (Fqbar E))).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Polynomial.irreducible_X_sub_C z₀)
  have hprime : (Ideal.comap
      (algebraMap (Polynomial (Fqbar E)) (ChordModel E lam))
      (chordPointIdeal E lam Q)).IsPrime :=
    Ideal.IsPrime.comap _ (hK := (geomPointPrime E Q).isPrime)
  have hle : Ideal.span {Polynomial.X - Polynomial.C z₀} ≤
      Ideal.comap (algebraMap (Polynomial (Fqbar E)) (ChordModel E lam))
        (chordPointIdeal E lam Q) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (X_sub_C_mem_comap E lam Q hz)
  exact (hmax.eq_of_le hprime.ne_top hle).symm

/-! ## The lower bound -/

/-- **The relNorm lower bound**: for every chord intercept `z₀`,
`(Z − z₀)^{Σ_{Q ↦ z₀} mult Q}` divides the relative norm of `D̄`. -/
theorem X_sub_C_pow_fiberSum_dvd_intNorm (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (gd : GeometricDivisorData E D)
    (z₀ : Fqbar E) [DecidableEq (Fqbar E)] :
    (Polynomial.X - Polynomial.C z₀) ^
        (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
          gd.mult Q) ∣
      Algebra.intNorm (Polynomial (Fqbar E)) (ChordModel E lam)
        (chordD E lam D) := by
  rw [← Ideal.span_singleton_le_span_singleton]
  calc Ideal.span {Algebra.intNorm (Polynomial (Fqbar E))
        (ChordModel E lam) (chordD E lam D)}
      = Ideal.relNorm (Polynomial (Fqbar E))
          (Ideal.span {chordD E lam D}) :=
        (Ideal.relNorm_singleton _ _).symm
    _ ≤ Ideal.relNorm (Polynomial (Fqbar E))
          (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
            chordPointIdeal E lam Q ^ gd.mult Q) :=
        Ideal.relNorm_mono (R := Polynomial (Fqbar E))
          (Ideal.le_of_dvd (prod_chordPointIdeal_pow_dvd E lam D hD gd z₀))
    _ = ∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
          Ideal.relNorm (Polynomial (Fqbar E))
            (chordPointIdeal E lam Q) ^ gd.mult Q := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun Q _ => map_pow _ _ _
    _ ≤ ∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
          Ideal.span {Polynomial.X - Polynomial.C z₀} ^ gd.mult Q := by
        gcongr with Q hQ
        exact relNorm_chordPointIdeal_le E lam Q
          (Finset.mem_filter.mp hQ).2
    _ = Ideal.span {(Polynomial.X - Polynomial.C z₀) ^
          (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z₀),
            gd.mult Q)} := by
        rw [Finset.prod_pow_eq_pow_sum, Ideal.span_singleton_pow]

end Divisor
