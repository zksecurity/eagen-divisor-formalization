/-
  Divisor/Bridges/ChordFiberProductBarFactored.lean

  Multiplicity bridge for the base-changed chord-fiber product.

  Over `F_qbar`, the chord-fiber product of `D` (a function-field norm
  for the extension `F_qbar(E) / F_qbar(zLambdaBar lam)`) splits as a
  nonzero scalar times a product of linear factors indexed by the
  geometric support of `D`. Local multiplicities are the geometric
  divisor multiplicities.

  Mathematically: the divisor of the norm equals the push-forward of
  the divisor of `D`. Over an algebraically closed base, the
  push-forward zero divisor unfolds into linear factors with
  multiplicities equal to `gd.mult Q`. The remaining unit is a nonzero
  leading scalar.

  The root-multiplicity identity for the concrete resultant is proved
  by a squeeze argument (per-fibre divisibility against the global
  degree bound); the global factored form follows by ordinary
  polynomial factorisation over `F_qbar`.

  No projection / accounting hypotheses are needed in the statement;
  the geometric data carried by `gd` (a `GeometricDivisorData E D`)
  already pins them down.
-/
import Divisor.Bridges.ChordFiberProductNormZ

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ### Off-fibre boundary — multiplicity = 0 outside `gd.support.image`

The all-`z` form of the divisor-of-norm pushforward can be split into
two pieces:

* **Off-image side**: if `z` is not in the image
  of `gd.support` under `zLambdaBar lam`, then both sides of the
  equality are zero. The LHS `rootMultiplicity z` is zero because the
  set of roots of the bar-resultant is exactly that image (existing
  `chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image`),
  and the RHS sum is empty.
* **In-image side**: for `z` in the image, the multiplicity equals
  the sum of `gd.mult Q` over the fibre (the squeeze argument below).

The unrestricted form combines the two by case-splitting on image
membership. -/

/-- Off-image: when `z` is not in `zLambdaBar lam`'s image of
`gd.support`, no `Q ∈ gd.support` projects to `z`, so the per-fibre
multiplicity sum is empty. -/
theorem chord_fiber_product_concrete_bar_zfiber_sum_eq_zero_of_not_image
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (gd : GeometricDivisorData E D) {z : Fqbar E}
    (hz : z ∉ gd.support.image (zLambdaBar E lam)) :
    (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro Q hQ
  exfalso
  rcases Finset.mem_filter.mp hQ with ⟨hQs, hQe⟩
  exact hz (Finset.mem_image.mpr ⟨Q, hQs, hQe⟩)

/-- Off-image: when `z` is not in the image of `gd.support` under
`zLambdaBar lam`, the bar-resultant has multiplicity zero at `z`. -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zero_of_not_image
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) {z : Fqbar E}
    (hz : z ∉ gd.support.image (zLambdaBar E lam)) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
      (chord_fiber_product_concrete E lam D)).rootMultiplicity z = 0 := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hroots :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
      E lam D hD gd
  have hnot_root : ¬ p.IsRoot z := by
    intro hroot
    apply hz
    rw [← hroots]
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots' (p := p)).mpr ⟨hpne, hroot⟩)
  exact Polynomial.rootMultiplicity_eq_zero hnot_root

/-- **Narrow divisor-of-norm multiplicity theorem for the concrete resultant.**

    For each `z` actually in the image of `gd.support` under
    `zLambdaBar lam`, the multiplicity of `z` as a root of the
    concrete chord-fiber resultant equals the sum of the local
    multiplicities of geometric zeros in the fibre
    `zLambdaBar = z`. The off-image case is proved separately above.

    This is exactly the push-forward of the zero divisor under the chord
    projection, i.e. `div(N(D)) = π_*(div D)` written coefficientwise.

    Proof: the squeeze argument
    `Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le` on
    - root set: `chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image`;
    - per-fibre divisibility (lower bound):
      `chord_fiber_product_concrete_bar_zfiber_pow_dvd`, from the
      chord-algebra relNorm calculus and the norm-is-resultant
      identity (`Divisor/OrdP/ChordNorm.lean`,
      `Divisor/OrdP/ChordResultant.lean`);
    - global natDegree bound (upper bound):
      `chord_fiber_product_concrete_natDegree_le_normPoly_natDegree`
      via the weighted-Sylvester analysis;
    - `mult_sum_eq_normPoly_natDegree`: Σ_Q gd.mult Q = (normPoly).natDegree. -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z ∈ gd.support.image (zLambdaBar E lam),
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hroots :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
      E lam D hD gd
  have hdvd : ∀ z ∈ gd.support.image (zLambdaBar E lam),
      (Polynomial.X - Polynomial.C z) ^
        (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
        ∣ p :=
    fun z _ =>
      chord_fiber_product_concrete_bar_zfiber_pow_dvd E D lam hD gd z
  have hdeg : p.natDegree ≤ ∑ Q ∈ gd.support, gd.mult Q := by
    rw [GeometricDivisorData.mult_sum_eq_normPoly_natDegree E D hD gd]
    rw [hp_def, Polynomial.natDegree_map_eq_of_injective
          (algebraMap (ZMod E.q) (Fqbar E)).injective]
    exact chord_fiber_product_concrete_natDegree_le_normPoly_natDegree E lam D hD
  exact fun z hz =>
    Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le
      p gd.support (zLambdaBar E lam) gd.mult hpne hroots hdvd hdeg z

/-- **The unrestricted divisor-of-norm pushforward**: the in-image
identity plus the off-image boundary lemma, combined by
case-splitting.

The unrestricted form is what downstream consumers
(`chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity`,
`chord_fiber_product_bar_eq_geom_prod`) actually use. -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  classical
  intro z
  by_cases hz : z ∈ gd.support.image (zLambdaBar E lam)
  · exact chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image
      E D lam hD gd z hz
  · rw [chord_fiber_product_concrete_bar_rootMultiplicity_eq_zero_of_not_image
        E D lam hD gd hz,
        chord_fiber_product_concrete_bar_zfiber_sum_eq_zero_of_not_image
        E D lam gd hz]

/-- **Polynomial factorisation from root-multiplicity accounting.** -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hZ : ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hpsplit : p.Splits := IsAlgClosed.splits _
  have hcard : p.roots.card = p.natDegree := hpsplit.natDegree_eq_card_roots.symm
  refine ⟨p.leadingCoeff, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hfac :
      C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hrootSet :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image E lam D hD gd
  have hMaps : ∀ Q ∈ gd.support, zLambdaBar E lam Q ∈
      gd.support.image (zLambdaBar E lam) :=
    fun Q hQ => Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
  have hprod :
      (p.roots.map fun a => X - C a).prod =
        ∏ Q ∈ gd.support, (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
    rw [Finset.prod_multiset_map_count]
    rw [hrootSet]
    have hcount_eq : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (X - C z) ^ (p.roots.count z) =
        (X - C z) ^
          (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
            gd.mult Q) := by
      intro z _
      rw [Polynomial.count_roots, hZ]
    rw [Finset.prod_congr rfl hcount_eq]
    rw [Finset.prod_congr rfl
      (fun z _ => (Finset.prod_pow_eq_pow_sum
        (gd.support.filter (fun Q => zLambdaBar E lam Q = z))
        gd.mult (X - C z)).symm)]
    have hZreplace : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (X - C z) ^ (gd.mult Q)) =
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)) := by
      intro z _
      refine Finset.prod_congr rfl ?_
      intro Q hQ
      rw [(Finset.mem_filter.mp hQ).2]
    rw [Finset.prod_congr rfl hZreplace]
    exact Finset.prod_fiberwise_of_maps_to hMaps
      (fun Q => (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q))
  conv_lhs => rw [← hfac]
  rw [hprod]

/-- **Geometric factored-form bridge for the chord-fiber product.**

    Over `F_qbar`, the base-changed chord-fiber product of a nonzero
    `D` splits as a nonzero leading scalar times a product of linear
    factors `(X - C (zLambdaBar E lam Q))^(gd.mult Q)` indexed by the
    geometric support of `D`.

    This is the divisor-of-norm formula
    `div(N(D)) = π_*(div D)` for the function-field extension
    `F_qbar(E) / F_qbar(zLambdaBar lam)`, evaluated globally over the
    algebraically closed base: every prime divisor of the base is a
    `(z)` for some `z : F_qbar`, the push-forward zero divisor is
    `∑_Q gd.mult Q · (zLambdaBar Q)`, and the principal divisor of
    the norm reads back as the product of linear factors above.

    Local multiplicities and the global non-vanishing follow from this
    bridge alone (see `chord_fiber_product_bar_rootMultiplicity_eq_zfiber`
    and `chord_fiber_product_ne_zero` in `Divisor/GeometricSoundness.lean`).
-/
theorem chord_fiber_product_bar_eq_geom_prod
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  dsimp [chord_fiber_product]
  exact chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity E D lam hD gd
    (chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber E D lam hD gd)

end Divisor
