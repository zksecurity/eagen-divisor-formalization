/-
  Divisor/OrdP/SupportClassification.lean — support classification
  and factorization for the point primes.

  * **Support classification** (`eq_pointPrime_of_mem`): under
    `splitsOnE E D`, every height-one prime of the coordinate ring
    containing `D.toCoordinateRing` is `pointPrime E P` for an
    `F_q`-rational point `P ∈ E.points` with `D.eval P = 0`.

    Route: the contraction of the prime to `F_q[X]` is a nonzero prime
    of a PID, so `(π)` with `π` prime; `N(D) = D·σD` lies in it, so
    `π ∣ N(D)`; `N(D)` splits, so `π` is linear with root `α` and
    `X − α` lies in the contraction. The fiber-rationality half of
    `splitsOnE` gives a rational `(α, y₀) ∈ E.points`; the relation
    `y² = f(x) ≡ f(α) = y₀²` modulo the prime forces `y ≡ ±y₀`, so the
    maximal ideal `⟨X − α, Y ∓ y₀⟩` sits inside the prime, hence equals
    it.

  * **2b Factorization** (`span_toCoordinateRing_eq_prod`):
    `span {D} = ∏_{P ∈ E.points} (XYIdeal P)^(ordAt E D P)`, from
    mathlib's `finprod_heightOneSpectrum_factorization`, with 2a
    bounding the support and Phase 1's `count_pointPrime_eq_ordAt`
    identifying the exponents.
-/
import Divisor.OrdP.ValuationBridgeOrd
import Divisor.SplitsOnE
import Mathlib.RingTheory.DedekindDomain.Factorization

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WithZero Multiplicative IsDedekindDomain

namespace Divisor

variable (E : ECSetup)

/-- `mk (C ·)` is the `F_q[X]`-algebra map into the coordinate ring. -/
theorem mk_C_eq_algebraMap (r : (ZMod E.q)[X]) :
    CoordinateRing.mk E.toW.toAffine (Polynomial.C r) =
      algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing r := by
  simp [AdjoinRoot.algebraMap_eq]

/-! ## 2a: support classification -/

/-- **Support classification.** Under `splitsOnE`, a height-one prime
containing `D` is the point prime of a rational point where `D`
vanishes. -/
theorem eq_pointPrime_of_mem (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (hSplit : splitsOnE E D)
    (v : HeightOneSpectrum E.toW.toAffine.CoordinateRing)
    (hmem : D.toCoordinateRing E ∈ v.asIdeal) :
    ∃ (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points),
      D.eval P.1 P.2 = 0 ∧ v = E.pointPrime hP := by
  classical
  -- The norm lies in the contraction of `v` to `F_q[X]`.
  have hNmem : algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
      (normPoly E D) ∈ v.asIdeal := by
    rw [← mk_C_eq_algebraMap, ← toCoordinateRing_mul_conjElt]
    exact Ideal.mul_mem_right _ _ hmem
  set p : Ideal (ZMod E.q)[X] :=
    Ideal.comap (algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing)
      v.asIdeal with hp
  have hpPrime : p.IsPrime := Ideal.IsPrime.comap _ (hK := v.isPrime)
  have hNp : normPoly E D ∈ p := hNmem
  have hN0 : normPoly E D ≠ 0 := normPoly_ne_zero E D hD
  -- `p` is `(π)` for a prime `π` dividing the split polynomial `N(D)`,
  -- so `π` is linear: extract the root `α`.
  obtain ⟨π, hπgen⟩ := (IsPrincipalIdealRing.principal p).principal
  rw [Ideal.submodule_span_eq] at hπgen
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [hπgen, Ideal.span_singleton_eq_bot.mpr rfl] at hNp
    exact hN0 (Ideal.mem_bot.mp hNp)
  have hπprime : Prime π := by
    have := hpPrime
    rw [hπgen] at this
    exact (Ideal.span_singleton_prime hπ0).mp this
  have hπdvd : π ∣ normPoly E D := by
    rw [hπgen, Ideal.mem_span_singleton] at hNp
    exact hNp
  have hNsplits : (normPoly E D).Splits :=
    (Polynomial.splits_iff_card_roots).mpr hSplit.1
  have hπdeg : π.degree = 1 :=
    (hNsplits.of_dvd hN0 hπdvd).degree_eq_one_of_irreducible hπprime.irreducible
  -- The root of `π`, and the monic linear generator `X − α` of `p`.
  have hπnat : π.natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some hπdeg
  have hπ1 : π.coeff 1 ≠ 0 := by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hπ0
    rwa [Polynomial.leadingCoeff, hπnat] at hlc
  have hπeq : π = Polynomial.C (π.coeff 1) * Polynomial.X +
      Polynomial.C (π.coeff 0) :=
    Polynomial.eq_X_add_C_of_degree_le_one hπdeg.le
  set a : ZMod E.q := π.coeff 1 with ha
  set b : ZMod E.q := π.coeff 0 with hb
  set α : ZMod E.q := -b / a with hα
  have hXsubmem : Polynomial.X - Polynomial.C α ∈ p := by
    have hkey : Polynomial.X - Polynomial.C α = Polynomial.C a⁻¹ * π := by
      rw [hπeq, hα, mul_add, ← mul_assoc, ← Polynomial.C_mul,
        inv_mul_cancel₀ hπ1, Polynomial.C_1, one_mul, ← Polynomial.C_mul,
        sub_eq_add_neg, ← Polynomial.C_neg]
      congr 1
      field_simp
    rw [hkey, hπgen]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hπroot : π.eval α = 0 := by
    rw [hπeq, hα]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    field_simp
    ring
  have hNroot : (normPoly E D).eval α = 0 := by
    obtain ⟨c, hc⟩ := hπdvd
    rw [hc, Polynomial.eval_mul, hπroot, zero_mul]
  -- Fiber rationality: a rational point `(α, y₀)` above `α`.
  obtain ⟨y₀, hy₀⟩ := hSplit.2 α
    (by rw [Polynomial.mem_roots hN0]; exact hNroot)
  -- `X − α ∈ v` at the coordinate-ring level.
  have hXv : CoordinateRing.XClass E.toW.toAffine α ∈ v.asIdeal := by
    have : CoordinateRing.XClass E.toW.toAffine α =
        algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
          (Polynomial.X - Polynomial.C α) := by
      rw [← mk_C_eq_algebraMap]
      rfl
    rw [this]
    exact hXsubmem
  -- `y² ≡ f(α) = y₀²` modulo `v`, so `y ≡ y₀` or `y ≡ −y₀`.
  have hy₀sq : y₀ ^ 2 = (curveX E).eval α := by
    have h := E.hOnCurve _ hy₀
    unfold curveX
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    exact h
  have hprod : (yClassZero E -
        algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
          (Polynomial.C y₀)) *
      (yClassZero E +
        algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
          (Polynomial.C y₀)) ∈ v.asIdeal := by
    have hcalc : (yClassZero E -
          algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
            (Polynomial.C y₀)) *
        (yClassZero E +
          algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
            (Polynomial.C y₀)) =
        algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
          (curveX E - Polynomial.C ((curveX E).eval α)) := by
      have hsq := yClassZero_sq E
      rw [mk_C_eq_algebraMap] at hsq
      rw [map_sub, ← hsq, ← hy₀sq, Polynomial.C_pow, map_pow]
      ring
    rw [hcalc]
    obtain ⟨g, hg⟩ := Polynomial.X_sub_C_dvd_sub_C_eval
      (a := α) (p := curveX E)
    rw [hg, map_mul]
    exact Ideal.mul_mem_right _ _ hXsubmem
  have hcases := v.isPrime.mem_or_mem hprod
  -- Package: pick the sheet on which `y` reduces rationally.
  have hmain : ∀ (y' : ZMod E.q), (α, y') ∈ E.points →
      (yClassZero E - algebraMap (ZMod E.q)[X] E.toW.toAffine.CoordinateRing
        (Polynomial.C y')) ∈ v.asIdeal →
      ∃ (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points),
        D.eval P.1 P.2 = 0 ∧ v = E.pointPrime hP := by
    intro y' hy' hyv
    have hYv : CoordinateRing.YClass E.toW.toAffine (Polynomial.C y') ∈
        v.asIdeal := by
      have : CoordinateRing.YClass E.toW.toAffine (Polynomial.C y') =
          yClassZero E - algebraMap (ZMod E.q)[X]
            E.toW.toAffine.CoordinateRing (Polynomial.C y') := by
        unfold CoordinateRing.YClass yClassZero
        rw [map_sub, mk_C_eq_algebraMap]
      rw [this]
      exact hyv
    -- `⟨X − α, Y − y'⟩ ≤ v`, and the left side is maximal.
    have hle : CoordinateRing.XYIdeal E.toW.toAffine α (Polynomial.C y') ≤
        v.asIdeal := by
      rw [CoordinateRing.XYIdeal, Ideal.span_le, Set.pair_subset_iff]
      exact ⟨hXv, hYv⟩
    have hmax : (CoordinateRing.XYIdeal E.toW.toAffine α
        (Polynomial.C y')).IsMaximal :=
      TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
        ((E.equation_iff α y').mpr (E.hOnCurve _ hy'))
    have heq := hmax.eq_of_le v.isPrime.ne_top hle
    refine ⟨(α, y'), hy', ?_, ?_⟩
    · have hmem' : D.toCoordinateRing E ∈
          CoordinateRing.XYIdeal E.toW.toAffine α (Polynomial.C y') := by
        rw [heq]
        exact hmem
      exact (CoordRingElt.toCoordinateRing_mem_XYIdeal_iff E D hy').mp hmem'
    · apply HeightOneSpectrum.ext
      rw [ECSetup.pointPrime_asIdeal]
      exact (heq ▸ rfl)
  rcases hcases with hyv | hyv
  · exact hmain y₀ hy₀ hyv
  · refine hmain (-y₀) (neg_snd_mem_points E hy₀) ?_
    rw [Polynomial.C_neg, map_neg, sub_neg_eq_add]
    exact hyv

/-! ## 2b: factorization of `span {D}` over the point primes -/

/-- **The ideal factorization** of `span {D.toCoordinateRing}` into
point primes with exponents `ordAt`. -/
theorem span_toCoordinateRing_eq_prod (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (hSplit : splitsOnE E D) :
    Ideal.span {D.toCoordinateRing E} =
      ∏ P ∈ E.points.attach,
        CoordinateRing.XYIdeal E.toW.toAffine P.1.1
          (Polynomial.C P.1.2) ^ ordAt E D P.1 := by
  classical
  have hI : Ideal.span {D.toCoordinateRing E} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact CoordRingElt.toCoordinateRing_ne_zero E D hD
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  have hsupp : (Function.mulSupport fun v :
      HeightOneSpectrum E.toW.toAffine.CoordinateRing =>
        v.maxPowDividing (Ideal.span {D.toCoordinateRing E})) ⊆
      ↑(E.points.attach.image fun P => E.pointPrime P.2) := by
    intro v hv
    rw [Function.mem_mulSupport, HeightOneSpectrum.maxPowDividing] at hv
    have hcount : (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {D.toCoordinateRing E})).factors ≠ 0 := by
      intro h
      rw [h, pow_zero] at hv
      exact hv rfl
    have hdvd : v.asIdeal ∣ Ideal.span {D.toCoordinateRing E} :=
      (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hcount
    have hmem : D.toCoordinateRing E ∈ v.asIdeal :=
      Ideal.dvd_span_singleton.mp hdvd
    obtain ⟨P, hP, -, hveq⟩ := eq_pointPrime_of_mem E D hD hSplit v hmem
    rw [Finset.coe_image, Set.mem_image]
    exact ⟨⟨P, hP⟩, by simp, hveq.symm⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  rw [Finset.prod_image (fun x _ y _ h => by
    apply Subtype.ext
    exact E.pointPrime_injective x.2 y.2 h)]
  apply Finset.prod_congr rfl
  intro P _
  rw [HeightOneSpectrum.maxPowDividing, count_pointPrime_eq_ordAt E D P.2 hD,
    ECSetup.pointPrime_asIdeal]

end Divisor
