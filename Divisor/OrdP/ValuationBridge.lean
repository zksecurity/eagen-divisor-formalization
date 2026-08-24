/-
  Divisor/OrdP/ValuationBridge.lean — foundations
  of the valuation bridge between the project's recursive `ordAt` and
  mathlib's `HeightOneSpectrum.intValuation` at the point primes of
  `Divisor/OrdP/DedekindSetup.lean`.

  Contents:

  * membership ↔ vanishing at the point (`mem_pointPrime_iff`),
    valuation-one ↔ non-vanishing;
  * the `XIdeal` factorization `⟨X − x₀⟩ = σP · P` (mathlib's
    `XYIdeal_neg_mul` in our short-Weierstrass shape), giving the
    uniformizer valuations: `v_P(X − x₀) = exp(−1)` at non-2-torsion
    points and `exp(−2)` at 2-torsion points;
  * univariate valuations: `v_P(g(x)) = exp(−(e_P · rootMult x₀ g))`
    with `e_P = 1` (resp. `2`) off (resp. on) 2-torsion;
  * the conjugate `D.conjElt = (a, −b)` and the norm identity
    `D · σD = N(D)` in the coordinate ring, via the vendored
    `mul_conj` route already reduced to `normPoly` by
    `norm_toCoordinateRing_eq_normPoly`.

  The `ordAt` bridge theorems themselves build on these
  in `Divisor/OrdP/ValuationBridgeOrd.lean`.
-/
import Divisor.OrdP.DedekindSetup
import Divisor.OrdP.Uniformizer
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WithZero Multiplicative IsDedekindDomain

namespace Divisor

variable (E : ECSetup)

/-! ## Generic helper: valuation from an `emultiplicity` computation -/

/-- If the `v`-multiplicity of `span {r}` is the natural number `n`,
the `v`-adic valuation of `r` is `exp (−n)`. -/
theorem intValuation_eq_exp_neg_of_emultiplicity
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {r : R} {n : ℕ}
    (h : emultiplicity v.asIdeal (Ideal.span {r}) = n) :
    v.intValuation r = exp (-(n : ℤ)) :=
  le_antisymm (v.intValuation_le_exp_iff_le_emultiplicity.mpr h.ge)
    (v.exp_le_intValuation_iff_emultiplicity_le.mpr h.le)

/-! ## Membership in the point prime ↔ vanishing at the point -/

/-- `D ∈ P` iff `D` vanishes at the point: `toCoordinateRing_mem_XYIdeal_iff`
restated at `pointPrime`. -/
theorem mem_pointPrime_iff (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    D.toCoordinateRing E ∈ (E.pointPrime hP).asIdeal ↔ D.eval P.1 P.2 = 0 := by
  rw [ECSetup.pointPrime_asIdeal]
  exact CoordRingElt.toCoordinateRing_mem_XYIdeal_iff E D hP

/-- `v_P(D) = 1` iff `D` does not vanish at `P`. -/
theorem pointPrime_intValuation_eq_one_iff (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) = 1 ↔
      D.eval P.1 P.2 ≠ 0 := by
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  exact not_congr (mem_pointPrime_iff E D hP)

/-! ## The conjugate point and the `XIdeal` factorization -/

/-- For our short-Weierstrass shape, mathlib's `negY` is plain negation. -/
@[simp] theorem toW_negY (x y : ZMod E.q) : E.toW.toAffine.negY x y = -y := by
  rw [Affine.negY]
  show -y - E.toW.a₁ * x - E.toW.a₃ = -y
  rw [ECSetup.toW_a₁, ECSetup.toW_a₃]
  ring

/-- The conjugate point `σP = (x₀, −y₀)` is on the curve. -/
theorem neg_snd_mem_points {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    (P.1, -P.2) ∈ E.points := by
  apply E.hComplete
  have h := E.hOnCurve P hP
  calc (-P.2) ^ 2 = P.2 ^ 2 := by ring
    _ = P.1 ^ 3 + E.curveA * P.1 + E.curveB := h

/-- The principal ideal `⟨X − x₀⟩` of the coordinate ring factors as
`σP · P` (mathlib's `XYIdeal_neg_mul` in our shape). -/
theorem xIdeal_eq_mul {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    CoordinateRing.XIdeal E.toW.toAffine P.1 =
      CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C (-P.2)) *
        CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C P.2) := by
  have h := CoordinateRing.XYIdeal_neg_mul (nonsing_of_mem E hP)
  rw [toW_negY] at h
  exact h.symm

/-- `2 ≠ 0` in `ZMod E.q` (the characteristic is a prime `≥ 5`). -/
theorem two_ne_zero_zmod : (2 : ZMod E.q) ≠ 0 := by
  have hq5 : E.q ≥ 5 := E.hq_ge
  have hcast : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
  rw [hcast, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
  intro hdvd
  have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Off 2-torsion, the conjugate prime is a different maximal ideal. -/
theorem xyIdeal_neg_ne {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hy : P.2 ≠ 0) :
    CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C (-P.2)) ≠
      CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C P.2) := by
  intro h
  have hσeq : E.toW.toAffine.Equation P.1 (-P.2) :=
    (E.equation_iff P.1 (-P.2)).mpr (E.hOnCurve _ (neg_snd_mem_points E hP))
  obtain ⟨-, hyy⟩ :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff hσeq).mp h
  -- hyy : -P.2 = P.2, so 2 · P.2 = 0 with 2 ≠ 0 in a field.
  apply hy
  have h2y : (2 : ZMod E.q) * P.2 = 0 := by linear_combination -hyy
  exact (mul_eq_zero.mp h2y).resolve_left (two_ne_zero_zmod E)

/-! ## Uniformizer valuations of `XClass` -/

/-- The point prime, like every ideal, is nonzero as an element of the
ideal monoid. -/
private theorem pointPrime_ne_zero {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) : (E.pointPrime hP).asIdeal ≠ 0 := fun h =>
  (E.pointPrime hP).ne_bot (by rwa [Ideal.zero_eq_bot] at h)

/-- **Non-2-torsion uniformizer**: at `P = (x₀, y₀)` with `y₀ ≠ 0`,
`v_P(X − x₀) = exp(−1)`; the class of `X − x₀` is a uniformizer. -/
theorem pointPrime_intValuation_XClass_of_ne_zero
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hy : P.2 ≠ 0) :
    (E.pointPrime hP).intValuation
      (CoordinateRing.XClass E.toW.toAffine P.1) = exp (-1 : ℤ) := by
  have hprime : Prime (E.pointPrime hP).asIdeal := (E.pointPrime hP).prime
  -- σP does not divide into P: distinct maximal ideals.
  have hnd : ¬ (E.pointPrime hP).asIdeal ∣
      CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C (-P.2)) := by
    rw [Ideal.dvd_iff_le]
    intro hle
    have hσmax :
        (CoordinateRing.XYIdeal E.toW.toAffine P.1
          (Polynomial.C (-P.2))).IsMaximal :=
      TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
        ((E.equation_iff P.1 (-P.2)).mpr (E.hOnCurve _ (neg_snd_mem_points E hP)))
    have heq := hσmax.eq_of_le (E.pointPrime_isMaximal hP).ne_top hle
    rw [ECSetup.pointPrime_asIdeal] at heq
    exact xyIdeal_neg_ne E hP hy heq
  have hcount : emultiplicity (E.pointPrime hP).asIdeal
      (Ideal.span {CoordinateRing.XClass E.toW.toAffine P.1}) = (1 : ℕ) := by
    have hspan : Ideal.span {CoordinateRing.XClass E.toW.toAffine P.1} =
        CoordinateRing.XYIdeal E.toW.toAffine P.1 (Polynomial.C (-P.2)) *
          (E.pointPrime hP).asIdeal := by
      rw [ECSetup.pointPrime_asIdeal]
      exact xIdeal_eq_mul E hP
    rw [hspan, emultiplicity_mul hprime, emultiplicity_eq_zero.mpr hnd, zero_add]
    exact (FiniteMultiplicity.of_prime_left hprime
      (pointPrime_ne_zero E hP)).emultiplicity_self
  simpa using intValuation_eq_exp_neg_of_emultiplicity _ hcount

/-- **2-torsion order of `X − x₀`**: at `P = (x₀, 0)`,
`v_P(X − x₀) = exp(−2)`. -/
theorem pointPrime_intValuation_XClass_of_eq_zero
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hy : P.2 = 0) :
    (E.pointPrime hP).intValuation
      (CoordinateRing.XClass E.toW.toAffine P.1) = exp (-2 : ℤ) := by
  have hprime : Prime (E.pointPrime hP).asIdeal := (E.pointPrime hP).prime
  have hcount : emultiplicity (E.pointPrime hP).asIdeal
      (Ideal.span {CoordinateRing.XClass E.toW.toAffine P.1}) = (2 : ℕ) := by
    have hspan : Ideal.span {CoordinateRing.XClass E.toW.toAffine P.1} =
        (E.pointPrime hP).asIdeal ^ 2 := by
      rw [ECSetup.pointPrime_asIdeal, hy]
      have h := xIdeal_eq_mul E hP
      rw [hy, neg_zero] at h
      rw [sq, ← h]
      rfl
    rw [hspan]
    exact emultiplicity_pow_self_of_prime hprime 2
  simpa using intValuation_eq_exp_neg_of_emultiplicity _ hcount

/-! ## Univariate valuations -/

/-- The univariate `g` as a `CoordRingElt` has coordinate-ring image
`mk (C g)`. -/
theorem toCoordinateRing_C (g : (ZMod E.q)[X]) :
    (⟨g, 0⟩ : CoordRingElt E.q).toCoordinateRing E =
      CoordinateRing.mk E.toW.toAffine (Polynomial.C g) := by
  unfold CoordRingElt.toCoordinateRing CoordRingElt.toBivar
  simp

/-- The evaluation of the univariate `g` as a `CoordRingElt`. -/
theorem eval_C_coordRingElt (g : (ZMod E.q)[X]) (x y : ZMod E.q) :
    (⟨g, 0⟩ : CoordRingElt E.q).eval x y = g.eval x := by
  unfold CoordRingElt.eval
  simp

/-- A univariate polynomial not vanishing at `x₀` is a unit at `P`:
its valuation is `1`. -/
theorem pointPrime_intValuation_mk_C_eq_one
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) {h : (ZMod E.q)[X]}
    (hh : h.eval P.1 ≠ 0) :
    (E.pointPrime hP).intValuation
      (CoordinateRing.mk E.toW.toAffine (Polynomial.C h)) = 1 := by
  rw [← toCoordinateRing_C]
  rw [pointPrime_intValuation_eq_one_iff E _ hP, eval_C_coordRingElt]
  exact hh

/-- **Univariate valuation**: for `g ≠ 0`,
`v_P(g(x)) = exp(−(e_P · rootMult x₀ g))` with `e_P = 1` at
non-2-torsion `P` and `e_P = 2` at 2-torsion `P`. -/
theorem pointPrime_intValuation_mk_C
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) {g : (ZMod E.q)[X]}
    (hg : g ≠ 0) :
    (E.pointPrime hP).intValuation
        (CoordinateRing.mk E.toW.toAffine (Polynomial.C g)) =
      exp (-(((if P.2 = 0 then 2 else 1) * rootMultiplicity P.1 g : ℕ) : ℤ)) := by
  set m := rootMultiplicity P.1 g with hm
  set h := g /ₘ (Polynomial.X - Polynomial.C P.1) ^ m with hh
  have hfact : (Polynomial.X - Polynomial.C P.1) ^ m * h = g :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq g P.1
  have hhne : h.eval P.1 ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero P.1 hg
  -- Push the factorization through `mk ∘ C`.
  have hmk : CoordinateRing.mk E.toW.toAffine (Polynomial.C g) =
      CoordinateRing.XClass E.toW.toAffine P.1 ^ m *
        CoordinateRing.mk E.toW.toAffine (Polynomial.C h) := by
    rw [← hfact]
    rw [map_mul, map_pow]
    rfl
  rw [hmk, map_mul, map_pow,
    pointPrime_intValuation_mk_C_eq_one E hP hhne, mul_one]
  by_cases hy : P.2 = 0
  · rw [pointPrime_intValuation_XClass_of_eq_zero E hP hy, if_pos hy,
      ← exp_nsmul]
    congr 1
    push_cast
    ring
  · rw [pointPrime_intValuation_XClass_of_ne_zero E hP hy, if_neg hy,
      ← exp_nsmul]
    congr 1
    push_cast
    ring

/-! ## The conjugate element and the norm identity -/

/-- The conjugate `σD = a + b·y` of `D = a − b·y`: `D` evaluated on the
other sheet. -/
noncomputable def CoordRingElt.conjElt {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) : CoordRingElt q :=
  ⟨D.a, -D.b⟩

@[simp] theorem CoordRingElt.conjElt_a {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) : D.conjElt.a = D.a := rfl

@[simp] theorem CoordRingElt.conjElt_b {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) : D.conjElt.b = -D.b := rfl

/-- Evaluating the conjugate at `(x, y)` is evaluating `D` at `(x, −y)`. -/
theorem CoordRingElt.conjElt_eval {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (x y : ZMod q) :
    D.conjElt.eval x y = D.eval x (-y) := by
  unfold CoordRingElt.eval
  simp only [conjElt_a, conjElt_b, Polynomial.eval_neg]
  ring

/-- The conjugate is zero exactly when `D` is. -/
theorem CoordRingElt.conjElt_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (D : CoordRingElt q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ¬ (D.conjElt.a = 0 ∧ D.conjElt.b = 0) := by
  simp only [conjElt_a, conjElt_b, neg_eq_zero]
  exact hD

/-- The Weierstrass polynomial of our short-Weierstrass curve is
`Y² − (X³ + A·X + B)`. -/
theorem toW_polynomial :
    E.toW.toAffine.polynomial = Polynomial.X ^ 2 - Polynomial.C (curveX E) := by
  rw [Affine.polynomial]
  show Polynomial.X ^ 2
      + Polynomial.C (Polynomial.C E.toW.a₁ * Polynomial.X + Polynomial.C E.toW.a₃)
        * Polynomial.X
      - Polynomial.C (Polynomial.X ^ 3 + Polynomial.C E.toW.a₂ * Polynomial.X ^ 2
          + Polynomial.C E.toW.a₄ * Polynomial.X + Polynomial.C E.toW.a₆) = _
  rw [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₃, ECSetup.toW_a₄,
    ECSetup.toW_a₆]
  unfold curveX
  simp only [Polynomial.C_0, zero_mul, add_zero]

/-- **The norm identity in the coordinate ring**: `D · σD = N(D)`,
with `N(D) = a² − b²·(X³ + A·X + B)` the project's `normPoly`. -/
theorem toCoordinateRing_mul_conjElt (D : CoordRingElt E.q) :
    D.toCoordinateRing E * D.conjElt.toCoordinateRing E =
      CoordinateRing.mk E.toW.toAffine (Polynomial.C (normPoly E D)) := by
  unfold CoordRingElt.toCoordinateRing
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  refine ⟨-Polynomial.C (D.b ^ 2), ?_⟩
  rw [toW_polynomial, normPoly_eq]
  unfold CoordRingElt.toBivar curveX
  simp only [CoordRingElt.conjElt_a, CoordRingElt.conjElt_b, Polynomial.C_neg,
    Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_pow]
  ring

/-- The valuation of `D · σD` through the norm identity and the
univariate valuation of `normPoly`. -/
theorem pointPrime_intValuation_mul_conjElt (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) *
        (E.pointPrime hP).intValuation (D.conjElt.toCoordinateRing E) =
      exp (-(((if P.2 = 0 then 2 else 1) *
        rootMultiplicity P.1 (normPoly E D) : ℕ) : ℤ)) := by
  rw [← map_mul, toCoordinateRing_mul_conjElt]
  exact pointPrime_intValuation_mk_C E hP (normPoly_ne_zero E D hD)

/-- **Lone-sheet valuation**: at non-2-torsion `P` where
`D` vanishes but its conjugate does not,
`v_P(D) = exp(−rootMult x₀ N(D))`. -/
theorem pointPrime_intValuation_of_lone (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hy : P.2 ≠ 0)
    (hlone : D.eval P.1 (-P.2) ≠ 0) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-(rootMultiplicity P.1 (normPoly E D) : ℤ)) := by
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := by
    rintro ⟨ha, hb⟩
    apply hlone
    unfold CoordRingElt.eval
    rw [ha, hb]
    simp
  have hconj : (E.pointPrime hP).intValuation
      (D.conjElt.toCoordinateRing E) = 1 := by
    rw [pointPrime_intValuation_eq_one_iff E _ hP, CoordRingElt.conjElt_eval]
    exact hlone
  have hmul := pointPrime_intValuation_mul_conjElt E D hP hD
  rw [hconj, mul_one, if_neg hy, one_mul] at hmul
  exact hmul

/-! ## 2-torsion: the valuation of `y` and the closed form -/

/-- The derivative of the fiber cubic, evaluated. -/
theorem curveX_derivative_eval (x₀ : ZMod E.q) :
    (Polynomial.derivative (curveX E)).eval x₀ = 3 * x₀ ^ 2 + E.curveA := by
  unfold curveX
  rw [Polynomial.derivative_add, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_C_mul,
    Polynomial.derivative_X, Polynomial.derivative_C]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, mul_one, add_zero]
  norm_num

/-- Nonsingularity at a 2-torsion point says the fiber cubic has a
simple root: `3x₀² + A ≠ 0`. -/
theorem three_sq_add_A_ne_zero {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hy : P.2 = 0) :
    3 * P.1 ^ 2 + E.curveA ≠ 0 := by
  have hns := nonsing_of_mem E hP
  rw [Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · intro hzero
    apply h
    show E.toW.a₁ * P.2 - (3 * P.1 ^ 2 + 2 * E.toW.a₂ * P.1 + E.toW.a₄) = 0
    rw [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
    linear_combination -hzero
  · exfalso
    apply h
    show 2 * P.2 + E.toW.a₁ * P.1 + E.toW.a₃ = 0
    rw [hy, ECSetup.toW_a₁, ECSetup.toW_a₃]
    ring

/-- At a 2-torsion point the fiber cubic has root multiplicity exactly
one at `x₀`. -/
theorem rootMultiplicity_curveX_eq_one {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hy : P.2 = 0) :
    rootMultiplicity P.1 (curveX E) = 1 := by
  have hroot : (curveX E).IsRoot P.1 := by
    show (curveX E).eval P.1 = 0
    unfold curveX
    have h := E.hOnCurve P hP
    rw [hy] at h
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination -h
  have hge : 1 ≤ rootMultiplicity P.1 (curveX E) :=
    (Polynomial.rootMultiplicity_pos (curveX_ne_zero E)).mpr hroot
  have hlt : rootMultiplicity P.1 (curveX E) < 2 := by
    by_contra hle
    rw [not_lt] at hle
    have hdvd : (Polynomial.X - Polynomial.C P.1) ^ 2 ∣ curveX E :=
      (Polynomial.le_rootMultiplicity_iff (curveX_ne_zero E)).mp hle
    have hdvd' : (Polynomial.X - Polynomial.C P.1) ^ (2 - 1) ∣
        Polynomial.derivative (curveX E) :=
      Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rw [pow_one, Polynomial.dvd_iff_isRoot] at hdvd'
    have := hdvd'
    rw [Polynomial.IsRoot, curveX_derivative_eval] at this
    exact three_sq_add_A_ne_zero E hP hy this
  omega

/-- The coordinate function `y` as an element of the coordinate ring. -/
noncomputable def yClassZero : E.toW.toAffine.CoordinateRing :=
  CoordinateRing.mk E.toW.toAffine Polynomial.X

theorem yClassZero_ne_zero : yClassZero E ≠ 0 := by
  have h := CoordinateRing.YClass_ne_zero (W' := E.toW.toAffine) (0 : (ZMod E.q)[X])
  unfold CoordinateRing.YClass at h
  unfold yClassZero
  simpa using h

/-- The relation `y² = x³ + A·x + B` in the coordinate ring. -/
theorem yClassZero_sq :
    yClassZero E ^ 2 = CoordinateRing.mk E.toW.toAffine (Polynomial.C (curveX E)) := by
  unfold yClassZero
  rw [← map_pow, AdjoinRoot.mk_eq_mk]
  exact ⟨1, by rw [toW_polynomial]; ring⟩

/-- **The valuation of `y` at a 2-torsion point is `exp(−1)`**: `y` is
the uniformizer there. -/
theorem pointPrime_intValuation_yClassZero {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hy : P.2 = 0) :
    (E.pointPrime hP).intValuation (yClassZero E) = exp (-1 : ℤ) := by
  have hsq : (E.pointPrime hP).intValuation (yClassZero E) ^ 2 = exp (-2 : ℤ) := by
    rw [← map_pow, yClassZero_sq,
      pointPrime_intValuation_mk_C E hP (curveX_ne_zero E),
      rootMultiplicity_curveX_eq_one E hP hy, if_pos hy]
    norm_num
  have hne : (E.pointPrime hP).intValuation (yClassZero E) ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ _ (yClassZero_ne_zero E)
  lift (E.pointPrime hP).intValuation (yClassZero E) to ℤ using hne with a ha
  rw [← exp_nsmul, exp_inj, nsmul_eq_mul] at hsq
  push_cast at hsq
  have : a = -1 := by omega
  rw [this]

/-- The basis decomposition of `D` in the coordinate ring:
`D = a(x) − b(x)·y`. -/
theorem toCoordinateRing_eq_sub (D : CoordRingElt E.q) :
    D.toCoordinateRing E =
      CoordinateRing.mk E.toW.toAffine (Polynomial.C D.a) -
        CoordinateRing.mk E.toW.toAffine (Polynomial.C D.b) * yClassZero E := by
  unfold CoordRingElt.toCoordinateRing CoordRingElt.toBivar yClassZero
  rw [map_sub, map_mul]

/-- `max` commutes with `exp`. -/
private theorem exp_max (s t : ℤ) :
    max (exp s) (exp t) = (exp (max s t) : ℤᵐ⁰) := by
  rcases le_total s t with h | h
  · rw [max_eq_right h, max_eq_right (exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (exp_le_exp.mpr h)]

/-- **2-torsion closed form**: at `P = (x₀, 0)`,
`v_P(D) = exp(−ordAt_twoTorsion E D P)` — the even/odd parity min. -/
theorem pointPrime_intValuation_twoTorsion (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hy : P.2 = 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (E.pointPrime hP).intValuation (D.toCoordinateRing E) =
      exp (-(ordAt_twoTorsion E D P : ℤ)) := by
  classical
  unfold ordAt_twoTorsion
  rw [if_neg hD]
  by_cases hb : D.b = 0
  · -- pure `a` part: even order
    have ha : D.a ≠ 0 := fun h => hD ⟨h, hb⟩
    rw [if_neg (fun h => ha h), if_pos hb]
    rw [toCoordinateRing_eq_sub, hb]
    simp only [map_zero, zero_mul, sub_zero]
    rw [pointPrime_intValuation_mk_C E hP ha, if_pos hy]
  · by_cases ha : D.a = 0
    · -- pure `b·y` part: odd order
      rw [if_pos ha]
      rw [toCoordinateRing_eq_sub, ha]
      simp only [map_zero, zero_sub]
      rw [Valuation.map_neg, map_mul,
        pointPrime_intValuation_mk_C E hP hb, if_pos hy,
        pointPrime_intValuation_yClassZero E hP hy, ← exp_add]
      congr 1
      push_cast
      ring
    · -- both parts present: distinct parities, valuation of the sum is
      -- the max (= exp of minus the min order)
      rw [if_neg ha, if_neg hb]
      have hva : (E.pointPrime hP).intValuation
          (CoordinateRing.mk E.toW.toAffine (Polynomial.C D.a)) =
          exp (-(2 * rootMultiplicity P.1 D.a : ℤ)) := by
        rw [pointPrime_intValuation_mk_C E hP ha, if_pos hy]
        congr 1
      have hvb : (E.pointPrime hP).intValuation
          (CoordinateRing.mk E.toW.toAffine (Polynomial.C D.b) * yClassZero E) =
          exp (-(2 * rootMultiplicity P.1 D.b + 1 : ℤ)) := by
        rw [map_mul, pointPrime_intValuation_mk_C E hP hb, if_pos hy,
          pointPrime_intValuation_yClassZero E hP hy, ← exp_add]
        congr 1
        push_cast
        ring
      have hne : (E.pointPrime hP).intValuation
          (CoordinateRing.mk E.toW.toAffine (Polynomial.C D.a)) ≠
          (E.pointPrime hP).intValuation
            (-(CoordinateRing.mk E.toW.toAffine (Polynomial.C D.b) * yClassZero E)) := by
        rw [Valuation.map_neg, hva, hvb]
        intro h
        rw [exp_inj] at h
        omega
      rw [toCoordinateRing_eq_sub, sub_eq_add_neg,
        Valuation.map_add_of_distinct_val _ hne, Valuation.map_neg, hva, hvb,
        exp_max]
      congr 1
      push_cast
      omega

end Divisor
