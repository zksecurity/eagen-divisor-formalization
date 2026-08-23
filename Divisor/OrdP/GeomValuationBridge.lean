/-
  Divisor/OrdP/GeomValuationBridge.lean — the valuation bridge over
  the base-changed curve `W̄` (the `Fqbar` counterpart of
  `ValuationBridge.lean`, reduced to what the chord-norm calculus
  consumes).

  Mirrors `Divisor/OrdP/ValuationBridge.lean`, with three changes:
  * the curve is `E.toWBar := E.toW.map (algebraMap F_q F̄)` over the
    algebraically closed `F̄ = Fqbar E`;
  * points are `GeomPoint E` (coordinates + curve equation), with no
    `E.points` membership — the equation is the hypothesis;
  * elements are indexed by *arbitrary* pairs `a b : F̄[X]` (via
    `barD E a b = mk (C a − C b · Y)`), because the closed-form
    `geomLocalOrder` analysis peels the common factor and then works
    with the residual pair `(geomATilde, geomBTilde)`, which is not a
    base-change of a rational pair.

  Headline (end of file), `geomPointPrime_intValuation_toBar`:
  `v_Q(D̄) = exp(−geomLocalOrder E D Q)` for every geometric point `Q`
  and nonzero `D` — by the closed formula, with no fuel induction.
-/
import Divisor.OrdP.DedekindSetup
import Divisor.OrdP.ValuationBridge
import Divisor.GeomLocalOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WithZero Multiplicative IsDedekindDomain
open scoped Polynomial.Bivariate

namespace Divisor

variable (E : ECSetup)

/-! ## The base-changed curve and its Dedekind structure -/

/-- The base-changed Weierstrass curve over `F̄ = Fqbar E`. -/
noncomputable def ECSetup.toWBar : WeierstrassCurve (Fqbar E) :=
  E.toW.map (algebraMap (ZMod E.q) (Fqbar E))

@[simp] theorem ECSetup.toWBar_a₁ : E.toWBar.a₁ = 0 := by
  show algebraMap (ZMod E.q) (Fqbar E) E.toW.a₁ = 0
  rw [ECSetup.toW_a₁, map_zero]

@[simp] theorem ECSetup.toWBar_a₂ : E.toWBar.a₂ = 0 := by
  show algebraMap (ZMod E.q) (Fqbar E) E.toW.a₂ = 0
  rw [ECSetup.toW_a₂, map_zero]

@[simp] theorem ECSetup.toWBar_a₃ : E.toWBar.a₃ = 0 := by
  show algebraMap (ZMod E.q) (Fqbar E) E.toW.a₃ = 0
  rw [ECSetup.toW_a₃, map_zero]

@[simp] theorem ECSetup.toWBar_a₄ : E.toWBar.a₄ = fqToBar E E.curveA := by
  show algebraMap (ZMod E.q) (Fqbar E) E.toW.a₄ = _
  rw [ECSetup.toW_a₄]
  rfl

@[simp] theorem ECSetup.toWBar_a₆ : E.toWBar.a₆ = fqToBar E E.curveB := by
  show algebraMap (ZMod E.q) (Fqbar E) E.toW.a₆ = _
  rw [ECSetup.toW_a₆]
  rfl

instance ECSetup.instIsEllipticBar : E.toWBar.IsElliptic := by
  unfold ECSetup.toWBar
  infer_instance

instance instIsDedekindDomainBarCoordinateRing :
    IsDedekindDomain E.toWBar.toAffine.CoordinateRing :=
  TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing
    E.toWBar.toAffine

/-- The affine equation of the base-changed curve in our short form. -/
theorem toWBar_equation_iff (x y : Fqbar E) :
    E.toWBar.toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB := by
  rw [Affine.equation_iff]
  simp only [ECSetup.toWBar_a₁, ECSetup.toWBar_a₂, ECSetup.toWBar_a₃,
    ECSetup.toWBar_a₄, ECSetup.toWBar_a₆]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- A geometric point satisfies the base-changed curve equation. -/
theorem GeomPoint.equation (Q : GeomPoint E) :
    E.toWBar.toAffine.Equation Q.x Q.y :=
  (toWBar_equation_iff E Q.x Q.y).mpr Q.onCurve

/-- The base-changed curve has nonzero discriminant. -/
theorem toWBar_Δ_ne_zero : E.toWBar.Δ ≠ 0 :=
  E.toWBar.isUnit_Δ.ne_zero

/-- Every geometric point is nonsingular. -/
theorem GeomPoint.nonsingular (Q : GeomPoint E) :
    E.toWBar.toAffine.Nonsingular Q.x Q.y :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (toWBar_Δ_ne_zero E)).mp
    (Q.equation E)

/-- The height-one prime `⟨X − Q.x, Y − Q.y⟩` of the base-changed
coordinate ring at a geometric point. -/
noncomputable def geomPointPrime (Q : GeomPoint E) :
    HeightOneSpectrum E.toWBar.toAffine.CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C Q.y)
  isPrime :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
      (Q.equation E)).isPrime
  ne_bot :=
    TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot Q.x
      (Polynomial.C Q.y)

@[simp] theorem geomPointPrime_asIdeal (Q : GeomPoint E) :
    (geomPointPrime E Q).asIdeal =
      CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C Q.y) := rfl

theorem geomPointPrime_isMaximal (Q : GeomPoint E) :
    (geomPointPrime E Q).asIdeal.IsMaximal :=
  TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
    (Q.equation E)

/-! ## Elements `a(x) − b(x)·y` of the base-changed coordinate ring -/

/-- The element `a(x) − b(x)·y` of the base-changed coordinate ring,
for an arbitrary coefficient pair over `F̄`. -/
noncomputable def barD (a b : Polynomial (Fqbar E)) :
    E.toWBar.toAffine.CoordinateRing :=
  CoordinateRing.mk E.toWBar.toAffine
    (Polynomial.C a - Polynomial.C b * Polynomial.X)

/-- Scalar evaluation of the pair `(a, b)` at a point `(x, y)`. -/
noncomputable def barEval (a b : Polynomial (Fqbar E)) (x y : Fqbar E) :
    Fqbar E :=
  a.eval x - b.eval x * y

/-- `barD` of the base-changed components of a rational `D` is the
image of `D`'s bivariate form. -/
theorem toBar_eq_barD (D : CoordRingElt E.q) :
    barD E (geomAPoly E D) (geomBPoly E D) =
      CoordinateRing.mk E.toWBar.toAffine
        (D.toBivar.map (Polynomial.mapRingHom
          (algebraMap (ZMod E.q) (Fqbar E)))) := by
  unfold barD CoordRingElt.toBivar geomAPoly geomBPoly
  congr 1
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- `barEval` of the base-changed components is `geomEval`. -/
theorem barEval_eq_geomEval (D : CoordRingElt E.q) (Q : GeomPoint E) :
    barEval E (geomAPoly E D) (geomBPoly E D) Q.x Q.y = D.geomEval E Q := by
  unfold barEval CoordRingElt.geomEval geomAPoly geomBPoly
  rw [Polynomial.eval_map, Polynomial.eval_map]

/-- `barD a b = 0` forces `a = b = 0` (freeness of the `{1, Y}` basis). -/
theorem barD_ne_zero {a b : Polynomial (Fqbar E)}
    (hab : ¬ (a = 0 ∧ b = 0)) : barD E a b ≠ 0 := by
  intro hZero
  apply hab
  have hsm : a • (1 : E.toWBar.toAffine.CoordinateRing)
      + (-b) • CoordinateRing.mk E.toWBar.toAffine Polynomial.X = 0 := by
    rw [← hZero]
    unfold barD
    rw [map_sub, map_mul, CoordinateRing.smul, CoordinateRing.smul,
      Polynomial.C_neg, map_neg, mul_one, neg_mul, sub_eq_add_neg]
  obtain ⟨ha, hb⟩ := CoordinateRing.smul_basis_eq_zero hsm
  exact ⟨ha, neg_eq_zero.mp hb⟩

/-! ## Membership ↔ vanishing at the point -/

/-- Forward direction: vanishing puts `barD` in the point ideal. -/
theorem barD_mem_XYIdeal_of_eval_zero {a b : Polynomial (Fqbar E)}
    {x y : Fqbar E} (h : barEval E a b x y = 0) :
    barD E a b ∈ CoordinateRing.XYIdeal E.toWBar.toAffine x (Polynomial.C y) := by
  have h1 : (Polynomial.C a - Polynomial.C b * Polynomial.X :
      (Fqbar E)[X][Y]).evalEval x y = 0 := by
    unfold Polynomial.evalEval
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    unfold barEval at h
    simpa using h
  have h2 : (Polynomial.C a - Polynomial.C b * Polynomial.X :
      (Fqbar E)[X][Y]) ∈
      (Ideal.span ({Polynomial.C (Polynomial.X - Polynomial.C x),
        Polynomial.X - Polynomial.C (Polynomial.C y)} :
          Set ((Fqbar E)[X][Y]))) :=
    Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h1
  have h3 := Ideal.mem_map_of_mem (CoordinateRing.mk E.toWBar.toAffine) h2
  rw [Ideal.map_span, Set.image_pair] at h3
  exact h3

/-- **Membership ↔ vanishing** at a geometric point. -/
theorem barD_mem_XYIdeal_iff {a b : Polynomial (Fqbar E)} (Q : GeomPoint E) :
    barD E a b ∈ (geomPointPrime E Q).asIdeal ↔
      barEval E a b Q.x Q.y = 0 := by
  rw [geomPointPrime_asIdeal]
  refine ⟨?_, barD_mem_XYIdeal_of_eval_zero E⟩
  intro hMem
  unfold CoordinateRing.XYIdeal CoordinateRing.XClass CoordinateRing.YClass
    barD at hMem
  rw [Ideal.mem_span_pair] at hMem
  obtain ⟨α, β, hαβ⟩ := hMem
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective α
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective β
  rw [← map_mul, ← map_mul, ← map_add, AdjoinRoot.mk_eq_mk] at hαβ
  obtain ⟨c, hc⟩ := hαβ
  have hRewrite : (Polynomial.C a - Polynomial.C b * Polynomial.X :
      (Fqbar E)[X][Y]) =
      p * Polynomial.C (Polynomial.X - Polynomial.C Q.x)
        + r * (Polynomial.X - Polynomial.C (Polynomial.C Q.y))
        - c * E.toWBar.toAffine.polynomial := by
    linear_combination -hc
  have h_eval := congr_arg (fun p => Polynomial.evalEval Q.x Q.y p) hRewrite
  have h_curveEval :
      Polynomial.evalEval Q.x Q.y E.toWBar.toAffine.polynomial = 0 := by
    have := Q.equation E
    rwa [WeierstrassCurve.Affine.Equation, Polynomial.evalEval] at this
  simp only [Polynomial.evalEval_add, Polynomial.evalEval_sub,
    Polynomial.evalEval_mul, Polynomial.evalEval_C, Polynomial.evalEval_X,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
    mul_zero, zero_add, h_curveEval] at h_eval
  unfold barEval
  exact h_eval

/-- `v_Q(barD a b) = 1` iff the pair does not vanish at `Q`. -/
theorem geomPointPrime_intValuation_eq_one_iff
    {a b : Polynomial (Fqbar E)} (Q : GeomPoint E) :
    (geomPointPrime E Q).intValuation (barD E a b) = 1 ↔
      barEval E a b Q.x Q.y ≠ 0 := by
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  exact not_congr (barD_mem_XYIdeal_iff E Q)

/-! ## Uniformizer valuations over the base-changed curve -/

/-- `negY` of the base-changed short-Weierstrass curve is negation. -/
@[simp] theorem toWBar_negY (x y : Fqbar E) :
    E.toWBar.toAffine.negY x y = -y := by
  rw [Affine.negY]
  rw [ECSetup.toWBar_a₁, ECSetup.toWBar_a₃]
  ring

/-- `2 ≠ 0` in `F̄` (characteristic `q ≥ 5`). -/
theorem two_ne_zero_bar : (2 : Fqbar E) ≠ 0 := by
  have h2 : (2 : Fqbar E) = algebraMap (ZMod E.q) (Fqbar E) 2 := by
    rw [map_ofNat]
  rw [h2, Ne, map_eq_zero_iff _ (algebraMap (ZMod E.q) (Fqbar E)).injective]
  exact two_ne_zero_zmod E

/-- The `XIdeal` factorization `⟨X − Q.x⟩ = σQ · Q` at a geometric
point. -/
theorem xIdeal_eq_mul_bar (Q : GeomPoint E) :
    CoordinateRing.XIdeal E.toWBar.toAffine Q.x =
      CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C (-Q.y)) *
        CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C Q.y) := by
  have h := CoordinateRing.XYIdeal_neg_mul (Q.nonsingular E)
  rw [toWBar_negY] at h
  exact h.symm

/-- Off 2-torsion, the conjugate prime is a different maximal ideal. -/
theorem xyIdeal_neg_ne_bar (Q : GeomPoint E) (hy : Q.y ≠ 0) :
    CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C (-Q.y)) ≠
      CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C Q.y) := by
  intro h
  have hσeq : E.toWBar.toAffine.Equation Q.x (-Q.y) :=
    (Q.conjugate E).equation E
  obtain ⟨-, hyy⟩ :=
    (TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_iff hσeq).mp h
  apply hy
  have h2y : (2 : Fqbar E) * Q.y = 0 := by linear_combination -hyy
  exact (mul_eq_zero.mp h2y).resolve_left (two_ne_zero_bar E)

private theorem geomPointPrime_ne_zero (Q : GeomPoint E) :
    (geomPointPrime E Q).asIdeal ≠ 0 := fun h =>
  (geomPointPrime E Q).ne_bot (by rwa [Ideal.zero_eq_bot] at h)

/-- **Non-2-torsion uniformizer** on the base-changed curve:
`v_Q(X − Q.x) = exp(−1)` when `Q.y ≠ 0`. -/
theorem geomPointPrime_intValuation_XClass_of_ne_zero
    (Q : GeomPoint E) (hy : Q.y ≠ 0) :
    (geomPointPrime E Q).intValuation
      (CoordinateRing.XClass E.toWBar.toAffine Q.x) = exp (-1 : ℤ) := by
  have hprime : Prime (geomPointPrime E Q).asIdeal := (geomPointPrime E Q).prime
  have hnd : ¬ (geomPointPrime E Q).asIdeal ∣
      CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C (-Q.y)) := by
    rw [Ideal.dvd_iff_le]
    intro hle
    have hσmax :
        (CoordinateRing.XYIdeal E.toWBar.toAffine Q.x
          (Polynomial.C (-Q.y))).IsMaximal :=
      TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal_of_equation
        ((Q.conjugate E).equation E)
    have heq := hσmax.eq_of_le (geomPointPrime_isMaximal E Q).ne_top hle
    rw [geomPointPrime_asIdeal] at heq
    exact xyIdeal_neg_ne_bar E Q hy heq
  have hcount : emultiplicity (geomPointPrime E Q).asIdeal
      (Ideal.span {CoordinateRing.XClass E.toWBar.toAffine Q.x}) = (1 : ℕ) := by
    have hspan : Ideal.span {CoordinateRing.XClass E.toWBar.toAffine Q.x} =
        CoordinateRing.XYIdeal E.toWBar.toAffine Q.x (Polynomial.C (-Q.y)) *
          (geomPointPrime E Q).asIdeal := by
      rw [geomPointPrime_asIdeal]
      exact xIdeal_eq_mul_bar E Q
    rw [hspan, emultiplicity_mul hprime, emultiplicity_eq_zero.mpr hnd, zero_add]
    exact (FiniteMultiplicity.of_prime_left hprime
      (geomPointPrime_ne_zero E Q)).emultiplicity_self
  simpa using intValuation_eq_exp_neg_of_emultiplicity _ hcount

/-- **2-torsion order of `X − Q.x`** on the base-changed curve:
`v_Q(X − Q.x) = exp(−2)` when `Q.y = 0`. -/
theorem geomPointPrime_intValuation_XClass_of_eq_zero
    (Q : GeomPoint E) (hy : Q.y = 0) :
    (geomPointPrime E Q).intValuation
      (CoordinateRing.XClass E.toWBar.toAffine Q.x) = exp (-2 : ℤ) := by
  have hprime : Prime (geomPointPrime E Q).asIdeal := (geomPointPrime E Q).prime
  have hcount : emultiplicity (geomPointPrime E Q).asIdeal
      (Ideal.span {CoordinateRing.XClass E.toWBar.toAffine Q.x}) = (2 : ℕ) := by
    have hspan : Ideal.span {CoordinateRing.XClass E.toWBar.toAffine Q.x} =
        (geomPointPrime E Q).asIdeal ^ 2 := by
      rw [geomPointPrime_asIdeal, hy]
      have h := xIdeal_eq_mul_bar E Q
      rw [hy, neg_zero] at h
      rw [sq, ← h]
      rfl
    rw [hspan]
    exact emultiplicity_pow_self_of_prime hprime 2
  simpa using intValuation_eq_exp_neg_of_emultiplicity _ hcount

/-! ## Univariate valuations over the base-changed curve -/

/-- The univariate `g` embeds as `barD g 0 = mk (C g)`. -/
theorem barD_C (g : Polynomial (Fqbar E)) :
    barD E g 0 = CoordinateRing.mk E.toWBar.toAffine (Polynomial.C g) := by
  unfold barD
  simp

/-- A univariate polynomial not vanishing at `Q.x` is a unit at `Q`. -/
theorem geomPointPrime_intValuation_mk_C_eq_one
    (Q : GeomPoint E) {h : Polynomial (Fqbar E)} (hh : h.eval Q.x ≠ 0) :
    (geomPointPrime E Q).intValuation
      (CoordinateRing.mk E.toWBar.toAffine (Polynomial.C h)) = 1 := by
  rw [← barD_C, geomPointPrime_intValuation_eq_one_iff E Q]
  unfold barEval
  simpa using hh

open Classical in
/-- **Univariate valuation** on the base-changed curve: for `g ≠ 0`,
`v_Q(g(x)) = exp(−(e_Q · rootMult Q.x g))` with `e_Q = 1` off
2-torsion and `2` on it. -/
theorem geomPointPrime_intValuation_mk_C
    (Q : GeomPoint E) {g : Polynomial (Fqbar E)} (hg : g ≠ 0) :
    (geomPointPrime E Q).intValuation
        (CoordinateRing.mk E.toWBar.toAffine (Polynomial.C g)) =
      exp (-(((if Q.y = 0 then 2 else 1) * rootMultiplicity Q.x g : ℕ) : ℤ)) := by
  classical
  set m := rootMultiplicity Q.x g with hm
  set h := g /ₘ (Polynomial.X - Polynomial.C Q.x) ^ m with hh
  have hfact : (Polynomial.X - Polynomial.C Q.x) ^ m * h = g :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq g Q.x
  have hhne : h.eval Q.x ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero Q.x hg
  have hmk : CoordinateRing.mk E.toWBar.toAffine (Polynomial.C g) =
      CoordinateRing.XClass E.toWBar.toAffine Q.x ^ m *
        CoordinateRing.mk E.toWBar.toAffine (Polynomial.C h) := by
    rw [← hfact, map_mul, map_pow]
    rfl
  rw [hmk, map_mul, map_pow,
    geomPointPrime_intValuation_mk_C_eq_one E Q hhne, mul_one]
  by_cases hy : Q.y = 0
  · rw [geomPointPrime_intValuation_XClass_of_eq_zero E Q hy, if_pos hy,
      ← exp_nsmul]
    congr 1
    push_cast
    ring
  · rw [geomPointPrime_intValuation_XClass_of_ne_zero E Q hy, if_neg hy,
      ← exp_nsmul]
    congr 1
    push_cast
    ring

/-! ## The norm identity for pairs over `F̄` -/

/-- The base-changed fiber cubic `X³ + Ā·X + B̄`. -/
noncomputable def curveXBar : Polynomial (Fqbar E) :=
  (curveX E).map (algebraMap (ZMod E.q) (Fqbar E))

theorem curveXBar_eq :
    curveXBar E = Polynomial.X ^ 3 + Polynomial.C (fqToBar E E.curveA) *
      Polynomial.X + Polynomial.C (fqToBar E E.curveB) := by
  unfold curveXBar curveX fqToBar
  simp

theorem curveXBar_ne_zero : curveXBar E ≠ 0 :=
  Polynomial.map_ne_zero (curveX_ne_zero E)

theorem curveXBar_natDegree : (curveXBar E).natDegree = 3 := by
  unfold curveXBar
  rw [Polynomial.natDegree_map_eq_of_injective
    (algebraMap (ZMod E.q) (Fqbar E)).injective, natDegree_curveX_eq]

/-- The Weierstrass polynomial of the base-changed curve is
`Y² − (X³ + Ā·X + B̄)`. -/
theorem toWBar_polynomial :
    E.toWBar.toAffine.polynomial =
      Polynomial.X ^ 2 - Polynomial.C (curveXBar E) := by
  rw [Affine.polynomial]
  rw [ECSetup.toWBar_a₁, ECSetup.toWBar_a₂, ECSetup.toWBar_a₃,
    ECSetup.toWBar_a₄, ECSetup.toWBar_a₆]
  rw [curveXBar_eq]
  simp only [Polynomial.C_0, zero_mul, add_zero]

/-- The norm polynomial of a pair over `F̄`. -/
noncomputable def barNormPoly (a b : Polynomial (Fqbar E)) :
    Polynomial (Fqbar E) :=
  a ^ 2 - b ^ 2 * curveXBar E

/-- `barNormPoly` of base-changed components is `normPolyBar`. -/
theorem barNormPoly_eq_normPolyBar (D : CoordRingElt E.q) :
    barNormPoly E (geomAPoly E D) (geomBPoly E D) = normPolyBar E D := by
  unfold barNormPoly normPolyBar geomAPoly geomBPoly curveXBar
  rw [normPoly_eq]
  simp

/-- The norm of a nonzero pair is nonzero (odd/even degree clash). -/
theorem barNormPoly_ne_zero {a b : Polynomial (Fqbar E)}
    (hab : ¬ (a = 0 ∧ b = 0)) : barNormPoly E a b ≠ 0 := by
  unfold barNormPoly
  intro h
  rw [sub_eq_zero] at h
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun h' => hab ⟨h', hb⟩
    rw [hb] at h
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_mul] at h
    exact pow_ne_zero 2 ha h
  · have ha : a ≠ 0 := by
      intro h'
      rw [h'] at h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
      rcases mul_eq_zero.mp h.symm with h2 | h2
      · exact hb (pow_eq_zero_iff (by norm_num) |>.mp h2)
      · exact curveXBar_ne_zero E h2
    have hdeg := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_pow,
      Polynomial.natDegree_mul (pow_ne_zero 2 hb) (curveXBar_ne_zero E),
      Polynomial.natDegree_pow, curveXBar_natDegree] at hdeg
    omega

/-- **The norm identity for pairs**: `(a − b·y)(a + b·y) = a² − b²·f̄`
in the base-changed coordinate ring. -/
theorem barD_mul_conj (a b : Polynomial (Fqbar E)) :
    barD E a b * barD E a (-b) =
      CoordinateRing.mk E.toWBar.toAffine
        (Polynomial.C (barNormPoly E a b)) := by
  unfold barD
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  refine ⟨-Polynomial.C (b ^ 2), ?_⟩
  rw [toWBar_polynomial]
  unfold barNormPoly
  simp only [Polynomial.C_neg, Polynomial.C_sub, Polynomial.C_mul,
    Polynomial.C_pow]
  ring

/-- Conjugating the pair is evaluating on the other sheet. -/
theorem barEval_conj (a b : Polynomial (Fqbar E)) (x y : Fqbar E) :
    barEval E a (-b) x y = barEval E a b x (-y) := by
  unfold barEval
  simp only [Polynomial.eval_neg]
  ring

open Classical in
/-- The valuation of `(a − b·y)(a + b·y)` through the univariate
valuation of the norm. -/
theorem geomPointPrime_intValuation_mul_conj
    {a b : Polynomial (Fqbar E)} (hab : ¬ (a = 0 ∧ b = 0)) (Q : GeomPoint E) :
    (geomPointPrime E Q).intValuation (barD E a b) *
        (geomPointPrime E Q).intValuation (barD E a (-b)) =
      exp (-(((if Q.y = 0 then 2 else 1) *
        rootMultiplicity Q.x (barNormPoly E a b) : ℕ) : ℤ)) := by
  rw [← map_mul, barD_mul_conj]
  exact geomPointPrime_intValuation_mk_C E Q (barNormPoly_ne_zero E hab)

/-- **Lone-sheet valuation** over `F̄`: at non-2-torsion `Q` where the
conjugate does not vanish, `v_Q(a − b·y) = exp(−rootMult Q.x N)`. -/
theorem geomPointPrime_intValuation_of_lone
    {a b : Polynomial (Fqbar E)} (Q : GeomPoint E) (hy : Q.y ≠ 0)
    (hlone : barEval E a b Q.x (-Q.y) ≠ 0) :
    (geomPointPrime E Q).intValuation (barD E a b) =
      exp (-(rootMultiplicity Q.x (barNormPoly E a b) : ℤ)) := by
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨ha, hb⟩
    apply hlone
    unfold barEval
    rw [ha, hb]
    simp
  have hconj : (geomPointPrime E Q).intValuation (barD E a (-b)) = 1 := by
    rw [geomPointPrime_intValuation_eq_one_iff E Q, barEval_conj]
    exact hlone
  have hmul := geomPointPrime_intValuation_mul_conj E hab Q
  rw [hconj, mul_one, if_neg hy, one_mul] at hmul
  exact hmul

/-! ## 2-torsion over `F̄`: parity min and the norm multiplicity -/

/-- `rootMultiplicity` is invariant under negation. -/
private theorem rootMultiplicity_neg (x : Fqbar E) (p : Polynomial (Fqbar E)) :
    rootMultiplicity x (-p) = rootMultiplicity x p := by
  by_cases hp : p = 0
  · rw [hp, neg_zero]
  · have hnp : (-p : Polynomial (Fqbar E)) ≠ 0 := neg_ne_zero.mpr hp
    apply le_antisymm
    · rw [Polynomial.le_rootMultiplicity_iff hp]
      exact dvd_neg.mp (Polynomial.pow_rootMultiplicity_dvd (-p) x)
    · rw [Polynomial.le_rootMultiplicity_iff hnp]
      exact dvd_neg.mpr (Polynomial.pow_rootMultiplicity_dvd p x)

/-- The coordinate function `y` on the base-changed curve. -/
noncomputable def yClassZeroBar : E.toWBar.toAffine.CoordinateRing :=
  CoordinateRing.mk E.toWBar.toAffine Polynomial.X

theorem yClassZeroBar_ne_zero : yClassZeroBar E ≠ 0 := by
  have h := CoordinateRing.YClass_ne_zero (W' := E.toWBar.toAffine)
    (0 : (Fqbar E)[X])
  unfold CoordinateRing.YClass at h
  unfold yClassZeroBar
  simpa using h

theorem yClassZeroBar_sq :
    yClassZeroBar E ^ 2 =
      CoordinateRing.mk E.toWBar.toAffine (Polynomial.C (curveXBar E)) := by
  unfold yClassZeroBar
  rw [← map_pow, AdjoinRoot.mk_eq_mk]
  exact ⟨1, by rw [toWBar_polynomial]; ring⟩

/-- Nonsingularity at 2-torsion: `3x₀² + Ā ≠ 0`. -/
theorem three_sq_add_A_bar_ne_zero (Q : GeomPoint E) (hy : Q.y = 0) :
    3 * Q.x ^ 2 + fqToBar E E.curveA ≠ 0 := by
  have hns := Q.nonsingular E
  rw [Affine.nonsingular_iff'] at hns
  rcases hns.2 with h | h
  · intro hzero
    apply h
    rw [ECSetup.toWBar_a₁, ECSetup.toWBar_a₂, ECSetup.toWBar_a₄]
    linear_combination -hzero
  · exfalso
    apply h
    rw [hy, ECSetup.toWBar_a₁, ECSetup.toWBar_a₃]
    ring

theorem curveXBar_derivative_eval (x₀ : Fqbar E) :
    (Polynomial.derivative (curveXBar E)).eval x₀ =
      3 * x₀ ^ 2 + fqToBar E E.curveA := by
  rw [curveXBar_eq]
  rw [Polynomial.derivative_add, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_C_mul,
    Polynomial.derivative_X, Polynomial.derivative_C]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, mul_one, add_zero]
  norm_num

/-- At a 2-torsion geometric point the fiber cubic has a simple root. -/
theorem rootMultiplicity_curveXBar_eq_one (Q : GeomPoint E) (hy : Q.y = 0) :
    rootMultiplicity Q.x (curveXBar E) = 1 := by
  have hroot : (curveXBar E).IsRoot Q.x := by
    show (curveXBar E).eval Q.x = 0
    rw [curveXBar_eq]
    have h := Q.onCurve
    rw [hy] at h
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination -h
  have hge : 1 ≤ rootMultiplicity Q.x (curveXBar E) :=
    (Polynomial.rootMultiplicity_pos (curveXBar_ne_zero E)).mpr hroot
  have hlt : rootMultiplicity Q.x (curveXBar E) < 2 := by
    by_contra hle
    rw [not_lt] at hle
    have hdvd : (Polynomial.X - Polynomial.C Q.x) ^ 2 ∣ curveXBar E :=
      (Polynomial.le_rootMultiplicity_iff (curveXBar_ne_zero E)).mp hle
    have hdvd' : (Polynomial.X - Polynomial.C Q.x) ^ (2 - 1) ∣
        Polynomial.derivative (curveXBar E) :=
      Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    rw [pow_one, Polynomial.dvd_iff_isRoot] at hdvd'
    have := hdvd'
    rw [Polynomial.IsRoot, curveXBar_derivative_eval] at this
    exact three_sq_add_A_bar_ne_zero E Q hy this
  omega

/-- `v_Q(y) = exp(−1)` at a 2-torsion geometric point. -/
theorem geomPointPrime_intValuation_yClassZeroBar (Q : GeomPoint E)
    (hy : Q.y = 0) :
    (geomPointPrime E Q).intValuation (yClassZeroBar E) = exp (-1 : ℤ) := by
  have hsq : (geomPointPrime E Q).intValuation (yClassZeroBar E) ^ 2 =
      exp (-2 : ℤ) := by
    rw [← map_pow, yClassZeroBar_sq,
      geomPointPrime_intValuation_mk_C E Q (curveXBar_ne_zero E),
      rootMultiplicity_curveXBar_eq_one E Q hy, if_pos hy]
    norm_num
  have hne : (geomPointPrime E Q).intValuation (yClassZeroBar E) ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ _ (yClassZeroBar_ne_zero E)
  lift (geomPointPrime E Q).intValuation (yClassZeroBar E) to ℤ
    using hne with u hu
  rw [← exp_nsmul, exp_inj, nsmul_eq_mul] at hsq
  push_cast at hsq
  have : u = -1 := by omega
  rw [this]

/-- The basis decomposition `a − b·y` in the base-changed coordinate
ring. -/
theorem barD_eq_sub (a b : Polynomial (Fqbar E)) :
    barD E a b =
      CoordinateRing.mk E.toWBar.toAffine (Polynomial.C a) -
        CoordinateRing.mk E.toWBar.toAffine (Polynomial.C b) *
          yClassZeroBar E := by
  unfold barD yClassZeroBar
  rw [map_sub, map_mul]

private theorem exp_max_bar (s t : ℤ) :
    max (exp s) (exp t) = (exp (max s t) : ℤᵐ⁰) := by
  rcases le_total s t with h | h
  · rw [max_eq_right h, max_eq_right (exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (exp_le_exp.mpr h)]

open Classical in
/-- **2-torsion parity min** over `F̄`: the valuation of `a − b·y` at a
ramified point is the even/odd min. -/
private theorem geomPointPrime_intValuation_twoTorsion_min
    {a b : Polynomial (Fqbar E)} (hab : ¬ (a = 0 ∧ b = 0))
    (Q : GeomPoint E) (hy : Q.y = 0) :
    (geomPointPrime E Q).intValuation (barD E a b) =
      exp (-((if a = 0 then 2 * rootMultiplicity Q.x b + 1
        else if b = 0 then 2 * rootMultiplicity Q.x a
        else min (2 * rootMultiplicity Q.x a)
          (2 * rootMultiplicity Q.x b + 1) : ℕ) : ℤ)) := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun h => hab ⟨h, hb⟩
    rw [if_neg ha, if_pos hb, barD_eq_sub, hb]
    simp only [map_zero, zero_mul, sub_zero]
    rw [geomPointPrime_intValuation_mk_C E Q ha, if_pos hy]
  · by_cases ha : a = 0
    · rw [if_pos ha, barD_eq_sub, ha]
      simp only [map_zero, zero_sub]
      rw [Valuation.map_neg, map_mul,
        geomPointPrime_intValuation_mk_C E Q hb, if_pos hy,
        geomPointPrime_intValuation_yClassZeroBar E Q hy, ← exp_add]
      congr 1
      push_cast
      ring
    · rw [if_neg ha, if_neg hb]
      have hva : (geomPointPrime E Q).intValuation
          (CoordinateRing.mk E.toWBar.toAffine (Polynomial.C a)) =
          exp (-(2 * rootMultiplicity Q.x a : ℤ)) := by
        rw [geomPointPrime_intValuation_mk_C E Q ha, if_pos hy]
        congr 1
      have hvb : (geomPointPrime E Q).intValuation
          (CoordinateRing.mk E.toWBar.toAffine (Polynomial.C b) *
            yClassZeroBar E) =
          exp (-(2 * rootMultiplicity Q.x b + 1 : ℤ)) := by
        rw [map_mul, geomPointPrime_intValuation_mk_C E Q hb, if_pos hy,
          geomPointPrime_intValuation_yClassZeroBar E Q hy, ← exp_add]
        congr 1
        push_cast
        ring
      have hne : (geomPointPrime E Q).intValuation
          (CoordinateRing.mk E.toWBar.toAffine (Polynomial.C a)) ≠
          (geomPointPrime E Q).intValuation
            (-(CoordinateRing.mk E.toWBar.toAffine (Polynomial.C b) *
              yClassZeroBar E)) := by
        rw [Valuation.map_neg, hva, hvb]
        intro h
        rw [exp_inj] at h
        omega
      rw [barD_eq_sub, sub_eq_add_neg,
        Valuation.map_add_of_distinct_val _ hne, Valuation.map_neg, hva, hvb,
        exp_max_bar]
      congr 1
      push_cast
      omega

/-- **2-torsion valuation = norm root multiplicity** over `F̄`: at a
ramified geometric point, `v_Q(a − b·y) = exp(−rootMult Q.x N)`. -/
theorem geomPointPrime_intValuation_twoTorsion
    {a b : Polynomial (Fqbar E)} (hab : ¬ (a = 0 ∧ b = 0))
    (Q : GeomPoint E) (hy : Q.y = 0) :
    (geomPointPrime E Q).intValuation (barD E a b) =
      exp (-(rootMultiplicity Q.x (barNormPoly E a b) : ℤ)) := by
  classical
  set μ : ℕ := (if a = 0 then 2 * rootMultiplicity Q.x b + 1
    else if b = 0 then 2 * rootMultiplicity Q.x a
    else min (2 * rootMultiplicity Q.x a)
      (2 * rootMultiplicity Q.x b + 1)) with hμ
  have hv := geomPointPrime_intValuation_twoTorsion_min E hab Q hy
  have hab' : ¬ (a = 0 ∧ -b = 0) := by
    simpa [neg_eq_zero] using hab
  have hv' := geomPointPrime_intValuation_twoTorsion_min E hab' Q hy
  have hμ' : (if a = 0 then 2 * rootMultiplicity Q.x (-b) + 1
      else if (-b : Polynomial (Fqbar E)) = 0 then 2 * rootMultiplicity Q.x a
      else min (2 * rootMultiplicity Q.x a)
        (2 * rootMultiplicity Q.x (-b) + 1)) = μ := by
    rw [hμ]
    rw [rootMultiplicity_neg]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha]
      by_cases hb : b = 0
      · rw [if_pos hb, if_pos (neg_eq_zero.mpr hb)]
      · rw [if_neg hb, if_neg (fun h => hb (neg_eq_zero.mp h))]
  rw [hμ'] at hv'
  have hmul := geomPointPrime_intValuation_mul_conj E hab Q
  rw [if_pos hy, hv, hv', ← exp_add, exp_inj] at hmul
  have : (μ : ℤ) = rootMultiplicity Q.x (barNormPoly E a b) := by omega
  rw [hv]
  congr 1
  omega

/-! ## The closed-form assembly: `v_Q(D̄) = exp(−geomLocalOrder)` -/

/-- Exact division by a monic power that divides. -/
private theorem pow_mul_divByMonic_eq {p : Polynomial (Fqbar E)}
    {x₀ : Fqbar E} {n : ℕ}
    (hdvd : (Polynomial.X - Polynomial.C x₀) ^ n ∣ p) :
    (Polynomial.X - Polynomial.C x₀) ^ n *
      (p /ₘ (Polynomial.X - Polynomial.C x₀) ^ n) = p := by
  have hmonic : ((Polynomial.X - Polynomial.C x₀) ^ n).Monic :=
    (Polynomial.monic_X_sub_C x₀).pow n
  have hmod : p %ₘ (Polynomial.X - Polynomial.C x₀) ^ n = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  conv_rhs => rw [← Polynomial.modByMonic_add_div p
    ((Polynomial.X - Polynomial.C x₀) ^ n)]
  rw [hmod, zero_add]

/-- Peeling a common `(X − x₀)^n` factor out of `barD`. -/
private theorem barD_factor {a b : Polynomial (Fqbar E)} {x₀ : Fqbar E}
    {n : ℕ} (hda : (Polynomial.X - Polynomial.C x₀) ^ n ∣ a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ^ n ∣ b) :
    barD E a b =
      CoordinateRing.XClass E.toWBar.toAffine x₀ ^ n *
        barD E (a /ₘ (Polynomial.X - Polynomial.C x₀) ^ n)
          (b /ₘ (Polynomial.X - Polynomial.C x₀) ^ n) := by
  unfold barD CoordinateRing.XClass
  rw [← map_pow, ← map_mul]
  congr 1
  conv_lhs => rw [← pow_mul_divByMonic_eq E hda, ← pow_mul_divByMonic_eq E hdb]
  simp only [Polynomial.C_mul, Polynomial.C_pow]
  ring

/-- After removing the common factor, the two residual coefficients do
not vanish simultaneously at `x₀`. -/
private theorem tilde_eval_not_both_zero (D : CoordRingElt E.q)
    (hab : ¬ (geomAPoly E D = 0 ∧ geomBPoly E D = 0)) (x₀ : Fqbar E) :
    ¬ ((geomATilde E D x₀).eval x₀ = 0 ∧
        (geomBTilde E D x₀).eval x₀ = 0) := by
  unfold geomATilde geomBTilde commonRootMultiplicity
  by_cases ha : geomAPoly E D = 0
  · have hb : geomBPoly E D ≠ 0 := fun h => hab ⟨ha, h⟩
    rw [if_pos ha]
    rintro ⟨-, hB⟩
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero x₀ hb hB
  · by_cases hb : geomBPoly E D = 0
    · rw [if_neg ha, if_pos hb]
      rintro ⟨hA, -⟩
      exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero x₀ ha hA
    · rw [if_neg ha, if_neg hb]
      rcases le_total (rootMultiplicity x₀ (geomAPoly E D))
        (rootMultiplicity x₀ (geomBPoly E D)) with hle | hle
      · rw [min_eq_left hle]
        rintro ⟨hA, -⟩
        exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero x₀ ha hA
      · rw [min_eq_right hle]
        rintro ⟨-, hB⟩
        exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero x₀ hb hB

/-- The residual pair is nonzero. -/
private theorem tilde_not_both_zero (D : CoordRingElt E.q)
    (hab : ¬ (geomAPoly E D = 0 ∧ geomBPoly E D = 0)) (x₀ : Fqbar E) :
    ¬ (geomATilde E D x₀ = 0 ∧ geomBTilde E D x₀ = 0) := by
  rintro ⟨hA, hB⟩
  apply hab
  constructor
  · rw [← pow_mul_divByMonic_eq E
      (commonRootFactor_dvd_left E (geomAPoly E D) (geomBPoly E D) x₀)]
    unfold geomATilde at hA
    rw [hA, mul_zero]
  · rw [← pow_mul_divByMonic_eq E
      (commonRootFactor_dvd_right E (geomAPoly E D) (geomBPoly E D) x₀)]
    unfold geomBTilde at hB
    rw [hB, mul_zero]

/-- The norm factors through the common factor:
`N(D̄) = (X − x₀)^{2k} · N(residual pair)`. -/
private theorem normPolyBar_factor (D : CoordRingElt E.q) (x₀ : Fqbar E) :
    normPolyBar E D =
      (Polynomial.X - Polynomial.C x₀) ^
          (2 * commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) x₀) *
        barNormPoly E (geomATilde E D x₀) (geomBTilde E D x₀) := by
  rw [← barNormPoly_eq_normPolyBar]
  unfold barNormPoly geomATilde geomBTilde
  set k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) x₀ with hk
  have ha : (Polynomial.X - Polynomial.C x₀) ^ k *
      (geomAPoly E D /ₘ (Polynomial.X - Polynomial.C x₀) ^ k) =
        geomAPoly E D :=
    pow_mul_divByMonic_eq E
      (commonRootFactor_dvd_left E (geomAPoly E D) (geomBPoly E D) x₀)
  have hb : (Polynomial.X - Polynomial.C x₀) ^ k *
      (geomBPoly E D /ₘ (Polynomial.X - Polynomial.C x₀) ^ k) =
        geomBPoly E D :=
    pow_mul_divByMonic_eq E
      (commonRootFactor_dvd_right E (geomAPoly E D) (geomBPoly E D) x₀)
  conv_lhs => rw [← ha, ← hb]
  ring

/-- Fiber accounting for the residual norm:
`rootMult x₀ N(D̄) = 2k + rootMult x₀ N(residual)`. -/
private theorem rootMultiplicity_normPolyBar_factor (D : CoordRingElt E.q)
    (hab : ¬ (geomAPoly E D = 0 ∧ geomBPoly E D = 0)) (x₀ : Fqbar E) :
    rootMultiplicity x₀ (normPolyBar E D) =
      2 * commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) x₀ +
        rootMultiplicity x₀
          (barNormPoly E (geomATilde E D x₀) (geomBTilde E D x₀)) := by
  have hN : barNormPoly E (geomATilde E D x₀) (geomBTilde E D x₀) ≠ 0 :=
    barNormPoly_ne_zero E (tilde_not_both_zero E D hab x₀)
  have hprod : ((Polynomial.X - Polynomial.C x₀) ^
      (2 * commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) x₀) *
        barNormPoly E (geomATilde E D x₀) (geomBTilde E D x₀)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x₀)) hN
  rw [normPolyBar_factor E D x₀, Polynomial.rootMultiplicity_mul hprod,
    Polynomial.rootMultiplicity_X_sub_C_pow]

/-- **The geometric valuation bridge**: at every
geometric point `Q` of the base-changed curve, the valuation of
`D̄ = ā − b̄·y` is `exp(−geomLocalOrder E D Q)` — the closed-form local
order of `Divisor/GeomLocalOrder.lean` computes the
`HeightOneSpectrum` valuation. -/
theorem geomPointPrime_intValuation_toBar (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (Q : GeomPoint E) :
    (geomPointPrime E Q).intValuation
        (barD E (geomAPoly E D) (geomBPoly E D)) =
      exp (-(geomLocalOrder E D Q : ℤ)) := by
  classical
  have hab : ¬ (geomAPoly E D = 0 ∧ geomBPoly E D = 0) := by
    rintro ⟨ha, hb⟩
    apply hD
    unfold geomAPoly at ha
    unfold geomBPoly at hb
    exact ⟨(Polynomial.map_eq_zero_iff
        (algebraMap (ZMod E.q) (Fqbar E)).injective).mp ha,
      (Polynomial.map_eq_zero_iff
        (algebraMap (ZMod E.q) (Fqbar E)).injective).mp hb⟩
  unfold geomLocalOrder
  by_cases hy : Q.y = 0
  · rw [if_pos hy]
    rw [geomPointPrime_intValuation_twoTorsion E hab Q hy,
      barNormPoly_eq_normPolyBar]
  · rw [if_neg hy]
    set k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x
      with hk
    have hfact : barD E (geomAPoly E D) (geomBPoly E D) =
        CoordinateRing.XClass E.toWBar.toAffine Q.x ^ k *
          barD E (geomATilde E D Q.x) (geomBTilde E D Q.x) :=
      barD_factor E
        (commonRootFactor_dvd_left E (geomAPoly E D) (geomBPoly E D) Q.x)
        (commonRootFactor_dvd_right E (geomAPoly E D) (geomBPoly E D) Q.x)
    have hXv := geomPointPrime_intValuation_XClass_of_ne_zero E Q hy
    by_cases hres : (geomATilde E D Q.x).eval Q.x -
        (geomBTilde E D Q.x).eval Q.x * Q.y = 0
    · rw [if_pos hres]
      -- residual sheet: lone case on the residual pair
      have hlone : barEval E (geomATilde E D Q.x) (geomBTilde E D Q.x)
          Q.x (-Q.y) ≠ 0 := by
        intro hzero
        unfold barEval at hzero
        have h2 : (2 : Fqbar E) * ((geomBTilde E D Q.x).eval Q.x * Q.y)
            = 0 := by linear_combination hzero - hres
        have hb0 : (geomBTilde E D Q.x).eval Q.x = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (two_ne_zero_bar E)
          · exact (mul_eq_zero.mp h).resolve_right hy
        have ha0 : (geomATilde E D Q.x).eval Q.x = 0 := by
          rw [hb0, zero_mul, sub_zero] at hres
          exact hres
        exact tilde_eval_not_both_zero E D hab Q.x ⟨ha0, hb0⟩
      have hres_val := geomPointPrime_intValuation_of_lone E Q hy hlone
      have hcount := rootMultiplicity_normPolyBar_factor E D hab Q.x
      rw [← hk] at hcount
      rw [hfact, map_mul, map_pow, hXv, hres_val, ← exp_nsmul, ← exp_add]
      congr 1
      rw [hcount, nsmul_eq_mul]
      omega
    · rw [if_neg hres]
      -- conjugate sheet: the residual pair is a unit at `Q`
      have hunit : (geomPointPrime E Q).intValuation
          (barD E (geomATilde E D Q.x) (geomBTilde E D Q.x)) = 1 := by
        rw [geomPointPrime_intValuation_eq_one_iff E Q]
        unfold barEval
        exact hres
      rw [hfact, map_mul, map_pow, hXv, hunit, mul_one, ← exp_nsmul]
      congr 1
      rw [nsmul_eq_mul]
      ring

end Divisor
