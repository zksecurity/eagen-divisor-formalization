import Divisor.Sketch.ChordFiberProductConcrete
import Divisor.ChordCubicSymmetric

namespace Divisor.Sketch

open Polynomial

variable (E : ECSetup)

/-- Explicit evaluation of the base-changed chord cubic. -/
theorem chordCubicBar_eval_eq
    (lam : ZMod E.q) (μ x : Fqbar E) :
    (chordCubicBar E lam μ).eval x =
      x ^ 3 - (fqToBar E lam) ^ 2 * x ^ 2 +
        (fqToBar E E.curveA - fqToBar E (2 * lam) * μ) * x +
        (fqToBar E E.curveB - μ ^ 2) := by
  unfold chordCubicBar chordCubicBivBar chordCubicBiv fqToBar
  simp

/-- The same evaluation, arranged as the curve residual of the chord-line
point `(x, λx + μ)`. -/
theorem chordCubicBar_eval_eq_curve_residual
    (lam : ZMod E.q) (μ x : Fqbar E) :
    (chordCubicBar E lam μ).eval x =
      x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB
        - (fqToBar E lam * x + μ) ^ 2 := by
  rw [chordCubicBar_eval_eq E lam μ x]
  have htwo : fqToBar E (2 * lam) = 2 * fqToBar E lam := by
    unfold fqToBar
    rw [map_mul]
    have h2 :
        (algebraMap (ZMod E.q) (Fqbar E)) (2 : ZMod E.q) =
          (2 : Fqbar E) := by
      rw [map_ofNat]
    rw [h2]
  rw [htwo]
  ring

/-- A root of the chord cubic gives a geometric point on the base-changed
curve, lying on the line `y = λx + μ`. -/
theorem chordCubicBar_root_onCurve
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) :
    (fqToBar E lam * x + μ) ^ 2 =
      x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB := by
  rw [chordCubicBar_eval_eq E lam μ x] at hroot
  have htwo : fqToBar E (2 * lam) = 2 * fqToBar E lam := by
    unfold fqToBar
    rw [map_mul]
    have h2 :
        (algebraMap (ZMod E.q) (Fqbar E)) (2 : ZMod E.q) =
          (2 : Fqbar E) := by
      rw [map_ofNat]
    rw [h2]
  rw [htwo] at hroot
  linear_combination -hroot

/-- The chord projection of the point `y = λx + μ` is `μ`. -/
@[simp] theorem zLambdaBar_chord_point
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hOnE :
      (fqToBar E lam * x + μ) ^ 2 =
        x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB) :
    zLambdaBar E lam ⟨x, fqToBar E lam * x + μ, hOnE⟩ = μ := by
  unfold zLambdaBar
  ring

/-- Point-generic version of `zLambdaBar_chord_point`. -/
theorem zLambdaBar_chord_point_of_y
    (lam : ZMod E.q) (μ : Fqbar E) (Q : GeomPoint E)
    (hY : Q.y = fqToBar E lam * Q.x + μ) :
    zLambdaBar E lam Q = μ := by
  unfold zLambdaBar
  rw [hY]
  ring

/-- Package a chord-cubic root as a geometric point above the chord
intercept `μ`. -/
noncomputable def geomPointOfChordCubicRoot
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) : GeomPoint E :=
  ⟨x, fqToBar E lam * x + μ, chordCubicBar_root_onCurve E lam μ x hroot⟩

@[simp] theorem geomPointOfChordCubicRoot_x
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) :
    (geomPointOfChordCubicRoot E lam μ x hroot).x = x := rfl

@[simp] theorem geomPointOfChordCubicRoot_y
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) :
    (geomPointOfChordCubicRoot E lam μ x hroot).y = fqToBar E lam * x + μ := rfl

@[simp] theorem zLambdaBar_geomPointOfChordCubicRoot
    (lam : ZMod E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) :
    zLambdaBar E lam (geomPointOfChordCubicRoot E lam μ x hroot) = μ :=
  zLambdaBar_chord_point E lam μ x _

/-- Evaluating the D-on-line polynomial at a chord-cubic root is the same
as evaluating `D` at the packaged geometric point. -/
theorem DLineBar_eval_eq_geomEval_of_root
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ x : Fqbar E)
    (hroot : (chordCubicBar E lam μ).eval x = 0) :
    (DLineBar E lam D μ).eval x =
      D.geomEval E (geomPointOfChordCubicRoot E lam μ x hroot) :=
  DLineBar_eval_eq_geomEval E lam D μ x
    (chordCubicBar_root_onCurve E lam μ x hroot)

/-! ## Converse direction: every geometric point's x is a root of the
chord cubic at its `zLambdaBar` -/

/-- For any `Q : GeomPoint E`, the `x`-coordinate of `Q` is a root of the
chord cubic at the chord intercept `zLambdaBar lam Q`. -/
theorem chordCubicBar_eval_eq_zero_of_geomPoint_zLambda
    (lam : ZMod E.q) (Q : GeomPoint E) :
    (chordCubicBar E lam (zLambdaBar E lam Q)).eval Q.x = 0 := by
  rw [chordCubicBar_eval_eq_curve_residual]
  have hY : fqToBar E lam * Q.x + zLambdaBar E lam Q = Q.y := by
    unfold zLambdaBar; ring
  rw [hY]
  linear_combination -Q.onCurve

/-- Evaluating the bar-level D-on-line polynomial at the intercept
`zLambdaBar lam Q` and the x-coordinate of `Q` recovers `D.geomEval Q`. -/
theorem DLineBar_eval_eq_geomEval_at_zLambda
    (lam : ZMod E.q) (D : CoordRingElt E.q) (Q : GeomPoint E) :
    (DLineBar E lam D (zLambdaBar E lam Q)).eval Q.x = D.geomEval E Q := by
  have hOnE : (fqToBar E lam * Q.x + zLambdaBar E lam Q) ^ 2 =
                Q.x ^ 3 + fqToBar E E.curveA * Q.x + fqToBar E E.curveB := by
    have hY : fqToBar E lam * Q.x + zLambdaBar E lam Q = Q.y := by
      unfold zLambdaBar; ring
    rw [hY]; exact Q.onCurve
  rw [DLineBar_eval_eq_geomEval E lam D (zLambdaBar E lam Q) Q.x hOnE]
  -- Goal: D.geomEval E ⟨Q.x, fqToBar E lam * Q.x + zLambdaBar E lam Q, hOnE⟩
  --       = D.geomEval E Q
  -- The two GeomPoints share their x; their y's are equal via `hY`.
  have hY : fqToBar E lam * Q.x + zLambdaBar E lam Q = Q.y := by
    unfold zLambdaBar; ring
  simp only [CoordRingElt.geomEval, hY]

/-! ## Formal X-derivative of `chordCubicBar`

Local helper for the log-derivative identity (proved on the
production side as `chord_sum_eq_chord_fiber_product_logDeriv` in
`Divisor/Bridges/ChordSumEqChordFiberProductLogDeriv.lean`).
Identifies the formal X-derivative
of the chord cubic with the chord-cone denominator factor
`3*x^2 + A - 2*lambda*y` that appears in `logDerivTerm`. -/

/-- Explicit closed form of `chordCubicBar` as a polynomial in
`Polynomial (Fqbar E)`. -/
theorem chordCubicBar_eq_explicit
    (lam : ZMod E.q) (μ : Fqbar E) :
    chordCubicBar E lam μ
      = Polynomial.X ^ 3
        - Polynomial.C ((fqToBar E lam) ^ 2) * Polynomial.X ^ 2
        + Polynomial.C (fqToBar E E.curveA - 2 * fqToBar E lam * μ) * Polynomial.X
        + Polynomial.C (fqToBar E E.curveB - μ ^ 2) := by
  unfold chordCubicBar chordCubicBivBar chordCubicBiv fqToBar
  simp [Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
        Polynomial.eval_C, Polynomial.eval_X, map_mul, map_pow, map_ofNat]

/-- **Formal X-derivative of `chordCubicBar`, evaluated at any `x`.**
The derivative coincides with the chord-cone denominator factor
`3*x^2 + A - 2*lambda*(lambda*x + μ)`. At a chord-cubic root `x`, where
`y = lambda*x + μ` lies on the curve, this is the bar-level denominator
appearing in `logDerivTerm`. -/
theorem chordCubicBar_derivative_eval
    (lam : ZMod E.q) (μ x : Fqbar E) :
    (chordCubicBar E lam μ).derivative.eval x =
      3 * x ^ 2 + fqToBar E E.curveA -
        2 * fqToBar E lam * (fqToBar E lam * x + μ) := by
  rw [chordCubicBar_eq_explicit]
  simp [Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_C,
        Polynomial.derivative_X, Polynomial.derivative_pow,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-! ## Chord-fiber-product evaluation at the chord intercept

Public bridge between the existing Vieta sums (`chord_x_pairwise_sum`,
`chord_x_triple_product` in `Divisor/ChordCubicSymmetric.lean`), the
chord-cubic factorisation, and the resultant-product form of
`chord_fiber_product_concrete`. -/

/-- **Vieta factorisation of `intersectionPoly` at the chord intercept.**
For two distinct chord-fiber points `A₀, A₁ ∈ E.points`, the
intersection polynomial at `μ = zLambda lam A₀` factors as
`(X − A₀.1)(X − A₁.1)(X − x₂)` over `(ZMod E.q)[X]`, where
`x₂ = λ² − A₀.1 − A₁.1` is the third chord x-coordinate.

This is the public version of the (private)
`Divisor.intersectionPoly_factorisation` in `GeometricSoundness.lean`.
Direct consequence of the Vieta identities `chord_x_pairwise_sum` and
`chord_x_triple_product`. -/
theorem intersectionPoly_factor_at_zLambda
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    Divisor.intersectionPoly E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
      = (Polynomial.X - Polynomial.C A₀.1) *
        (Polynomial.X - Polynomial.C A₁.1) *
        (Polynomial.X - Polynomial.C
          ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)) := by
  have he₂ := Divisor.chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  have he₃ := Divisor.chord_x_triple_product E A₀ A₁ hA₀ hA₁ hNV
  simp only [] at he₂ he₃
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set mu : ZMod E.q := A₀.2 - lam * A₀.1
  set x₂ : ZMod E.q := lam ^ 2 - A₀.1 - A₁.1
  have hMu_eq : zLambda E lam A₀ = mu := rfl
  rw [hMu_eq]
  unfold Divisor.intersectionPoly
  have hKey :
      (Polynomial.X - Polynomial.C A₀.1) *
          (Polynomial.X - Polynomial.C A₁.1) *
          (Polynomial.X - Polynomial.C x₂)
        = Polynomial.X ^ 3 - Polynomial.C (A₀.1 + A₁.1 + x₂) * Polynomial.X ^ 2
            + Polynomial.C (A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂) * Polynomial.X
            - Polynomial.C (A₀.1 * A₁.1 * x₂) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  rw [hKey]
  have hSum : A₀.1 + A₁.1 + x₂ = lam ^ 2 := by
    show A₀.1 + A₁.1 + (lam ^ 2 - A₀.1 - A₁.1) = _; ring
  rw [hSum]
  rw [show A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂ = E.curveA - 2 * lam * mu from he₂]
  rw [show A₀.1 * A₁.1 * x₂ = mu ^ 2 - E.curveB from he₃]
  rw [show E.curveB - mu ^ 2 = -(mu ^ 2 - E.curveB) from by ring,
      Polynomial.C_neg]
  ring

/-- **`intersectionPoly` splits at the chord intercept.** Immediate
consequence of `intersectionPoly_factor_at_zLambda`: a product of three
linear `X − C _` factors trivially splits over the base field. -/
theorem intersectionPoly_splits_at_zLambda
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    (Divisor.intersectionPoly E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)).Splits := by
  rw [intersectionPoly_factor_at_zLambda E A₀ A₁ hA₀ hA₁ hNV]
  exact ((Polynomial.Splits.X_sub_C A₀.1).mul
            (Polynomial.Splits.X_sub_C A₁.1)).mul
          (Polynomial.Splits.X_sub_C
            ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1))

/-- **Chord-fiber-product evaluation at the chord intercept.**
For two distinct chord-fiber points `A₀, A₁ ∈ E.points`, the value of
`chord_fiber_product_concrete E lam D` at `μ = zLambda lam A₀` factors
as the explicit three-term product `D(A₀)·D(A₁)·D(A₂)`, where
`A₂ = (λ² − A₀.1 − A₁.1, λ·A₂.1 + A₀.2 − λ·A₀.1)` is the third
chord-fiber point.

This is the bridge from the Vieta factorisation of the chord cubic to
the chord-side of the log-derivative identity (proved on the
production side as `chord_sum_eq_chord_fiber_product_logDeriv`). -/
theorem chord_fiber_product_concrete_eval_at_zLambda
    (D : CoordRingElt E.q) (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    (chord_fiber_product_concrete E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
      = D.eval A₀.1 A₀.2 *
        D.eval A₁.1 A₁.2 *
        D.eval ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
              ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
                 ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) +
               (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)) := by
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  set x₂ : ZMod E.q := lam ^ 2 - A₀.1 - A₁.1 with hx₂
  -- Chord-fiber-product evaluation: prod-split form.
  have hSplit := intersectionPoly_splits_at_zLambda E A₀ A₁ hA₀ hA₁ hNV
  rw [chord_fiber_product_concrete_eval_eq_prod_split E lam μ D hSplit]
  -- intersectionPoly factors into linear factors at the three chord roots.
  have hFact := intersectionPoly_factor_at_zLambda E A₀ A₁ hA₀ hA₁ hNV
  -- Roots multiset.
  have h₁_ne : (Polynomial.X - Polynomial.C A₀.1) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h₂_ne : (Polynomial.X - Polynomial.C A₁.1) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h₃_ne : (Polynomial.X - Polynomial.C x₂) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hProd_ne :
      (Polynomial.X - Polynomial.C A₀.1) * (Polynomial.X - Polynomial.C A₁.1) ≠ 0 :=
    mul_ne_zero h₁_ne h₂_ne
  have hRoots :
      (Divisor.intersectionPoly E lam μ).roots = {A₀.1, A₁.1, x₂} := by
    rw [hFact, Polynomial.roots_mul (mul_ne_zero hProd_ne h₃_ne),
        Polynomial.roots_mul hProd_ne,
        Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C,
        Polynomial.roots_X_sub_C]
    rfl
  rw [hRoots]
  -- Compute multiset .map .prod for {A₀.1, A₁.1, x₂}.
  show D.eval A₀.1 (lam * A₀.1 + μ) * (D.eval A₁.1 (lam * A₁.1 + μ) *
      (D.eval x₂ (lam * x₂ + μ) * 1)) = _
  -- Slope identity: λ·(A₁.1 − A₀.1) = A₁.2 − A₀.2.
  have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    show slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2
    have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
    rw [slopeOf]
    field_simp
  -- λ · A₀.1 + μ = A₀.2 (since μ = A₀.2 - λ·A₀.1).
  have h0 : lam * A₀.1 + μ = A₀.2 := by
    show lam * A₀.1 + zLambda E lam A₀ = A₀.2
    unfold zLambda; ring
  -- λ · A₁.1 + μ = A₁.2 (uses slope identity).
  have h1 : lam * A₁.1 + μ = A₁.2 := by
    show lam * A₁.1 + zLambda E lam A₀ = A₁.2
    unfold zLambda
    linear_combination hSlope
  rw [h0, h1]
  -- The third factor's y-arg expands μ = A₀.2 − lam · A₀.1.
  have h2 : lam * x₂ + μ = lam * x₂ + (A₀.2 - lam * A₀.1) := by
    show lam * x₂ + zLambda E lam A₀ = _
    unfold zLambda; ring
  rw [h2]
  ring
