import Divisor.Sketch.ChordFiberProductConcrete

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

end Divisor.Sketch
