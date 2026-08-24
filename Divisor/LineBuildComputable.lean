/-
  Divisor/LineBuildComputable.lean

  Computable line-build recursive driver built on `CoordRingEltC`.
  Mirrors `Divisor/LineBuildRecursive.lean` structurally but uses
  only computable primitives.

  Curve coefficients (`curveA`, `curveB`) are passed explicitly to
  avoid the noncomputable `ECSetup` projections.
-/
import Divisor.CoordRingEltC

namespace Divisor

/-- Computable analog of `Accum`: a running point + accumulated
    polynomial. -/
structure AccumC (q : ℕ) where
  point : ZMod q × ZMod q
  poly : CoordRingEltC q
  deriving Repr, DecidableEq

namespace AccumC

variable {q : ℕ}

/-- Slope of the chord through two affine points; matches `slopeOf`. -/
@[inline] def slopeOf (x₀ y₀ x₁ y₁ : ZMod q) : ZMod q :=
  (y₁ - y₀) * (x₁ - x₀)⁻¹

/-- Build a level-1 accumulator from two distinct-`x` affine points. -/
def fromChordPair_distinct (curveA : ZMod q)
    (P Q : ZMod q × ZMod q) : AccumC q :=
  let chord := CoordRingEltC.chord curveA P Q
  let lam := slopeOf P.1 P.2 Q.1 Q.2
  let Qx := lam ^ 2 - P.1 - Q.1
  let Qy := lam * Qx + (P.2 - lam * P.1)
  { point := (Qx, -Qy), poly := chord }

/-- Vertical chord branch (`P = -Q`).  Carries `P` as sentinel and
    `(X − C P.1, 0)` as the vertical line. -/
def fromChordPair_vertical (P : ZMod q × ZMod q) : AccumC q :=
  { point := P
    poly := { a := CoeffPoly.X - CoeffPoly.C P.1, b := 0 } }

/-- Combine two distinct-`x` accumulators (level ≥ 1). -/
def combine_higher_distinct (curveA curveB : ZMod q)
    (a b : AccumC q) : AccumC q :=
  let chord := CoordRingEltC.chord curveA a.point b.point
  let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
  let Qx := lam ^ 2 - a.point.1 - b.point.1
  let Qy := lam * Qx + (a.point.2 - lam * a.point.1)
  let mul_with_chord :=
    CoordRingEltC.mul curveA curveB
      (CoordRingEltC.mul curveA curveB chord a.poly) b.poly
  let after_div_a := mul_with_chord.divLin a.point.1
  let after_div_b := after_div_a.divLin b.point.1
  { point := (Qx, -Qy), poly := after_div_b }

/-- Combine two negative-of-each-other accumulators (vertical chord). -/
def combine_higher_vertical (curveA curveB : ZMod q)
    (a b : AccumC q) : AccumC q :=
  let mul_ab := CoordRingEltC.mul curveA curveB a.poly b.poly
  let combined := mul_ab.divLin a.point.1
  { point := a.point, poly := combined }

end AccumC

/-- Level-0 step: pair adjacent inputs, build chord lines. -/
def lineBuild_level0C {q : ℕ} (curveA : ZMod q)
    (Ps : List (ZMod q × ZMod q)) : List (AccumC q) :=
  match Ps with
  | [] => []
  | [P] => [{ point := P, poly := { a := 1, b := 0 } }]
  | P :: Q :: rest =>
      if P.1 ≠ Q.1 then
        AccumC.fromChordPair_distinct curveA P Q ::
          lineBuild_level0C curveA rest
      else if P.2 = -Q.2 then
        AccumC.fromChordPair_vertical P :: lineBuild_level0C curveA rest
      else
        -- Tangent doubling case: deferred (matches the noncomputable
        -- driver's placeholder behavior).
        { point := P, poly := { a := 1, b := 0 } } ::
          lineBuild_level0C curveA rest

/-- Level-(k+1) step: pair adjacent accumulators and combine. -/
def lineBuild_level_stepC {q : ℕ} (curveA curveB : ZMod q)
    (xs : List (AccumC q)) : List (AccumC q) :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if a.point.1 ≠ b.point.1 then
        AccumC.combine_higher_distinct curveA curveB a b ::
          lineBuild_level_stepC curveA curveB rest
      else if a.point.2 = -b.point.2 then
        AccumC.combine_higher_vertical curveA curveB a b ::
          lineBuild_level_stepC curveA curveB rest
      else
        a :: b :: lineBuild_level_stepC curveA curveB rest

/-- Fuel-based iteration to convergence. -/
def lineBuild_iterateC {q : ℕ} (curveA curveB : ZMod q) :
    ℕ → List (AccumC q) → List (AccumC q)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else lineBuild_iterateC curveA curveB n
        (lineBuild_level_stepC curveA curveB xs)

/-- Top-level computable line-build driver. -/
def lineBuildC {q : ℕ} (curveA curveB : ZMod q)
    (Ps : List (ZMod q × ZMod q)) : CoordRingEltC q :=
  let level1 := lineBuild_level0C curveA Ps
  let final := lineBuild_iterateC curveA curveB Ps.length level1
  match final with
  | [] => { a := 1, b := 0 }
  | [single] => single.poly
  | _ => { a := 1, b := 0 }

end Divisor
