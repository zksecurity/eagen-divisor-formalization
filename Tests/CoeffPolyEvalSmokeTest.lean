/-
  Tests/CoeffPolyEvalSmokeTest.lean

  Sanity #eval for `CoeffPoly` over `F_5`.  Confirms add / mul / eval /
  divXSubC work computably end-to-end.
-/
import Divisor.CoeffPoly
import Divisor.CoordRingEltC

open Divisor.CoeffPoly

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- X over F_5
def fX : Divisor.CoeffPoly 5 := X
def f1 : Divisor.CoeffPoly 5 := C 1
def fXm1 : Divisor.CoeffPoly 5 := X - C 1
def fX2m1 : Divisor.CoeffPoly 5 := X * X - C 1

#eval fX.coeffs            -- [0, 1]
#eval fXm1.coeffs          -- [4, 1] (since -1 = 4 in F_5)
#eval fX2m1.coeffs         -- expect coefficients of X² - 1 = -1 + 0·X + X²

#eval fX2m1.eval 1         -- 0 (1² - 1 = 0)
#eval fX2m1.eval 2         -- 3 (4 - 1 = 3)

-- (X² - 1) / (X - 1) should be X + 1.
#eval (fX2m1.divXSubC 1).coeffs   -- expect [1, 1]

-- (X² - 1) / (X - (-1)) should be X - 1, i.e. coeffs [4, 1].
#eval (fX2m1.divXSubC (-1)).coeffs   -- expect [4, 1]

example : fX2m1.eval 1 = 0 := by native_decide
example : (fX2m1.divXSubC 1).coeffs = [1, 1] := by native_decide
example : (fX2m1.divXSubC (-1)).coeffs = [4, 1] := by native_decide

/-! ## CoordRingEltC sanity over `y² = x³ + 1` / F_5 -/

open Divisor (CoordRingEltC)

-- Curve y² = x³ + 1: curveA = 0, curveB = 1.
-- Chord through (0, 1) and (2, 3): slope = (3-1)*(2-0)⁻¹ = 2 * 3 = 6 ≡ 1.
-- mu = 1 - 1*0 = 1. Line: y - x - 1.  D = (-(1·X+1), -1), so
--   D.eval x y = -(x+1) - (-1)*y = -x - 1 + y. Matches IncrementalSmokeTest.
def chord01_23 : CoordRingEltC 5 := CoordRingEltC.chord (0 : ZMod 5) (0, 1) (2, 3)

#eval chord01_23.a.coeffs   -- expect coefficients of -X - 1 = [4, 4]
#eval chord01_23.b.coeffs   -- expect -1 = [4]

#eval chord01_23.eval 0 1   -- 0 (chord through (0,1))
#eval chord01_23.eval 2 3   -- 0 (chord through (2,3))
#eval chord01_23.eval 4 0   -- 0 (third intersection (4,0))
#eval chord01_23.eval 0 4   -- 3 (non-zero off support)

example : chord01_23.eval 0 1 = 0 := by native_decide
example : chord01_23.eval 2 3 = 0 := by native_decide
example : chord01_23.eval 4 0 = 0 := by native_decide
example : chord01_23.eval 0 4 ≠ 0 := by native_decide

-- Multiplication: D₁·D₂ where D₁ is chord through (0,1),(2,3),(4,0).
-- D₁ vanishes on all three; D₁² should also.
def chord01_23_squared : CoordRingEltC 5 :=
  CoordRingEltC.mul (0 : ZMod 5) (1 : ZMod 5) chord01_23 chord01_23

#eval chord01_23_squared.eval 0 1   -- 0
#eval chord01_23_squared.eval 4 0   -- 0

example : chord01_23_squared.eval 0 1 = 0 := by native_decide
example : chord01_23_squared.eval 4 0 = 0 := by native_decide

-- divLin: chord01_23 vanishes at (0,1), so divLin by x = 0 should
-- produce a quotient that doesn't vanish at (0,1) (lifts the order
-- by one, leaving the rest of the divisor intact).
#eval (chord01_23.divLin 0).a.coeffs
#eval (chord01_23.divLin 0).b.coeffs
