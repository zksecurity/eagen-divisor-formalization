/-
  Tests/EagenBuildEvalSmokeTest.lean

  Full end-to-end `#eval` of `eagenBuildC` over `y² = x³ + 1` / F_5.

  Affine points: (0, 1), (0, 4), (2, 2), (2, 3), (4, 0).  The
  2-torsion point is (4, 0).

  Sum-zero quadruple: [(0,1), (2,3), (0,4), (2,2)].
    Verification: (0,1)+(2,3) = -(4,0) = (4,0) (2-torsion).
                  (0,4)+(2,2) = -(4,0) = (4,0).
                  Sum = 2·(4,0) = O.  ✓

  Eagen level-0: pair adjacent inputs.
    Pair 1: chord through (0,1),(2,3) ⇒ accumulator point (4, 0).
    Pair 2: chord through (0,4),(2,2) ⇒ accumulator point (4, 0).
  Eagen level-1: both points equal (4, 0), and the vertical branch
    fires (since (4,0).2 = 0 = -0).  Output is
    `(chord_1 · chord_2) / (X − 4)`.

  Expected divisor of the eagenBuild output:
    chord_1 + chord_2 − (X−4) =
       (0,1)+(2,3)+(4,0) + (0,4)+(2,2)+(4,0) − 2·(4,0) − 4·∞
       = (0,1)+(2,3)+(0,4)+(2,2) − 4·∞.

  So the eagenBuild output should vanish at each of the four input
  points, with no other zeros over the affine support.
-/
import Divisor.EagenBuildComputable

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

open Divisor

/-- The four input points, sum-zero on `y² = x³ + 1` / F_5. -/
def Ps : List (ZMod 5 × ZMod 5) := [(0, 1), (2, 3), (0, 4), (2, 2)]

/-- eagenBuild output for the sum-zero length-4 list. -/
def D : CoordRingEltC 5 :=
  eagenBuildC (curveA := (0 : ZMod 5)) (curveB := (1 : ZMod 5)) Ps

#eval D.a.coeffs
#eval D.b.coeffs

-- D should vanish at each of the four input points.
#eval D.eval 0 1   -- expect 0
#eval D.eval 2 3   -- expect 0
#eval D.eval 0 4   -- expect 0
#eval D.eval 2 2   -- expect 0

-- D should not vanish at (4, 0) (the 2-torsion point, divided out).
#eval D.eval 4 0   -- expect ≠ 0

example : D.eval 0 1 = 0 := by native_decide
example : D.eval 2 3 = 0 := by native_decide
example : D.eval 0 4 = 0 := by native_decide
example : D.eval 2 2 = 0 := by native_decide
example : D.eval 4 0 ≠ 0 := by native_decide
