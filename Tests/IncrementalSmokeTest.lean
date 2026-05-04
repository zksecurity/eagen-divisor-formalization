/-
  Tests/IncrementalSmokeTest.lean

  Concrete `#eval` smoke test for the chord-line construction over
  `F_5` with `y² = x³ + 1`.

  Affine points of `y² = x³ + 1` over `F_5`:
  * `(0, 1)`, `(0, 4)` (= `−(0,1)`)
  * `(2, 2)`, `(2, 3)` (= `−(2,2)`)
  * `(4, 0)` (2-torsion)

  The chord through `(0, 1)` and `(2, 3)` has slope `λ = 1`, intercept
  `μ = 1`. Its third intersection with the curve is `(4, 0)`, so the
  three points sum to zero in the group.

  Concrete chord polynomial: `D = y − x − 1`. Expected: vanishes at
  `(0, 1)`, `(2, 3)`, `(4, 0)`. Pinned via `native_decide`.
-/
import Mathlib.Data.ZMod.Basic

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Inline chord polynomial value `D(x, y) = -x - 1 + y` over `F_5`. -/
def D_eval (x y : ZMod 5) : ZMod 5 := -x - 1 + y

#eval D_eval 0 1   -- 0 (chord vanishes at (0, 1))
#eval D_eval 2 3   -- 0 (chord vanishes at (2, 3))
#eval D_eval 4 0   -- 0 (chord vanishes at the third intersection (4, 0))
#eval D_eval 0 4   -- 3 (non-zero)
#eval D_eval 2 2   -- 4 (non-zero)

example : D_eval 0 1 = 0 := by native_decide
example : D_eval 2 3 = 0 := by native_decide
example : D_eval 4 0 = 0 := by native_decide
example : D_eval 0 4 ≠ 0 := by native_decide
example : D_eval 2 2 ≠ 0 := by native_decide
