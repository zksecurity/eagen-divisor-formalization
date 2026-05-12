/-
  Tests/CoeffPolyEvalSmokeTest.lean

  Sanity #eval for `CoeffPoly` over `F_5`.  Confirms add / mul / eval /
  divXSubC work computably end-to-end.
-/
import Divisor.CoeffPoly

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
