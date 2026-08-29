/-
  Tests/MAExtractorExec.lean

  Native-code smoke test for the public MA recovery function. The base is
  `-target`, so the extractor takes its unconditional special branch and
  returns the scalar `-1`.
-/
import Divisor.Soundness
import Tests.CurveFixtures

namespace Tests.MAExtractorExec

open Divisor
open Tests.CurveFixtures

private def stmt : DlogStatement E17.q where
  k := 1
  degBound := 2
  bases := fun _ => (0, 16)
  target := (0, 1)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def oneCoeff : ℕ →₀ ZMod E17.q where
  support := {0}
  toFun n := if n = 0 then 1 else 0
  mem_support_toFun := by
    intro n
    simp

private def msg : MAProverMsg E17.q stmt.k where
  m := fun _ => 0
  polyA := Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff oneCoeff)
  polyB := Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff oneCoeff)

private def recoveredScalar : Option (Nat × Int) :=
  match maExtractor E17 stmt msg with
  | none => none
  | some wit =>
      if hk : 0 < wit.k then some (wit.k, wit.scalars ⟨0, hk⟩) else none

#eval recoveredScalar

example : recoveredScalar = some (1, -1) := by
  native_decide

end Tests.MAExtractorExec
