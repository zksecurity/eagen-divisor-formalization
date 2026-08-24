/-
  Tests/AnyLengthCompletenessSmoke.lean

  Smoke test for the any-length completeness chain
  (`Divisor/SafeSupport.lean`): on the F₄₃ curve `y² = x³ + 1`, the
  computable general-position certificate `SafePairsCert` holds for a
  concrete LENGTH-5 support — an odd length covered by none of the
  structured once-and-for-all families (2/4 and chord 4/6/8) — and
  discharges the full point-skeleton chain certificate through
  `iteratedPointChordCase_of_safePairs`, i.e. through the any-length
  theorem rather than a per-instance check of the accumulator run.
-/
import Divisor.SafeSupport
import Tests.CurveFixtures

namespace Tests.AnyLengthCompletenessSmoke

open Divisor Divisor.LineAccum Tests.CurveFixtures

/-- A sum-zero, nodup, length-5 support in general position (found by
search; not closed under negation, so not an inverse-pair shape). -/
private def support5 : List (ZMod E43.q × ZMod E43.q) :=
  [(31, 6), (40, 24), (12, 40), (19, 25), (12, 3)]

-- The support is on-curve, nodup, and sums to zero.
example : ∀ P ∈ support5, P ∈ E43.points := by native_decide
example : support5.Nodup := by native_decide

-- The computable general-position certificate holds for the support.
example : SafePairsCert E43 support5 := by native_decide

-- It discharges the full chain certificate at the support's length,
-- through the semantic bridge (no per-instance check of the run).
example :
    IteratedPointChordCase E43 support5.length
      (level0SingletonPoints E43 support5) := by
  have h_on : ∀ P ∈ support5, P ∈ E43.points := by native_decide
  have hcert : SafePairsCert E43 support5 := by native_decide
  exact iteratedPointChordCase_of_safePairs E43 support5 h_on
    (SafePairs.of_cert E43 h_on hcert)

end Tests.AnyLengthCompletenessSmoke
