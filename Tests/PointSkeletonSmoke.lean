/-
  Tests/PointSkeletonSmoke.lean

  Smoke test for the Landmark point-skeleton chain certificate: on
  `E17`, the length-4 support `[(0,1), (1,6), (2,3), (6,8)]` passes
  the full iterated chord-case check by direct computation.
-/
import Divisor.EagenBuildLandmark
import Tests.CurveFixtures

namespace Tests.PointSkeletonSmoke

open Divisor Divisor.Landmark Tests.CurveFixtures

example :
    IteratedPointChordCase E17 4
      (level0SingletonPoints E17 [(0, 1), (1, 6), (2, 3), (6, 8)]) := by
  native_decide

end Tests.PointSkeletonSmoke
