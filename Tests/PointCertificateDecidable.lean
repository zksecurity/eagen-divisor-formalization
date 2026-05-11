/-
  Tests/PointCertificateDecidable.lean

  Smoke test: the point-skeleton chord-chain certificate has working
  `Decidable` instances at every level. This is what enables
  `native_decide` discharge of `h_chain` for concrete numerical inputs.

  See `docs/binary-completeness-summary.md` for the full picture.
-/
import Divisor.EagenBuildLandmark

namespace Divisor.Landmark

variable (E : ECSetup)

/-- Per-pair `PointChordCase` is Decidable. -/
example (p q : ECPoint E) : Decidable (PointChordCase E p q) := inferInstance

/-- Per-level `LevelStepPointChordCase` is Decidable. -/
example (points : List (ECPoint E)) :
    Decidable (LevelStepPointChordCase E points) := inferInstance

/-- Iterated `IteratedPointChordCase` is Decidable, recursively constructed. -/
example (n : ℕ) (points : List (ECPoint E)) :
    Decidable (IteratedPointChordCase E n points) := inferInstance

/-! For a concrete numerical input (specific `q`, `A`, `B`, and a list of
    affine points), users can write:

    ```lean
    example : IteratedPointChordCase E 4
        (level0SingletonPoints E [(x_0, y_0), …, (x_n, y_n)]) := by
      native_decide
    ```

    This validates the chord-chain certificate computationally and
    feeds into `ma_completeness_binary_*_point_certificate`. -/

end Divisor.Landmark
