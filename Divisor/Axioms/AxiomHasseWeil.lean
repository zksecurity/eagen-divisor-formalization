/-
  Divisor/Axioms/AxiomHasseWeil.lean

  Hasse-Weil bound on #E(F_q): |#E(F_q) - q - 1| ≤ 2√q.
-/
import Mathlib.Data.Real.Sqrt
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Hasse-Weil Bound (Hasse 1936, Weil 1948)

|#E(F_q) - (q + 1)| ≤ 2·√q, equivalently (#E - q - 1)² ≤ 4q.

Human-readable version: the number of `F_q`-rational points on `E`
differs from `q + 1` by at most `2 * sqrt(q)`. The Lean axiom records
the equivalent integer-squared inequality.

**Integer-squared form.** The derived theorem `hasse_weil` states
`((numPoints - q - 1) : ℤ)² ≤ 4q`. The squared form is preferred over
`2·Nat.sqrt q` because `2·⌊√q⌋` is strictly smaller than `⌊2·√q⌋` in
general (e.g. at `q = 7`, `2·⌊√7⌋ = 4` while `⌊2·√7⌋ = 5`). The
squared form is the sharp integer statement and implies both
one-sided bounds when needed.

The axiom below is the absolute-value/√ form
`|#E(F_q) - q - 1| ≤ 2√q`. -/
axiom hasse_weil_textbook :
  |(((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)| ≤ 2 * Real.sqrt (E.q : ℝ)

/-- Integer-squared form of Hasse-Weil used by the project. -/
theorem hasse_weil :
  ((E.numPoints : ℤ) - E.q - 1)^2 ≤ 4 * E.q
    := by
  have hAbs := hasse_weil_textbook E
  have hR :
      (((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)^2
        ≤ (4 * (E.q : ℝ)) := by
    have hSq :
        (((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)^2
          ≤ (2 * Real.sqrt (E.q : ℝ))^2 := by
      rw [sq_le_sq]
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
      exact hAbs
    have hSqrtSq : (Real.sqrt (E.q : ℝ))^2 = (E.q : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith
  exact_mod_cast hR

end Divisor
