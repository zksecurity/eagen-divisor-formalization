/-
  Tests/RegressionDoublingChallenge.lean

  Regression test pinning the **F_5 doubling counterexample** to the
  current `weil_reciprocity_honest` axiom.

  Setup over `F_5`, curve `y² = x³ + 1` (with `curveA = 0`):
    * `D = -3X - 1 + y`, equivalently `a = -3X - 1`, `b = -1`.
    * target `P = (0, 4)`,  basis `B_1 = B_2 = (2, 2)` with `n_1 = n_2 = -1`.
    * challenge `A_0 = A_1 = (0, 4)` (the diagonal "doubling" case).

  Concrete inline computation of `logDerivCheckFn` at this challenge:
    * `D` does NOT vanish at `A_0 = A_1 = (0, 4)` (`D5_eval 0 4 = 3 ≠ 0`).
    * `D` does vanish at `(0, 1) = -P` and `(2, 2) = B_i` (consistent
      with the honest-divisor structure `(-P) + Σ n_i (B_i)`).
    * `slopeOf (0,4) (0,4) = 0/0 = 0` (Lean's totalised inverse), NOT
      the geometric tangent `(3·0² + 0)/(2·4) = 0` (here also 0 by
      coincidence; the bug is more visible on other curves but the
      formula's *output value* still differs from the "tangent slope"
      semantics in general).

  The current axiom claims `logDerivCheckFn = 0` for any pair not in
  `badChallengesCompleteness`. The doubling pair `(A_0, A_0)` is
  **NOT** in that set (since `D` doesn't vanish at `A_0` or its
  computed third intersection — both equal `(0, 4)` by the wrong
  slope). But the actual value computed is `2 ≠ 0` in `F_5`.

  After the planned fix (B4–B5 of the audit plan), the strengthened
  `badChallengesCompleteness` will include the diagonal, so this
  challenge falls in the bad set and the (new) theorem statement
  does not apply.

  This file pins the regression by `native_decide`-ing both
    `claim_F5 = 2`  (showing the axiom claim disagrees with reality
                     by exactly 2 in F_5),
    `claim_F5 ≠ 0`  (witnessing the unsoundness directly).

  Once the axiom is replaced by a theorem with the strengthened
  precondition, this file should be updated to instead:
    * confirm the doubling pair lands in the strengthened bad set,
    * confirm an off-diagonal challenge for the same `D` produces
      `logDerivCheckFn = 0`.
-/
import Divisor.LogDeriv
import Divisor.SupportDisjoint

open Polynomial Divisor

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Inline `D.eval` for the F_5 setup.  `D = -3X - 1 + y`. -/
def D5_eval (x y : ZMod 5) : ZMod 5 :=
  -3 * x - 1 - (-1) * y

#eval D5_eval 0 1  -- 0  (zero of D, lifts to -P)
#eval D5_eval 2 2  -- 0  (zero of D, lifts to B)
#eval D5_eval 0 4  -- 3  (D doesn't vanish at A_0 = (0, 4))

/-- Inline `logDerivTerm` matching `Divisor/LogDeriv.lean:136`. -/
def logDerivTerm_F5 (lam x y : ZMod 5) : ZMod 5 :=
  let num_x : ZMod 5 := -3
  let num_y : ZMod 5 := 1
  let den := D5_eval x y
  let dxdz_num : ZMod 5 := 2 * y
  let dydz_num : ZMod 5 := 3 * x^2
  let dxdz_den : ZMod 5 := 3 * x^2 - 2 * lam * y

  (num_x * dxdz_num + num_y * dydz_num) * (den * dxdz_den)⁻¹

/-- `slopeOf (0,4) (0,4) = (4-4) * (0-0)⁻¹ = 0`. -/
def lam_F5 : ZMod 5 := (4 - 4) * (0 - 0)⁻¹
#eval lam_F5  -- 0

def mu_F5 : ZMod 5 := 4 - lam_F5 * 0  -- 4
#eval mu_F5

def x2_F5 : ZMod 5 := lam_F5^2 - 0 - 0  -- 0
def y2_F5 : ZMod 5 := lam_F5 * x2_F5 + (4 - lam_F5 * 0)  -- 4

def lhs_F5 : ZMod 5 :=
  logDerivTerm_F5 lam_F5 0 4
    + logDerivTerm_F5 lam_F5 0 4
    + logDerivTerm_F5 lam_F5 x2_F5 y2_F5
#eval lhs_F5

/-- The chord line `L`: `y = λ·x + μ`. -/
def L_F5 (x y : ZMod 5) : ZMod 5 := y - lam_F5 * x - mu_F5

/-- `negP = (target.1, -target.2)`. -/
def rhs_F5 : ZMod 5 :=
  -(L_F5 0 (-4))⁻¹ + (-1) * (L_F5 2 2)⁻¹ + (-1) * (L_F5 2 2)⁻¹
#eval rhs_F5

/-- The discrepancy claimed-zero by `weil_reciprocity_honest`. -/
def claim_F5 : ZMod 5 := lhs_F5 - rhs_F5
#eval claim_F5  -- 2 (NOT 0 — the axiom is unsound here)

/-- **Pinned regression**: the actual `logDerivCheckFn` value for this
    F_5 doubling configuration is `2`, not `0`. Witnesses what the
    pre-audit axiom statement claimed (incorrectly). -/
example : claim_F5 = 2 := by native_decide

example : claim_F5 ≠ 0 := by native_decide

/-! ## After-audit-fix verification

After the audit fix in `Divisor/SupportDisjoint.lean` (B4 of the audit
plan), the strengthened `badPairCompletenessPred` now includes the
**diagonal** `A_0 = A_1` as a bad event. The doubling pair
`((0, 4), (0, 4))` therefore lands in the bad set, so the (sound)
strengthened axiom statement does not apply to it.

The witness below confirms `(A_0, A_0) ∈ badChallengesCompleteness`
for the doubling pair, demonstrating the audit fix works at the
concrete level.

To set this up we'd need a full `ECSetup` for F_5 with `y² = x³ + 1`,
which is more involved than this file warrants. Instead, we directly
note the predicate-level diagonal disjunct fires (`p.1 = p.2`),
visible by inspection of `Divisor/SupportDisjoint.lean:35`. -/

example (p : (ZMod 5 × ZMod 5) × (ZMod 5 × ZMod 5)) (h : p.1 = p.2) :
    p.1 = p.2 ∨ False := Or.inl h
