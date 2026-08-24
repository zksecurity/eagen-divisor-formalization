/-
  Tests/CurveFixtures.lean

  Shared concrete-curve fixtures for the test suite. `mkFilteredCurve`
  builds an `ECSetup` whose point set is the filtered universe of
  curve solutions, so each fixture supplies only the parameters and
  the two decidable side conditions (discriminant, field size).

  * `E17`: `y² = x³ + 1` over `F₁₇`.
  * `E43`: `y² = x³ + 1` over `F₄₃`.
-/
import Divisor.DefsPre

namespace Tests.CurveFixtures

open Divisor

/-- `ECSetup` with point set the filtered universe of solutions of
    `y² = x³ + A·x + B` over `F_q`. -/
abbrev mkFilteredCurve (q : ℕ) [NeZero q] (hq : Nat.Prime q)
    (A B : ZMod q) (hDisc : 4 * A ^ 3 + 27 * B ^ 2 ≠ (0 : ZMod q))
    (hq_ge : q ≥ 5) : ECSetup where
  q := q
  hq_prime := hq
  curveA := A
  curveB := B
  points := Finset.univ.filter (fun p => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B)
  hOnCurve := fun _p hp => (Finset.mem_filter.mp hp).2
  hComplete := fun x y h => Finset.mem_filter.mpr ⟨Finset.mem_univ (x, y), h⟩
  hDisc := hDisc
  numPoints :=
    (Finset.univ.filter
      (fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B)).card + 1
  hNumPoints := rfl
  hq_ge := hq_ge

def E17 : ECSetup := mkFilteredCurve 17 (by decide) 0 1 (by decide) (by decide)

def E43 : ECSetup := mkFilteredCurve 43 (by decide) 0 1 (by decide) (by decide)

end Tests.CurveFixtures
