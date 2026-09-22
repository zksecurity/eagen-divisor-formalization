/-
  Tests/DegreeExactRegression.lean

  Pins the semantics of `CoordRingElt.degE` as the *exact* pole order
  at the point at infinity.

  The Comparator judge (`Judge/README.md`) compares exported types, and
  `degE` is a named constant resolved through `Divisor/DefsPre.lean` by
  both `Challenge.lean` and the library. A change to its body therefore
  shifts the meaning of every frozen statement that mentions it while
  leaving the judge green. These regressions are the audit trail for
  that: they fail loudly if the definition ever drifts back to the old
  `max (2·deg a) (3 + 2·deg b)`, which — because `natDegree 0 = 0` —
  assigned order three to every element, including the vertical line.
-/
import Divisor.BetaConstructive
import Divisor.Protocol
import Tests.CurveFixtures

namespace Tests.DegreeExactRegression

open Polynomial Divisor

/-- The defining property: `degE` is the degree of the norm polynomial
    `a² − b²·(x³ + Ax + B)`, with no honesty or nonzero premise. -/
theorem degE_eq_normPoly_natDegree (E : ECSetup) (D : CoordRingElt E.q) :
    D.degE = (normPoly E D).natDegree :=
  (normPoly_natDegree_eq E D).symm

section Values

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- A vertical line `x − c` has a double pole at infinity, not a triple
    one. This is the case the old definition got wrong, and the reason
    length-two binary completeness was uninstantiable. -/
theorem degE_vertical (c : ZMod q) :
    (⟨X - C c, 0⟩ : CoordRingElt q).degE = 2 := by
  simp [CoordRingElt.degE]

/-- A nonzero constant is regular at infinity. -/
theorem degE_const (c : ZMod q) : (⟨C c, 0⟩ : CoordRingElt q).degE = 0 := by
  simp [CoordRingElt.degE]

/-- `−y` keeps its triple pole: the `b` branch is unaffected. -/
theorem degE_y : (⟨0, 1⟩ : CoordRingElt q).degE = 3 := by
  simp [CoordRingElt.degE]

/-- The `b ≠ 0` branch still agrees with the old formula, so nothing
    outside the `b = 0` corner changed value. -/
theorem degE_eq_old_of_b_ne_zero (D : CoordRingElt q) (hb : D.b ≠ 0) :
    D.degE = max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree) :=
  CoordRingElt.degE_of_b_ne_zero hb

end Values

/-- The verifier's degree check admits the vertical message at the
    smallest public bound `ma_soundness` allows (`2 ≤ stmt.degBound`).
    Under the old definition no message at all passed at bound two. -/
theorem verifierDegreeCheck_vertical_at_bound_two
    {q : ℕ} [Fact (Nat.Prime q)] (c : ZMod q) :
    verifierDegreeCheck (k := 0) ⟨fun i => i.elim0, X - C c, 0⟩ 2 := by
  have h := degE_vertical (q := q) c
  show (⟨X - C c, 0⟩ : CoordRingElt q).degE ≤ 2
  omega

/--
info: 'Tests.DegreeExactRegression.degE_eq_normPoly_natDegree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms degE_eq_normPoly_natDegree

end Tests.DegreeExactRegression
