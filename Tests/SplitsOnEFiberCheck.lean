/-
  Tests/SplitsOnEFiberCheck.lean

  Regression test for the auditor's fiber-rationality finding (P0.8).

  Pre-fix flaw: `normPoly_splits_over_Fq E D` (a univariate-poly-in-X
  splitting condition) was used as the precondition for the
  accounting and group-sum-zero clauses of
  `CoordRingElt.exists_divisor_multiplicity`. That hypothesis is
  *strictly weaker* than fiber-rationality: a root of `normPoly`
  may correspond to no F_q-point on `E`, in which case
  F_q-restricted β must vanish above it but the axiom would force
  it to contribute to the multiplicity sum.

  Concrete witness (auditor): `E : y² = x³ + 1 / F_5`, `D = X − 1`.
  `normPoly D = (X − 1)²` splits with natDeg 2, but `1³ + 1 = 2` is
  not a QR mod 5, so no F_5-points have x = 1. Under the old axiom
  Σβ would have been forced to 2; under the actual `E.points` β = 0
  identically. The old axiom was therefore false on this `D`.

  Fix: gate the accounting / group-sum-zero clauses on the
  *stronger* `splitsOnE E D` predicate, which adds the missing
  fiber-rationality condition. This file does not directly invoke
  the axiom (which is now sound) — it documents the predicate
  shape so the regression is grep-able.
-/
import Divisor.Axioms.AxiomExistsDivisorMultiplicity

namespace DivisorTest

open Divisor

/-- Documentation: `splitsOnE` requires both x-polynomial splitting
    AND fiber rationality (every root has an F_q-point above it). -/
example (E : ECSetup) (D : CoordRingElt E.q) :
    splitsOnE E D ↔
      normPoly_splits_over_Fq E D ∧
      (∀ α ∈ (normPoly E D).roots, ∃ y : ZMod E.q, (α, y) ∈ E.points) :=
  Iff.rfl

end DivisorTest
