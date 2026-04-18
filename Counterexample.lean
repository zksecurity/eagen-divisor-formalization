import Divisor

/-!
  Counterexample.lean

  **This file documents a historical inconsistency that has now been
  FIXED by Steps 1 & 2 of the remediation.**

  ## The original attack (paper `obs:neg-P-collapse`)

  Prior to the fix, the axiom
    `Divisor.extractorSucceeds_of_logDerivCheck_identically_zero`
  was logically inconsistent under Eagen's admissible set:

  - Curve `y² = x³ + 1` over `F_5` (5 affine F_5-points).
  - `stmt.k = 1`, `target = (0, 1)`, `bases 0 = (0, 4) = -target`.
  - `admSet` = Eagen, `{(a, b) : a.coeff 0 = 1}` — accepts `(1, 0)`.
  - `msg`: `polyA = 1`, `polyB = 0`, `m 0 = 4 = q - 1`.

  Under this configuration, the axiom's hypotheses all held, but its
  conclusion `extractorSucceeds E stmt msg 3 rfl` was *false*: the
  no-underflow guard at `i = 0` required `(1 + 4 : ZMod 5).val ≥ 1`,
  but `(1 + 4 : ZMod 5) = 0` whose `.val = 0`, failing `≥ 1`.

  ## The fix (Steps 1 & 2)

  - `DlogWitness.scalars` changed from `Fin k → ℕ` to `Fin k → ℤ` so
    that the paper's extractor `n_{j*} = -1` special case has a
    natural representation.
  - `extractedScalars` now includes the paper's unconditional
    `-P ∈ {B_j}` special case, returning `-1` at `j*` without reading
    `msg.m`.
  - `extractorSucceeds` dropped the underflow guard (no longer needed
    — the residue wraparound is handled by the special case).

  Under the new extractor, on the malicious instance above: the special
  case returns `scalars = (-1, 0, …)`, giving `|-1|.natAbs = 1 < 3 = d`,
  so `extractorSucceeds` holds. The axiom's conclusion is now true.
  The bridge axiom was additionally upgraded (Step 4) to assert the
  dlog relation directly in its conclusion.

  ## This file

  We keep the core arithmetic fact mechanized (the `ZMod` computation
  that used to make the old counterexample go through) as a witness
  that the underflow scenario is real and required the fix.

  The full `axiom_is_inconsistent` theorem from the pre-fix version
  no longer type-checks: the bridge axiom's conclusion now includes
  a `dlogHolds` conjunct that the old counterexample did not provide.
-/

open Polynomial
namespace CounterExample

/-- The core arithmetic kernel that drove the old inconsistency:
    `(1 + 4 : ZMod 5)` has natural-number value `0`, failing `≥ 1`.
    Still a true fact, just no longer reachable from the (now
    strengthened) bridge axiom. -/
theorem no_underflow_guard_failure_still_true :
    ¬ ((1 + (4 : ZMod 5)).val ≥ 1) := by decide

/-- Equivalent phrasing. -/
theorem sum_val_is_zero : (1 + (4 : ZMod 5)).val = 0 := by decide

end CounterExample
