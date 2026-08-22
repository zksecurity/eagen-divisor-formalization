/-
  Tests/F5RegressionAxiomClosure.lean

  Regression sanity-check for the soundness restoration:
  * The headline theorems no longer depend on the false
    `CoordRingElt.divisor_group_sum_zero` axiom.
  * On the geometric-zero skeleton branch, the MA/IP closures are
    sorry-free and expose the current named geometric/class-group
    obligations directly.

  Run via `lake env lean Tests/F5RegressionAxiomClosure.lean` (the
  `#print axioms` outputs land in the build log).
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness

-- Axiom closure of the headline soundness/completeness theorems.
-- Confirms the soundness restoration: the previous unsound axiom
-- `Divisor.CoordRingElt.divisor_group_sum_zero` is no longer in the
-- closure of the headline theorem.

/--
info: 'Divisor.ma_extractable' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable

/--
info: 'Divisor.ip_extractable' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable

/--
info: 'Divisor.ma_completeness' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness

-- Raw point-count-dependent base forms remain available under `_base`.
/--
info: 'Divisor.ma_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_base

/--
info: 'Divisor.ip_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_base

/--
info: 'Divisor.ma_completeness_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_base
