/-
  Tests/F5RegressionAxiomClosure.lean

  Compact closure pins for the six primary theorems — a fast
  regression companion to the exhaustive `Tests/AxiomClosurePin.lean`.

  Run via `lake env lean Tests/F5RegressionAxiomClosure.lean`.
-/
import Divisor.Completeness
import Divisor.Hasse

/--
info: 'Divisor.ma_soundness_count_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_count_bound

/--
info: 'Divisor.ip_extractable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable

/--
info: 'Divisor.ma_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness

-- Two-event accounting forms.
/--
info: 'Divisor.ma_soundness_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_base

/--
info: 'Divisor.ip_extractable_base' depends on axioms: [propext,
 Classical.choice,
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

-- The `_hasse` variants are the only consumers of the Hasse axiom.
/--
info: 'Divisor.ma_soundness_count_bound_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_count_bound_hasse
