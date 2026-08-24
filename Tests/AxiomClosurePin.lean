/-
  Tests/AxiomClosurePin.lean

  Pin the axiom closure of every headline theorem. Each
  `#print axioms` below is wrapped in `#guard_msgs`, so the build
  FAILS if any closure drifts from the expected list — a new axiom, a
  revived `sorryAx`, or `Lean.ofReduceBool` in a closure is caught
  without reading the build log.

  Expected closures come in exactly two classes:

  * **Lean core three** (`propext`, `Classical.choice`, `Quot.sound`)
    — every theorem outside the terminal leaf `Divisor/Hasse.lean`.
    The library is stated in the point-count currency
    `n = E.points.card`, and the leaf is the only module importing
    the axiom file, so this class is axiom-free by construction.
    It includes the extractability headlines (`ma_extractable`,
    `ip_extractable` and their `_base`/`_paper`/probability/
    contrapositive forms), the whole completeness side
    (`ma_completeness*`, `ip_completeness*`, the binary chain, the
    any-length `SafePairs` route), the divisor-multiplicity bridge
    (`CoordRingElt.exists_divisor_multiplicity*`,
    `ordAt_group_sum_zero_under_split`), and the leaf's `_of_count`
    flavors (field-size forms with explicit count-bound hypotheses).

  * **Core three + `Divisor.hasse_weil_textbook`** (Silverman V.1.1)
    — the leaf's `_hasse` theorems only. These pins certify the
    entire axiom surface of the project: one axiom, nothing else.

  Suffix conventions: short name = point-count form; `_q` =
  field-size form via the trivial fiber bound `|E| ≤ 2q` (axiom-free,
  completeness side); `_hasse` = field-size form priced by the axiom,
  which supplies the lower bound `q ≤ 2n + 3` the extractability side
  needs (density/sampling hypotheses and the `36·(d+k+4)·q`
  constant); `_of_count` = the same conversion with the count bounds
  as explicit hypotheses.

  The `example` block below additionally re-states the
  divisor-multiplicity theorem's exact shape, guarding the
  `splitsOnE` gating of its accounting and group-sum-zero clauses.
-/
import Divisor.SafeSupport
import Divisor.Hasse

/--
info: 'Divisor.ma_extractable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable
/--
info: 'Divisor.ip_extractable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable
/--
info: 'Divisor.ma_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_base
/--
info: 'Divisor.ip_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_base
/--
info: 'Divisor.ma_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness
/--
info: 'Divisor.ma_completeness_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_base
/--
info: 'Divisor.ma_completeness_q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_q
/--
info: 'Divisor.ip_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_completeness
/--
info: 'Divisor.ip_completeness_q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_completeness_q
/--
info: 'Divisor.ma_completeness_for_length4Simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_for_length4Simple
/--
info: 'Divisor.ma_completeness_clean_for_length4Simple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_clean_for_length4Simple
/--
info: 'Divisor.CoordRingElt.exists_divisor_multiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity
/--
info: 'Divisor.CoordRingElt.exists_divisor_multiplicity_ecpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity_ecpoint
/--
info: 'Divisor.ordAt_group_sum_zero_under_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ordAt_group_sum_zero_under_split
/--
info: 'Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois

/-! ## Statement-shape guard -/

-- The divisor-multiplicity existence theorem has the expected shape:
-- accounting and group-sum-zero are gated on the *stronger*
-- `splitsOnE` predicate (polynomial splitting + fiber-rationality of
-- every root), not just univariate `normPoly_splits_over_Fq`.
example {E : Divisor.ECSetup} (D : Divisor.CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (Divisor.splitsOnE E D →
        (∑ P ∈ E.points, β P) = (Divisor.normPoly E D).natDegree) ∧
      (Divisor.splitsOnE E D →
        Divisor.ECPoint.weightedSum E E.points
          (fun P => Divisor.ECPoint.nsmul E (β P)
                      (Divisor.ECPoint.affine E P.1 P.2)) = 0) :=
  Divisor.CoordRingElt.exists_divisor_multiplicity E D hD

-- The paper implication: large acceptance ⇒ extraction, not a
-- vacuous disjunction.
/--
info: 'Divisor.ma_extractable_paper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_paper

/-! ## Binary completeness chain

  The binary chain (`ma_completeness_binary_extras` and its `_clean`
  variant, gated on the per-input `h_extras` certificate rather than
  the universal `PairwiseCombineHyp`) has the same closure as
  `ma_completeness*`: the LandmarkInvStrong infrastructure introduces
  no axioms. -/
/--
info: 'Divisor.ma_completeness_binary_extras' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_extras
/--
info: 'Divisor.ma_completeness_binary_extras_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_extras_clean

/-! Unconditional binary corollaries (no `h_extras`):
  `ma_completeness_binary_length2` (`Ps = [P, -P]`) and
  `ma_completeness_binary_length4` (two inverse pairs). -/
/--
info: 'Divisor.ma_completeness_binary_length2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length2
/--
info: 'Divisor.ma_completeness_binary_length2_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length2_clean
/--
info: 'Divisor.ma_completeness_binary_length4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4
/--
info: 'Divisor.ma_completeness_binary_length4_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_clean
/--
info: 'Divisor.ma_completeness_binary_length4_chord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_chord
/--
info: 'Divisor.ma_completeness_binary_length4_chord_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_chord_clean
/--
info: 'Divisor.ma_completeness_binary_length6_chord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length6_chord
/--
info: 'Divisor.ma_completeness_binary_length8_chord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length8_chord
/--
info: 'Divisor.ma_completeness_binary_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain
/--
info: 'Divisor.ma_completeness_binary_chain_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_clean
/--
info: 'Divisor.ma_completeness_binary_admSetMax_extras' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetMax_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetMax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetMax
/--
info: 'Divisor.ma_completeness_binary_admSetParker_extras' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetParker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetParker
/--
info: 'Divisor.ma_completeness_binary_admSetEagen_extras' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetEagen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetEagen
/--
info: 'Divisor.ma_completeness_binary_admSetHash_extras' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetHash

/-! Top-level all-in-one user-facing binary theorems -/
/--
info: 'Divisor.ma_completeness_binary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary
/--
info: 'Divisor.ma_completeness_binary_admSetParker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker
/--
info: 'Divisor.ma_completeness_binary_admSetEagen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen
/--
info: 'Divisor.ma_completeness_binary_admSetHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash

/-! Certifying-wrapper bridges for the combine certificates -/
/--
info: 'Divisor.Landmark.landmarkInvStrongCombineAffineExtras_of_combineCanFire_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.Landmark.landmarkInvStrongCombineAffineExtras_of_combineCanFire_full
/--
info: 'Divisor.Landmark.landmarkInvStrongCombineExtras_of_combineCanFire_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.Landmark.landmarkInvStrongCombineExtras_of_combineCanFire_full

/-! Point-skeleton certificate — Decidable, native_decide-able -/
/--
info: 'Divisor.ma_completeness_binary_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetParker_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetEagen_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetHash_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash_point_certificate

/-! Any-length binary completeness (`Divisor/SafeSupport.lean`):
  the chain certificate discharged for ANY support length from the
  semantic general-position hypothesis `SafePairs` (decidable per
  instance via `SafePairsCert`). Axiom-free, like the rest of the
  completeness side. `pointCombine_eq_add` is the enabling bridge:
  the computable point skeleton is mathlib's group law. -/
/--
info: 'Divisor.ma_completeness_binary_any_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_any_length
/--
info: 'Divisor.ma_completeness_binary_any_length_cert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_any_length_cert
/--
info: 'Divisor.Landmark.pointCombine_eq_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.Landmark.pointCombine_eq_add
/--
info: 'Divisor.Landmark.iteratedPointChordCase_of_safePairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.Landmark.iteratedPointChordCase_of_safePairs

/-! ## Terminal Hasse layer (`Divisor/Hasse.lean`)

The only theorems that consume the Hasse axiom — everything else in
the library is axiom-free by import structure (`Divisor/Hasse.lean`
is the sole importer of `Divisor.Axioms.AxiomHasseWeil`). These
closures pin the entire axiom surface of the project:
`hasse_weil_textbook` and nothing else beyond the Lean built-ins. -/

/--
info: 'Divisor.hasse_points_bound' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.hasse_points_bound
/--
info: 'Divisor.hasse_points_bound_lb' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.hasse_points_bound_lb
/--
info: 'Divisor.ma_extractable_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_hasse
/--
info: 'Divisor.ip_extractable_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_hasse
/--
info: 'Divisor.ma_extractable_base_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_base_hasse
/--
info: 'Divisor.ip_extractable_base_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_base_hasse
/--
info: 'Divisor.ma_soundness_probability_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_probability_hasse
/--
info: 'Divisor.ma_extractable_witness_of_excess_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_witness_of_excess_hasse
/--
info: 'Divisor.ip_extractable_witness_of_excess_hasse' depends on axioms: [propext,
 Classical.choice,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_witness_of_excess_hasse

/-! ## Axiom-free soundness-probability chain (point-count currency) -/

/--
info: 'Divisor.ma_soundness_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_probability
/--
info: 'Divisor.ma_extractable_witness_of_excess_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_witness_of_excess_ratio
/--
info: 'Divisor.ma_extractable_witness_of_excess_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_witness_of_excess_clean

/-! ## `_of_count` flavors in the leaf: axiom-free field-size forms

These live in `Divisor/Hasse.lean` but take the two linear
point-count bounds (`2n ≤ 3q + 3`, `q ≤ 2n + 3`) as explicit
hypotheses instead of invoking the axiom — checkable arithmetic for
any concrete curve, so their closures stay at the Lean core three. -/

/--
info: 'Divisor.ma_extractable_of_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_of_count
/--
info: 'Divisor.ip_extractable_of_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_of_count
/--
info: 'Divisor.ma_soundness_probability_of_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_soundness_probability_of_count
/--
info: 'Divisor.validPairs_card_ge_q_of_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.validPairs_card_ge_q_of_count
