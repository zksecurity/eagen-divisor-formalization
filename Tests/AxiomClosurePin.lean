/-
  Tests/AxiomClosurePin.lean

  Pin the axiom closure of the headline soundness theorems. Every
  `#print axioms` below is wrapped in `#guard_msgs`, so the build
  FAILS if any closure drifts from the expected list — a reviewer no
  longer needs to read the build log to catch a new axiom, a revived
  `sorryAx`, or `Lean.ofReduceBool` sneaking into a closure.

  Expected closures on the geometric-zero skeleton branch:

  * `ma_extractable`, `ip_extractable`:
      propext, Classical.choice, Quot.sound,
      Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
      Divisor.hasse_weil_textbook,
      Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero

    The Frobenius descent proof gap is closed: there is no `sorryAx` in
    the MA/IP closure. The headline theorem signatures no longer carry
    `hSplit : splitsOnE E D`; the `splitsOnE` predicate now only gates
    the multiplicity-accounting test below. The Hasse bound now enters
    the closure as `hasse_weil_textbook` (Silverman V.1.1 verbatim);
    the legacy integer-squared `Divisor.hasse_weil` is a derived theorem
    retained for downstream compatibility. The remaining algebraic
    assumptions are narrow:
    * divisor-of-norm divisibility (lower bound) for the concrete
      resultant: `chord_fiber_product_concrete_bar_zfiber_pow_dvd`
      (Stacks 02RS lower-bound coefficient form). This *replaces* the
      previous multiplicity-equality axiom: the matching upper bound
      (the global natDegree inequality) is now a theorem
      (`chord_fiber_product_concrete_natDegree_le_normPoly_natDegree`
      in `Divisor/ChordFiberWeightedDegree.lean`, via the
      weighted-Sylvester analysis). The squeeze argument promotes
      lower-bound-divisibility plus upper-bound-natDegree to
      multiplicity equality.
    * principal divisor class triviality for the concrete `D`.

    The previously listed axiom
    `Divisor.ordAt_eq_rationalMultAt_of_gd_support_rational` has been
    eliminated: the rational-vs-geometric local-order bridge is now a
    proved theorem (induction on `divLin`'s natDegree-sum measure,
    combined with the closed-form `geomLocalOrder` formula on rational
    lifts). `GeometricDivisorData.mult` is now certified to coincide
    pointwise with `geomLocalOrder`, so `rationalMultAt` reduces to
    `geomLocalOrder` at the lifted rational point.

    The generic dual-number resultant product formula at a split
    specialization is now proved locally in
    `AxiomResultantLogDerivAtSplit.lean`; it is no longer in the
    closure. The related Galois norm/trace theorem
    `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
    is also printed below to guard against drift.

  * `ma_completeness_base`:
      propext, Classical.choice, Quot.sound,
      Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd

  * `ma_completeness`:
      propext, Classical.choice, Quot.sound,
      Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
      Divisor.hasse_weil_textbook

  The unsound `Divisor.weil_reciprocity_honest` axiom (which falsely
  claimed Eagen's eq. (1) on the diagonal `A_0 = A_1` where `slopeOf`
  totalises to `0/0`) is no longer reachable from `ma_completeness*`.

  `Divisor.principal_divisor_iff` (Silverman III.3.5) was a transitional
  intermediary in `ma_completeness*`'s closure and has now been removed.
  The bridge previously round-tripped through it (build IsPrincipal via
  .mpr from sum-zero + group-sum-zero, then immediately destruct via .mp
  to recover sum-zero); replacing the IsPrincipal conjunct of
  `MAProverMsg.isHonestFor` with `splitsOnE E msg.toD` lets the consumer
  derive degree-zero directly via `sum_ordAt_eq_natDegree_under_split`
  plus the divisor identity at infinity.

  The bridge: strengthened `MAProverMsg.isHonestFor` requires the
  extensional divisor identity `divisorOfD msg.toD R = honestDivisorCoeffs R`
  at every `R : ECPoint E` and `splitsOnE E msg.toD`; the residue-side
  Weil identity is then a theorem of the chord-resultant infrastructure.

  * `ma_completeness_for_length4Simple` and
    `ma_completeness_clean_for_length4Simple`:
      same closure as `ma_completeness_base` (and `ma_completeness`) respectively.

  These compose `Divisor.isHonestFor_of_isHonestForLength4Simple` with
  `ma_completeness_base`. The length-4-simple bridge supplies the strengthened
  `isHonestFor` constructively (without the unsound axiom), validating
  end-to-end that the strengthening admits a concrete witness.

  * `CoordRingElt.exists_divisor_multiplicity`,
    `CoordRingElt.exists_divisor_multiplicity_ecpoint`,
    `ordAt_group_sum_zero_under_split`:
      propext, Classical.choice, Quot.sound,
      Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero

  In particular: `Divisor.CoordRingElt.divisor_group_sum_zero` (the
  previously unsound axiom) is no longer reachable from any headline
  theorem, and `CoordRingElt.exists_divisor_multiplicity` is now
  theorem-backed (no longer an axiom) with the strong-accounting and
  group-sum-zero clauses gated on `splitsOnE`.
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Soundness
import Divisor.IsHonestForBinary

/--
info: 'Divisor.ma_extractable' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable
/--
info: 'Divisor.ip_extractable' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable
/--
info: 'Divisor.ma_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_base
/--
info: 'Divisor.ip_extractable_base' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ip_extractable_base
/--
info: 'Divisor.ma_completeness' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness
/--
info: 'Divisor.ma_completeness_base' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_base
/--
info: 'Divisor.ma_completeness_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_clean
/--
info: 'Divisor.ma_completeness_for_length4Simple' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_for_length4Simple
/--
info: 'Divisor.ma_completeness_clean_for_length4Simple' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_clean_for_length4Simple
/--
info: 'Divisor.CoordRingElt.exists_divisor_multiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity
/--
info: 'Divisor.CoordRingElt.exists_divisor_multiplicity_ecpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.CoordRingElt.exists_divisor_multiplicity_ecpoint
/--
info: 'Divisor.ordAt_group_sum_zero_under_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
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

/-! ## Hard guards: typecheck-fail if these axioms ever come back

    Constructing an `Empty` from the false axiom would let us prove
    `False`. We deliberately do NOT have such a construction; the test
    below would compile only if an inconsistency were introduced. -/

-- Sanity: the new sound axiom exists and has the expected shape.
-- Accounting and group-sum-zero are gated on the *stronger* `splitsOnE`
-- predicate (polynomial splitting + fiber-rationality of every root),
-- not just univariate `normPoly_splits_over_Fq`.
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

-- The paper implication is now a genuine large-acceptance ⇒ extraction
-- theorem, not a vacuous disjunction that can always choose the
-- accept-set-containment branch.
/--
info: 'Divisor.ma_extractable_paper' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound,
 Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_extractable_paper

/-! ## Binary completeness — unconditional via LandmarkInvStrong path

  The new unconditional binary chain
  (`ma_completeness_binary_extras` and its `_clean` variant)
  has the EXACT same axiom closure as `ma_completeness*` — confirming no
  new axioms are introduced by the LandmarkInvStrong infrastructure.

  Hypotheses replaced:
  - Old: gated on `Landmark.PairwiseCombineHyp E` (universal: ∀ xs ys a b...).
  - New: gated on `h_extras` (per-input: holds at each level of the iterate).
-/
/--
info: 'Divisor.ma_completeness_binary_extras' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_extras
/--
info: 'Divisor.ma_completeness_binary_extras_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_extras_clean

/-! Fully-unconditional binary completeness corollaries (no `h_extras`):
  - `ma_completeness_binary_length2` — `Ps = [P, -P]`.
  - `ma_completeness_binary_length4` — two inverse pairs. -/
/--
info: 'Divisor.ma_completeness_binary_length2' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length2
/--
info: 'Divisor.ma_completeness_binary_length2_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length2_clean
/--
info: 'Divisor.ma_completeness_binary_length4' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4
/--
info: 'Divisor.ma_completeness_binary_length4_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_clean
/--
info: 'Divisor.ma_completeness_binary_length4_chord' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_chord
/--
info: 'Divisor.ma_completeness_binary_length4_chord_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length4_chord_clean
/--
info: 'Divisor.ma_completeness_binary_length6_chord' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length6_chord
/--
info: 'Divisor.ma_completeness_binary_length8_chord' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_length8_chord
/--
info: 'Divisor.ma_completeness_binary_chain' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain
/--
info: 'Divisor.ma_completeness_binary_chain_clean' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Divisor.hasse_weil_textbook,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_clean
/--
info: 'Divisor.ma_completeness_binary_admSetMax_extras' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetMax_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetMax' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetMax
/--
info: 'Divisor.ma_completeness_binary_admSetParker_extras' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetParker' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetParker
/--
info: 'Divisor.ma_completeness_binary_admSetEagen_extras' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetEagen' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetEagen
/--
info: 'Divisor.ma_completeness_binary_admSetHash_extras' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash_extras
/--
info: 'Divisor.ma_completeness_binary_chain_admSetHash' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_chain_admSetHash

/-! Top-level all-in-one user-facing theorems (commit a0fd520) -/
/--
info: 'Divisor.ma_completeness_binary' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary
/--
info: 'Divisor.ma_completeness_binary_admSetParker' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker
/--
info: 'Divisor.ma_completeness_binary_admSetEagen' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen
/--
info: 'Divisor.ma_completeness_binary_admSetHash' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash

/-! Certifying-wrapper bridges (commits fd7da92, 618a2b2, c33c200) -/
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

/-! Point-skeleton certificate (commit 600c442) — Decidable, native_decide-able -/
/--
info: 'Divisor.ma_completeness_binary_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetParker_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetParker_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetEagen_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetEagen_point_certificate
/--
info: 'Divisor.ma_completeness_binary_admSetHash_point_certificate' depends on axioms: [propext,
 Classical.choice,
 Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Divisor.ma_completeness_binary_admSetHash_point_certificate
