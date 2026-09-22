/-
  Tests/Length2CompletenessSmoke.lean

  Inhabited length-two binary MA completeness.

  This is the non-vacuity regression for the corrected `CoordRingElt.degE`.
  The honesty record's divisor identity at infinity forces
  `Ps.length = msg.toD.degE`; under the old degree definition every
  coordinate-ring element had `3 ≤ degE`, so the length-two premises were
  contradictory and `ma_completeness_binary_length2` — while a valid Lean
  implication — could never be instantiated.

  Here every premise is constructed rather than assumed, on a concrete
  curve, for the vertical line `D = x − 1`:

      div(D) = (P) + (−P) − 2·(O),   P = (1, 6) on y² = x³ + 1 over F₁₇.

  The public degree bound is `2`, the smallest `ma_soundness` admits
  (`hd2 : 2 ≤ stmt.degBound`); the old definition rejected *every*
  message at that bound.

  The same message also inhabits every judged MA completeness headline:
  `ma_completeness` and `ma_completeness_q` through the protocol predicate
  `isHonestFor`, and both any-length forms (`SafePairs` and its
  certificate).
-/
import Divisor.Headlines
import Divisor.IsHonestForBinary
import Tests.CurveFixtures

open Polynomial Finset

namespace Tests.Length2CompletenessSmoke

open Divisor

private abbrev E17 : ECSetup := Tests.CurveFixtures.E17

/-- One base, equal to the target, with scalar `1`: `P = [1]·P`. -/
private def stmt : DlogStatement E17.q where
  k := 1
  degBound := 2
  bases := fun _ => (1, 6)
  target := (1, 6)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 1
  degBound := 2
  hRange := by intro i; norm_num

private theorem hk : stmt.k = wit.k := rfl

private theorem h_binary :
    ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1 := by
  intro i
  right
  rfl

/-- `(−P) :: [P]`, with `−6 = 11` in `ZMod 17`. The two points share an
    `x`-coordinate and have opposite `y`, so the build is the vertical
    line through them. -/
private def support : List (ZMod E17.q × ZMod E17.q) := [(1, 11), (1, 6)]

/-- On-curve witnesses, via `hComplete` rather than by deciding
    membership in the filtered point set (which exceeds the kernel's
    recursion budget). -/
private theorem mem_1_6 : ((1 : ZMod E17.q), (6 : ZMod E17.q)) ∈ E17.points :=
  E17.hComplete 1 6 (by decide)

private theorem mem_1_11 : ((1 : ZMod E17.q), (11 : ZMod E17.q)) ∈ E17.points :=
  E17.hComplete 1 11 (by decide)

private theorem binarySupport_eq_support :
    binarySupport stmt wit hk h_binary = support := by
  decide

private theorem h_valid : relDlog E17 stmt wit := by
  refine ⟨hk, ?_⟩
  simp only [ECPoint.weightedSum]
  rw [show (Finset.univ : Finset (Fin wit.k))
        = {(⟨0, by decide⟩ : Fin wit.k)} from by decide,
    Finset.sum_singleton]
  simp [stmt, wit, ECPoint.zsmul, Fin.cast]

private theorem h_ps_on : ∀ P ∈ binarySupport stmt wit hk h_binary, P ∈ E17.points := by
  rw [binarySupport_eq_support]
  intro P hP
  fin_cases hP
  · exact mem_1_11
  · exact mem_1_6

private theorem h_nodup : (binarySupport stmt wit hk h_binary).Nodup := by
  rw [binarySupport_eq_support]
  decide

private theorem h_sum_zero : LineAccum.sumOnE E17 (binarySupport stmt wit hk h_binary) = 0 :=
  binarySupport_sumOnE_eq_zero stmt wit hk h_binary h_valid h_ps_on

private noncomputable def msg : MAProverMsg E17.q stmt.k where
  m := fun _ => 1
  polyA := (LineAccum.lineBuild_singletons E17
    (binarySupport stmt wit hk h_binary)).a
  polyB := (LineAccum.lineBuild_singletons E17
    (binarySupport stmt wit hk h_binary)).b

private theorem h_toD_eq :
    msg.toD = LineAccum.lineBuild_singletons E17
      (binarySupport stmt wit hk h_binary) := rfl

/-- The vertical pair certificate, supplying the chord-case extras for
    the two-element build. -/
private theorem h_extras :
    ∀ k < (binarySupport stmt wit hk h_binary).length,
      LineAccum.LevelStepCombineExtras E17
        (LineAccum.iterate E17 k
          (LineAccum.level0_singletons E17 (binarySupport stmt wit hk h_binary))) := by
  rw [binarySupport_eq_support]
  exact LineAccum.h_extras_holds_for_length2_sum_zero E17 (1, 11) (1, 6)
    mem_1_11 mem_1_6 rfl (by decide)

/-- **The point of the whole repair.** The vertical line has pole order
    two at infinity, matching the support length. The old definition gave
    it three, which is what made the length-two premises contradictory. -/
private theorem h_degE_eq :
    msg.toD.degE = (binarySupport stmt wit hk h_binary).length := by
  rw [h_toD_eq]
  exact LineAccum.degE_lineBuild_singletons_eq_length E17
    (binarySupport stmt wit hk h_binary) h_ps_on h_sum_zero h_nodup
    (by rw [binarySupport_eq_support]; decide) h_extras

private theorem h_support_len : (binarySupport stmt wit hk h_binary).length = 2 := by
  rw [binarySupport_eq_support]
  decide

private theorem h_scalars_match :
    ∀ i : Fin stmt.k, msg.m i = ((wit.scalars (hk ▸ i) : ZMod E17.q)) := by
  intro i
  fin_cases i
  · rfl

private theorem h_target_on : (stmt.target.1, -stmt.target.2) ∈ E17.points :=
  E17.hComplete _ _ (by decide)

private theorem h_bases_on : ∀ i, stmt.bases i ∈ E17.points := by
  intro _
  exact mem_1_6

/-- A fully constructed binary-honesty record at support length two.
    Every field is proved; nothing is assumed. -/
private noncomputable def honest :
    MAProverMsg.IsHonestForBinary E17 stmt msg wit hk :=
  MAProverMsg.IsHonestForBinary.fromWitness E17 stmt wit hk msg h_binary h_valid
    h_toD_eq h_degE_eq h_scalars_match h_target_on h_bases_on h_nodup

private theorem h_length2 :
    ∃ P Q : ZMod E17.q × ZMod E17.q,
      honest.Ps = [P, Q] ∧ P.1 = Q.1 ∧ Q.2 = -P.2 :=
  ⟨(1, 11), (1, 6), binarySupport_eq_support, rfl, by decide⟩

private theorem h_deg : msg.toD.degE ≤ wit.degBound := by
  rw [h_degE_eq, h_support_len]
  norm_num [wit]

private theorem h_deg_k : msg.toD.degE ≤ stmt.degBound := by
  rw [h_degE_eq, h_support_len]
  norm_num [stmt]

/-- Admissibility: the build is nonzero, so `(polyA, polyB) ≠ (0, 0)`.
    The nonzero check stays enforced — with the exact degree, `degE 0`
    is `0`, so it is no longer implied by the degree accounting. -/
private theorem h_adm : stmt.admSet (msg.polyA, msg.polyB) := by
  have h := LineAccum.lineBuild_singletons_spec_unconditional E17
    (binarySupport stmt wit hk h_binary) h_ps_on h_sum_zero h_nodup
    (by rw [binarySupport_eq_support]; decide) h_extras
  show (msg.polyA, msg.polyB) ≠ (0, 0)
  intro heq
  rw [Prod.mk.injEq] at heq
  exact h.1 heq

/-- The verifier's degree check passes at public bound two. -/
theorem verifier_degree_check_holds : verifierDegreeCheck msg stmt.degBound :=
  h_deg_k

/-- `ma_completeness_binary_length2`, instantiated. -/
theorem length2_completeness :
    (maRejectSet E17 stmt msg).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine :=
  ma_completeness_binary_length2 E17 stmt msg wit hk honest h_length2 h_valid
    h_deg h_deg_k h_adm

/-- `ma_completeness_binary_length2_admSetMax`, instantiated. -/
theorem length2_completeness_admSetMax :
    (maRejectSet E17 stmt msg).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine :=
  ma_completeness_binary_length2_admSetMax E17 stmt msg wit hk rfl honest
    h_length2 h_valid h_deg h_deg_k

/-- The judged any-length headline, instantiated at length two. -/
theorem any_length_completeness_at_length_two :
    (maRejectSet E17 stmt msg).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine :=
  ma_completeness_binary_any_length_cert E17 stmt wit hk msg h_binary h_valid
    h_toD_eq h_degE_eq h_scalars_match h_target_on h_bases_on h_nodup
    (by rw [binarySupport_eq_support]; decide) rfl h_deg h_deg_k

/-! ## Protocol-level honesty

The binary record implies the protocol predicate `isHonestFor`, so the
general completeness headlines are inhabited by the same message. -/

private theorem h_honest : msg.isHonestFor E17 stmt wit hk :=
  isHonestFor_of_isHonestForBinary honest
    (by rw [show honest.Ps = binarySupport stmt wit hk h_binary from rfl,
      h_support_len]) h_extras

private theorem h_D : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
  admSet_implies_toD_nonzero stmt msg h_adm

/-- The judged `ma_completeness`, instantiated. -/
theorem completeness :
    (maRejectSet E17 stmt msg).card ≤ (3 * stmt.degBound + 4) * E17.points.card :=
  ma_completeness E17 stmt wit hk h_valid msg h_deg h_deg_k h_adm h_honest h_D

/-- The judged `ma_completeness_q`, instantiated. -/
theorem completeness_q :
    (maRejectSet E17 stmt msg).card ≤ (6 * (stmt.degBound + 1) + 6) * E17.q :=
  ma_completeness_q E17 stmt wit hk h_valid msg h_deg h_deg_k h_adm h_honest h_D

/-- The judged `ma_completeness_binary_any_length`, instantiated through
    the semantic general-position hypothesis `SafePairs`. -/
theorem any_length_completeness_safePairs :
    (maRejectSet E17 stmt msg).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine :=
  ma_completeness_binary_any_length E17 stmt wit hk msg h_binary h_valid
    h_toD_eq h_degE_eq h_scalars_match h_target_on h_bases_on h_nodup
    (LineAccum.SafePairs.of_cert E17 h_ps_on
      (by rw [binarySupport_eq_support]; decide)) rfl h_deg h_deg_k

/-! ## Axiom closure

The instantiations stay at the Lean core three, so the non-vacuity
evidence carries no extra assumption. -/

/--
info: 'Tests.Length2CompletenessSmoke.length2_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length2_completeness
/--
info: 'Tests.Length2CompletenessSmoke.length2_completeness_admSetMax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length2_completeness_admSetMax
/--
info: 'Tests.Length2CompletenessSmoke.any_length_completeness_at_length_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms any_length_completeness_at_length_two
/--
info: 'Tests.Length2CompletenessSmoke.completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms completeness
/--
info: 'Tests.Length2CompletenessSmoke.completeness_q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms completeness_q
/--
info: 'Tests.Length2CompletenessSmoke.any_length_completeness_safePairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms any_length_completeness_safePairs

end Tests.Length2CompletenessSmoke
