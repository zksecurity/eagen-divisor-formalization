/-
  Divisor/IsHonestForBinary.lean

  Bridge from the binary Eagen-singletons construction to the protocol
  honesty predicate.
-/
import Divisor.EagenBuildLandmark
import Divisor.Protocol
import Divisor.Soundness

namespace Divisor

open Classical

namespace Landmark

/-- The per-pair preservation hypothesis needed by the conditional
    `eagenBuild_singletons` landmark theorem. -/
abbrev PairwiseCombineHyp (E : ECSetup) : Prop :=
  forall (xs ys : List (ZMod E.q × ZMod E.q))
      (a b : EagenAccum E),
    LandmarkInv E xs a -> LandmarkInv E ys b ->
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)

end Landmark

/-- Binary honest construction data for an MA prover message.

The field `Ps` is the binary support list: `(-target)` together with the
bases selected by scalar `1`.  The field `h_formal_eq_honest` is the
binary-specific encoding obligation: it identifies the formal divisor of
that list with the protocol-level `honestDivisorCoeffs`. -/
structure MAProverMsg.IsHonestForBinary (E : ECSetup)
    (msg : MAProverMsg E.q) (stmt : DlogStatement E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k) where
  /-- Binary scalars in the witness. -/
  h_binary : forall i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1
  /-- The binary support list used by `eagenBuild_singletons`. -/
  Ps : List (ZMod E.q × ZMod E.q)
  /-- The committed coordinate-ring element is the singleton Eagen build. -/
  h_toD_eq : msg.toD = Landmark.eagenBuild_singletons E Ps
  /-- Every support point is rational on `E`. -/
  hPs_on : forall P, P ∈ Ps -> P ∈ E.points
  /-- The support list sums to zero in the elliptic-curve group. -/
  hSumZero : Landmark.sumOnE E Ps = 0
  /-- The support list is non-empty. -/
  hNonEmpty : Ps ≠ []
  /-- The support list has no duplicate points. -/
  hNodup : Ps.Nodup
  /-- The message scalars reduce the integer witness scalars modulo `E.q`. -/
  h_scalars_match :
    forall i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q))
  /-- Binary divisor encoding obligation. -/
  h_formal_eq_honest :
    forall R : ECPoint E,
      Landmark.formalDivisorOfList E Ps R =
        honestDivisorCoeffs E stmt wit hk msg R
  /-- The negated target point is on `E`. -/
  h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points
  /-- Every statement base is on `E`. -/
  h_bases_on_curve : forall i : Fin stmt.k, stmt.bases i ∈ E.points

/-- The landmark facts for the singleton Eagen build attached to a binary
    honesty witness. -/
private theorem eagenBuild_singletons_landmark_of_isHonestForBinary
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    let D := Landmark.eagenBuild_singletons E h_binary.Ps
    ¬ (D.a = 0 ∧ D.b = 0) ∧
    (∀ P ∈ h_binary.Ps, D.eval P.1 P.2 = 0) ∧
    (normPoly E D).natDegree = h_binary.Ps.length := by
  exact Landmark.eagenBuild_singletons_landmark E h_binary.Ps
    h_binary.hPs_on h_binary.hSumZero h_binary.hNonEmpty h_combine

/-- The binary singleton build splits over `E`. -/
theorem splitsOnE_msg_toD_for_binary
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    splitsOnE E msg.toD := by
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  have h_landmark :
      ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ P ∈ h_binary.Ps, D.eval P.1 P.2 = 0) ∧
      (normPoly E D).natDegree = h_binary.Ps.length := by
    simpa [D] using
      eagenBuild_singletons_landmark_of_isHonestForBinary h_binary h_combine
  exact Landmark.splitsOnE_of_landmark E h_binary.Ps D
    h_binary.hPs_on h_binary.hNodup
    h_landmark.1 h_landmark.2.1 h_landmark.2.2

/-- The divisor of the binary singleton build is the protocol honest
    divisor. -/
theorem divisor_identity_for_binary
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    forall R : ECPoint E,
      divisorOfD E msg.toD R =
        honestDivisorCoeffs E stmt wit hk msg R := by
  intro R
  rw [h_binary.h_toD_eq]
  calc
    divisorOfD E (Landmark.eagenBuild_singletons E h_binary.Ps) R
        = Landmark.formalDivisorOfList E h_binary.Ps R := by
          exact Landmark.eagenBuild_singletons_divisor_identity E h_binary.Ps
            h_binary.hPs_on h_binary.hSumZero h_binary.hNonEmpty
            h_binary.hNodup h_combine R
    _ = honestDivisorCoeffs E stmt wit hk msg R :=
          h_binary.h_formal_eq_honest R

/-- Bridge from binary construction data to the protocol-level honest
    prover predicate. -/
theorem isHonestFor_of_isHonestForBinary
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    msg.isHonestFor E stmt wit hk hkm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_binary.h_scalars_match
  · exact splitsOnE_msg_toD_for_binary h_binary h_combine
  · exact divisor_identity_for_binary h_binary h_combine
  · exact h_binary.h_target_on_curve
  · exact h_binary.h_bases_on_curve

theorem ma_completeness_for_binary
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness E stmt wit hk hValid msg hkm hDeg hDegK hAdm
    (isHonestFor_of_isHonestForBinary (E := E) h_binary h_combine)

theorem ma_completeness_clean_for_binary
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  exact ma_completeness_clean E stmt wit hk hValid msg hkm hDeg hDegK hAdm
    (isHonestFor_of_isHonestForBinary (E := E) h_binary h_combine)
    hD hQ

/-- M=3 binary completeness via the constructive length-4 simple bridge.

This is the all-selected binary case: `stmt.k = msg.k = 3` is carried by
`h_simple`, and every witness scalar is `1`.  Unlike
`ma_completeness_for_binary`, this corollary does not need
`PairwiseCombineHyp`; it composes through the existing
`ma_completeness_for_length4Simple` proof, whose divisor witness is
`eagenBuild_length4_explicit`. -/
theorem ma_completeness_for_binary_M_eq_3
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have hkm_eq :
      hkm = h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm :=
    Subsingleton.elim _ _
  rw [hkm_eq]
  exact ma_completeness_for_length4Simple E stmt msg h_simple wit hk
    h_scalars hValid hDeg hDegK hAdm

/-! ## Unconditional binary completeness — discharges `PairwiseCombineHyp`.

The new conditional hypothesis `h_extras` is a per-input geometric side
condition (no chord/tangent collinearities at any iterate level), strictly
weaker than the universal `PairwiseCombineHyp E`. -/

theorem splitsOnE_msg_toD_for_binary_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    splitsOnE E msg.toD := by
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  have h_landmark :
      ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ P ∈ h_binary.Ps, D.eval P.1 P.2 = 0) ∧
      (normPoly E D).natDegree = h_binary.Ps.length := by
    simpa [D] using
      Landmark.eagenBuild_singletons_landmark_unconditional E h_binary.Ps
        h_binary.hPs_on h_binary.hSumZero h_binary.hNodup hLen h_extras
  exact Landmark.splitsOnE_of_landmark E h_binary.Ps D
    h_binary.hPs_on h_binary.hNodup
    h_landmark.1 h_landmark.2.1 h_landmark.2.2

theorem divisor_identity_for_binary_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    forall R : ECPoint E,
      divisorOfD E msg.toD R =
        honestDivisorCoeffs E stmt wit hk msg R := by
  intro R
  rw [h_binary.h_toD_eq]
  calc
    divisorOfD E (Landmark.eagenBuild_singletons E h_binary.Ps) R
        = Landmark.formalDivisorOfList E h_binary.Ps R := by
          exact Landmark.eagenBuild_singletons_divisor_identity_unconditional E
            h_binary.Ps h_binary.hPs_on h_binary.hSumZero
            h_binary.hNodup hLen h_extras R
    _ = honestDivisorCoeffs E stmt wit hk msg R :=
          h_binary.h_formal_eq_honest R

theorem isHonestFor_of_isHonestForBinary_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    msg.isHonestFor E stmt wit hk hkm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_binary.h_scalars_match
  · exact splitsOnE_msg_toD_for_binary_unconditional h_binary hLen h_extras
  · exact divisor_identity_for_binary_unconditional h_binary hLen h_extras
  · exact h_binary.h_target_on_curve
  · exact h_binary.h_bases_on_curve

theorem ma_completeness_for_binary_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness E stmt wit hk hValid msg hkm hDeg hDegK hAdm
    (isHonestFor_of_isHonestForBinary_unconditional (E := E) h_binary hLen h_extras)

theorem ma_completeness_clean_for_binary_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  exact ma_completeness_clean E stmt wit hk hValid msg hkm hDeg hDegK hAdm
    (isHonestFor_of_isHonestForBinary_unconditional (E := E) h_binary hLen h_extras)
    hD hQ

/-! ## Length-2 fully-unconditional binary completeness.

For `Ps = [P, Q]` with `P + Q = 0` on `E`, both branches of the
`LandmarkInvStrongCombineAffineExtras` predicate have failing
hypotheses, so `h_extras` is discharged by
`Landmark.h_extras_holds_for_length2_sum_zero`.

The result is a fully unconditional binary completeness theorem for
length-2 inputs (no `h_extras`, no `PairwiseCombineHyp`). -/

theorem ma_completeness_for_binary_length2_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length2 : ∃ P Q : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P, Q] ∧ P.1 = Q.1 ∧ Q.2 = -P.2)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P, Q, hPs_eq, hxx, hyy⟩ := h_length2
  have hLen : 2 ≤ h_binary.Ps.length := by rw [hPs_eq]; simp
  have hP_on : P ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]; simp
  have hQ_on : Q ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]; simp
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length2_sum_zero E P Q hP_on hQ_on hxx hyy
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_clean_for_binary_length2_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length2 : ∃ P Q : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P, Q] ∧ P.1 = Q.1 ∧ Q.2 = -P.2)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  obtain ⟨P, R, hPs_eq, hxx, hyy⟩ := h_length2
  have hLen : 2 ≤ h_binary.Ps.length := by rw [hPs_eq]; simp
  have hP_on : P ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]; simp
  have hR_on : R ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]; simp
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length2_sum_zero E P R hP_on hR_on hxx hyy
  exact ma_completeness_clean_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm hQ

namespace Landmark

theorem levelInitSingleton_chord_combine_extras
    (E : ECSetup) (P Q : ZMod E.q × ZMod E.q)
    (hP_on : P ∈ E.points) (hQ_on : Q ∈ E.points)
    (h_x_ne : P.1 ≠ Q.1)
    (hP_y_ne : P.2 ≠ 0) (hQ_y_ne : Q.2 ≠ 0)
    (hThird_ne_P :
      (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) ≠ P.1)
    (hThird_ne_Q :
      (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) ≠ Q.1) :
    LandmarkInvStrongCombineExtras E
      (levelInitSingleton E P) (levelInitSingleton E Q) := by
  classical
  intro _ _ xa ya xb yb h_a_pt h_b_pt
  have h_a_eq : (levelInitSingleton E P).point = ECPoint.affine E P.1 P.2 := rfl
  have h_b_eq : (levelInitSingleton E Q).point = ECPoint.affine E Q.1 Q.2 := rfl
  have hP_ns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP_on))
  have hQ_ns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ_on))
  rw [ECPoint.affine_of_nonsingular E hP_ns] at h_a_eq
  rw [ECPoint.affine_of_nonsingular E hQ_ns] at h_b_eq
  have h_a_eq2 : ECPoint.affine E xa ya = (.some hP_ns : ECPoint E) := by
    rw [← h_a_pt, h_a_eq]
  have h_b_eq2 : ECPoint.affine E xb yb = (.some hQ_ns : ECPoint E) := by
    rw [← h_b_pt, h_b_eq]
  have hxa_eq : xa = P.1 ∧ ya = P.2 := by
    unfold ECPoint.affine at h_a_eq2
    by_cases hns : E.toW.toAffine.Nonsingular xa ya
    · rw [dif_pos hns] at h_a_eq2
      exact WeierstrassCurve.Affine.Point.some.inj h_a_eq2
    · rw [dif_neg hns] at h_a_eq2
      exfalso
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP_ns) h_a_eq2.symm
  have hxb_eq : xb = Q.1 ∧ yb = Q.2 := by
    unfold ECPoint.affine at h_b_eq2
    by_cases hns : E.toW.toAffine.Nonsingular xb yb
    · rw [dif_pos hns] at h_b_eq2
      exact WeierstrassCurve.Affine.Point.some.inj h_b_eq2
    · rw [dif_neg hns] at h_b_eq2
      exfalso
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hQ_ns) h_b_eq2.symm
  obtain ⟨hxa, hya⟩ := hxa_eq
  obtain ⟨hxb, hyb⟩ := hxb_eq
  refine ⟨?_, ?_⟩
  · intro _h_xa_ne_xb
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hya] using hP_y_ne
    · simpa [hyb] using hQ_y_ne
    · simpa [hxa, hya, hxb, hyb] using hThird_ne_P
    · simpa [hxa, hya, hxb, hyb] using hThird_ne_Q
  · intro h_xa_eq_xb _ _
    rw [hxa, hxb] at h_xa_eq_xb
    exact False.elim (h_x_ne h_xa_eq_xb)

def chordSumX (E : ECSetup) (P Q : ZMod E.q × ZMod E.q) : ZMod E.q :=
  slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1

def chordThirdY (E : ECSetup) (P Q : ZMod E.q × ZMod E.q) : ZMod E.q :=
  slopeOf P.1 P.2 Q.1 Q.2 * chordSumX E P Q +
    (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1)

def chordSumY (E : ECSetup) (P Q : ZMod E.q × ZMod E.q) : ZMod E.q :=
  -chordThirdY E P Q

theorem chordSum_mem_points
    (E : ECSetup) (P Q : ZMod E.q × ZMod E.q)
    (hP_on : P ∈ E.points) (hQ_on : Q ∈ E.points)
    (h_x_ne : P.1 ≠ Q.1) :
    (chordSumX E P Q, chordSumY E P Q) ∈ E.points := by
  classical
  have hThird_on :
      (chordSumX E P Q, chordThirdY E P Q) ∈ E.points := by
    apply E.hComplete
    simpa [chordSumX, chordThirdY] using
      chord_third_point_on_E E P Q hP_on hQ_on h_x_ne
  simpa [chordSumY] using points_neg_y E hThird_on

theorem levelInitSingleton_chord_combine_point
    (E : ECSetup) (P Q : ZMod E.q × ZMod E.q)
    (hP_on : P ∈ E.points) (hQ_on : Q ∈ E.points)
    (h_x_ne : P.1 ≠ Q.1) :
    (EagenAccum.combine E (levelInitSingleton E P) (levelInitSingleton E Q)).point =
      ECPoint.affine E (chordSumX E P Q) (chordSumY E P Q) := by
  classical
  have hP_ns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP_on))
  have hQ_ns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ_on))
  have hP_acc :
      levelInitSingleton E P =
        { point := (.some hP_ns : ECPoint E),
          poly := { a := Polynomial.X - Polynomial.C P.1, b := 0 } } := by
    simp [levelInitSingleton, ECPoint.affine_of_nonsingular E hP_ns]
  have hQ_acc :
      levelInitSingleton E Q =
        { point := (.some hQ_ns : ECPoint E),
          poly := { a := Polynomial.X - Polynomial.C Q.1, b := 0 } } := by
    simp [levelInitSingleton, ECPoint.affine_of_nonsingular E hQ_ns]
  rw [hP_acc, hQ_acc]
  simp [EagenAccum.combine, EagenAccum.combine_distinct, h_x_ne,
    chordSumX, chordSumY, chordThirdY]

theorem combine_extras_of_affine_chord_conditions
    (E : ECSetup) (a b : EagenAccum E)
    (xa ya xb yb : ZMod E.q)
    (ha_on : (xa, ya) ∈ E.points) (hb_on : (xb, yb) ∈ E.points)
    (ha_pt : a.point = ECPoint.affine E xa ya)
    (hb_pt : b.point = ECPoint.affine E xb yb)
    (h_x_ne : xa ≠ xb)
    (hya_ne : ya ≠ 0) (hyb_ne : yb ≠ 0)
    (hThird_ne_a : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xa)
    (hThird_ne_b : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xb) :
    LandmarkInvStrongCombineExtras E a b := by
  classical
  intro _ _ xa' ya' xb' yb' h_a_pt h_b_pt
  have ha_ns : E.toW.toAffine.Nonsingular xa ya :=
    E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ ha_on))
  have hb_ns : E.toW.toAffine.Nonsingular xb yb :=
    E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hb_on))
  have h_a_eq2 : ECPoint.affine E xa' ya' = (.some ha_ns : ECPoint E) := by
    rw [← h_a_pt, ha_pt, ECPoint.affine_of_nonsingular E ha_ns]
  have h_b_eq2 : ECPoint.affine E xb' yb' = (.some hb_ns : ECPoint E) := by
    rw [← h_b_pt, hb_pt, ECPoint.affine_of_nonsingular E hb_ns]
  have hxa_eq : xa' = xa ∧ ya' = ya := by
    unfold ECPoint.affine at h_a_eq2
    by_cases hns : E.toW.toAffine.Nonsingular xa' ya'
    · rw [dif_pos hns] at h_a_eq2
      exact WeierstrassCurve.Affine.Point.some.inj h_a_eq2
    · rw [dif_neg hns] at h_a_eq2
      exfalso
      exact (WeierstrassCurve.Affine.Point.some_ne_zero ha_ns) h_a_eq2.symm
  have hxb_eq : xb' = xb ∧ yb' = yb := by
    unfold ECPoint.affine at h_b_eq2
    by_cases hns : E.toW.toAffine.Nonsingular xb' yb'
    · rw [dif_pos hns] at h_b_eq2
      exact WeierstrassCurve.Affine.Point.some.inj h_b_eq2
    · rw [dif_neg hns] at h_b_eq2
      exfalso
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hb_ns) h_b_eq2.symm
  obtain ⟨hxa, hya⟩ := hxa_eq
  obtain ⟨hxb, hyb⟩ := hxb_eq
  refine ⟨?_, ?_⟩
  · intro _h_xa_ne_xb
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hya] using hya_ne
    · simpa [hyb] using hyb_ne
    · simpa [hxa, hya, hxb, hyb] using hThird_ne_a
    · simpa [hxa, hya, hxb, hyb] using hThird_ne_b
  · intro h_xa_eq_xb _ _
    rw [hxa, hxb] at h_xa_eq_xb
    exact False.elim (h_x_ne h_xa_eq_xb)

def Length6Level1ChordConditions
    (E : ECSetup) (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q) : Prop :=
  chordSumX E P₀ P₁ ≠ chordSumX E P₂ P₃ ∧
  chordSumY E P₀ P₁ ≠ 0 ∧
  chordSumY E P₂ P₃ ≠ 0 ∧
  (slopeOf (chordSumX E P₀ P₁) (chordSumY E P₀ P₁)
      (chordSumX E P₂ P₃) (chordSumY E P₂ P₃) ^ 2 -
      chordSumX E P₀ P₁ - chordSumX E P₂ P₃) ≠ chordSumX E P₀ P₁ ∧
  (slopeOf (chordSumX E P₀ P₁) (chordSumY E P₀ P₁)
      (chordSumX E P₂ P₃) (chordSumY E P₂ P₃) ^ 2 -
      chordSumX E P₀ P₁ - chordSumX E P₂ P₃) ≠ chordSumX E P₂ P₃

theorem length6_chord_level1_extras
    (E : ECSetup) (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (h01_x_ne : P₀.1 ≠ P₁.1) (h23_x_ne : P₂.1 ≠ P₃.1)
    (hLevel1 : Length6Level1ChordConditions E P₀ P₁ P₂ P₃) :
    LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) := by
  classical
  rcases hLevel1 with
    ⟨h_x_ne, h01_y_ne, h23_y_ne, hThird_ne_01, hThird_ne_23⟩
  exact combine_extras_of_affine_chord_conditions E
    (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
    (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))
    (chordSumX E P₀ P₁) (chordSumY E P₀ P₁)
    (chordSumX E P₂ P₃) (chordSumY E P₂ P₃)
    (chordSum_mem_points E P₀ P₁ hP₀_on hP₁_on h01_x_ne)
    (chordSum_mem_points E P₂ P₃ hP₂_on hP₃_on h23_x_ne)
    (levelInitSingleton_chord_combine_point E P₀ P₁ hP₀_on hP₁_on h01_x_ne)
    (levelInitSingleton_chord_combine_point E P₂ P₃ hP₂_on hP₃_on h23_x_ne)
    h_x_ne h01_y_ne h23_y_ne hThird_ne_01 hThird_ne_23

theorem length4_chord_level1_extras
    (E : ECSetup) (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃] : List (ZMod E.q × ZMod E.q)).Nodup)
    (hPair01 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁))
    (hPair23 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃))
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃] = 0) :
    LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) := by
  classical
  let xss : List (List (ZMod E.q × ZMod E.q)) := [[P₀], [P₁], [P₂], [P₃]]
  let accs : List (EagenAccum E) :=
    [levelInitSingleton E P₀, levelInitSingleton E P₁,
     levelInitSingleton E P₂, levelInitSingleton E P₃]
  have hxss_on : ∀ xs ∈ xss, ∀ P ∈ xs, P ∈ E.points := by
    intro xs hxs P hP
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₀_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₁_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₂_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₃_on
  have hxss_ne : ∀ xs ∈ xss, xs ≠ [] := by
    intro xs hxs
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl <;> simp
  have hNodup_concat : xss.flatten.Nodup := by
    simpa [xss] using hNodup
  have h_init : LandmarkInvStrongList E xss accs := by
    subst xss
    subst accs
    simpa [level0_singletons] using
      landmarkInvStrongList_level0_singletons E [P₀, P₁, P₂, P₃]
        (by
          intro P hP
          simp at hP
          rcases hP with rfl | rfl | rfl | rfl
          · exact hP₀_on
          · exact hP₁_on
          · exact hP₂_on
          · exact hP₃_on)
  have h_level0_extras : LevelStepCombineExtras E accs := by
    subst accs
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧ True)
    exact ⟨hPair01, hPair23, trivial⟩
  have h_step :=
    (landmarkInvStrongList_level_step E xss accs h_init
      hxss_on hNodup_concat hxss_ne h_level0_extras).1
  have h_step' :
      LandmarkInvStrongList E [[P₀, P₁], [P₂, P₃]]
        [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
         EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)] := by
    simpa [xss, accs, level_step_lists, pairUp, level_step] using h_step
  obtain ⟨h01, h_step_tail⟩ := List.forall₂_cons.mp h_step'
  obtain ⟨h23, _⟩ := List.forall₂_cons.mp h_step_tail
  have h01_sum :
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁)).point =
        sumOnE E [P₀, P₁] :=
    LandmarkInvStrong.running_sum E h01
  have h23_sum :
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)).point =
        sumOnE E [P₂, P₃] :=
    LandmarkInvStrong.running_sum E h23
  have hSumPairs : sumOnE E [P₀, P₁] + sumOnE E [P₂, P₃] = 0 := by
    calc
      sumOnE E [P₀, P₁] + sumOnE E [P₂, P₃]
          = sumOnE E ([P₀, P₁] ++ [P₂, P₃]) := by
            rw [sumOnE_append]
      _ = sumOnE E [P₀, P₁, P₂, P₃] := rfl
      _ = 0 := hSumZero
  have h_inverse :
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)).point =
        -((EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁)).point) := by
    rw [h01_sum, h23_sum]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hSumPairs)
  by_cases h_left_zero :
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁)).point =
        (0 : ECPoint E)
  · exact combine_extras_vacuous_of_left_zero E _ _ h_left_zero
  · intro _ _
    exact affine_extras_vacuous_on_inverse_affine_points E _ _ h_inverse h_left_zero

theorem h_extras_holds_for_length4_chord_pairs
    (E : ECSetup) (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃] : List (ZMod E.q × ZMod E.q)).Nodup)
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃] = 0)
    (h01_x_ne : P₀.1 ≠ P₁.1) (h23_x_ne : P₂.1 ≠ P₃.1)
    (hP₀_y_ne : P₀.2 ≠ 0) (hP₁_y_ne : P₁.2 ≠ 0)
    (hP₂_y_ne : P₂.2 ≠ 0) (hP₃_y_ne : P₃.2 ≠ 0)
    (hThird01_ne_P₀ :
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1)
    (hThird01_ne_P₁ :
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1)
    (hThird23_ne_P₂ :
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1)
    (hThird23_ne_P₃ :
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1) :
    ∀ k < ([P₀, P₁, P₂, P₃] : List (ZMod E.q × ZMod E.q)).length,
      LevelStepCombineExtras E
        (iterate E k (level0_singletons E [P₀, P₁, P₂, P₃])) := by
  classical
  have hPair01 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) :=
    levelInitSingleton_chord_combine_extras E P₀ P₁ hP₀_on hP₁_on h01_x_ne
      hP₀_y_ne hP₁_y_ne hThird01_ne_P₀ hThird01_ne_P₁
  have hPair23 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) :=
    levelInitSingleton_chord_combine_extras E P₂ P₃ hP₂_on hP₃_on h23_x_ne
      hP₂_y_ne hP₃_y_ne hThird23_ne_P₂ hThird23_ne_P₃
  have hLevel1 :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) :=
    length4_chord_level1_extras E P₀ P₁ P₂ P₃ hP₀_on hP₁_on hP₂_on hP₃_on
      hNodup hPair01 hPair23 hSumZero
  intro k hk
  have hk_lt4 : k < 4 := by simpa using hk
  interval_cases k
  · show LevelStepCombineExtras E
      [levelInitSingleton E P₀, levelInitSingleton E P₁,
       levelInitSingleton E P₂, levelInitSingleton E P₃]
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧ True)
    exact ⟨hPair01, hPair23, trivial⟩
  · have h_iter_eq :
        iterate E 1 (level0_singletons E [P₀, P₁, P₂, P₃])
          = level_step E (level0_singletons E [P₀, P₁, P₂, P₃]) := by
      show (if (level0_singletons E [P₀, P₁, P₂, P₃]).length ≤ 1 then _ else _) = _
      have h_len :
          (level0_singletons E [P₀, P₁, P₂, P₃]).length = 4 := by
        simp [level0_singletons]
      rw [if_neg (by rw [h_len]; omega)]
      rfl
    rw [h_iter_eq]
    show LevelStepCombineExtras E
      (level_step E
        [levelInitSingleton E P₀, levelInitSingleton E P₁,
         levelInitSingleton E P₂, levelInitSingleton E P₃])
    show LevelStepCombineExtras E
      [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
       EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)]
    change LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) ∧ True
    exact ⟨hLevel1, trivial⟩
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]

theorem length6_chord_level2_extras
    (E : ECSetup)
    (P₀ P₁ P₂ P₃ P₄ P₅ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hP₄_on : P₄ ∈ E.points) (hP₅_on : P₅ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅] :
      List (ZMod E.q × ZMod E.q)).Nodup)
    (hPair01 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁))
    (hPair23 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃))
    (hPair45 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅))
    (hLevel1 :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅] = 0) :
    LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
      (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)) := by
  classical
  let xss : List (List (ZMod E.q × ZMod E.q)) :=
    [[P₀], [P₁], [P₂], [P₃], [P₄], [P₅]]
  let accs : List (EagenAccum E) :=
    [levelInitSingleton E P₀, levelInitSingleton E P₁,
     levelInitSingleton E P₂, levelInitSingleton E P₃,
     levelInitSingleton E P₄, levelInitSingleton E P₅]
  have hxss_on : ∀ xs ∈ xss, ∀ P ∈ xs, P ∈ E.points := by
    intro xs hxs P hP
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₀_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₁_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₂_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₃_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₄_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₅_on
  have hxss_ne : ∀ xs ∈ xss, xs ≠ [] := by
    intro xs hxs
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hNodup_concat : xss.flatten.Nodup := by
    simpa [xss] using hNodup
  have h_init : LandmarkInvStrongList E xss accs := by
    subst xss
    subst accs
    simpa [level0_singletons] using
      landmarkInvStrongList_level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]
        (by
          intro P hP
          simp at hP
          rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
          · exact hP₀_on
          · exact hP₁_on
          · exact hP₂_on
          · exact hP₃_on
          · exact hP₄_on
          · exact hP₅_on)
  have h_level0_extras : LevelStepCombineExtras E accs := by
    subst accs
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅) ∧ True))
    exact ⟨hPair01, hPair23, hPair45, trivial⟩
  have h_step1_all :=
    landmarkInvStrongList_level_step E xss accs h_init
      hxss_on hNodup_concat hxss_ne h_level0_extras
  have h_step1 :
      LandmarkInvStrongList E [[P₀, P₁], [P₂, P₃], [P₄, P₅]]
        [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
         EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
         EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)] := by
    simpa [xss, accs, level_step_lists, pairUp, level_step] using h_step1_all.1
  have hxss_on1 : ∀ xs ∈ ([[P₀, P₁], [P₂, P₃], [P₄, P₅]] :
      List (List (ZMod E.q × ZMod E.q))), ∀ P ∈ xs, P ∈ E.points := by
    simpa [xss, level_step_lists, pairUp] using h_step1_all.2.2
  have hNodup1 : (([[P₀, P₁], [P₂, P₃], [P₄, P₅]] :
      List (List (ZMod E.q × ZMod E.q))).flatten).Nodup := by
    simpa [xss, level_step_lists, pairUp] using h_step1_all.2.1
  have hxss_ne1 : ∀ xs ∈ ([[P₀, P₁], [P₂, P₃], [P₄, P₅]] :
      List (List (ZMod E.q × ZMod E.q))), xs ≠ [] := by
    simp
  have h_level1_extras :
      LevelStepCombineExtras E
        [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
         EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
         EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)] := by
    change LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) ∧ True
    exact ⟨hLevel1, trivial⟩
  have h_step2_all :=
    landmarkInvStrongList_level_step E
      ([[P₀, P₁], [P₂, P₃], [P₄, P₅]] :
        List (List (ZMod E.q × ZMod E.q)))
      [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
       EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
       EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)]
      h_step1 hxss_on1 hNodup1 hxss_ne1 h_level1_extras
  have h_step2 :
      LandmarkInvStrongList E [[P₀, P₁, P₂, P₃], [P₄, P₅]]
        [EagenAccum.combine E
            (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
            (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)),
         EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)] := by
    simpa [level_step_lists, pairUp, level_step] using h_step2_all.1
  obtain ⟨h0123, h_step2_tail⟩ := List.forall₂_cons.mp h_step2
  obtain ⟨h45, _⟩ := List.forall₂_cons.mp h_step2_tail
  have h0123_sum :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point =
        sumOnE E [P₀, P₁, P₂, P₃] :=
    LandmarkInvStrong.running_sum E h0123
  have h45_sum :
      (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)).point =
        sumOnE E [P₄, P₅] :=
    LandmarkInvStrong.running_sum E h45
  have hSumPairs : sumOnE E [P₀, P₁, P₂, P₃] + sumOnE E [P₄, P₅] = 0 := by
    calc
      sumOnE E [P₀, P₁, P₂, P₃] + sumOnE E [P₄, P₅]
          = sumOnE E ([P₀, P₁, P₂, P₃] ++ [P₄, P₅]) := by
            rw [sumOnE_append]
      _ = sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅] := rfl
      _ = 0 := hSumZero
  have h_inverse :
      (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)).point =
        -((EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point) := by
    rw [h0123_sum, h45_sum]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hSumPairs)
  by_cases h_left_zero :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point =
        (0 : ECPoint E)
  · exact combine_extras_vacuous_of_left_zero E _ _ h_left_zero
  · intro _ _
    exact affine_extras_vacuous_on_inverse_affine_points E _ _ h_inverse h_left_zero

theorem h_extras_holds_for_length6_chord_pairs
    (E : ECSetup)
    (P₀ P₁ P₂ P₃ P₄ P₅ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hP₄_on : P₄ ∈ E.points) (hP₅_on : P₅ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅] :
      List (ZMod E.q × ZMod E.q)).Nodup)
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅] = 0)
    (h01_x_ne : P₀.1 ≠ P₁.1) (h23_x_ne : P₂.1 ≠ P₃.1)
    (h45_x_ne : P₄.1 ≠ P₅.1)
    (hP₀_y_ne : P₀.2 ≠ 0) (hP₁_y_ne : P₁.2 ≠ 0)
    (hP₂_y_ne : P₂.2 ≠ 0) (hP₃_y_ne : P₃.2 ≠ 0)
    (hP₄_y_ne : P₄.2 ≠ 0) (hP₅_y_ne : P₅.2 ≠ 0)
    (hThird01_ne_P₀ :
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1)
    (hThird01_ne_P₁ :
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1)
    (hThird23_ne_P₂ :
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1)
    (hThird23_ne_P₃ :
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1)
    (hThird45_ne_P₄ :
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₄.1)
    (hThird45_ne_P₅ :
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₅.1)
    (hLevel1 : Length6Level1ChordConditions E P₀ P₁ P₂ P₃) :
    ∀ k < ([P₀, P₁, P₂, P₃, P₄, P₅] :
        List (ZMod E.q × ZMod E.q)).length,
      LevelStepCombineExtras E
        (iterate E k (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])) := by
  classical
  have hPair01 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) :=
    levelInitSingleton_chord_combine_extras E P₀ P₁ hP₀_on hP₁_on h01_x_ne
      hP₀_y_ne hP₁_y_ne hThird01_ne_P₀ hThird01_ne_P₁
  have hPair23 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) :=
    levelInitSingleton_chord_combine_extras E P₂ P₃ hP₂_on hP₃_on h23_x_ne
      hP₂_y_ne hP₃_y_ne hThird23_ne_P₂ hThird23_ne_P₃
  have hPair45 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅) :=
    levelInitSingleton_chord_combine_extras E P₄ P₅ hP₄_on hP₅_on h45_x_ne
      hP₄_y_ne hP₅_y_ne hThird45_ne_P₄ hThird45_ne_P₅
  have hLevel1Extra :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) :=
    length6_chord_level1_extras E P₀ P₁ P₂ P₃
      hP₀_on hP₁_on hP₂_on hP₃_on h01_x_ne h23_x_ne hLevel1
  have hLevel2 :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)) :=
    length6_chord_level2_extras E P₀ P₁ P₂ P₃ P₄ P₅
      hP₀_on hP₁_on hP₂_on hP₃_on hP₄_on hP₅_on hNodup
      hPair01 hPair23 hPair45 hLevel1Extra hSumZero
  intro k hk
  have hk_lt6 : k < 6 := by simpa using hk
  interval_cases k
  · show LevelStepCombineExtras E
      [levelInitSingleton E P₀, levelInitSingleton E P₁,
       levelInitSingleton E P₂, levelInitSingleton E P₃,
       levelInitSingleton E P₄, levelInitSingleton E P₅]
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅) ∧ True))
    exact ⟨hPair01, hPair23, hPair45, trivial⟩
  · have h_iter_eq :
        iterate E 1 (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])
          = level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]) := by
      show (if (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]).length ≤ 1 then _ else _) = _
      have h_len :
          (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]).length = 6 := by
        simp [level0_singletons]
      rw [if_neg (by rw [h_len]; omega)]
      rfl
    rw [h_iter_eq]
    show LevelStepCombineExtras E
      (level_step E
        [levelInitSingleton E P₀, levelInitSingleton E P₁,
         levelInitSingleton E P₂, levelInitSingleton E P₃,
         levelInitSingleton E P₄, levelInitSingleton E P₅])
    show LevelStepCombineExtras E
      [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
       EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
       EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)]
    change LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) ∧ True
    exact ⟨hLevel1Extra, trivial⟩
  · have h_iter_eq :
        iterate E 2 (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])
          = level_step E
              (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])) := by
      show (if (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]).length ≤ 1 then _ else _) = _
      have h_len0 :
          (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅]).length = 6 := by
        simp [level0_singletons]
      rw [if_neg (by rw [h_len0]; omega)]
      show (if (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])).length ≤ 1 then _ else _) = _
      have h_len1 :
          (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅])).length = 3 := by
        simp [level0_singletons, level_step]
      rw [if_neg (by rw [h_len1]; omega)]
      rfl
    rw [h_iter_eq]
    show LevelStepCombineExtras E
      (level_step E
        (level_step E
          [levelInitSingleton E P₀, levelInitSingleton E P₁,
           levelInitSingleton E P₂, levelInitSingleton E P₃,
           levelInitSingleton E P₄, levelInitSingleton E P₅]))
    show LevelStepCombineExtras E
      [EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)),
       EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)]
    change LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
      (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅)) ∧ True
    exact ⟨hLevel2, trivial⟩
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]

end Landmark

/-! ## Length-4 fully-unconditional binary completeness.

For `Ps = [P₀, -P₀, P₂, -P₂]`, level-0 extras are the two length-2
inverse-pair discharges, level 1 combines two zero-point accumulators,
and later levels are singleton/vacuous. -/

theorem ma_completeness_for_binary_length4_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length4 : ∃ P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃] ∧
      P₁ = (P₀.1, -P₀.2) ∧
      P₃ = (P₂.1, -P₂.2))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P₀, P₁, P₂, P₃, hPs_eq, hP₁, hP₃⟩ := h_length4
  subst P₁
  subst P₃
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP₀_on : P₀ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₂_on : P₂ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length4_two_inverse_pairs
      E P₀ P₂ hP₀_on hP₂_on
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_clean_for_binary_length4_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length4 : ∃ P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃] ∧
      P₁ = (P₀.1, -P₀.2) ∧
      P₃ = (P₂.1, -P₂.2))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  obtain ⟨P₀, P₁, P₂, P₃, hPs_eq, hP₁, hP₃⟩ := h_length4
  subst P₁
  subst P₃
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP₀_on : P₀ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₂_on : P₂ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length4_two_inverse_pairs
      E P₀ P₂ hP₀_on hP₂_on
  exact ma_completeness_clean_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm hQ

theorem ma_completeness_for_binary_length4_chord_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length4 : ∃ P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃] ∧
      P₀.1 ≠ P₁.1 ∧ P₂.1 ≠ P₃.1 ∧
      P₀.2 ≠ 0 ∧ P₁.2 ≠ 0 ∧ P₂.2 ≠ 0 ∧ P₃.2 ≠ 0 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P₀, P₁, P₂, P₃, hPs_eq, h01_x_ne, h23_x_ne,
    hP₀_y_ne, hP₁_y_ne, hP₂_y_ne, hP₃_y_ne,
    hThird01_ne_P₀, hThird01_ne_P₁,
    hThird23_ne_P₂, hThird23_ne_P₃⟩ := h_length4
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP₀_on : P₀ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₁_on : P₁ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₂_on : P₂ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₃_on : P₃ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hNodup : ([P₀, P₁, P₂, P₃] : List (ZMod E.q × ZMod E.q)).Nodup := by
    simpa [hPs_eq] using h_binary.hNodup
  have hSumZero : Landmark.sumOnE E [P₀, P₁, P₂, P₃] = 0 := by
    simpa [hPs_eq] using h_binary.hSumZero
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length4_chord_pairs E P₀ P₁ P₂ P₃
      hP₀_on hP₁_on hP₂_on hP₃_on hNodup hSumZero
      h01_x_ne h23_x_ne hP₀_y_ne hP₁_y_ne hP₂_y_ne hP₃_y_ne
      hThird01_ne_P₀ hThird01_ne_P₁ hThird23_ne_P₂ hThird23_ne_P₃
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_for_binary_length6_chord_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length6 : ∃ P₀ P₁ P₂ P₃ P₄ P₅ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃, P₄, P₅] ∧
      P₀.1 ≠ P₁.1 ∧ P₂.1 ≠ P₃.1 ∧ P₄.1 ≠ P₅.1 ∧
      P₀.2 ≠ 0 ∧ P₁.2 ≠ 0 ∧ P₂.2 ≠ 0 ∧
      P₃.2 ≠ 0 ∧ P₄.2 ≠ 0 ∧ P₅.2 ≠ 0 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₄.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₅.1)
    (h_extras_level1 :
      ∀ P₀ P₁ P₂ P₃ P₄ P₅ : ZMod E.q × ZMod E.q,
        h_binary.Ps = [P₀, P₁, P₂, P₃, P₄, P₅] →
          Landmark.Length6Level1ChordConditions E P₀ P₁ P₂ P₃)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P₀, P₁, P₂, P₃, P₄, P₅, hPs_eq,
    h01_x_ne, h23_x_ne, h45_x_ne,
    hP₀_y_ne, hP₁_y_ne, hP₂_y_ne,
    hP₃_y_ne, hP₄_y_ne, hP₅_y_ne,
    hThird01_ne_P₀, hThird01_ne_P₁,
    hThird23_ne_P₂, hThird23_ne_P₃,
    hThird45_ne_P₄, hThird45_ne_P₅⟩ := h_length6
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP₀_on : P₀ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₁_on : P₁ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₂_on : P₂ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₃_on : P₃ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₄_on : P₄ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₅_on : P₅ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅] :
      List (ZMod E.q × ZMod E.q)).Nodup := by
    simpa [hPs_eq] using h_binary.hNodup
  have hSumZero :
      Landmark.sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅] = 0 := by
    simpa [hPs_eq] using h_binary.hSumZero
  have hLevel1 : Landmark.Length6Level1ChordConditions E P₀ P₁ P₂ P₃ :=
    h_extras_level1 P₀ P₁ P₂ P₃ P₄ P₅ hPs_eq
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length6_chord_pairs E P₀ P₁ P₂ P₃ P₄ P₅
      hP₀_on hP₁_on hP₂_on hP₃_on hP₄_on hP₅_on hNodup hSumZero
      h01_x_ne h23_x_ne h45_x_ne
      hP₀_y_ne hP₁_y_ne hP₂_y_ne hP₃_y_ne hP₄_y_ne hP₅_y_ne
      hThird01_ne_P₀ hThird01_ne_P₁
      hThird23_ne_P₂ hThird23_ne_P₃
      hThird45_ne_P₄ hThird45_ne_P₅
      hLevel1
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_clean_for_binary_length4_chord_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length4 : ∃ P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃] ∧
      P₀.1 ≠ P₁.1 ∧ P₂.1 ≠ P₃.1 ∧
      P₀.2 ≠ 0 ∧ P₁.2 ≠ 0 ∧ P₂.2 ≠ 0 ∧ P₃.2 ≠ 0 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  obtain ⟨P₀, P₁, P₂, P₃, hPs_eq, h01_x_ne, h23_x_ne,
    hP₀_y_ne, hP₁_y_ne, hP₂_y_ne, hP₃_y_ne,
    hThird01_ne_P₀, hThird01_ne_P₁,
    hThird23_ne_P₂, hThird23_ne_P₃⟩ := h_length4
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP₀_on : P₀ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₁_on : P₁ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₂_on : P₂ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₃_on : P₃ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hNodup : ([P₀, P₁, P₂, P₃] : List (ZMod E.q × ZMod E.q)).Nodup := by
    simpa [hPs_eq] using h_binary.hNodup
  have hSumZero : Landmark.sumOnE E [P₀, P₁, P₂, P₃] = 0 := by
    simpa [hPs_eq] using h_binary.hSumZero
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length4_chord_pairs E P₀ P₁ P₂ P₃
      hP₀_on hP₁_on hP₂_on hP₃_on hNodup hSumZero
      h01_x_ne h23_x_ne hP₀_y_ne hP₁_y_ne hP₂_y_ne hP₃_y_ne
      hThird01_ne_P₀ hThird01_ne_P₁ hThird23_ne_P₂ hThird23_ne_P₃
  exact ma_completeness_clean_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm hQ

/-- Hasse-clean form of `ma_completeness_for_binary_M_eq_3`. -/
theorem ma_completeness_clean_for_binary_M_eq_3
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hkm_eq :
      hkm = h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm :=
    Subsingleton.elim _ _
  rw [hkm_eq]
  exact ma_completeness_clean_for_length4Simple E stmt msg h_simple wit hk
    h_scalars hValid hDeg hDegK hAdm hQ

end Divisor
