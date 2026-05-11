/-
  Divisor/IsHonestForBinary.lean

  Bridge from the binary Eagen-singletons construction to the protocol
  honesty predicate.
-/
import Divisor.EagenBuildLandmark
import Divisor.CoordRingElt.Smul
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

/-- Binary honest construction data where the committed divisor is a
    nonzero scalar multiple of the singleton Eagen build.

This is the admSet-agnostic normalization hook.  Parker/Eagen/hash
specializations pick the scalar and discharge their own admissibility
predicate; the divisor, split, degree, and zero-count facts are invariant
under the nonzero scalar by `Divisor.CoordRingElt.Smul`. -/
structure MAProverMsg.IsHonestForBinaryScaled (E : ECSetup)
    (msg : MAProverMsg E.q) (stmt : DlogStatement E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k) where
  /-- Binary scalars in the witness. -/
  h_binary : forall i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1
  /-- The binary support list used by `eagenBuild_singletons`. -/
  Ps : List (ZMod E.q × ZMod E.q)
  /-- The nonzero normalizing scalar. -/
  c : ZMod E.q
  /-- The normalizing scalar is nonzero. -/
  h_c_ne : c ≠ 0
  /-- The committed coordinate-ring element is the scaled singleton Eagen build. -/
  h_toD_eq : msg.toD = c • Landmark.eagenBuild_singletons E Ps
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

namespace MAProverMsg.IsHonestForBinaryScaled

/-- Existing unscaled binary witnesses are scaled witnesses with scalar `1`. -/
def ofBinary
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm) :
    MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm where
  h_binary := h_binary.h_binary
  Ps := h_binary.Ps
  c := 1
  h_c_ne := one_ne_zero
  h_toD_eq := by
    rw [h_binary.h_toD_eq]
    cases Landmark.eagenBuild_singletons E h_binary.Ps with
    | mk a b =>
      rw [CoordRingElt.mk.injEq]
      simp
  hPs_on := h_binary.hPs_on
  hSumZero := h_binary.hSumZero
  hNonEmpty := h_binary.hNonEmpty
  hNodup := h_binary.hNodup
  h_scalars_match := h_binary.h_scalars_match
  h_formal_eq_honest := h_binary.h_formal_eq_honest
  h_target_on_curve := h_binary.h_target_on_curve
  h_bases_on_curve := h_binary.h_bases_on_curve

end MAProverMsg.IsHonestForBinaryScaled

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

/-- The scaled binary singleton build splits over `E`. -/
theorem splitsOnE_msg_toD_for_binary_scaled
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    splitsOnE E msg.toD := by
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  have h_landmark :
      ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ P ∈ h_binary.Ps, D.eval P.1 P.2 = 0) ∧
      (normPoly E D).natDegree = h_binary.Ps.length := by
    simpa [D] using
      Landmark.eagenBuild_singletons_landmark E h_binary.Ps
        h_binary.hPs_on h_binary.hSumZero h_binary.hNonEmpty h_combine
  exact (splitsOnE_smul E h_binary.c h_binary.h_c_ne D).mpr
    (Landmark.splitsOnE_of_landmark E h_binary.Ps D
      h_binary.hPs_on h_binary.hNodup
      h_landmark.1 h_landmark.2.1 h_landmark.2.2)

/-- The divisor of a scaled binary singleton build is the protocol honest
    divisor. -/
theorem divisor_identity_for_binary_scaled
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    forall R : ECPoint E,
      divisorOfD E msg.toD R =
        honestDivisorCoeffs E stmt wit hk msg R := by
  intro R
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  calc
    divisorOfD E (h_binary.c • D) R
        = divisorOfD E D R := divisorOfD_smul E h_binary.c h_binary.h_c_ne D R
    _ = Landmark.formalDivisorOfList E h_binary.Ps R := by
          exact Landmark.eagenBuild_singletons_divisor_identity E h_binary.Ps
            h_binary.hPs_on h_binary.hSumZero h_binary.hNonEmpty
            h_binary.hNodup h_combine R
    _ = honestDivisorCoeffs E stmt wit hk msg R :=
          h_binary.h_formal_eq_honest R

/-- Bridge from scaled binary construction data to the protocol-level honest
    prover predicate. -/
theorem isHonestFor_of_isHonestForBinaryScaled
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_combine : Landmark.PairwiseCombineHyp E) :
    msg.isHonestFor E stmt wit hk hkm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_binary.h_scalars_match
  · exact splitsOnE_msg_toD_for_binary_scaled h_binary h_combine
  · exact divisor_identity_for_binary_scaled h_binary h_combine
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

theorem ma_completeness_for_binary_with_scalar
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
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
    (isHonestFor_of_isHonestForBinaryScaled (E := E) h_binary h_combine)

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

theorem ma_completeness_clean_for_binary_with_scalar
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
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
    (isHonestFor_of_isHonestForBinaryScaled (E := E) h_binary h_combine)
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

theorem splitsOnE_msg_toD_for_binary_scaled_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
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
  exact (splitsOnE_smul E h_binary.c h_binary.h_c_ne D).mpr
    (Landmark.splitsOnE_of_landmark E h_binary.Ps D
      h_binary.hPs_on h_binary.hNodup
      h_landmark.1 h_landmark.2.1 h_landmark.2.2)

theorem divisor_identity_for_binary_scaled_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    forall R : ECPoint E,
      divisorOfD E msg.toD R =
        honestDivisorCoeffs E stmt wit hk msg R := by
  intro R
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  calc
    divisorOfD E (h_binary.c • D) R
        = divisorOfD E D R := divisorOfD_smul E h_binary.c h_binary.h_c_ne D R
    _ = Landmark.formalDivisorOfList E h_binary.Ps R := by
          exact Landmark.eagenBuild_singletons_divisor_identity_unconditional E
            h_binary.Ps h_binary.hPs_on h_binary.hSumZero
            h_binary.hNodup hLen h_extras R
    _ = honestDivisorCoeffs E stmt wit hk msg R :=
          h_binary.h_formal_eq_honest R

theorem isHonestFor_of_isHonestForBinaryScaled_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {wit : DlogWitness E.q}
    {msg : MAProverMsg E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    msg.isHonestFor E stmt wit hk hkm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_binary.h_scalars_match
  · exact splitsOnE_msg_toD_for_binary_scaled_unconditional h_binary hLen h_extras
  · exact divisor_identity_for_binary_scaled_unconditional h_binary hLen h_extras
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

theorem ma_completeness_for_binary_with_scalar_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
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
    (isHonestFor_of_isHonestForBinaryScaled_unconditional (E := E)
      h_binary hLen h_extras)

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

theorem ma_completeness_clean_for_binary_with_scalar_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
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
    (isHonestFor_of_isHonestForBinaryScaled_unconditional (E := E)
      h_binary hLen h_extras)
    hD hQ

private theorem admSetMax_of_isHonestForBinary_unconditional
    {E : ECSetup} {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    {wit : DlogWitness E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps))) :
    stmt.admSet (msg.polyA, msg.polyB) := by
  let D := Landmark.eagenBuild_singletons E h_binary.Ps
  have h_landmark :
      ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ P ∈ h_binary.Ps, D.eval P.1 P.2 = 0) ∧
      (normPoly E D).natDegree = h_binary.Ps.length := by
    simpa [D] using
      Landmark.eagenBuild_singletons_landmark_unconditional E h_binary.Ps
        h_binary.hPs_on h_binary.hSumZero h_binary.hNodup hLen h_extras
  have hD_msg : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
    rw [h_binary.h_toD_eq]
    exact h_landmark.1
  have hPair_ne :
      (msg.polyA, msg.polyB) ≠
        ((0 : Polynomial (ZMod E.q)), (0 : Polynomial (ZMod E.q))) := by
    intro hPair
    apply hD_msg
    constructor
    · simpa [MAProverMsg.toD] using congrArg Prod.fst hPair
    · simpa [MAProverMsg.toD] using congrArg Prod.snd hPair
  simpa [h_admSetMax, admSetMax] using hPair_ne

private theorem admSetParker_of_isHonestForBinaryScaled
    {E : ECSetup} {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    {wit : DlogWitness E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_admSetParker : stmt.admSet = admSetParker (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1)⁻¹)
    (hParker_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1 ≠ 0) :
    stmt.admSet (msg.polyA, msg.polyB) := by
  rw [h_admSetParker]
  unfold admSetParker
  change msg.toD.a.coeff 1 = 1
  rw [h_binary.h_toD_eq, h_c_eq]
  simp [CoordRingElt.smul_a, Polynomial.coeff_smul,
    inv_mul_cancel₀ hParker_pre]

private theorem admSetEagen_of_isHonestForBinaryScaled
    {E : ECSetup} {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    {wit : DlogWitness E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (h_admSetEagen : stmt.admSet = admSetEagen (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0)⁻¹)
    (hEagen_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0 ≠ 0) :
    stmt.admSet (msg.polyA, msg.polyB) := by
  rw [h_admSetEagen]
  unfold admSetEagen
  change msg.toD.a.coeff 0 = 1
  rw [h_binary.h_toD_eq, h_c_eq]
  simp [CoordRingElt.smul_a, Polynomial.coeff_smul,
    inv_mul_cancel₀ hEagen_pre]

private theorem admSetHashInner_smul
    {q : ℕ} [Fact (Nat.Prime q)] (r : ℕ → ZMod q)
    (c : ZMod q) (hc : c ≠ 0) (D : CoordRingElt q) :
    admSetHashInner r ((c • D).a, (c • D).b) =
      c * admSetHashInner r (D.a, D.b) := by
  unfold admSetHashInner
  rw [CoordRingElt.smul_a, CoordRingElt.smul_b,
    Polynomial.natDegree_smul _ hc, Polynomial.natDegree_smul _ hc]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Polynomial.coeff_smul, smul_eq_mul]
    ring
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [Polynomial.coeff_smul, smul_eq_mul]
    ring

private theorem admSetHash_of_isHonestForBinaryScaled
    {E : ECSetup} {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    {wit : DlogWitness E.q} {hk : stmt.k = wit.k} {hkm : stmt.k = msg.k}
    (r : ℕ → ZMod E.q)
    (h_admSetHash : stmt.admSet = admSetHash r)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      (admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b))⁻¹)
    (hHash_pre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b) ≠ 0) :
    stmt.admSet (msg.polyA, msg.polyB) := by
  rw [h_admSetHash]
  unfold admSetHash
  change admSetHashInner r (msg.toD.a, msg.toD.b) ≠ 0
  rw [h_binary.h_toD_eq]
  set D := Landmark.eagenBuild_singletons E h_binary.Ps
  have h_c_eq' : h_binary.c = (admSetHashInner r (D.a, D.b))⁻¹ := by
    simpa [D] using h_c_eq
  have hHash_pre' : admSetHashInner r (D.a, D.b) ≠ 0 := by
    simpa [D] using hHash_pre
  rw [admSetHashInner_smul r h_binary.c h_binary.h_c_ne D, h_c_eq']
  simp [inv_mul_cancel₀ hHash_pre']

theorem ma_completeness_for_binary_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK
    (admSetMax_of_isHonestForBinary_unconditional
      h_admSetMax h_binary hLen h_extras)

theorem ma_completeness_for_binary_admSetParker_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetParker : stmt.admSet = admSetParker (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1)⁻¹)
    (hParker_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1 ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_for_binary_with_scalar_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK
    (admSetParker_of_isHonestForBinaryScaled
      h_admSetParker h_binary h_c_eq hParker_pre)

theorem ma_completeness_for_binary_admSetEagen_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetEagen : stmt.admSet = admSetEagen (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0)⁻¹)
    (hEagen_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0 ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_for_binary_with_scalar_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK
    (admSetEagen_of_isHonestForBinaryScaled
      h_admSetEagen h_binary h_c_eq hEagen_pre)

theorem ma_completeness_for_binary_admSetHash_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (r : ℕ → ZMod E.q)
    (h_admSetHash : stmt.admSet = admSetHash r)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      (admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b))⁻¹)
    (hHash_pre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b) ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_extras : ∀ k < h_binary.Ps.length,
      Landmark.LevelStepCombineExtras E
        (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_for_binary_with_scalar_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK
    (admSetHash_of_isHonestForBinaryScaled
      r h_admSetHash h_binary h_c_eq hHash_pre)

theorem ma_completeness_binary_chain
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_binary_chain_admSetParker
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetParker : stmt.admSet = admSetParker (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1)⁻¹)
    (hParker_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 1 ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_for_binary_admSetParker_unconditional
    E stmt msg wit hk hkm h_admSetParker h_binary h_c_eq hParker_pre
    hLen h_extras hValid hDeg hDegK

theorem ma_completeness_binary_chain_admSetEagen
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetEagen : stmt.admSet = admSetEagen (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      ((Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0)⁻¹)
    (hEagen_pre :
      (Landmark.eagenBuild_singletons E h_binary.Ps).a.coeff 0 ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_for_binary_admSetEagen_unconditional
    E stmt msg wit hk hkm h_admSetEagen h_binary h_c_eq hEagen_pre
    hLen h_extras hValid hDeg hDegK

theorem ma_completeness_binary_chain_admSetHash
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (r : ℕ → ZMod E.q)
    (h_admSetHash : stmt.admSet = admSetHash r)
    (h_binary : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm)
    (h_c_eq : h_binary.c =
      (admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b))⁻¹)
    (hHash_pre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_binary.Ps).a,
          (Landmark.eagenBuild_singletons E h_binary.Ps).b) ≠ 0)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_for_binary_admSetHash_unconditional
    E stmt msg wit hk hkm r h_admSetHash h_binary h_c_eq hHash_pre
    hLen h_extras hValid hDeg hDegK

theorem ma_completeness_clean_for_binary_chord_chain_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_clean_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm hQ

theorem ma_completeness_binary_chain_admSetMax
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (hLen : 2 ≤ h_binary.Ps.length)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E h_binary.Ps.length
                  (Landmark.level0_singletons E h_binary.Ps))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) :=
    Landmark.h_extras_of_iteratedLevelStepCombineExtras E h_binary.Ps h_chain
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

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

theorem length8_chord_level2_extras
    (E : ECSetup)
    (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hP₄_on : P₄ ∈ E.points) (hP₅_on : P₅ ∈ E.points)
    (hP₆_on : P₆ ∈ E.points) (hP₇_on : P₇ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] :
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
    (hPair67 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₆) (levelInitSingleton E P₇))
    (hLevel1Left :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
    (hLevel1Right :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)))
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] = 0) :
    LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))) := by
  classical
  let xss : List (List (ZMod E.q × ZMod E.q)) :=
    [[P₀], [P₁], [P₂], [P₃], [P₄], [P₅], [P₆], [P₇]]
  let accs : List (EagenAccum E) :=
    [levelInitSingleton E P₀, levelInitSingleton E P₁,
     levelInitSingleton E P₂, levelInitSingleton E P₃,
     levelInitSingleton E P₄, levelInitSingleton E P₅,
     levelInitSingleton E P₆, levelInitSingleton E P₇]
  have hxss_on : ∀ xs ∈ xss, ∀ P ∈ xs, P ∈ E.points := by
    intro xs hxs P hP
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₆_on
    · rw [List.mem_singleton] at hP
      rw [hP]
      exact hP₇_on
  have hxss_ne : ∀ xs ∈ xss, xs ≠ [] := by
    intro xs hxs
    simp [xss] at hxs
    rcases hxs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hNodup_concat : xss.flatten.Nodup := by
    simpa [xss] using hNodup
  have h_init : LandmarkInvStrongList E xss accs := by
    subst xss
    subst accs
    simpa [level0_singletons] using
      landmarkInvStrongList_level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]
        (by
          intro P hP
          simp at hP
          rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hP₀_on
          · exact hP₁_on
          · exact hP₂_on
          · exact hP₃_on
          · exact hP₄_on
          · exact hP₅_on
          · exact hP₆_on
          · exact hP₇_on)
  have h_level0_extras : LevelStepCombineExtras E accs := by
    subst accs
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₆) (levelInitSingleton E P₇) ∧ True)))
    exact ⟨hPair01, hPair23, hPair45, hPair67, trivial⟩
  have h_step1_all :=
    landmarkInvStrongList_level_step E xss accs h_init
      hxss_on hNodup_concat hxss_ne h_level0_extras
  have h_step1 :
      LandmarkInvStrongList E [[P₀, P₁], [P₂, P₃], [P₄, P₅], [P₆, P₇]]
        [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
         EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
         EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅),
         EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)] := by
    simpa [xss, accs, level_step_lists, pairUp, level_step] using h_step1_all.1
  have hxss_on1 : ∀ xs ∈ ([[P₀, P₁], [P₂, P₃], [P₄, P₅], [P₆, P₇]] :
      List (List (ZMod E.q × ZMod E.q))), ∀ P ∈ xs, P ∈ E.points := by
    simpa [xss, level_step_lists, pairUp] using h_step1_all.2.2
  have hNodup1 : (([[P₀, P₁], [P₂, P₃], [P₄, P₅], [P₆, P₇]] :
      List (List (ZMod E.q × ZMod E.q))).flatten).Nodup := by
    simpa [xss, level_step_lists, pairUp] using h_step1_all.2.1
  have hxss_ne1 : ∀ xs ∈ ([[P₀, P₁], [P₂, P₃], [P₄, P₅], [P₆, P₇]] :
      List (List (ZMod E.q × ZMod E.q))), xs ≠ [] := by
    simp
  have h_level1_extras :
      LevelStepCombineExtras E
        [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
         EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
         EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅),
         EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)] := by
    change LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) ∧
      (LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)) ∧ True)
    exact ⟨hLevel1Left, hLevel1Right, trivial⟩
  have h_step2_all :=
    landmarkInvStrongList_level_step E
      ([[P₀, P₁], [P₂, P₃], [P₄, P₅], [P₆, P₇]] :
        List (List (ZMod E.q × ZMod E.q)))
      [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
       EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
       EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅),
       EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)]
      h_step1 hxss_on1 hNodup1 hxss_ne1 h_level1_extras
  have h_step2 :
      LandmarkInvStrongList E [[P₀, P₁, P₂, P₃], [P₄, P₅, P₆, P₇]]
        [EagenAccum.combine E
            (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
            (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)),
         EagenAccum.combine E
            (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
            (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))] := by
    simpa [level_step_lists, pairUp, level_step] using h_step2_all.1
  obtain ⟨h0123, h_step2_tail⟩ := List.forall₂_cons.mp h_step2
  obtain ⟨h4567, _⟩ := List.forall₂_cons.mp h_step2_tail
  have h0123_sum :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point =
        sumOnE E [P₀, P₁, P₂, P₃] :=
    LandmarkInvStrong.running_sum E h0123
  have h4567_sum :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))).point =
        sumOnE E [P₄, P₅, P₆, P₇] :=
    LandmarkInvStrong.running_sum E h4567
  have hSumPairs : sumOnE E [P₀, P₁, P₂, P₃] + sumOnE E [P₄, P₅, P₆, P₇] = 0 := by
    calc
      sumOnE E [P₀, P₁, P₂, P₃] + sumOnE E [P₄, P₅, P₆, P₇]
          = sumOnE E ([P₀, P₁, P₂, P₃] ++ [P₄, P₅, P₆, P₇]) := by
            rw [sumOnE_append]
      _ = sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] := rfl
      _ = 0 := hSumZero
  have h_inverse :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))).point =
        -((EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point) := by
    rw [h0123_sum, h4567_sum]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hSumPairs)
  by_cases h_left_zero :
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃))).point =
        (0 : ECPoint E)
  · exact combine_extras_vacuous_of_left_zero E _ _ h_left_zero
  · intro _ _
    exact affine_extras_vacuous_on_inverse_affine_points E _ _ h_inverse h_left_zero

theorem h_extras_holds_for_length8_chord_pairs
    (E : ECSetup)
    (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : ZMod E.q × ZMod E.q)
    (hP₀_on : P₀ ∈ E.points) (hP₁_on : P₁ ∈ E.points)
    (hP₂_on : P₂ ∈ E.points) (hP₃_on : P₃ ∈ E.points)
    (hP₄_on : P₄ ∈ E.points) (hP₅_on : P₅ ∈ E.points)
    (hP₆_on : P₆ ∈ E.points) (hP₇_on : P₇ ∈ E.points)
    (hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] :
      List (ZMod E.q × ZMod E.q)).Nodup)
    (hSumZero : sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] = 0)
    (h01_x_ne : P₀.1 ≠ P₁.1) (h23_x_ne : P₂.1 ≠ P₃.1)
    (h45_x_ne : P₄.1 ≠ P₅.1) (h67_x_ne : P₆.1 ≠ P₇.1)
    (hP₀_y_ne : P₀.2 ≠ 0) (hP₁_y_ne : P₁.2 ≠ 0)
    (hP₂_y_ne : P₂.2 ≠ 0) (hP₃_y_ne : P₃.2 ≠ 0)
    (hP₄_y_ne : P₄.2 ≠ 0) (hP₅_y_ne : P₅.2 ≠ 0)
    (hP₆_y_ne : P₆.2 ≠ 0) (hP₇_y_ne : P₇.2 ≠ 0)
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
    (hThird67_ne_P₆ :
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₆.1)
    (hThird67_ne_P₇ :
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₇.1)
    (hLevel1Left : Length6Level1ChordConditions E P₀ P₁ P₂ P₃)
    (hLevel1Right : Length6Level1ChordConditions E P₄ P₅ P₆ P₇) :
    ∀ k < ([P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] :
        List (ZMod E.q × ZMod E.q)).length,
      LevelStepCombineExtras E
        (iterate E k (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])) := by
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
  have hPair67 :
      LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₆) (levelInitSingleton E P₇) :=
    levelInitSingleton_chord_combine_extras E P₆ P₇ hP₆_on hP₇_on h67_x_ne
      hP₆_y_ne hP₇_y_ne hThird67_ne_P₆ hThird67_ne_P₇
  have hLevel1LeftExtra :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) :=
    length6_chord_level1_extras E P₀ P₁ P₂ P₃
      hP₀_on hP₁_on hP₂_on hP₃_on h01_x_ne h23_x_ne hLevel1Left
  have hLevel1RightExtra :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)) :=
    length6_chord_level1_extras E P₄ P₅ P₆ P₇
      hP₄_on hP₅_on hP₆_on hP₇_on h45_x_ne h67_x_ne hLevel1Right
  have hLevel2 :
      LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
        (EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
          (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))) :=
    length8_chord_level2_extras E P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇
      hP₀_on hP₁_on hP₂_on hP₃_on hP₄_on hP₅_on hP₆_on hP₇_on hNodup
      hPair01 hPair23 hPair45 hPair67 hLevel1LeftExtra hLevel1RightExtra hSumZero
  intro k hk
  have hk_lt8 : k < 8 := by simpa using hk
  interval_cases k
  · show LevelStepCombineExtras E
      [levelInitSingleton E P₀, levelInitSingleton E P₁,
       levelInitSingleton E P₂, levelInitSingleton E P₃,
       levelInitSingleton E P₄, levelInitSingleton E P₅,
       levelInitSingleton E P₆, levelInitSingleton E P₇]
    change LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₀) (levelInitSingleton E P₁) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₂) (levelInitSingleton E P₃) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₄) (levelInitSingleton E P₅) ∧
      (LandmarkInvStrongCombineExtras E
        (levelInitSingleton E P₆) (levelInitSingleton E P₇) ∧ True)))
    exact ⟨hPair01, hPair23, hPair45, hPair67, trivial⟩
  · have h_iter_eq :
        iterate E 1 (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])
          = level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]) := by
      show (if (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]).length ≤ 1 then _ else _) = _
      have h_len :
          (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]).length = 8 := by
        simp [level0_singletons]
      rw [if_neg (by rw [h_len]; omega)]
      rfl
    rw [h_iter_eq]
    show LevelStepCombineExtras E
      (level_step E
        [levelInitSingleton E P₀, levelInitSingleton E P₁,
         levelInitSingleton E P₂, levelInitSingleton E P₃,
         levelInitSingleton E P₄, levelInitSingleton E P₅,
         levelInitSingleton E P₆, levelInitSingleton E P₇])
    show LevelStepCombineExtras E
      [EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁),
       EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃),
       EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅),
       EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)]
    change LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
      (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)) ∧
      (LandmarkInvStrongCombineExtras E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇)) ∧ True)
    exact ⟨hLevel1LeftExtra, hLevel1RightExtra, trivial⟩
  · have h_iter_eq :
        iterate E 2 (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])
          = level_step E
              (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])) := by
      show (if (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]).length ≤ 1 then _ else _) = _
      have h_len0 :
          (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇]).length = 8 := by
        simp [level0_singletons]
      rw [if_neg (by rw [h_len0]; omega)]
      show (if (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])).length ≤ 1 then _ else _) = _
      have h_len1 :
          (level_step E (level0_singletons E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇])).length = 4 := by
        simp [level0_singletons, level_step]
      rw [if_neg (by rw [h_len1]; omega)]
      rfl
    rw [h_iter_eq]
    show LevelStepCombineExtras E
      (level_step E
        (level_step E
          [levelInitSingleton E P₀, levelInitSingleton E P₁,
           levelInitSingleton E P₂, levelInitSingleton E P₃,
           levelInitSingleton E P₄, levelInitSingleton E P₅,
           levelInitSingleton E P₆, levelInitSingleton E P₇]))
    show LevelStepCombineExtras E
      [EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
          (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)),
       EagenAccum.combine E
          (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
          (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))]
    change LandmarkInvStrongCombineExtras E
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₀) (levelInitSingleton E P₁))
        (EagenAccum.combine E (levelInitSingleton E P₂) (levelInitSingleton E P₃)))
      (EagenAccum.combine E
        (EagenAccum.combine E (levelInitSingleton E P₄) (levelInitSingleton E P₅))
        (EagenAccum.combine E (levelInitSingleton E P₆) (levelInitSingleton E P₇))) ∧ True
    exact ⟨hLevel2, trivial⟩
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]
  · simp [iterate, level0_singletons, level_step, LevelStepCombineExtras]
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

theorem ma_completeness_for_binary_length2_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length2 : ∃ P Q : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P, Q] ∧ P.1 = Q.1 ∧ Q.2 = -P.2)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P, Q, hPs_eq, hxx, hyy⟩ := h_length2
  have hLen : 2 ≤ h_binary.Ps.length := by
    rw [hPs_eq]
    simp
  have hP_on : P ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hQ_on : Q ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length2_sum_zero E P Q hP_on hQ_on hxx hyy
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

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

theorem ma_completeness_for_binary_length4_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length4 : ∃ P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃] ∧
      P₁ = (P₀.1, -P₀.2) ∧
      P₃ = (P₂.1, -P₂.2))
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
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
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

theorem ma_completeness_for_binary_length4_chord_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
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
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
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
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

theorem ma_completeness_for_binary_length8_chord_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length8 : ∃ P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] ∧
      P₀.1 ≠ P₁.1 ∧ P₂.1 ≠ P₃.1 ∧ P₄.1 ≠ P₅.1 ∧ P₆.1 ≠ P₇.1 ∧
      P₀.2 ≠ 0 ∧ P₁.2 ≠ 0 ∧ P₂.2 ≠ 0 ∧ P₃.2 ≠ 0 ∧
      P₄.2 ≠ 0 ∧ P₅.2 ≠ 0 ∧ P₆.2 ≠ 0 ∧ P₇.2 ≠ 0 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₄.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₅.1 ∧
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₆.1 ∧
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₇.1 ∧
      Landmark.chordSumX E P₀ P₁ ≠ Landmark.chordSumX E P₂ P₃ ∧
      Landmark.chordSumY E P₀ P₁ ≠ 0 ∧
      Landmark.chordSumY E P₂ P₃ ≠ 0 ∧
      (slopeOf (Landmark.chordSumX E P₀ P₁) (Landmark.chordSumY E P₀ P₁)
          (Landmark.chordSumX E P₂ P₃) (Landmark.chordSumY E P₂ P₃) ^ 2 -
          Landmark.chordSumX E P₀ P₁ - Landmark.chordSumX E P₂ P₃) ≠
        Landmark.chordSumX E P₀ P₁ ∧
      (slopeOf (Landmark.chordSumX E P₀ P₁) (Landmark.chordSumY E P₀ P₁)
          (Landmark.chordSumX E P₂ P₃) (Landmark.chordSumY E P₂ P₃) ^ 2 -
          Landmark.chordSumX E P₀ P₁ - Landmark.chordSumX E P₂ P₃) ≠
        Landmark.chordSumX E P₂ P₃ ∧
      Landmark.chordSumX E P₄ P₅ ≠ Landmark.chordSumX E P₆ P₇ ∧
      Landmark.chordSumY E P₄ P₅ ≠ 0 ∧
      Landmark.chordSumY E P₆ P₇ ≠ 0 ∧
      (slopeOf (Landmark.chordSumX E P₄ P₅) (Landmark.chordSumY E P₄ P₅)
          (Landmark.chordSumX E P₆ P₇) (Landmark.chordSumY E P₆ P₇) ^ 2 -
          Landmark.chordSumX E P₄ P₅ - Landmark.chordSumX E P₆ P₇) ≠
        Landmark.chordSumX E P₄ P₅ ∧
      (slopeOf (Landmark.chordSumX E P₄ P₅) (Landmark.chordSumY E P₄ P₅)
          (Landmark.chordSumX E P₆ P₇) (Landmark.chordSumY E P₆ P₇) ^ 2 -
          Landmark.chordSumX E P₄ P₅ - Landmark.chordSumX E P₆ P₇) ≠
        Landmark.chordSumX E P₆ P₇)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇, hPs_eq,
    h01_x_ne, h23_x_ne, h45_x_ne, h67_x_ne,
    hP₀_y_ne, hP₁_y_ne, hP₂_y_ne, hP₃_y_ne,
    hP₄_y_ne, hP₅_y_ne, hP₆_y_ne, hP₇_y_ne,
    hThird01_ne_P₀, hThird01_ne_P₁,
    hThird23_ne_P₂, hThird23_ne_P₃,
    hThird45_ne_P₄, hThird45_ne_P₅,
    hThird67_ne_P₆, hThird67_ne_P₇,
    h01_23_x_ne, h01_y_ne, h23_y_ne,
    hThird0123_ne_01, hThird0123_ne_23,
    h45_67_x_ne, h45_y_ne, h67_y_ne,
    hThird4567_ne_45, hThird4567_ne_67⟩ := h_length8
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
  have hP₆_on : P₆ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₇_on : P₇ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] :
      List (ZMod E.q × ZMod E.q)).Nodup := by
    simpa [hPs_eq] using h_binary.hNodup
  have hSumZero :
      Landmark.sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] = 0 := by
    simpa [hPs_eq] using h_binary.hSumZero
  have hLevel1Left : Landmark.Length6Level1ChordConditions E P₀ P₁ P₂ P₃ :=
    ⟨h01_23_x_ne, h01_y_ne, h23_y_ne, hThird0123_ne_01, hThird0123_ne_23⟩
  have hLevel1Right : Landmark.Length6Level1ChordConditions E P₄ P₅ P₆ P₇ :=
    ⟨h45_67_x_ne, h45_y_ne, h67_y_ne, hThird4567_ne_45, hThird4567_ne_67⟩
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length8_chord_pairs E
      P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇
      hP₀_on hP₁_on hP₂_on hP₃_on hP₄_on hP₅_on hP₆_on hP₇_on
      hNodup hSumZero
      h01_x_ne h23_x_ne h45_x_ne h67_x_ne
      hP₀_y_ne hP₁_y_ne hP₂_y_ne hP₃_y_ne
      hP₄_y_ne hP₅_y_ne hP₆_y_ne hP₇_y_ne
      hThird01_ne_P₀ hThird01_ne_P₁
      hThird23_ne_P₂ hThird23_ne_P₃
      hThird45_ne_P₄ hThird45_ne_P₅
      hThird67_ne_P₆ hThird67_ne_P₇
      hLevel1Left hLevel1Right
  exact ma_completeness_for_binary_unconditional E stmt msg wit hk hkm
    h_binary hLen h_extras hValid hDeg hDegK hAdm

theorem ma_completeness_for_binary_length6_chord_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
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
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
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
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

theorem ma_completeness_for_binary_length8_chord_admSetMax_unconditional
    (E : ECSetup) (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (hkm : stmt.k = msg.k)
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_binary : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm)
    (h_length8 : ∃ P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : ZMod E.q × ZMod E.q,
      h_binary.Ps = [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] ∧
      P₀.1 ≠ P₁.1 ∧ P₂.1 ≠ P₃.1 ∧ P₄.1 ≠ P₅.1 ∧ P₆.1 ≠ P₇.1 ∧
      P₀.2 ≠ 0 ∧ P₁.2 ≠ 0 ∧ P₂.2 ≠ 0 ∧ P₃.2 ≠ 0 ∧
      P₄.2 ≠ 0 ∧ P₅.2 ≠ 0 ∧ P₆.2 ≠ 0 ∧ P₇.2 ≠ 0 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₀.1 ∧
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1) ≠ P₁.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₂.1 ∧
      (slopeOf P₂.1 P₂.2 P₃.1 P₃.2 ^ 2 - P₂.1 - P₃.1) ≠ P₃.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₄.1 ∧
      (slopeOf P₄.1 P₄.2 P₅.1 P₅.2 ^ 2 - P₄.1 - P₅.1) ≠ P₅.1 ∧
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₆.1 ∧
      (slopeOf P₆.1 P₆.2 P₇.1 P₇.2 ^ 2 - P₆.1 - P₇.1) ≠ P₇.1 ∧
      Landmark.chordSumX E P₀ P₁ ≠ Landmark.chordSumX E P₂ P₃ ∧
      Landmark.chordSumY E P₀ P₁ ≠ 0 ∧
      Landmark.chordSumY E P₂ P₃ ≠ 0 ∧
      (slopeOf (Landmark.chordSumX E P₀ P₁) (Landmark.chordSumY E P₀ P₁)
          (Landmark.chordSumX E P₂ P₃) (Landmark.chordSumY E P₂ P₃) ^ 2 -
          Landmark.chordSumX E P₀ P₁ - Landmark.chordSumX E P₂ P₃) ≠
        Landmark.chordSumX E P₀ P₁ ∧
      (slopeOf (Landmark.chordSumX E P₀ P₁) (Landmark.chordSumY E P₀ P₁)
          (Landmark.chordSumX E P₂ P₃) (Landmark.chordSumY E P₂ P₃) ^ 2 -
          Landmark.chordSumX E P₀ P₁ - Landmark.chordSumX E P₂ P₃) ≠
        Landmark.chordSumX E P₂ P₃ ∧
      Landmark.chordSumX E P₄ P₅ ≠ Landmark.chordSumX E P₆ P₇ ∧
      Landmark.chordSumY E P₄ P₅ ≠ 0 ∧
      Landmark.chordSumY E P₆ P₇ ≠ 0 ∧
      (slopeOf (Landmark.chordSumX E P₄ P₅) (Landmark.chordSumY E P₄ P₅)
          (Landmark.chordSumX E P₆ P₇) (Landmark.chordSumY E P₆ P₇) ^ 2 -
          Landmark.chordSumX E P₄ P₅ - Landmark.chordSumX E P₆ P₇) ≠
        Landmark.chordSumX E P₄ P₅ ∧
      (slopeOf (Landmark.chordSumX E P₄ P₅) (Landmark.chordSumY E P₄ P₅)
          (Landmark.chordSumX E P₆ P₇) (Landmark.chordSumY E P₆ P₇) ^ 2 -
          Landmark.chordSumX E P₄ P₅ - Landmark.chordSumX E P₆ P₇) ≠
        Landmark.chordSumX E P₆ P₇)
    (hValid : relDlog E stmt wit)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  obtain ⟨P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇, hPs_eq,
    h01_x_ne, h23_x_ne, h45_x_ne, h67_x_ne,
    hP₀_y_ne, hP₁_y_ne, hP₂_y_ne, hP₃_y_ne,
    hP₄_y_ne, hP₅_y_ne, hP₆_y_ne, hP₇_y_ne,
    hThird01_ne_P₀, hThird01_ne_P₁,
    hThird23_ne_P₂, hThird23_ne_P₃,
    hThird45_ne_P₄, hThird45_ne_P₅,
    hThird67_ne_P₆, hThird67_ne_P₇,
    h01_23_x_ne, h01_y_ne, h23_y_ne,
    hThird0123_ne_01, hThird0123_ne_23,
    h45_67_x_ne, h45_y_ne, h67_y_ne,
    hThird4567_ne_45, hThird4567_ne_67⟩ := h_length8
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
  have hP₆_on : P₆ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hP₇_on : P₇ ∈ E.points := by
    apply h_binary.hPs_on
    rw [hPs_eq]
    simp
  have hNodup : ([P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] :
      List (ZMod E.q × ZMod E.q)).Nodup := by
    simpa [hPs_eq] using h_binary.hNodup
  have hSumZero :
      Landmark.sumOnE E [P₀, P₁, P₂, P₃, P₄, P₅, P₆, P₇] = 0 := by
    simpa [hPs_eq] using h_binary.hSumZero
  have hLevel1Left : Landmark.Length6Level1ChordConditions E P₀ P₁ P₂ P₃ :=
    ⟨h01_23_x_ne, h01_y_ne, h23_y_ne, hThird0123_ne_01, hThird0123_ne_23⟩
  have hLevel1Right : Landmark.Length6Level1ChordConditions E P₄ P₅ P₆ P₇ :=
    ⟨h45_67_x_ne, h45_y_ne, h67_y_ne, hThird4567_ne_45, hThird4567_ne_67⟩
  have h_extras :
      ∀ k < h_binary.Ps.length,
        Landmark.LevelStepCombineExtras E
          (Landmark.iterate E k (Landmark.level0_singletons E h_binary.Ps)) := by
    rw [hPs_eq]
    exact Landmark.h_extras_holds_for_length8_chord_pairs E
      P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇
      hP₀_on hP₁_on hP₂_on hP₃_on hP₄_on hP₅_on hP₆_on hP₇_on
      hNodup hSumZero
      h01_x_ne h23_x_ne h45_x_ne h67_x_ne
      hP₀_y_ne hP₁_y_ne hP₂_y_ne hP₃_y_ne
      hP₄_y_ne hP₅_y_ne hP₆_y_ne hP₇_y_ne
      hThird01_ne_P₀ hThird01_ne_P₁
      hThird23_ne_P₂ hThird23_ne_P₃
      hThird45_ne_P₄ hThird45_ne_P₅
      hThird67_ne_P₆ hThird67_ne_P₇
      hLevel1Left hLevel1Right
  exact ma_completeness_for_binary_admSetMax_unconditional E stmt msg wit hk hkm
    h_admSetMax h_binary hLen h_extras hValid hDeg hDegK

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

/-! ## Automatic binary support constructors -/

/-- The binary support list: `(-target)` followed by every statement base
    whose transported binary witness scalar is `1`. -/
def binarySupport
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (_h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1) :
    List (ZMod E.q × ZMod E.q) :=
  (stmt.target.1, -stmt.target.2) ::
    (List.finRange wit.k).filterMap (fun i =>
      if wit.scalars i = 1 then
        some (stmt.bases (Fin.cast hk.symm i))
      else
        none)

private theorem sumOnE_filterMap_binary
    {E : ECSetup} {α : Type*} [DecidableEq α]
    (xs : List α) (hxs : xs.Nodup)
    (f : α → ZMod E.q × ZMod E.q) (s : α → ℤ)
    (h_binary : ∀ i ∈ xs, s i = 0 ∨ s i = 1)
    (h_on : ∀ i ∈ xs, s i = 1 → f i ∈ E.points) :
    Landmark.sumOnE E
        (xs.filterMap (fun i => if s i = 1 then some (f i) else none))
      =
    ECPoint.weightedSum E xs.toFinset
      (fun i => ECPoint.zsmul E (s i)
        (ECPoint.affine E (f i).1 (f i).2)) := by
  classical
  induction xs with
  | nil =>
      simp [Landmark.sumOnE, ECPoint.weightedSum]
  | cons a xs ih =>
      have ha_not_mem : a ∉ xs := by
        exact (List.nodup_cons.mp hxs).1
      have ha_not_mem_finset : a ∉ xs.toFinset := by
        simpa [List.mem_toFinset] using ha_not_mem
      have hxs_tail : xs.Nodup := hxs.of_cons
      have hbin_a : s a = 0 ∨ s a = 1 := h_binary a (by simp)
      have hbin_tail : ∀ i ∈ xs, s i = 0 ∨ s i = 1 := by
        intro i hi
        exact h_binary i (by simp [hi])
      have hon_tail : ∀ i ∈ xs, s i = 1 → f i ∈ E.points := by
        intro i hi hs
        exact h_on i (by simp [hi]) hs
      have ih_tail := ih hxs_tail hbin_tail hon_tail
      rw [List.filterMap_cons, List.toFinset_cons]
      unfold ECPoint.weightedSum
      rw [Finset.sum_insert ha_not_mem_finset]
      by_cases hs1 : s a = 1
      · have ha_on : f a ∈ E.points := h_on a (by simp) hs1
        rw [if_pos hs1]
        rw [Landmark.sumOnE_cons E ha_on, ih_tail]
        rw [hs1, ECPoint.zsmul_one]
        rw [← ECPoint.affine_eq_affineOfMem E ha_on]
      · have hs0 : s a = 0 := hbin_a.resolve_right hs1
        rw [if_neg hs1, ih_tail]
        rw [hs0, ECPoint.zsmul_zero, zero_add]

private theorem length_filter_filterMap_binary_eq_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (xs : List α) (hxs : xs.Nodup)
    (f : α → β) (s : α → ℤ)
    (h_binary : ∀ i ∈ xs, s i = 0 ∨ s i = 1) (Q : β) :
    ((((xs.filterMap (fun i => if s i = 1 then some (f i) else none)).filter
        (fun P => P = Q)).length : ℤ))
      =
    ∑ i ∈ xs.toFinset, if f i = Q then s i else 0 := by
  classical
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      have ha_not_mem : a ∉ xs := by
        exact (List.nodup_cons.mp hxs).1
      have ha_not_mem_finset : a ∉ xs.toFinset := by
        simpa [List.mem_toFinset] using ha_not_mem
      have hxs_tail : xs.Nodup := hxs.of_cons
      have hbin_a : s a = 0 ∨ s a = 1 := h_binary a (by simp)
      have hbin_tail : ∀ i ∈ xs, s i = 0 ∨ s i = 1 := by
        intro i hi
        exact h_binary i (by simp [hi])
      have ih_tail := ih hxs_tail hbin_tail
      rw [List.filterMap_cons, List.toFinset_cons]
      rw [Finset.sum_insert ha_not_mem_finset]
      by_cases hs1 : s a = 1
      · rw [if_pos hs1]
        by_cases hQ : f a = Q
        · simp [hQ, hs1, ih_tail]
          ring
        · simp [hQ, ih_tail]
      · have hs0 : s a = 0 := hbin_a.resolve_right hs1
        rw [if_neg hs1]
        by_cases hQ : f a = Q
        · simp [hQ, hs0, ih_tail]
        · simp [hQ, ih_tail]

private theorem relDlog_weightedSum_with_hk
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit) :
    (ECPoint.affine E stmt.target.1 stmt.target.2 : ECPoint E)
      =
    ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
      (fun i => ECPoint.zsmul E (wit.scalars i)
        (ECPoint.affine E
          (stmt.bases (Fin.cast hk.symm i)).1
          (stmt.bases (Fin.cast hk.symm i)).2)) := by
  obtain ⟨hkRel, hRel⟩ := hValid
  have hkRel_eq : hkRel = hk := Subsingleton.elim _ _
  simpa [hkRel_eq] using hRel

private theorem finCongr_symm_sum_binary
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (Q : ZMod E.q × ZMod E.q) :
    (∑ i ∈ (Finset.univ : Finset (Fin wit.k)),
        if stmt.bases (Fin.cast hk.symm i) = Q then wit.scalars i else 0)
      =
    ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)),
        if stmt.bases i = Q then wit.scalars (hk ▸ i) else 0 := by
  classical
  let e : Fin wit.k ≃ Fin stmt.k := finCongr hk.symm
  refine Finset.sum_equiv e (fun _ => by simp) ?_
  intro i _hi
  have hcast : hk ▸ Fin.cast hk.symm i = i := by
    rw [eqRec_eq_cast]
    rw [← Fin.cast_eq_cast hk]
    rw [Fin.cast_cast]
    rw [Fin.cast_eq_self]
  simp [e, hcast]

/-- The binary support sums to zero on `E` under the dlog relation. -/
theorem binarySupport_sumOnE_eq_zero
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hPs_on : ∀ P ∈ binarySupport stmt wit hk h_binary, P ∈ E.points) :
    Landmark.sumOnE E (binarySupport stmt wit hk h_binary) = 0 := by
  classical
  let selected : List (ZMod E.q × ZMod E.q) :=
    (List.finRange wit.k).filterMap (fun i =>
      if wit.scalars i = 1 then
        some (stmt.bases (Fin.cast hk.symm i))
      else
        none)
  have h_selected_sum :
      Landmark.sumOnE E selected
        =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
        (fun i => ECPoint.zsmul E (wit.scalars i)
          (ECPoint.affine E
            (stmt.bases (Fin.cast hk.symm i)).1
            (stmt.bases (Fin.cast hk.symm i)).2)) := by
    have h_on_selected :
        ∀ i ∈ List.finRange wit.k, wit.scalars i = 1 →
          stmt.bases (Fin.cast hk.symm i) ∈ E.points := by
      intro i hi hs
      apply hPs_on
      rw [binarySupport, List.mem_cons, List.mem_filterMap]
      right
      refine ⟨i, hi, ?_⟩
      simp [hs]
    simpa [selected, List.toFinset_finRange, ECPoint.weightedSum] using
      (sumOnE_filterMap_binary
        (E := E) (xs := List.finRange wit.k) (f := fun i =>
          stmt.bases (Fin.cast hk.symm i)) (s := fun i => wit.scalars i)
        (List.nodup_finRange wit.k)
        (by intro i _hi; exact h_binary i)
        h_on_selected)
  have h_target_on :
      (stmt.target.1, -stmt.target.2) ∈ E.points := by
    apply hPs_on
    simp [binarySupport]
  have hRel := relDlog_weightedSum_with_hk stmt wit hk hValid
  rw [binarySupport]
  change Landmark.sumOnE E ((stmt.target.1, -stmt.target.2) :: selected) = 0
  rw [Landmark.sumOnE_cons E h_target_on, h_selected_sum]
  rw [← ECPoint.affine_eq_affineOfMem E h_target_on]
  rw [← ECPoint.affine_neg E stmt.target.1 stmt.target.2]
  rw [← hRel]
  simp

/-- The formal divisor of `binarySupport` agrees with
    `honestDivisorCoeffs`, provided the committed divisor has the
    matching degree at infinity. -/
theorem binarySupport_formalDivisorOfList_eq_honestDivisorCoeffs
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (msg : MAProverMsg E.q)
    (h_degE_eq :
      msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (R : ECPoint E) :
    Landmark.formalDivisorOfList E (binarySupport stmt wit hk h_binary) R
      = honestDivisorCoeffs E stmt wit hk msg R := by
  classical
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
      show -(((binarySupport stmt wit hk h_binary).length : ℤ))
        = -((msg.toD.degE : ℤ))
      rw [h_degE_eq]
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ =>
      let Q : ZMod E.q × ZMod E.q := (x, y)
      let selected : List (ZMod E.q × ZMod E.q) :=
        (List.finRange wit.k).filterMap (fun i =>
          if wit.scalars i = 1 then
            some (stmt.bases (Fin.cast hk.symm i))
          else
            none)
      have h_count :
          (((selected.filter (fun P => P = Q)).length : ℤ))
            =
          ∑ i ∈ (Finset.univ : Finset (Fin wit.k)),
              if stmt.bases (Fin.cast hk.symm i) = Q then wit.scalars i else 0 := by
        simpa [selected, List.toFinset_finRange] using
          (length_filter_filterMap_binary_eq_sum
            (xs := List.finRange wit.k)
            (f := fun i => stmt.bases (Fin.cast hk.symm i))
            (s := fun i => wit.scalars i)
            (List.nodup_finRange wit.k)
            (by intro i _hi; exact h_binary i)
            Q)
      have h_cast_sum :
          (∑ i ∈ (Finset.univ : Finset (Fin wit.k)),
              if stmt.bases (Fin.cast hk.symm i) = Q then wit.scalars i else 0)
            =
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)),
              if stmt.bases i = Q then wit.scalars (hk ▸ i) else 0 :=
        finCongr_symm_sum_binary stmt wit hk Q
      have h_filter_sum :
          (∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
              (fun i => stmt.bases i = Q), wit.scalars (hk ▸ i))
            =
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)),
              if stmt.bases i = Q then wit.scalars (hk ▸ i) else 0 := by
        rw [Finset.sum_filter]
      unfold Landmark.formalDivisorOfList honestDivisorCoeffs binarySupport
      change (((((stmt.target.1, -stmt.target.2) :: selected).filter
          (fun P => P = Q)).length : ℤ))
        =
        (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
            (fun i => stmt.bases i = Q), wit.scalars (hk ▸ i)
      calc
        (((((stmt.target.1, -stmt.target.2) :: selected).filter
            (fun P => P = Q)).length : ℤ))
            =
          (if (stmt.target.1, -stmt.target.2) = Q then (1 : ℤ) else 0) +
            ((selected.filter (fun P => P = Q)).length : ℤ) := by
              by_cases hT : (stmt.target.1, -stmt.target.2) = Q <;>
                simp [hT, add_comm]
        _ =
          (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
            ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
              (fun i => stmt.bases i = Q), wit.scalars (hk ▸ i) := by
              rw [h_count, h_cast_sum, ← h_filter_sum]
              by_cases hT : Q = (stmt.target.1, -stmt.target.2) <;>
                simp [hT, eq_comm]

namespace MAProverMsg.IsHonestForBinary

/-- Build binary honesty data directly from a binary witness and its
    derived support list. -/
noncomputable def fromWitness
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (h_toD_eq : msg.toD = Landmark.eagenBuild_singletons E
                  (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
      msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup) :
    MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm where
  h_binary := h_binary
  Ps := binarySupport stmt wit hk h_binary
  h_toD_eq := h_toD_eq
  hPs_on := by
    intro P hP
    rw [binarySupport, List.mem_cons, List.mem_filterMap] at hP
    rcases hP with hP | ⟨i, _hi, hSome⟩
    · rw [hP]
      exact h_target_on_curve
    · by_cases hs : wit.scalars i = 1
      · simp [hs] at hSome
        rw [← hSome]
        exact h_bases_on_curve (Fin.cast hk.symm i)
      · simp [hs] at hSome
  hSumZero := by
    apply binarySupport_sumOnE_eq_zero stmt wit hk h_binary hValid
    intro P hP
    rw [binarySupport, List.mem_cons, List.mem_filterMap] at hP
    rcases hP with hP | ⟨i, _hi, hSome⟩
    · rw [hP]
      exact h_target_on_curve
    · by_cases hs : wit.scalars i = 1
      · simp [hs] at hSome
        rw [← hSome]
        exact h_bases_on_curve (Fin.cast hk.symm i)
      · simp [hs] at hSome
  hNonEmpty := by
    simp [binarySupport]
  hNodup := hNodup
  h_scalars_match := h_scalars_match
  h_formal_eq_honest := by
    intro R
    exact binarySupport_formalDivisorOfList_eq_honestDivisorCoeffs
      stmt wit hk h_binary msg h_degE_eq R
  h_target_on_curve := h_target_on_curve
  h_bases_on_curve := h_bases_on_curve

end MAProverMsg.IsHonestForBinary

namespace MAProverMsg.IsHonestForBinaryScaled

/-- Build scaled binary honesty data directly from a binary witness and its
    derived support list. -/
noncomputable def fromWitness
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (c : ZMod E.q) (h_c_ne : c ≠ 0)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (h_toD_eq : msg.toD = c • Landmark.eagenBuild_singletons E
                  (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
      msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup) :
    MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm where
  h_binary := h_binary
  Ps := binarySupport stmt wit hk h_binary
  c := c
  h_c_ne := h_c_ne
  h_toD_eq := h_toD_eq
  hPs_on := by
    intro P hP
    rw [binarySupport, List.mem_cons, List.mem_filterMap] at hP
    rcases hP with hP | ⟨i, _hi, hSome⟩
    · rw [hP]
      exact h_target_on_curve
    · by_cases hs : wit.scalars i = 1
      · simp [hs] at hSome
        rw [← hSome]
        exact h_bases_on_curve (Fin.cast hk.symm i)
      · simp [hs] at hSome
  hSumZero := by
    apply binarySupport_sumOnE_eq_zero stmt wit hk h_binary hValid
    intro P hP
    rw [binarySupport, List.mem_cons, List.mem_filterMap] at hP
    rcases hP with hP | ⟨i, _hi, hSome⟩
    · rw [hP]
      exact h_target_on_curve
    · by_cases hs : wit.scalars i = 1
      · simp [hs] at hSome
        rw [← hSome]
        exact h_bases_on_curve (Fin.cast hk.symm i)
      · simp [hs] at hSome
  hNonEmpty := by
    simp [binarySupport]
  hNodup := hNodup
  h_scalars_match := h_scalars_match
  h_formal_eq_honest := by
    intro R
    exact binarySupport_formalDivisorOfList_eq_honestDivisorCoeffs
      stmt wit hk h_binary msg h_degE_eq R
  h_target_on_curve := h_target_on_curve
  h_bases_on_curve := h_bases_on_curve

end MAProverMsg.IsHonestForBinaryScaled

/-- A valid binary witness with an affine target has at least one selected
    base, so its binary support has length at least two. -/
private theorem binarySupport_length_ge_two
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points) :
    2 ≤ (binarySupport stmt wit hk h_binary).length := by
  classical
  let selected : List (ZMod E.q × ZMod E.q) :=
    (List.finRange wit.k).filterMap (fun i =>
      if wit.scalars i = 1 then
        some (stmt.bases (Fin.cast hk.symm i))
      else
        none)
  by_contra hlt
  have hLen_le : (binarySupport stmt wit hk h_binary).length ≤ 1 := by
    omega
  have hLen_eq :
      (binarySupport stmt wit hk h_binary).length = selected.length + 1 := by
    simp [binarySupport, selected]
  have hSelected_len : selected.length = 0 := by
    rw [hLen_eq] at hLen_le
    omega
  have hSelected_nil : selected = [] := List.length_eq_zero_iff.mp hSelected_len
  have h_no_one : ∀ i : Fin wit.k, wit.scalars i ≠ 1 := by
    intro i hi
    have hmem : stmt.bases (Fin.cast hk.symm i) ∈ selected := by
      change stmt.bases (Fin.cast hk.symm i) ∈
        (List.finRange wit.k).filterMap (fun i =>
          if wit.scalars i = 1 then
            some (stmt.bases (Fin.cast hk.symm i))
          else
            none)
      rw [List.mem_filterMap]
      exact ⟨i, List.mem_finRange i, by simp [hi]⟩
    rw [hSelected_nil] at hmem
    simp at hmem
  have h_zero : ∀ i : Fin wit.k, wit.scalars i = 0 := by
    intro i
    exact (h_binary i).resolve_right (h_no_one i)
  have h_weighted_zero :
      ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
        (fun i => ECPoint.zsmul E (wit.scalars i)
          (ECPoint.affine E
            (stmt.bases (Fin.cast hk.symm i)).1
            (stmt.bases (Fin.cast hk.symm i)).2)) = 0 := by
    rw [ECPoint.weightedSum]
    apply Finset.sum_eq_zero
    intro i _hi
    simp [h_zero i]
  have hRel := relDlog_weightedSum_with_hk stmt wit hk hValid
  have hTarget_zero :
      ECPoint.affine E stmt.target.1 stmt.target.2 = (0 : ECPoint E) := by
    rw [hRel, h_weighted_zero]
  have hNegTarget_zero :
      ECPoint.affine E stmt.target.1 (-stmt.target.2) = (0 : ECPoint E) := by
    have h := congrArg Neg.neg hTarget_zero
    rw [ECPoint.affine_neg E stmt.target.1 stmt.target.2, neg_zero] at h
    exact h
  have hNegTarget_ne_zero :
      ECPoint.affine E stmt.target.1 (-stmt.target.2) ≠ (0 : ECPoint E) := by
    have h_aff :
        ECPoint.affine E (stmt.target.1, -stmt.target.2).1
            (stmt.target.1, -stmt.target.2).2 ≠ (0 : ECPoint E) := by
      rw [ECPoint.affine_eq_affineOfMem E h_target_on_curve]
      unfold ECPoint.affineOfMem ECPoint.affineOfEqn
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    simpa using h_aff
  exact hNegTarget_ne_zero hNegTarget_zero

/-- End-to-end binary completeness for the maximal admissible set.

This user-facing wrapper derives the binary honesty structure directly
from the witness support and then applies the chord-chain `admSetMax`
completeness theorem. -/
theorem ma_completeness_binary
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       Landmark.eagenBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0_singletons E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let h_honest : MAProverMsg.IsHonestForBinary E msg stmt wit hk hkm :=
    MAProverMsg.IsHonestForBinary.fromWitness E stmt wit hk msg hkm
      h_binary hValid h_toD_eq h_degE_eq h_scalars_match
      h_target_on_curve h_bases_on_curve hNodup
  have hLen : 2 ≤ h_honest.Ps.length := by
    simpa [h_honest] using
      binarySupport_length_ge_two stmt wit hk h_binary hValid
        h_target_on_curve
  have hChain :
      Landmark.IteratedLevelStepCombineExtras E h_honest.Ps.length
        (Landmark.level0_singletons E h_honest.Ps) := by
    simpa [h_honest] using h_chain
  exact ma_completeness_binary_chain_admSetMax
    E stmt msg wit hk hkm h_admSetMax h_honest hLen hChain
    hValid hDeg hDegK

/-- End-to-end binary completeness for Parker normalization. -/
theorem ma_completeness_binary_admSetParker
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hParker_pre :
      (Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).a.coeff 1 ≠ 0)
    (h_toD_eq : msg.toD =
       ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a.coeff 1)⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0_singletons E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetParker : stmt.admSet = admSetParker (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let c : ZMod E.q :=
    ((Landmark.eagenBuild_singletons E
      (binarySupport stmt wit hk h_binary)).a.coeff 1)⁻¹
  have hc_ne : c ≠ 0 := by
    exact inv_ne_zero hParker_pre
  let h_honest : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm :=
    MAProverMsg.IsHonestForBinaryScaled.fromWitness E stmt wit hk msg hkm
      c hc_ne h_binary hValid h_toD_eq h_degE_eq h_scalars_match
      h_target_on_curve h_bases_on_curve hNodup
  have hLen : 2 ≤ h_honest.Ps.length := by
    simpa [h_honest] using
      binarySupport_length_ge_two stmt wit hk h_binary hValid
        h_target_on_curve
  have hChain :
      Landmark.IteratedLevelStepCombineExtras E h_honest.Ps.length
        (Landmark.level0_singletons E h_honest.Ps) := by
    simpa [h_honest] using h_chain
  have hc_eq :
      h_honest.c =
        ((Landmark.eagenBuild_singletons E h_honest.Ps).a.coeff 1)⁻¹ := by
    simp [h_honest, MAProverMsg.IsHonestForBinaryScaled.fromWitness, c]
  have hPre :
      (Landmark.eagenBuild_singletons E h_honest.Ps).a.coeff 1 ≠ 0 := by
    simpa [h_honest] using hParker_pre
  exact ma_completeness_binary_chain_admSetParker
    E stmt msg wit hk hkm h_admSetParker h_honest hc_eq hPre
    hLen hChain hValid hDeg hDegK

/-- End-to-end binary completeness for Eagen normalization. -/
theorem ma_completeness_binary_admSetEagen
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hEagen_pre :
      (Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).a.coeff 0 ≠ 0)
    (h_toD_eq : msg.toD =
       ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a.coeff 0)⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0_singletons E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetEagen : stmt.admSet = admSetEagen (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let c : ZMod E.q :=
    ((Landmark.eagenBuild_singletons E
      (binarySupport stmt wit hk h_binary)).a.coeff 0)⁻¹
  have hc_ne : c ≠ 0 := by
    exact inv_ne_zero hEagen_pre
  let h_honest : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm :=
    MAProverMsg.IsHonestForBinaryScaled.fromWitness E stmt wit hk msg hkm
      c hc_ne h_binary hValid h_toD_eq h_degE_eq h_scalars_match
      h_target_on_curve h_bases_on_curve hNodup
  have hLen : 2 ≤ h_honest.Ps.length := by
    simpa [h_honest] using
      binarySupport_length_ge_two stmt wit hk h_binary hValid
        h_target_on_curve
  have hChain :
      Landmark.IteratedLevelStepCombineExtras E h_honest.Ps.length
        (Landmark.level0_singletons E h_honest.Ps) := by
    simpa [h_honest] using h_chain
  have hc_eq :
      h_honest.c =
        ((Landmark.eagenBuild_singletons E h_honest.Ps).a.coeff 0)⁻¹ := by
    simp [h_honest, MAProverMsg.IsHonestForBinaryScaled.fromWitness, c]
  have hPre :
      (Landmark.eagenBuild_singletons E h_honest.Ps).a.coeff 0 ≠ 0 := by
    simpa [h_honest] using hEagen_pre
  exact ma_completeness_binary_chain_admSetEagen
    E stmt msg wit hk hkm h_admSetEagen h_honest hc_eq hPre
    hLen hChain hValid hDeg hDegK

/-- End-to-end binary completeness for hash normalization. -/
theorem ma_completeness_binary_admSetHash
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (r : ℕ → ZMod E.q)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hHash_pre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a,
         (Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).b) ≠ 0)
    (h_toD_eq : msg.toD =
       (admSetHashInner r
          ((Landmark.eagenBuild_singletons E
            (binarySupport stmt wit hk h_binary)).a,
           (Landmark.eagenBuild_singletons E
            (binarySupport stmt wit hk h_binary)).b))⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_chain : Landmark.IteratedLevelStepCombineExtras E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0_singletons E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetHash : stmt.admSet = admSetHash r)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let c : ZMod E.q :=
    (admSetHashInner r
      ((Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).a,
       (Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).b))⁻¹
  have hc_ne : c ≠ 0 := by
    exact inv_ne_zero hHash_pre
  let h_honest : MAProverMsg.IsHonestForBinaryScaled E msg stmt wit hk hkm :=
    MAProverMsg.IsHonestForBinaryScaled.fromWitness E stmt wit hk msg hkm
      c hc_ne h_binary hValid h_toD_eq h_degE_eq h_scalars_match
      h_target_on_curve h_bases_on_curve hNodup
  have hLen : 2 ≤ h_honest.Ps.length := by
    simpa [h_honest] using
      binarySupport_length_ge_two stmt wit hk h_binary hValid
        h_target_on_curve
  have hChain :
      Landmark.IteratedLevelStepCombineExtras E h_honest.Ps.length
        (Landmark.level0_singletons E h_honest.Ps) := by
    simpa [h_honest] using h_chain
  have hc_eq :
      h_honest.c =
        (admSetHashInner r
          ((Landmark.eagenBuild_singletons E h_honest.Ps).a,
            (Landmark.eagenBuild_singletons E h_honest.Ps).b))⁻¹ := by
    simp [h_honest, MAProverMsg.IsHonestForBinaryScaled.fromWitness, c]
  have hPre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E h_honest.Ps).a,
          (Landmark.eagenBuild_singletons E h_honest.Ps).b) ≠ 0 := by
    simpa [h_honest] using hHash_pre
  exact ma_completeness_binary_chain_admSetHash
    E stmt msg wit hk hkm r h_admSetHash h_honest hc_eq hPre
    hLen hChain hValid hDeg hDegK

/-- End-to-end binary completeness for the maximal admissible set, with the
    level-chain certificate supplied by the computable point skeleton. -/
theorem ma_completeness_binary_point_certificate
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       Landmark.eagenBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_point_chain : Landmark.IteratedPointChordCase E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0SingletonPoints E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_chain :
      Landmark.IteratedLevelStepCombineExtras E
        (binarySupport stmt wit hk h_binary).length
        (Landmark.level0_singletons E
          (binarySupport stmt wit hk h_binary)) :=
    Landmark.iteratedLevelStepCombineExtras_of_level0SingletonPoints
      E (binarySupport stmt wit hk h_binary) h_point_chain
  exact ma_completeness_binary E stmt wit hk msg hkm h_binary hValid
    h_toD_eq h_degE_eq h_scalars_match h_target_on_curve h_bases_on_curve
    hNodup h_chain h_admSetMax hDeg hDegK

/-- Parker-normalized binary completeness with a computable point-chain
    certificate. -/
theorem ma_completeness_binary_admSetParker_point_certificate
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hParker_pre :
      (Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).a.coeff 1 ≠ 0)
    (h_toD_eq : msg.toD =
       ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a.coeff 1)⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_point_chain : Landmark.IteratedPointChordCase E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0SingletonPoints E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetParker : stmt.admSet = admSetParker (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_chain :
      Landmark.IteratedLevelStepCombineExtras E
        (binarySupport stmt wit hk h_binary).length
        (Landmark.level0_singletons E
          (binarySupport stmt wit hk h_binary)) :=
    Landmark.iteratedLevelStepCombineExtras_of_level0SingletonPoints
      E (binarySupport stmt wit hk h_binary) h_point_chain
  exact ma_completeness_binary_admSetParker E stmt wit hk msg hkm
    h_binary hValid hParker_pre h_toD_eq h_degE_eq h_scalars_match
    h_target_on_curve h_bases_on_curve hNodup h_chain h_admSetParker
    hDeg hDegK

/-- Eagen-normalized binary completeness with a computable point-chain
    certificate. -/
theorem ma_completeness_binary_admSetEagen_point_certificate
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hEagen_pre :
      (Landmark.eagenBuild_singletons E
        (binarySupport stmt wit hk h_binary)).a.coeff 0 ≠ 0)
    (h_toD_eq : msg.toD =
       ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a.coeff 0)⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_point_chain : Landmark.IteratedPointChordCase E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0SingletonPoints E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetEagen : stmt.admSet = admSetEagen (q := E.q))
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_chain :
      Landmark.IteratedLevelStepCombineExtras E
        (binarySupport stmt wit hk h_binary).length
        (Landmark.level0_singletons E
          (binarySupport stmt wit hk h_binary)) :=
    Landmark.iteratedLevelStepCombineExtras_of_level0SingletonPoints
      E (binarySupport stmt wit hk h_binary) h_point_chain
  exact ma_completeness_binary_admSetEagen E stmt wit hk msg hkm
    h_binary hValid hEagen_pre h_toD_eq h_degE_eq h_scalars_match
    h_target_on_curve h_bases_on_curve hNodup h_chain h_admSetEagen
    hDeg hDegK

/-- Hash-normalized binary completeness with a computable point-chain
    certificate. -/
theorem ma_completeness_binary_admSetHash_point_certificate
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (r : ℕ → ZMod E.q)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (hValid : relDlog E stmt wit)
    (hHash_pre :
      admSetHashInner r
        ((Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).a,
         (Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary)).b) ≠ 0)
    (h_toD_eq : msg.toD =
       (admSetHashInner r
          ((Landmark.eagenBuild_singletons E
            (binarySupport stmt wit hk h_binary)).a,
           (Landmark.eagenBuild_singletons E
            (binarySupport stmt wit hk h_binary)).b))⁻¹ •
        Landmark.eagenBuild_singletons E
          (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hNodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_point_chain : Landmark.IteratedPointChordCase E
                  (binarySupport stmt wit hk h_binary).length
                  (Landmark.level0SingletonPoints E
                    (binarySupport stmt wit hk h_binary)))
    (h_admSetHash : stmt.admSet = admSetHash r)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_chain :
      Landmark.IteratedLevelStepCombineExtras E
        (binarySupport stmt wit hk h_binary).length
        (Landmark.level0_singletons E
          (binarySupport stmt wit hk h_binary)) :=
    Landmark.iteratedLevelStepCombineExtras_of_level0SingletonPoints
      E (binarySupport stmt wit hk h_binary) h_point_chain
  exact ma_completeness_binary_admSetHash E stmt wit hk msg hkm r
    h_binary hValid hHash_pre h_toD_eq h_degE_eq h_scalars_match
    h_target_on_curve h_bases_on_curve hNodup h_chain h_admSetHash
    hDeg hDegK

end Divisor
