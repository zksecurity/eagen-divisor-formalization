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

end Divisor
