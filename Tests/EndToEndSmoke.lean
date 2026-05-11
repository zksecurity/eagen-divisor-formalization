/-
  Tests/EndToEndSmoke.lean

  Concrete end-to-end smoke test for binary MA completeness.
-/
import Divisor.IsHonestForBinary

open Polynomial Finset
open Classical

namespace Divisor
namespace EndToEndSmoke

private def pointsF17 : Finset (ZMod 17 × ZMod 17) :=
  (Finset.univ : Finset (ZMod 17 × ZMod 17)).filter
    (fun p => p.2 ^ 2 = p.1 ^ 3 + (0 : ZMod 17) * p.1 + (1 : ZMod 17))

private def E17 : ECSetup where
  q := 17
  hq_prime := by decide
  curveA := 0
  curveB := 1
  points := pointsF17
  hOnCurve := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  hComplete := by
    intro x y h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (x, y), h⟩
  hDisc := by native_decide
  numPoints := pointsF17.card + 1
  hNumPoints := rfl
  hq_ge := by decide

private def stmt : DlogStatement E17.q where
  k := 3
  degBound := 8
  bases := fun
    | ⟨0, _⟩ => (1, 11)
    | ⟨1, _⟩ => (0, 1)
    | ⟨2, _⟩ => (0, 16)
  target := (1, 11)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit : DlogWitness E17.q where
  k := 3
  scalars := fun _ => 1
  degBound := 8
  hRange := by
    intro i
    norm_num

private theorem hk : stmt.k = wit.k := rfl

private theorem hBinary :
    ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1 := by
  intro i
  right
  rfl

private def support : List (ZMod E17.q × ZMod E17.q) :=
  [(1, 6), (1, 11), (0, 1), (0, 16)]

private theorem binarySupport_eq_support :
    binarySupport stmt wit hk hBinary = support := by
  native_decide

private noncomputable def msg : MAProverMsg E17.q where
  k := 3
  m := fun _ => 1
  polyA := (Landmark.eagenBuild_singletons E17
    (binarySupport stmt wit hk hBinary)).a
  polyB := (Landmark.eagenBuild_singletons E17
    (binarySupport stmt wit hk hBinary)).b

private theorem hkm : stmt.k = msg.k := rfl

private theorem aff_1_6 :
    ECPoint.affine E17 (1 : ZMod 17) (6 : ZMod 17) =
      .some (by native_decide :
        E17.toW.toAffine.Nonsingular (1 : ZMod 17) (6 : ZMod 17)) := by
  rw [ECPoint.affine, dif_pos (by native_decide)]

private theorem aff_1_11 :
    ECPoint.affine E17 (1 : ZMod 17) (11 : ZMod 17) =
      .some (by native_decide :
        E17.toW.toAffine.Nonsingular (1 : ZMod 17) (11 : ZMod 17)) := by
  rw [ECPoint.affine, dif_pos (by native_decide)]

private theorem aff_0_1 :
    ECPoint.affine E17 (0 : ZMod 17) (1 : ZMod 17) =
      .some (by native_decide :
        E17.toW.toAffine.Nonsingular (0 : ZMod 17) (1 : ZMod 17)) := by
  rw [ECPoint.affine, dif_pos (by native_decide)]

private theorem aff_0_16 :
    ECPoint.affine E17 (0 : ZMod 17) (16 : ZMod 17) =
      .some (by native_decide :
        E17.toW.toAffine.Nonsingular (0 : ZMod 17) (16 : ZMod 17)) := by
  rw [ECPoint.affine, dif_pos (by native_decide)]

private theorem support_degE :
    (Landmark.eagenBuild_singletons E17 support).degE = support.length := by
  simp only [support, Landmark.eagenBuild_singletons, Landmark.level0_singletons,
    List.map_cons, List.map_nil, Landmark.levelInitSingleton]
  rw [aff_1_6, aff_1_11, aff_0_1, aff_0_16]
  have hpair1 : (6 : ZMod 17) = -(11 : ZMod 17) := by native_decide
  have hpair2 : (1 : ZMod 17) = -(16 : ZMod 17) := by native_decide
  simp [Landmark.iterate, Landmark.level_step, Landmark.EagenAccum.combine,
    Landmark.EagenAccum.combine_oo, Landmark.EagenAccum.combine_vertical,
    mulCoordRingElt, CoordRingElt.divLin, CoordRingElt.degE, hpair1, hpair2]
  rw [Polynomial.mul_divByMonic_cancel_left _
    (Polynomial.monic_X_add_C (16 : ZMod E17.q))]
  rw [Polynomial.mul_divByMonic_cancel_left _
    (Polynomial.monic_X : (Polynomial.X : (ZMod E17.q)[X]).Monic)]
  have hnat :
      ((Polynomial.X + Polynomial.C (16 : ZMod E17.q)) * Polynomial.X).natDegree = 2 := by
    rw [(Polynomial.monic_X_add_C (16 : ZMod E17.q)).natDegree_mul'
      (Polynomial.monic_X : (Polynomial.X : (ZMod E17.q)[X]).Monic).ne_zero]
    simp
  rw [hnat]
  norm_num

private theorem hValid : relDlog E17 stmt wit := by
  refine ⟨hk, ?_⟩
  simp [stmt, wit, ECPoint.weightedSum]
  rw [Fin.sum_univ_three]
  rw [show (16 : ZMod 17) = -(1 : ZMod 17) by native_decide]
  rw [← ECPoint.affine_neg E17 (0 : ZMod 17) (1 : ZMod 17)]
  abel

example :
    ((E17.points ×ˢ E17.points).filter
        (fun p : (ZMod E17.q × ZMod E17.q) × (ZMod E17.q × ZMod E17.q) =>
          ¬ maVerifierAccepts E17 stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine := by
  have hSupportLen : (binarySupport stmt wit hk hBinary).length = 4 := by
    native_decide
  have hToD : msg.toD = Landmark.eagenBuild_singletons E17
      (binarySupport stmt wit hk hBinary) := rfl
  have hDegE : msg.toD.degE = (binarySupport stmt wit hk hBinary).length := by
    rw [hToD, binarySupport_eq_support, support_degE]
  have hScalars : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E17.q)) := by
    intro i
    fin_cases i <;> rfl
  have hTargetOn : (stmt.target.1, -stmt.target.2) ∈ E17.points := by
    native_decide
  have hBasesOn : ∀ i, stmt.bases i ∈ E17.points := by
    intro i
    fin_cases i <;> native_decide
  have hNodup : (binarySupport stmt wit hk hBinary).Nodup := by
    native_decide
  have hPointChain : Landmark.IteratedPointChordCase E17
      (binarySupport stmt wit hk hBinary).length
      (Landmark.level0SingletonPoints E17
        (binarySupport stmt wit hk hBinary)) := by
    rw [binarySupport_eq_support]
    native_decide
  have hDeg : msg.toD.degE ≤ wit.degBound := by
    rw [hDegE, hSupportLen]
    norm_num [wit]
  have hDegK : msg.toD.degE ≤ stmt.degBound := by
    rw [hDegE, hSupportLen]
    norm_num [stmt]
  exact ma_completeness_binary_point_certificate E17 stmt wit hk msg hkm
    hBinary hValid hToD hDegE hScalars hTargetOn hBasesOn hNodup hPointChain
    rfl hDeg hDegK

end EndToEndSmoke
end Divisor
