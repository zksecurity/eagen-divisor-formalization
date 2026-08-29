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

private theorem h_binary :
    ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1 := by
  intro i
  right
  rfl

private def support : List (ZMod E17.q × ZMod E17.q) :=
  [(1, 6), (1, 11), (0, 1), (0, 16)]

private theorem binarySupport_eq_support :
    binarySupport stmt wit hk h_binary = support := by
  native_decide

private noncomputable def msg : MAProverMsg E17.q stmt.k where
  m := fun _ => 1
  polyA := (LineAccum.lineBuild_singletons E17
    (binarySupport stmt wit hk h_binary)).a
  polyB := (LineAccum.lineBuild_singletons E17
    (binarySupport stmt wit hk h_binary)).b

private theorem aff_1_6 :
    ECPoint.affine E17 (1 : ZMod E17.q) (6 : ZMod E17.q) =
      .some _ _ (E17.equation_iff_nonsingular.mp
        ((E17.equation_iff (1 : ZMod E17.q) (6 : ZMod E17.q)).mpr
          (by native_decide))) :=
  ECPoint.affine_of_nonsingular E17 _

private theorem aff_1_11 :
    ECPoint.affine E17 (1 : ZMod E17.q) (11 : ZMod E17.q) =
      .some _ _ (E17.equation_iff_nonsingular.mp
        ((E17.equation_iff (1 : ZMod E17.q) (11 : ZMod E17.q)).mpr
          (by native_decide))) :=
  ECPoint.affine_of_nonsingular E17 _

private theorem aff_0_1 :
    ECPoint.affine E17 (0 : ZMod E17.q) (1 : ZMod E17.q) =
      .some _ _ (E17.equation_iff_nonsingular.mp
        ((E17.equation_iff (0 : ZMod E17.q) (1 : ZMod E17.q)).mpr
          (by native_decide))) :=
  ECPoint.affine_of_nonsingular E17 _

private theorem aff_0_16 :
    ECPoint.affine E17 (0 : ZMod E17.q) (16 : ZMod E17.q) =
      .some _ _ (E17.equation_iff_nonsingular.mp
        ((E17.equation_iff (0 : ZMod E17.q) (16 : ZMod E17.q)).mpr
          (by native_decide))) :=
  ECPoint.affine_of_nonsingular E17 _

private theorem support_degE :
    (LineAccum.lineBuild_singletons E17 support).degE = support.length := by
  simp only [support, LineAccum.lineBuild_singletons, LineAccum.level0_singletons,
    List.map_cons, List.map_nil, LineAccum.levelInitSingleton]
  simp only [aff_1_6, aff_1_11, aff_0_1, aff_0_16]
  have hpair1 : (6 : ZMod E17.q) = -(11 : ZMod E17.q) := by native_decide
  have hpair2 : (1 : ZMod E17.q) = -(16 : ZMod E17.q) := by native_decide
  simp [LineAccum.iterate, LineAccum.level_step, LineAccum.Accum.combine,
    LineAccum.Accum.combine_oo, LineAccum.Accum.combine_vertical,
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

private theorem h_valid : relDlog E17 stmt wit := by
  refine ⟨hk, ?_⟩
  simp only [ECPoint.weightedSum]
  rw [show (Finset.univ : Finset (Fin wit.k))
      = {(⟨0, by decide⟩ : Fin wit.k), ⟨1, by decide⟩, ⟨2, by decide⟩} from
        by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [stmt, wit, ECPoint.zsmul, Fin.cast]
  try rw [show (16 : ZMod E17.q) = -(1 : ZMod E17.q) by native_decide]
  rw [← ECPoint.affine_neg E17 (0 : ZMod E17.q) (1 : ZMod E17.q)]
  abel

example :
    ((E17.points ×ˢ E17.points).filter
        (fun p : (ZMod E17.q × ZMod E17.q) × (ZMod E17.q × ZMod E17.q) =>
          ¬ maVerifierAccepts E17 stmt msg ⟨p.1, p.2⟩)).card
      ≤ (3 * numZeros E17 msg.toD + 4) * E17.numAffine := by
  have h_support_len : (binarySupport stmt wit hk h_binary).length = 4 := by
    native_decide
  have h_toD : msg.toD = LineAccum.lineBuild_singletons E17
      (binarySupport stmt wit hk h_binary) := rfl
  have h_deg_e : msg.toD.degE = (binarySupport stmt wit hk h_binary).length := by
    rw [h_toD, binarySupport_eq_support, support_degE]
  have h_scalars : ∀ i : Fin stmt.k,
      msg.m i = ((wit.scalars (hk ▸ i) : ZMod E17.q)) := by
    intro i
    fin_cases i <;> rfl
  have h_target_on : (stmt.target.1, -stmt.target.2) ∈ E17.points := by
    native_decide
  have h_bases_on : ∀ i, stmt.bases i ∈ E17.points := by
    intro i
    fin_cases i <;> native_decide
  have h_nodup : (binarySupport stmt wit hk h_binary).Nodup := by
    native_decide
  have h_point_chain : LineAccum.IteratedPointChordCase E17
      (binarySupport stmt wit hk h_binary).length
      (LineAccum.level0SingletonPoints E17
        (binarySupport stmt wit hk h_binary)) := by
    rw [binarySupport_eq_support]
    native_decide
  have h_deg : msg.toD.degE ≤ wit.degBound := by
    rw [h_deg_e, h_support_len]
    norm_num [wit]
  have h_deg_k : msg.toD.degE ≤ stmt.degBound := by
    rw [h_deg_e, h_support_len]
    norm_num [stmt]
  exact ma_completeness_binary_point_certificate E17 stmt wit hk msg
    h_binary h_valid h_toD h_deg_e h_scalars h_target_on h_bases_on h_nodup h_point_chain
    rfl h_deg h_deg_k

end EndToEndSmoke
end Divisor
