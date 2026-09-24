/-
  Divisor/HonestSupport.lean — the point list the honest prover builds.

  For a witness with nonnegative scalars `nᵢ`, the honest divisor is
  `(−P) + Σ nᵢ·(Bᵢ) − (1 + Σ nᵢ)·(O)`. `honestSupport` lists its affine
  part as a multiset: `−P` followed by each base `Bᵢ` repeated `nᵢ`
  times. This file proves that the list

  * counts every point exactly as `honestDivisorCoeffs` does,
  * has length `1 + Σ nᵢ`,
  * lies on the curve, and
  * sums to zero on `E` under the discrete-log relation.
-/
import Divisor.LineBuild
import Divisor.Protocol

open Polynomial

namespace Divisor

variable {E : ECSetup}

/-- `−P` followed by each base `Bᵢ` repeated `nᵢ` times (negative scalars
    contribute nothing; the prover theorems assume `0 ≤ nᵢ`). -/
def honestSupport (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) : List (ZMod E.q × ZMod E.q) :=
  (stmt.target.1, -stmt.target.2) ::
    (List.finRange wit.k).flatMap (fun i =>
      List.replicate (wit.scalars i).toNat (stmt.bases (Fin.cast hk.symm i)))

section

variable (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)

theorem honestSupport_length :
    (honestSupport stmt wit hk).length = 1 + ∑ i, (wit.scalars i).toNat := by
  simp only [honestSupport, List.length_cons, List.length_flatMap, List.length_replicate]
  rw [add_comm, Fin.sum_univ_def]

theorem honestSupport_count (Q : ZMod E.q × ZMod E.q) :
    (honestSupport stmt wit hk).count Q =
      (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ i, if stmt.bases (Fin.cast hk.symm i) = Q then (wit.scalars i).toNat else 0 := by
  simp only [honestSupport, List.count_cons, List.count_flatMap, Fin.sum_univ_def]
  rw [add_comm]
  congr 1
  · by_cases h : Q = (stmt.target.1, -stmt.target.2)
    · simp [h]
    · have h' : ((stmt.target.1, -stmt.target.2) == Q) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp only [h', h, Bool.false_eq_true, if_false]
  · congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [List.count_replicate]

theorem honestSupport_on_curve
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points) :
    ∀ P ∈ honestSupport stmt wit hk, P ∈ E.points := by
  intro P hP
  simp only [honestSupport, List.mem_cons, List.mem_flatMap, List.mem_replicate] at hP
  rcases hP with rfl | ⟨i, _, _, rfl⟩
  · exact h_target_on_curve
  · exact h_bases_on_curve _

private theorem sumOnE_replicate (n : ℕ) {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    LineAccum.sumOnE E (List.replicate n P) = n • ECPoint.affine E P.1 P.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, LineAccum.sumOnE_cons E hP, ih,
      ← ECPoint.affine_eq_affineOfMem E hP, succ_nsmul, add_comm]

private theorem sumOnE_flatMap {ι : Type*} (l : List ι)
    (f : ι → List (ZMod E.q × ZMod E.q)) :
    LineAccum.sumOnE E (l.flatMap f) = (l.map fun i => LineAccum.sumOnE E (f i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.flatMap_cons, LineAccum.sumOnE_append, ih, List.map_cons,
      List.sum_cons]

/-- Under the discrete-log relation with nonnegative scalars, the honest
    support sums to zero on `E`. -/
theorem honestSupport_sumOnE_eq_zero (hValid : relDlog E stmt wit)
    (hNonneg : ∀ i, 0 ≤ wit.scalars i)
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points) :
    LineAccum.sumOnE E (honestSupport stmt wit hk) = 0 := by
  obtain ⟨hk', hRel⟩ := hValid
  obtain rfl : hk' = hk := rfl
  rw [honestSupport, LineAccum.sumOnE_cons E h_target_on_curve,
    ← ECPoint.affine_eq_affineOfMem E h_target_on_curve, ← ECPoint.affine_neg, hRel,
    sumOnE_flatMap]
  simp only [ECPoint.weightedSum, Fin.sum_univ_def]
  rw [neg_add_eq_zero]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [sumOnE_replicate _ (h_bases_on_curve _), ECPoint.zsmul_def,
    ← natCast_zsmul, Int.toNat_of_nonneg (hNonneg i)]

/-- The support's count at `Q` is the honest divisor's coefficient at `Q`. -/
theorem honestSupport_count_eq (hNonneg : ∀ i, 0 ≤ wit.scalars i)
    (Q : ZMod E.q × ZMod E.q) :
    ((honestSupport stmt wit hk).count Q : ℤ) =
      (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ i ∈ Finset.univ.filter (fun i => stmt.bases i = Q), wit.scalars (hk ▸ i) := by
  rw [honestSupport_count, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Nat.cast_sum, Finset.sum_filter]
  congr 1
  refine Finset.sum_equiv (finCongr hk.symm) (fun _ => by simp) fun i _ => ?_
  have hcast : hk ▸ Fin.cast hk.symm i = i := by
    rw [eqRec_eq_cast, ← Fin.cast_eq_cast hk, Fin.cast_cast, Fin.cast_eq_self]
  simp only [finCongr_apply, hcast]
  split_ifs <;> simp [Int.toNat_of_nonneg (hNonneg i)]

end

end Divisor
