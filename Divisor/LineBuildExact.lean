/-
  Divisor/LineBuildExact.lean — the line build is correct for every
  on-curve support multiset summing to zero.

  * `exactInvList_iterate`: `ExactInv` is carried through every level of
    `iterate` (no `Nodup`, no per-level side conditions).
  * `lineBuild_singletons_exact`: for on-curve `Ps` with
    `sumOnE Ps = 0`, the built `D` is nonzero, generates
    `∏_{P ∈ Ps} ⟨P⟩`, has `ordAt = Ps.count` at every rational point,
    splits over `E`, and has `degE = Ps.length`.
  * `lineBuild_singletons_divisor_exact`: `divisorOfD = formalDivisorOfList`.

  Repeated points, tangents, 2-torsion and chords meeting the curve
  again at a support point are all allowed.
-/
import Divisor.LineBuildExact.Combine

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Divisor.LineAccum.Exact

variable (E : ECSetup)

/-! ## Lists of accumulators -/

/-- Pointwise `ExactInv` between absorbed blocks and accumulators. -/
def ExactInvList (xss : List (List (ZMod E.q × ZMod E.q))) (accs : List (Accum E)) : Prop :=
  List.Forall₂ (ExactInv E) xss accs

theorem exactInvList_level0_singletons (Ps : List (ZMod E.q × ZMod E.q))
    (hPs : ∀ P ∈ Ps, P ∈ E.points) :
    ExactInvList E (Ps.map (fun P => [P])) (level0_singletons E Ps) := by
  induction Ps with
  | nil => exact List.Forall₂.nil
  | cons P rest ih =>
    exact List.Forall₂.cons (exactInv_levelInitSingleton E (hPs P List.mem_cons_self))
      (ih fun Q hQ => hPs Q (List.mem_cons_of_mem P hQ))

/-- One level of pairing preserves `ExactInv`, unconditionally. -/
theorem exactInvList_level_step :
    ∀ (xss : List (List (ZMod E.q × ZMod E.q))) (accs : List (Accum E)),
      ExactInvList E xss accs → ExactInvList E (pairUp xss) (level_step E accs)
  | [], [], _ => List.Forall₂.nil
  | [_], [_], h => h
  | xs :: ys :: rest, a :: b :: accs, h => by
    obtain ⟨ha, h'⟩ := List.forall₂_cons.mp h
    obtain ⟨hb, hrest⟩ := List.forall₂_cons.mp h'
    exact List.Forall₂.cons (exactInv_combine E ha hb)
      (exactInvList_level_step rest accs hrest)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | [_], _ :: _ :: _, h => by
    obtain ⟨-, h'⟩ := List.forall₂_cons.mp h; cases h'
  | _ :: _ :: _, [_], h => by
    obtain ⟨-, h'⟩ := List.forall₂_cons.mp h; cases h'

/-- **Iterate preservation**: every level keeps `ExactInv`. -/
theorem exactInvList_iterate (n : ℕ) (xss : List (List (ZMod E.q × ZMod E.q)))
    (accs : List (Accum E)) (h : ExactInvList E xss accs) :
    ExactInvList E (pairUpN n xss) (iterate E n accs) := by
  induction n generalizing xss accs with
  | zero => exact h
  | succ n ih =>
    have hlen : xss.length = accs.length := List.Forall₂.length_eq h
    show ExactInvList E (if xss.length ≤ 1 then xss else pairUpN n (pairUp xss))
      (if accs.length ≤ 1 then accs else iterate E n (level_step E accs))
    by_cases hL : accs.length ≤ 1
    · rw [if_pos hL, if_pos (hlen ▸ hL)]; exact h
    · rw [if_neg hL, if_neg (hlen ▸ hL)]
      exact ih _ _ (exactInvList_level_step E xss accs h)

/-- The final accumulator of the singleton line build is exact for the
whole support list. -/
theorem exactInv_lineBuild_singletons (Ps : List (ZMod E.q × ZMod E.q))
    (hPs : ∀ P ∈ Ps, P ∈ E.points) (hne : Ps ≠ []) :
    ∃ a : Accum E, iterate E Ps.length (level0_singletons E Ps) = [a] ∧ ExactInv E Ps a := by
  have h := exactInvList_iterate E Ps.length _ _ (exactInvList_level0_singletons E Ps hPs)
  have hlen := List.Forall₂.length_eq h
  have hle : (iterate E Ps.length (level0_singletons E Ps)).length ≤ 1 :=
    iterate_length_le_one_of_fuel_geq E Ps.length _ (by simp [level0_singletons])
  have hflat : (pairUpN Ps.length (Ps.map (fun P => [P]))).flatten = Ps := by
    rw [pairUpN_flatten, map_singleton_flatten]
  have hpos : (pairUpN Ps.length (Ps.map (fun P => [P]))).length ≠ 0 := by
    intro h0
    rw [List.length_eq_zero_iff.mp h0] at hflat
    exact hne hflat.symm
  have hone : (pairUpN Ps.length (Ps.map (fun P => [P]))).length = 1 := by omega
  have hsingle := pairUpN_eq_singleton_of_len_one _ _ hone
  rw [map_singleton_flatten] at hsingle
  rw [hsingle] at h
  match hiter : iterate E Ps.length (level0_singletons E Ps), h with
  | [a], h => exact ⟨a, rfl, (List.forall₂_cons.mp h).1⟩

/-! ## The final specification -/

/-- **The singleton line build is exact for every on-curve support
multiset summing to zero.** No `Nodup`, no per-level side conditions:
the result is nonzero, generates `∏_{P ∈ Ps} ⟨P⟩`, has order
`Ps.count P` at every rational point, splits over `E`, and has
`degE = Ps.length`. -/
theorem lineBuild_singletons_exact (Ps : List (ZMod E.q × ZMod E.q))
    (hPs : ∀ P ∈ Ps, P ∈ E.points) (hSum : sumOnE E Ps = 0) (hne : Ps ≠ []) :
    ¬ ((lineBuild_singletons E Ps).a = 0 ∧ (lineBuild_singletons E Ps).b = 0) ∧
    Ideal.span {(lineBuild_singletons E Ps).toCoordinateRing E} = listIdeal E Ps ∧
    (∀ P ∈ E.points, ordAt E (lineBuild_singletons E Ps) P = Ps.count P) ∧
    splitsOnE E (lineBuild_singletons E Ps) ∧
    (lineBuild_singletons E Ps).degE = Ps.length := by
  obtain ⟨a, hiter, ha⟩ := exactInv_lineBuild_singletons E Ps hPs hne
  have hD : lineBuild_singletons E Ps = a.poly := by
    show (match iterate E Ps.length (level0_singletons E Ps) with
          | [a] => a.poly
          | _ => { a := 1, b := 0 }) = a.poly
    rw [hiter]
  have hpt : a.point = 0 := ha.1.trans hSum
  have hspan : Ideal.span {a.poly.toCoordinateRing E} = listIdeal E Ps := by
    rw [ha.2.1, hpt, resList_zero, List.append_nil]
  have hdeg : (normPoly E a.poly).natDegree = Ps.length := by
    rw [ha.2.2, hpt, if_pos rfl, add_zero]
  have hnz := ha.not_both_zero
  rw [hD]
  refine ⟨hnz, hspan, fun P hP => ordAt_eq_count_of_span_eq_listIdeal E _ _ hPs hspan hP,
    splitsOnE_of_sum_ordAt_eq E _ hnz ?_, ?_⟩
  · rw [sum_ordAt_eq_length_of_span_eq_listIdeal E _ _ hPs hspan, hdeg]
  · rw [← normPoly_natDegree_eq, hdeg]

/-- **Divisor identity**: the line build realises the formal divisor
`Σ_{P ∈ Ps} (P) − |Ps|·(∞)`, with multiplicities. -/
theorem lineBuild_singletons_divisor_exact (Ps : List (ZMod E.q × ZMod E.q))
    (hPs : ∀ P ∈ Ps, P ∈ E.points) (hSum : sumOnE E Ps = 0) (hne : Ps ≠ []) :
    ∀ R : ECPoint E,
      divisorOfD E (lineBuild_singletons E Ps) R = formalDivisorOfList E Ps R := by
  obtain ⟨-, -, hord, -, hdeg⟩ := lineBuild_singletons_exact E Ps hPs hSum hne
  intro R
  rcases R with _ | ⟨x, y, hns⟩
  · show -((normPoly E (lineBuild_singletons E Ps)).natDegree : ℤ) = -(Ps.length : ℤ)
    rw [normPoly_natDegree_eq, hdeg]
  · have hmem : (x, y) ∈ E.points :=
      E.hComplete x y ((E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns))
    show (ordAt E (lineBuild_singletons E Ps) (x, y) : ℤ) =
      ((Ps.filter (fun P => P = (x, y))).length : ℤ)
    rw [hord _ hmem, List.count_eq_length_filter]
    congr 2
    apply List.filter_congr
    intro P _
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]

end Divisor.LineAccum.Exact
