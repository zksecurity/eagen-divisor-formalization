/-
  Divisor/SafeSupport.lean

  Any-length binary completeness from a semantic general-position
  hypothesis on the support.

  The binary completeness chain is gated on the per-level combine
  certificate `IteratedLevelStepCombineExtras` (equivalently, via the
  computable skeleton, `IteratedPointChordCase`), discharged
  once-and-for-all only for the structured shapes (lengths 2/4 and
  the chord families at 4/6/8). This file discharges it for ANY
  support length from a single semantic hypothesis on the support:

    `SafePairs E Ps` — for every split `xs ++ ys` of every sublist of
    `Ps` (both halves nonempty), the pair of elliptic-curve sums
    `(Σ xs, Σ ys)` is chord-safe (`PointChordCase`): one of them is
    `O`, or they are inverse, or they have distinct `x`-coordinates,
    neither is 2-torsion, and the chord's third intersection avoids
    both.

  Why this shape: the accumulation tree of `lineBuild_singletons`
  (`iterate`/`level_step`) combines, at every level, blocks whose
  underlying support chunks are adjacent — so each combined pair of
  block sums is `(Σ xs, Σ ys)` for some split `xs ++ ys` that is a
  SUBLIST of `Ps`. `SafePairs` therefore covers every combine of
  every level of the committed schedule, stated semantically about
  subset sums of the support rather than about the accumulator run.

  The key bridging fact is `pointCombine_eq_add`: the computable
  point-skeleton combine agrees with mathlib's elliptic-curve group
  law on every pair of points, unconditionally. Block sums in the
  skeleton are therefore genuine subset sums.

  Deliverables:
  * `LineAccum.pointCombine_eq_add` — skeleton combine = group law.
  * `LineAccum.pointSum` — computable EC sum of a support list, with
    `pointSum_eq_sumOnE` (so certificates can be `native_decide`d).
  * `LineAccum.SafePairs` (semantic) and `LineAccum.SafePairsCert`
    (computable, `Decidable`), with `SafePairs.of_cert`.
  * `LineAccum.iteratedPointChordCase_of_safePairs` — the certificate
    for the whole accumulation, at any length. The headline built on
    it, `ma_completeness_binary_any_length`, lives in
    `Divisor/Headlines.lean`.

  Degenerate supports genuinely exist (2-torsion points in the
  support; block sums colliding as `B = −2A`), so an unconditional
  any-support statement is false; `SafePairs` is the mild
  general-position exclusion, decidable per instance.
-/
import Divisor.IsHonestForBinary
import Divisor.PointCombine

open Polynomial Classical

namespace Divisor.LineAccum

variable (E : ECSetup)

/-! ## Block bookkeeping: skeleton levels are chunk sums -/

/-- `pointLevelStep` on a list of chunk sums is `pairUp` on the chunks:
the skeleton's per-level combine merges adjacent chunks. -/
theorem pointLevelStep_map_sumOnE :
    ∀ chunks : List (List (ZMod E.q × ZMod E.q)),
      pointLevelStep E (chunks.map (sumOnE E)) =
        (pairUp chunks).map (sumOnE E)
  | [] => rfl
  | [_] => rfl
  | c₁ :: c₂ :: rest => by
      show pointCombine E (sumOnE E c₁) (sumOnE E c₂) ::
            pointLevelStep E (rest.map (sumOnE E))
          = sumOnE E (c₁ ++ c₂) :: (pairUp rest).map (sumOnE E)
      rw [pointCombine_eq_add, ← sumOnE_append,
        pointLevelStep_map_sumOnE rest]

/-! ## The general-position hypothesis -/

/-- Per-level certificate from `SafePairs`: the current level's chunks
flatten to a sublist of `Ps`, and each adjacent chunk pair is a
nonempty split of a sublist. -/
theorem levelStepPointChordCase_of_safePairs
    {Ps : List (ZMod E.q × ZMod E.q)} (hSafe : SafePairs E Ps) :
    ∀ chunks : List (List (ZMod E.q × ZMod E.q)),
      chunks.flatten.Sublist Ps → (∀ c ∈ chunks, c ≠ []) →
      LevelStepPointChordCase E (chunks.map (sumOnE E))
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | c₁ :: c₂ :: rest, hsub, hne => by
      refine ⟨?_, ?_⟩
      · apply hSafe c₁ c₂ (hne c₁ (by simp)) (hne c₂ (by simp))
        have h1 : (c₁ ++ c₂).Sublist ((c₁ :: c₂ :: rest).flatten) := by
          rw [List.flatten_cons, List.flatten_cons, ← List.append_assoc]
          exact List.sublist_append_left _ _
        exact h1.trans hsub
      · apply levelStepPointChordCase_of_safePairs hSafe rest
        · have h2 : rest.flatten.Sublist ((c₁ :: c₂ :: rest).flatten) := by
            rw [List.flatten_cons, List.flatten_cons]
            exact (List.sublist_append_right _ _).trans
              (List.sublist_append_right _ _)
          exact h2.trans hsub
        · intro c hc
          exact hne c (by simp [hc])

/-- Iterated certificate from `SafePairs`, over an arbitrary chunk
partition whose flatten is a sublist of `Ps`. -/
theorem iteratedPointChordCase_of_safePairs_chunks
    {Ps : List (ZMod E.q × ZMod E.q)} (hSafe : SafePairs E Ps) :
    ∀ (n : ℕ) (chunks : List (List (ZMod E.q × ZMod E.q))),
      chunks.flatten.Sublist Ps → (∀ c ∈ chunks, c ≠ []) →
      IteratedPointChordCase E n (chunks.map (sumOnE E)) := by
  intro n
  induction n with
  | zero => intro chunks _ _; trivial
  | succ n ih =>
      intro chunks hsub hne
      refine ⟨levelStepPointChordCase_of_safePairs E hSafe chunks hsub hne, ?_⟩
      rw [pointLevelStep_map_sumOnE]
      apply ih
      · rw [pairUp_flatten]; exact hsub
      · exact level_step_lists_forall_ne chunks hne

/-- The singleton chunks of the level-0 skeleton are the support
points themselves. -/
theorem level0SingletonPoints_eq_map_sumOnE
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points) :
    level0SingletonPoints E Ps = (Ps.map (fun P => [P])).map (sumOnE E) := by
  induction Ps with
  | nil => rfl
  | cons P rest ih =>
      have hP : P ∈ E.points := hPs_on P (by simp)
      have hsingle : sumOnE E [P] = ECPoint.affine E P.1 P.2 := by
        rw [sumOnE_cons E hP]
        show ECPoint.affineOfMem E hP + 0 = ECPoint.affine E P.1 P.2
        rw [add_zero, ECPoint.affine_eq_affineOfMem E hP]
      show ECPoint.affine E P.1 P.2 :: level0SingletonPoints E rest
          = sumOnE E [P] :: (rest.map (fun P => [P])).map (sumOnE E)
      rw [hsingle, ih (fun Q hQ => hPs_on Q (by simp [hQ]))]

/-- **Any-length chain certificate from general position.** For any
on-curve support satisfying `SafePairs`, the full point-skeleton
certificate holds — at any length, with no case-by-case shape
analysis. -/
theorem iteratedPointChordCase_of_safePairs
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hSafe : SafePairs E Ps) :
    IteratedPointChordCase E Ps.length (level0SingletonPoints E Ps) := by
  rw [level0SingletonPoints_eq_map_sumOnE E Ps hPs_on]
  apply iteratedPointChordCase_of_safePairs_chunks E hSafe
  · rw [map_singleton_flatten]
  · intro c hc
    rcases List.mem_map.mp hc with ⟨P, _, rfl⟩
    simp

/-! ## Computable certificate (for `decide`/`native_decide`) -/

/-- On on-curve lists, `pointSum` computes `sumOnE`. -/
theorem pointSum_eq_sumOnE
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points) :
    pointSum E Ps = sumOnE E Ps := by
  induction Ps with
  | nil => rfl
  | cons P rest ih =>
      have hP : P ∈ E.points := hPs_on P (by simp)
      show pointCombine E (ECPoint.affine E P.1 P.2) (pointSum E rest)
          = sumOnE E (P :: rest)
      rw [pointCombine_eq_add, sumOnE_cons E hP,
        ih (fun Q hQ => hPs_on Q (by simp [hQ])),
        ECPoint.affine_eq_affineOfMem E hP]

/-- The computable certificate implies the semantic hypothesis (on
on-curve supports). -/
theorem SafePairs.of_cert
    {Ps : List (ZMod E.q × ZMod E.q)}
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (h : SafePairsCert E Ps) : SafePairs E Ps := by
  intro xs ys hxs hys hsub
  have hxs_on : ∀ P ∈ xs, P ∈ E.points := fun P hP =>
    hPs_on P (hsub.subset (by simp [hP]))
  have hys_on : ∀ P ∈ ys, P ∈ E.points := fun P hP =>
    hPs_on P (hsub.subset (by simp [hP]))
  have hmem : (xs ++ ys) ∈ Ps.sublists := List.mem_sublists.mpr hsub
  have hklt : xs.length < (xs ++ ys).length := by
    rw [List.length_append]
    have : 0 < ys.length := List.length_pos_iff.mpr hys
    omega
  have hk : xs.length ∈ List.range (xs ++ ys).length :=
    List.mem_range.mpr hklt
  rcases h (xs ++ ys) hmem xs.length hk with h0 | hpcc
  · exact absurd (List.length_eq_zero_iff.mp h0) hxs
  · rw [List.take_left, List.drop_left] at hpcc
    rwa [pointSum_eq_sumOnE E xs hxs_on, pointSum_eq_sumOnE E ys hys_on]
      at hpcc

end Divisor.LineAccum

namespace Divisor

open LineAccum

/-- Every point of `binarySupport` lies on the curve. -/
theorem binarySupport_on_curve
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points) :
    ∀ P ∈ binarySupport stmt wit hk h_binary, P ∈ E.points := by
  intro P hP
  rcases List.mem_cons.mp hP with rfl | hP'
  · exact h_target_on_curve
  · rcases List.mem_filterMap.mp hP' with ⟨i, _, hi⟩
    by_cases hs : wit.scalars i = 1
    · rw [if_pos hs, Option.some.injEq] at hi
      exact hi ▸ h_bases_on_curve (Fin.cast hk.symm i)
    · rw [if_neg hs] at hi
      simp at hi

end Divisor
