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

  Why this shape: the accumulation tree of `eagenBuild_singletons`
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
  * `Landmark.pointCombine_eq_add` — skeleton combine = group law.
  * `Landmark.pointSum` — computable EC sum of a support list, with
    `pointSum_eq_sumOnE` (so certificates can be `native_decide`d).
  * `Landmark.SafePairs` (semantic) and `Landmark.SafePairsCert`
    (computable, `Decidable`), with `SafePairs.of_cert`.
  * `Landmark.iteratedPointChordCase_of_safePairs` — the certificate
    for the whole accumulation, at any length.
  * `ma_completeness_binary_any_length` — headline: binary
    completeness at any support length under `SafePairs`.

  Degenerate supports genuinely exist (2-torsion points in the
  support; block sums colliding as `B = −2A`), so an unconditional
  any-support statement is false; `SafePairs` is the mild
  general-position exclusion, decidable per instance.
-/
import Divisor.IsHonestForBinary

open Polynomial Classical

namespace Divisor.Landmark

variable (E : ECSetup)

/-! ## The skeleton combine is the group law -/

/-- Membership in `E.points` from mathlib nonsingularity. -/
private theorem mem_of_nonsingular {x y : ZMod E.q}
    (h : E.toW.toAffine.Nonsingular x y) : (x, y) ∈ E.points :=
  E.hComplete x y ((E.equation_iff x y).mp (E.equation_iff_nonsingular.mpr h))

/-- The distinct-`x` chord formula computes the group-law sum. -/
private theorem chord_formula_add
    {xa ya xb yb : ZMod E.q}
    (hns_a : E.toW.toAffine.Nonsingular xa ya)
    (hns_b : E.toW.toAffine.Nonsingular xb yb)
    (hxx : xa ≠ xb) :
    ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
        (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
            (ya - slopeOf xa ya xb yb * xa)))
      = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := by
  classical
  have hA : (xa, ya) ∈ E.points := mem_of_nonsingular E hns_a
  have hB : (xb, yb) ∈ E.points := mem_of_nonsingular E hns_b
  have hT : thirdPoint E (xa, ya) (xb, yb) =
      some (slopeOf xa ya xb yb ^ 2 - xa - xb,
        slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
          (ya - slopeOf xa ya xb yb * xa)) := by
    unfold thirdPoint
    rw [if_neg (by exact hxx)]
    rfl
  have hmem := third_point_on_curve E (xa, ya) (xb, yb) hA hB hT
  have hsum := thirdPoint_some_eq_neg_add (E := E) hA hB hT
  calc ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
        (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
            (ya - slopeOf xa ya xb yb * xa)))
      = -(ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
            (slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
              (ya - slopeOf xa ya xb yb * xa))) := by
        rw [ECPoint.affine_neg]
    _ = -(ECPoint.affineOfMem E hmem) := by
        rw [ECPoint.affine_eq_affineOfMem E hmem]
    _ = ECPoint.affineOfMem E hA + ECPoint.affineOfMem E hB := hsum.symm
    _ = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := rfl

/-- The smooth-tangent formula computes the doubling. -/
private theorem tangent_formula_add
    {xa ya : ZMod E.q}
    (hns_a hns_b : E.toW.toAffine.Nonsingular xa ya)
    (hy0 : ¬ ya = 0) :
    ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
        (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa)))
      = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := by
  classical
  have hA : (xa, ya) ∈ E.points := mem_of_nonsingular E hns_a
  have hT : thirdPoint E (xa, ya) (xa, ya) =
      some (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa,
        (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
            (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
          (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa)) := by
    unfold thirdPoint
    rw [if_pos rfl, if_pos rfl, if_neg (by exact hy0)]
  have hmem := third_point_on_curve E (xa, ya) (xa, ya) hA hA hT
  have hsum := thirdPoint_some_eq_neg_add (E := E) hA hA hT
  calc ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
        (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))) =
      -(ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
          ((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))) := by
        rw [ECPoint.affine_neg]
    _ = -(ECPoint.affineOfMem E hmem) := by
        rw [ECPoint.affine_eq_affineOfMem E hmem]
    _ = ECPoint.affineOfMem E hA + ECPoint.affineOfMem E hA := hsum.symm
    _ = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := rfl

/-- **The computable point-skeleton combine is mathlib's group law**,
unconditionally: every `ECPoint` carries its nonsingularity witness,
which rules the junk branches out. This upgrades every block point in
the skeleton run to a genuine elliptic-curve subset sum. -/
theorem pointCombine_eq_add (p q : ECPoint E) :
    pointCombine E p q = p + q := by
  classical
  match p, q with
  | WeierstrassCurve.Affine.Point.zero, q =>
      show q = 0 + q
      exact (zero_add q).symm
  | WeierstrassCurve.Affine.Point.some xa ya hns_a, WeierstrassCurve.Affine.Point.zero =>
      show WeierstrassCurve.Affine.Point.some xa ya hns_a
          = WeierstrassCurve.Affine.Point.some xa ya hns_a + 0
      exact (add_zero _).symm
  | WeierstrassCurve.Affine.Point.some xa ya hns_a,
    WeierstrassCurve.Affine.Point.some xb yb hns_b =>
      show (if _h_xx : xa ≠ xb then
              ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
                (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
                    (ya - slopeOf xa ya xb yb * xa)))
            else if _h_yy : ya = -yb then 0
            else if _h_y0 : ya = 0 then 0
            else
              ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
                (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
                      (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
                    (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))))
          = WeierstrassCurve.Affine.Point.some xa ya hns_a +
            WeierstrassCurve.Affine.Point.some xb yb hns_b
      have ea : ya ^ 2 = xa ^ 3 + E.curveA * xa + E.curveB :=
        (E.equation_iff xa ya).mp (E.equation_iff_nonsingular.mpr hns_a)
      have eb : yb ^ 2 = xb ^ 3 + E.curveA * xb + E.curveB :=
        (E.equation_iff xb yb).mp (E.equation_iff_nonsingular.mpr hns_b)
      split_ifs with hxx hyy hy0
      · exact chord_formula_add E hns_a hns_b hxx
      · -- Vertical: the two points are inverse.
        have hxe : xa = xb := not_not.mp hxx
        have hyb : yb = -ya := by rw [hyy, neg_neg]
        subst hxe
        subst hyb
        have hneg : (WeierstrassCurve.Affine.Point.some xa (-ya) hns_b : ECPoint E)
            = -(WeierstrassCurve.Affine.Point.some xa ya hns_a) := by
          have h1 : -(WeierstrassCurve.Affine.Point.some xa ya hns_a : ECPoint E)
              = ECPoint.affine E xa (-ya) := by
            rw [← ECPoint.affine_of_nonsingular E hns_a]
            exact ECPoint.affine_neg E xa ya
          rw [h1, ECPoint.affine_of_nonsingular E hns_b]
        rw [hneg, add_neg_cancel]
      · -- Equal `x`, not inverse, `ya = 0`: impossible on the curve.
        exfalso
        have hxe : xa = xb := not_not.mp hxx
        rw [← hxe] at eb
        have hyb2 : yb ^ 2 = 0 := by rw [eb, ← ea, hy0]; ring
        have hyb0 : yb = 0 := pow_eq_zero_iff two_ne_zero |>.mp hyb2
        exact hyy (by rw [hy0, hyb0, neg_zero])
      · -- Smooth tangent: on the curve the operands are equal.
        have hxe : xa = xb := not_not.mp hxx
        subst hxe
        have hyb : yb = ya := by
          have h2 : yb ^ 2 = ya ^ 2 := by rw [eb, ea]
          have h3 : (yb - ya) * (yb + ya) = 0 := by ring_nf; linear_combination h2
          rcases mul_eq_zero.mp h3 with h | h
          · exact sub_eq_zero.mp h
          · exact absurd (by rw [← eq_neg_of_add_eq_zero_right h]) hyy
        subst hyb
        exact tangent_formula_add E hns_a hns_b hy0

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

end Divisor.Landmark

namespace Divisor

open Landmark

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

/-- **Any-length binary completeness.** For a binary
witness whose support satisfies the semantic general-position
hypothesis `SafePairs` — every nonempty split of every sublist has a
chord-safe pair of subset sums — the honest Eagen-singletons message
achieves the completeness bound, at ANY support length. The
hypothesis is decidable per instance via `SafePairsCert` +
`SafePairs.of_cert`. -/
theorem ma_completeness_binary_any_length
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (h_valid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       Landmark.eagenBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (h_nodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_safe : Landmark.SafePairs E (binarySupport stmt wit hk h_binary))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_deg : msg.toD.degE ≤ wit.degBound)
    (h_deg_k : msg.toD.degE ≤ stmt.degBound) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_ps_on := binarySupport_on_curve stmt wit hk h_binary
    h_target_on_curve h_bases_on_curve
  exact ma_completeness_binary_point_certificate E stmt wit hk msg hkm
    h_binary h_valid h_toD_eq h_degE_eq h_scalars_match
    h_target_on_curve h_bases_on_curve h_nodup
    (Landmark.iteratedPointChordCase_of_safePairs E
      (binarySupport stmt wit hk h_binary) h_ps_on h_safe)
    h_admSetMax h_deg h_deg_k

/-- Any-length binary completeness with the general-position
hypothesis supplied by the computable certificate
(`decide`/`native_decide`-friendly). -/
theorem ma_completeness_binary_any_length_cert
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (h_valid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       Landmark.eagenBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (h_nodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_cert : Landmark.SafePairsCert E (binarySupport stmt wit hk h_binary))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_deg : msg.toD.degE ≤ wit.degBound)
    (h_deg_k : msg.toD.degE ≤ stmt.degBound) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_binary_any_length E stmt wit hk msg hkm h_binary h_valid
    h_toD_eq h_degE_eq h_scalars_match h_target_on_curve h_bases_on_curve
    h_nodup
    (Landmark.SafePairs.of_cert E
      (binarySupport_on_curve stmt wit hk h_binary
        h_target_on_curve h_bases_on_curve)
      h_cert)
    h_admSetMax h_deg h_deg_k

end Divisor
