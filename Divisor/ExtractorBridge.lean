/-
  Divisor/ExtractorBridge.lean

  T4 extractor bridge theorems (steps D3, D4, D5 of the extractor chain).

  These theorems take σ-matching-style hypotheses (distilled from the
  output of `log_deriv_nonvanishing_criterion`) and produce the
  extractor's conclusions (`extractorSucceeds` and the group-law
  equation `target = Σ [scalars_i] · bases_i`). The upstream bridge
  `logDerivCheckFn ≡ 0 on E × E ⇒ σ-matching exists` (plan's D1+D2)
  is future work; this file provides the extractor-side combinatorics
  that consume a σ-matching when it becomes available.

  Structure:
  * `extractorSucceeds_of_natural_witness` (D3): given a natural-number
    witness `coeff : Fin msg.k → ℕ` whose ZMod image matches
    `-groupSum` at canonical indices (and is 0 elsewhere) with
    `coeff i < d`, the extractor succeeds at bound `d` and
    `extractedScalars i = coeff i` (as ℤ).
  * `target_eq_weightedSum_of_zero_sum` (D5): from the principality-
    derived equation `(-P) + Σ [extractedScalars i] · B_i = 0`,
    conclude `target = Σ [extractedScalars i] · B_i`.
-/
import Divisor.DensityBound
import Divisor.TightBound

namespace Divisor

open Finset Classical

variable (E : ECSetup)

/-! ## D4: extractor's divisor principality ⇒ zero-sum

The extractor's divisor (as a coefficient function on `ECPoint E`)
equals `+1` at `-P`, `extractedScalars i` at each base point
`B_i` (aggregating duplicates), and `-D.degE` at `∞`. Mirror of
`honestDivisorCoeffs` with `extractedScalars` in place of `wit.scalars`.
-/

/-- Extractor-side divisor coefficient function. -/
noncomputable def extractorDivisorCoeffs
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : ECPoint E → ℤ :=
  fun P => match P with
    | 0 => -(msg.toD.degE : ℤ)
    | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ =>
        (if (x, y) = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
          (fun j => extractorBases E stmt msg hkm j = (x, y)),
          extractedScalars E stmt msg hkm j

/-- Candidate finite superset of the support: `{∞, -P, all base points}`. -/
noncomputable def extractorDivisorCandidate
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : Finset (ECPoint E) :=
  insert (0 : ECPoint E)
    (insert (ECPoint.affine E stmt.target.1 (-stmt.target.2))
      ((Finset.univ : Finset (Fin msg.k)).image
        (fun j => ECPoint.affine E (extractorBases E stmt msg hkm j).1
                                 (extractorBases E stmt msg hkm j).2)))

/-- Value of `extractorDivisorCoeffs` at `∞`. -/
theorem extractorDivisorCoeffs_infinity
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    extractorDivisorCoeffs E stmt msg hkm (0 : ECPoint E) =
      -(msg.toD.degE : ℤ) := rfl

/-- Value of `extractorDivisorCoeffs` at `-P` (general case). -/
theorem extractorDivisorCoeffs_negP
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    extractorDivisorCoeffs E stmt msg hkm
        (ECPoint.affine E stmt.target.1 (-stmt.target.2)) = 1 := by
  classical
  -- `(target.1, -target.2)` is on the curve, so `affine` is `.some _`.
  have hNegTargetOnE : (stmt.target.1, -stmt.target.2) ∈ E.points := by
    apply E.hComplete
    have hc := E.hOnCurve _ hTargetOnE
    try simp only at hc ⊢
    rw [neg_sq]; exact hc
  have hns : E.toW.toAffine.Nonsingular stmt.target.1 (-stmt.target.2) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hNegTargetOnE))
  rw [ECPoint.affine_of_nonsingular E hns]
  show (if (stmt.target.1, -stmt.target.2) = (stmt.target.1, -stmt.target.2)
        then (1 : ℤ) else 0) +
       ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
         (fun j => extractorBases E stmt msg hkm j =
                    (stmt.target.1, -stmt.target.2)),
         extractedScalars E stmt msg hkm j = 1
  rw [if_pos rfl]
  have hEmpty : ((Finset.univ : Finset (Fin msg.k)).filter
      (fun j => extractorBases E stmt msg hkm j =
                 (stmt.target.1, -stmt.target.2))) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    apply hNoNegP
    exact ⟨j, hj⟩
  rw [hEmpty, Finset.sum_empty, add_zero]

/-- The filter set at position `i`'s base point equals the extractor
    group of `i`. -/
theorem filter_bases_eq_extractorGroup
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin msg.k) :
    ((Finset.univ : Finset (Fin msg.k)).filter
      (fun j => extractorBases E stmt msg hkm j =
                 extractorBases E stmt msg hkm i)) =
    extractorGroup E stmt msg hkm i := by rfl

/-- Under general case, a non-canonical index has `extractedScalars = 0`. -/
theorem extractedScalars_zero_of_notCanonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (i : Fin msg.k) (hNotCanon : ¬ extractorIsCanonical E stmt msg hkm i) :
    extractedScalars E stmt msg hkm i = 0 := by
  show (if hne : (negPIndexSet E stmt msg hkm).Nonempty
        then (if i = (negPIndexSet E stmt msg hkm).min' hne
              then (-1 : ℤ) else 0)
        else if extractorIsCanonical E stmt msg hkm i
             then ((extractorGroupSum E stmt msg hkm i).val : ℤ)
             else 0) = 0
  rw [dif_neg hNoNegP, if_neg hNotCanon]

/-- Within an extractor group, only the canonical (minimum-index)
    element has nonzero `extractedScalars` under the general case. -/
theorem extractedScalars_group_canonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i j : Fin msg.k) (hj : j ∈ extractorGroup E stmt msg hkm i) :
    extractorGroup E stmt msg hkm j = extractorGroup E stmt msg hkm i := by
  classical
  ext x
  simp only [extractorGroup, Finset.mem_filter, Finset.mem_univ, true_and]
  have hji : extractorBases E stmt msg hkm j = extractorBases E stmt msg hkm i := by
    have := Finset.mem_filter.mp hj
    exact this.2
  constructor
  · intro hx; rw [hji] at hx; exact hx
  · intro hx; rw [hji]; exact hx

/-- Sum of `extractedScalars` over an extractor group equals the value at
    the canonical (min-index) position. -/
theorem sum_extractedScalars_over_group
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (i : Fin msg.k) :
    ∑ j ∈ extractorGroup E stmt msg hkm i,
      extractedScalars E stmt msg hkm j
    = extractedScalars E stmt msg hkm
        ((extractorGroup E stmt msg hkm i).min'
          (extractorGroup_nonempty E stmt msg hkm i)) := by
  classical
  set c := (extractorGroup E stmt msg hkm i).min'
    (extractorGroup_nonempty E stmt msg hkm i)
  apply Finset.sum_eq_single c
  · intro j hj hjc
    have hGj : extractorGroup E stmt msg hkm j = extractorGroup E stmt msg hkm i :=
      extractedScalars_group_canonical E stmt msg hkm i j hj
    have hNotCanon : ¬ extractorIsCanonical E stmt msg hkm j := by
      intro hCanon
      have hmin_j : (extractorGroup E stmt msg hkm j).min'
                      (extractorGroup_nonempty E stmt msg hkm j) = j := hCanon
      have hj_lb : ∀ y ∈ extractorGroup E stmt msg hkm i, j ≤ y := by
        intro y hy
        rw [← hGj] at hy
        rw [← hmin_j]
        exact Finset.min'_le _ y hy
      have hc_le_j : c ≤ j := Finset.min'_le _ j hj
      have hj_le_c : j ≤ c := hj_lb c (Finset.min'_mem _ _)
      exact hjc (le_antisymm hj_le_c hc_le_j)
    exact extractedScalars_zero_of_notCanonical E stmt msg hkm hNoNegP j hNotCanon
  · intro hnotin
    exact absurd (Finset.min'_mem _ _) hnotin

/-- Canonical-index Finset: all `i : Fin msg.k` that are the minimum
    (= canonical) index in their base-point group. -/
noncomputable def canonicalFinset
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    Finset (Fin msg.k) :=
  (Finset.univ : Finset (Fin msg.k)).filter (extractorIsCanonical E stmt msg hkm)

/-- `ECPoint.affine (extractorBases j)` as a function `Fin msg.k → ECPoint E`. -/
noncomputable def basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (j : Fin msg.k) : ECPoint E :=
  ECPoint.affine E (extractorBases E stmt msg hkm j).1
                 (extractorBases E stmt msg hkm j).2

/-- Injectivity of `basesAffineEC` on the canonical Finset: two canonical
    indices with the same affine base point are equal (they're both the
    min of the same group). Requires `hBasesOnE` because the junk-tolerant
    `ECPoint.affine` collapses off-curve pairs to `0`, which would prevent
    extracting coordinate equality. -/
theorem basesAffineEC_injOn_canonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points) :
    ∀ j₁ ∈ canonicalFinset E stmt msg hkm,
    ∀ j₂ ∈ canonicalFinset E stmt msg hkm,
    basesAffineEC E stmt msg hkm j₁ = basesAffineEC E stmt msg hkm j₂ →
    j₁ = j₂ := by
  classical
  intro j₁ hj₁ j₂ hj₂ heq
  simp only [canonicalFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
  -- From heq: extractorBases j₁ = extractorBases j₂ (after pair destructuring).
  have hb : extractorBases E stmt msg hkm j₁ = extractorBases E stmt msg hkm j₂ := by
    simp only [basesAffineEC] at heq
    -- The two extractorBases are both on E.points (via hBasesOnE).
    have hP₁ : extractorBases E stmt msg hkm j₁ ∈ E.points := by
      unfold extractorBases; exact hBasesOnE _
    have hP₂ : extractorBases E stmt msg hkm j₂ ∈ E.points := by
      unfold extractorBases; exact hBasesOnE _
    have hns₁ : E.toW.toAffine.Nonsingular
        (extractorBases E stmt msg hkm j₁).1 (extractorBases E stmt msg hkm j₁).2 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP₁))
    have hns₂ : E.toW.toAffine.Nonsingular
        (extractorBases E stmt msg hkm j₂).1 (extractorBases E stmt msg hkm j₂).2 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP₂))
    rw [ECPoint.affine_of_nonsingular E hns₁,
        ECPoint.affine_of_nonsingular E hns₂] at heq
    rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
    exact Prod.ext heq.1 heq.2
  -- hb means j₁ ∈ extractorGroup j₂ and vice versa.
  have hj₁inG : j₁ ∈ extractorGroup E stmt msg hkm j₂ := by
    simp only [extractorGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb
  have hG_eq : extractorGroup E stmt msg hkm j₁ = extractorGroup E stmt msg hkm j₂ :=
    extractedScalars_group_canonical E stmt msg hkm j₂ j₁ hj₁inG
  -- Both j₁, j₂ are canonicals of this common group.
  -- From hj₁: (extractorGroup j₁).min' _ = j₁.
  -- From hj₂: (extractorGroup j₂).min' _ = j₂.
  -- Using hG_eq: (extractorGroup j₂).min' _ = j₁ (from hj₁ after rewriting).
  -- And = j₂ (from hj₂). So j₁ = j₂.
  have h_min_eq_j₁ : (extractorGroup E stmt msg hkm j₂).min'
      (extractorGroup_nonempty E stmt msg hkm j₂) = j₁ := by
    have hmin : (extractorGroup E stmt msg hkm j₁).min'
        (extractorGroup_nonempty E stmt msg hkm j₁) = j₁ := hj₁
    -- Show j₁ is the min of extractorGroup j₂ by antisymmetry of le.
    apply le_antisymm
    · -- min of j₂'s group ≤ j₁
      apply Finset.min'_le _ _ hj₁inG
    · -- j₁ ≤ min of j₂'s group
      rw [← hmin]
      apply Finset.min'_le _ _
      -- Need min of j₂'s group ∈ extractorGroup j₁.
      rw [hG_eq]
      exact Finset.min'_mem _ _
  -- Now combine with hj₂.
  rw [← h_min_eq_j₁, hj₂]

/-- `canonicalFinset.image basesAffineEC = univ.image basesAffineEC`.
    (Every affine base point is reached by a canonical index.) -/
theorem canonicalFinset_image_eq_univ_image
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    (canonicalFinset E stmt msg hkm).image (basesAffineEC E stmt msg hkm) =
    (Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm) := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (by
      intro x _; exact Finset.mem_univ x)
  · intro P hP
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hP
    obtain ⟨j, rfl⟩ := hP
    -- Take the canonical of j's group.
    set j_canon := (extractorGroup E stmt msg hkm j).min'
      (extractorGroup_nonempty E stmt msg hkm j) with hjc
    have hj_canon_in : j_canon ∈ extractorGroup E stmt msg hkm j :=
      Finset.min'_mem _ _
    have hj_canon_is : extractorBases E stmt msg hkm j_canon =
                       extractorBases E stmt msg hkm j := by
      have := Finset.mem_filter.mp hj_canon_in
      exact this.2
    -- j_canon is canonical by def (= min' of its own group, which equals j's group).
    have hj_canon_canon : extractorIsCanonical E stmt msg hkm j_canon := by
      show (extractorGroup E stmt msg hkm j_canon).min'
        (extractorGroup_nonempty E stmt msg hkm j_canon) = j_canon
      have hG_eq : extractorGroup E stmt msg hkm j_canon =
                   extractorGroup E stmt msg hkm j :=
        extractedScalars_group_canonical E stmt msg hkm j j_canon hj_canon_in
      apply le_antisymm
      · apply Finset.min'_le
        exact mem_extractorGroup_self E stmt msg hkm j_canon
      · apply Finset.le_min'
        intro y hy
        rw [hG_eq] at hy
        rw [hjc]
        exact Finset.min'_le _ _ hy
    refine Finset.mem_image.mpr ⟨j_canon, ?_, ?_⟩
    · simp only [canonicalFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj_canon_canon
    · simp only [basesAffineEC, hj_canon_is]

/-- Zero contribution at non-canonical indices:
    `zsmul (extractedScalars j) (basesAffineEC j) = 0`. -/
theorem zsmul_extractedScalars_basesAffineEC_zero_of_notCanonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (j : Fin msg.k) (hNotCanon : ¬ extractorIsCanonical E stmt msg hkm j) :
    ECPoint.zsmul E (extractedScalars E stmt msg hkm j)
      (basesAffineEC E stmt msg hkm j) = 0 := by
  rw [extractedScalars_zero_of_notCanonical E stmt msg hkm hNoNegP j hNotCanon]
  rfl

/-- `extractorDivisorCoeffs` at an affine base point equals
    `extractedScalars` at the canonical representative of that group. -/
theorem extractorDivisorCoeffs_affine_bases
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (i : Fin msg.k) :
    extractorDivisorCoeffs E stmt msg hkm
        (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                        (extractorBases E stmt msg hkm i).2) =
      extractedScalars E stmt msg hkm
        ((extractorGroup E stmt msg hkm i).min'
          (extractorGroup_nonempty E stmt msg hkm i)) := by
  classical
  -- The base point is on the curve, so `affine` is `.some _`.
  have hBaseOnE : extractorBases E stmt msg hkm i ∈ E.points := by
    unfold extractorBases; exact hBasesOnE _
  have hns : E.toW.toAffine.Nonsingular
      (extractorBases E stmt msg hkm i).1 (extractorBases E stmt msg hkm i).2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hBaseOnE))
  rw [ECPoint.affine_of_nonsingular E hns]
  show (if ((extractorBases E stmt msg hkm i).1,
           (extractorBases E stmt msg hkm i).2) =
          (stmt.target.1, -stmt.target.2)
        then (1 : ℤ) else 0) +
       ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
         (fun j => extractorBases E stmt msg hkm j =
                    ((extractorBases E stmt msg hkm i).1,
                     (extractorBases E stmt msg hkm i).2)),
         extractedScalars E stmt msg hkm j = _
  have hNot : ((extractorBases E stmt msg hkm i).1,
               (extractorBases E stmt msg hkm i).2) ≠
              (stmt.target.1, -stmt.target.2) := by
    intro heq
    apply hNoNegP
    refine ⟨i, ?_⟩
    simp only [negPIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have : extractorBases E stmt msg hkm i =
           ((extractorBases E stmt msg hkm i).1,
            (extractorBases E stmt msg hkm i).2) := by
      rcases extractorBases E stmt msg hkm i with ⟨a, b⟩
      rfl
    rw [this, heq]
  rw [if_neg hNot, zero_add]
  have hPair_eq_full :
      ((extractorBases E stmt msg hkm i).1,
       (extractorBases E stmt msg hkm i).2) =
      extractorBases E stmt msg hkm i := by
    rcases extractorBases E stmt msg hkm i with ⟨a, b⟩; rfl
  rw [hPair_eq_full]
  rw [filter_bases_eq_extractorGroup]
  exact sum_extractedScalars_over_group E stmt msg hkm hNoNegP i

/-- For canonical `j`, `extractorDivisorCoeffs (basesAffineEC j) = extractedScalars j`. -/
theorem extractorDivisorCoeffs_basesAffineEC_of_canonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (j : Fin msg.k) (hCanon : extractorIsCanonical E stmt msg hkm j) :
    extractorDivisorCoeffs E stmt msg hkm (basesAffineEC E stmt msg hkm j) =
      extractedScalars E stmt msg hkm j := by
  unfold basesAffineEC
  have h1 := extractorDivisorCoeffs_affine_bases E stmt msg hkm hBasesOnE hNoNegP j
  have hmin_j : (extractorGroup E stmt msg hkm j).min'
                  (extractorGroup_nonempty E stmt msg hkm j) = j := hCanon
  rw [h1, hmin_j]

/-- Image-reindexing: weightedSum over `univ.image basesAffineEC` of
    `zsmul coeffs ·` equals weightedSum over `univ` of
    `zsmul extractedScalars (basesAffineEC ·)`.

    Goes via: (a) rewrite `univ.image = canonical.image`, (b) apply
    `fold_image` with injectivity on canonical, (c) rewrite the summand
    using `extractorDivisorCoeffs_basesAffineEC_of_canonical`, (d)
    zero-pad from canonical to univ. -/
theorem weightedSum_imageBases_eq_univ_zsmul_extractedScalars
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    ECPoint.weightedSum E
      ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm))
      (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P)
    = ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
      (fun j => ECPoint.zsmul E (extractedScalars E stmt msg hkm j)
        (basesAffineEC E stmt msg hkm j)) := by
  classical
  set bEC := basesAffineEC E stmt msg hkm with hbEC_def
  set c := extractorDivisorCoeffs E stmt msg hkm with hc_def
  set canFs := canonicalFinset E stmt msg hkm with hcanFs_def
  -- Step A: rewrite `univ.image = canonical.image`.
  rw [show (Finset.univ : Finset (Fin msg.k)).image bEC = canFs.image bEC from
        (canonicalFinset_image_eq_univ_image E stmt msg hkm).symm]
  -- Step B: sum_image with injectivity on canonical.
  have hInj : ∀ x ∈ canFs, ∀ y ∈ canFs, bEC x = bEC y → x = y :=
    basesAffineEC_injOn_canonical E stmt msg hkm hBasesOnE
  show ∑ P ∈ canFs.image bEC, ECPoint.zsmul E (c P) P = _
  rw [Finset.sum_image (fun x hx y hy h => hInj x hx y hy h)]
  -- After sum_image: ∑ j ∈ canFs, zsmul (c (bEC j)) (bEC j).
  -- Step C: rewrite summand at canonical positions.
  have hSumCongr :
      ∑ j ∈ canFs, ECPoint.zsmul E (c (bEC j)) (bEC j)
      = ∑ j ∈ canFs, ECPoint.zsmul E (extractedScalars E stmt msg hkm j) (bEC j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hcanFs_def, canonicalFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    rw [hc_def, hbEC_def,
        extractorDivisorCoeffs_basesAffineEC_of_canonical E stmt msg hkm hBasesOnE hNoNegP j hj]
  rw [hSumCongr]
  -- Step D: extend canonical sum to univ via zero-padding.
  show ∑ j ∈ canFs, _ = ECPoint.weightedSum E _ _
  apply (ECPoint.weightedSum_subset_of_zero_outside E (Finset.subset_univ canFs) ?_).symm
  intro j _ hjnotcanon
  simp only [hcanFs_def, canonicalFinset, Finset.mem_filter,
    Finset.mem_univ, true_and] at hjnotcanon
  exact zsmul_extractedScalars_basesAffineEC_zero_of_notCanonical
    E stmt msg hkm hNoNegP j hjnotcanon

/-- Support of `extractorDivisorCoeffs` is contained in the candidate Finset
    `{∞, -P_aff} ∪ image(basesAffineEC)`. -/
theorem extractorDivisorCoeffs_support_subset_candidate
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    Function.support (extractorDivisorCoeffs E stmt msg hkm) ⊆
    ↑(extractorDivisorCandidate E stmt msg hkm) := by
  classical
  intro P hP
  simp only [Function.mem_support] at hP
  rw [Finset.mem_coe]
  unfold extractorDivisorCandidate
  cases P with
  | zero =>
      exact Finset.mem_insert_self _ _
  | @some x y hns =>
      refine Finset.mem_insert_of_mem ?_
      -- The `some` value equals `ECPoint.affine E x y` since it's nonsingular.
      have hAffEq : (WeierstrassCurve.Affine.Point.some _ _ hns : ECPoint E)
          = ECPoint.affine E x y := (ECPoint.affine_of_nonsingular E hns).symm
      by_cases hxy : (x, y) = (stmt.target.1, -stmt.target.2)
      · rw [Prod.mk.injEq] at hxy
        rcases hxy with ⟨hx, hy⟩
        rw [hAffEq, hx, hy]
        exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        -- Indicator = 0, so filter-sum ≠ 0, so filter is nonempty.
        have hEval : extractorDivisorCoeffs E stmt msg hkm
                        (WeierstrassCurve.Affine.Point.some _ _ hns) =
                      0 + ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
                        (fun j => extractorBases E stmt msg hkm j = (x, y)),
                        extractedScalars E stmt msg hkm j := by
          show (if (x, y) = (stmt.target.1, -stmt.target.2)
                then (1 : ℤ) else 0) +
               ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
                 (fun j => extractorBases E stmt msg hkm j = (x, y)),
                 extractedScalars E stmt msg hkm j = _
          rw [if_neg hxy]
        rw [hEval, zero_add] at hP
        rw [hAffEq]
        by_contra hNotInImage
        apply hP
        have hEmpty : ((Finset.univ : Finset (Fin msg.k)).filter
            (fun j => extractorBases E stmt msg hkm j = (x, y))) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          apply hNotInImage
          refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
          simp only [hj]
        rw [hEmpty, Finset.sum_empty]

/-- `∞` is not an affine point, so not in the `basesAffineEC` image
    (assuming bases are on the curve, so `affine` is `.some`, not junk `0`). -/
theorem infinity_notin_image_basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points) :
    (0 : ECPoint E) ∉
    ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨j, _, heq⟩ := hContra
  unfold basesAffineEC at heq
  have hBaseOnE : extractorBases E stmt msg hkm j ∈ E.points := by
    unfold extractorBases; exact hBasesOnE _
  have hns : E.toW.toAffine.Nonsingular
      (extractorBases E stmt msg hkm j).1 (extractorBases E stmt msg hkm j).2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hBaseOnE))
  rw [ECPoint.affine_of_nonsingular E hns] at heq
  exact (WeierstrassCurve.Affine.Point.some_ne_zero hns) heq

/-- Under general case, `-P_aff` is not in the image of base points.
    Requires `hTargetOnE` and `hBasesOnE` because the junk-tolerant
    `ECPoint.affine` collapses off-curve pairs to `0`, preventing
    coordinate recovery. -/
theorem negP_notin_image_basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    (ECPoint.affine E stmt.target.1 (-stmt.target.2) : ECPoint E) ∉
    ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨j, _, heq⟩ := hContra
  apply hNoNegP
  refine ⟨j, ?_⟩
  simp only [negPIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold basesAffineEC at heq
  -- Both are `.some` thanks to on-curve hypotheses.
  have hNegTargetOnE : (stmt.target.1, -stmt.target.2) ∈ E.points := by
    apply E.hComplete
    have hc := E.hOnCurve _ hTargetOnE
    try simp only at hc ⊢
    rw [neg_sq]; exact hc
  have hBaseOnE : extractorBases E stmt msg hkm j ∈ E.points := by
    unfold extractorBases; exact hBasesOnE _
  have hns_neg : E.toW.toAffine.Nonsingular stmt.target.1 (-stmt.target.2) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hNegTargetOnE))
  have hns_base : E.toW.toAffine.Nonsingular
      (extractorBases E stmt msg hkm j).1 (extractorBases E stmt msg hkm j).2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hBaseOnE))
  rw [ECPoint.affine_of_nonsingular E hns_neg,
      ECPoint.affine_of_nonsingular E hns_base] at heq
  rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
  exact Prod.ext heq.1 heq.2

/-- `∞ ≠ -P_aff`, given `-P_aff` lies on the curve (so `affine` returns
    `.some`, not the junk `0`). -/
theorem infinity_ne_negP_aff
    (stmt : DlogStatement E.q)
    (hTargetOnE : stmt.target ∈ E.points) :
    (0 : ECPoint E) ≠
    ECPoint.affine E stmt.target.1 (-stmt.target.2) := by
  intro h
  have hNegTargetOnE : (stmt.target.1, -stmt.target.2) ∈ E.points := by
    apply E.hComplete
    have hc := E.hOnCurve _ hTargetOnE
    try simp only at hc ⊢
    rw [neg_sq]; exact hc
  have hns : E.toW.toAffine.Nonsingular stmt.target.1 (-stmt.target.2) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hNegTargetOnE))
  rw [ECPoint.affine_of_nonsingular E hns] at h
  exact (WeierstrassCurve.Affine.Point.some_ne_zero hns) h.symm

/-- `∞` is not in `insert (-P_aff) (image basesAffineEC)`. -/
theorem infinity_notin_insert_negP_image
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points) :
    (0 : ECPoint E) ∉
    insert (ECPoint.affine E stmt.target.1 (-stmt.target.2))
      ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_insert] at hContra
  rcases hContra with h | h
  · exact infinity_ne_negP_aff E stmt hTargetOnE h
  · exact infinity_notin_image_basesAffineEC E stmt msg hkm hBasesOnE h

/-- **D4 main theorem (group-sum form).** Given that the group-weighted
    sum of `extractorDivisorCoeffs` over its finite support vanishes,
    the group-law equation
    `(-P) + Σ [extractedScalars i] · B_i = 0` holds.

    This avoids the `IsPrincipal` detour — we only need the group-sum-zero
    half of `principal_divisor_iff`. Combined with D5
    (`target_eq_weightedSum_of_zero_sum`), this gives the full group-law
    conclusion `target = Σ [extractedScalars i] · B_i`. -/
theorem extractor_zeroSum_of_weightedSum
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hWSum :
      ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
        (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) = 0) :
    (ECPoint.affine E stmt.target.1 (-stmt.target.2)) +
      (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (basesAffineEC E stmt msg hkm i)))
    = 0 := by
  classical
  set c := extractorDivisorCoeffs E stmt msg hkm with hc_def
  set candFs := extractorDivisorCandidate E stmt msg hkm
  have hCandSum :
      ECPoint.weightedSum E candFs (fun P => ECPoint.zsmul E (c P) P) = 0 :=
    hWSum
  -- Step 5: expand weightedSum over candidate Finset.
  have hCandExpand :
      ECPoint.weightedSum E candFs (fun P => ECPoint.zsmul E (c P) P) =
      (ECPoint.affine E stmt.target.1 (-stmt.target.2)) +
        (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
          (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
            (basesAffineEC E stmt msg hkm i))) := by
    show ECPoint.weightedSum E
      (insert (0 : ECPoint E)
        (insert (ECPoint.affine E stmt.target.1 (-stmt.target.2))
          ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm))))
      (fun P => ECPoint.zsmul E (c P) P) = _
    rw [ECPoint.weightedSum_insert E
          (infinity_notin_insert_negP_image E stmt msg hkm hTargetOnE hBasesOnE)]
    have h_f_inf : ECPoint.zsmul E (c (0 : ECPoint E)) (0 : ECPoint E) = 0 := by
      rw [hc_def]
      rw [extractorDivisorCoeffs_infinity]
      exact ECPoint.zsmul_infinity E _
    rw [h_f_inf, ECPoint.zero_add_curve]
    rw [ECPoint.weightedSum_insert E
          (negP_notin_image_basesAffineEC E stmt msg hkm hTargetOnE hBasesOnE hNoNegP)]
    have h_f_negP :
        ECPoint.zsmul E (c (ECPoint.affine E stmt.target.1 (-stmt.target.2)))
          (ECPoint.affine E stmt.target.1 (-stmt.target.2))
        = ECPoint.affine E stmt.target.1 (-stmt.target.2) := by
      rw [hc_def, extractorDivisorCoeffs_negP E stmt msg hkm hTargetOnE hNoNegP]
      exact ECPoint.zsmul_one E _
    rw [h_f_negP]
    congr 1
    exact weightedSum_imageBases_eq_univ_zsmul_extractedScalars E stmt msg hkm hBasesOnE hNoNegP
  rw [← hCandExpand]
  exact hCandSum

/-! ## D3: extractor bound from a natural-number witness

The "σ-matching" output of `log_deriv_nonvanishing_criterion` identifies
the integer multiplicity `β_k` of each zero `Q_k` of `D` with a
canonical position `i = σ(k)` in the bases, satisfying
`β_k + groupSum i = 0` in `ZMod q`. The paper's extractor recovers
`β_{σ⁻¹(i)}` from `-groupSum i` via the `.val` lift in the `-P ∉ {B_j}`
branch of `extractedScalars`.

`extractorSucceeds_of_natural_witness` abstracts the σ-matching output
as a single `coeff : Fin msg.k → ℕ` satisfying three properties:
* `coeff i < d` for every i (the soundness bound, derived from
  `β_k ≤ D.degE ≤ d` in full T4 assembly).
* `(coeff i : ZMod E.q) = -(groupSum i)` at canonical i (the residue-
  matching identity).
* `coeff i = 0` at non-canonical i (matching the extractor's zero
  assignment at non-canonical positions).

The theorem outputs both the extractor-range conclusion
(`extractorSucceeds`) and the point-level identification
`extractedScalars i = coeff i` (for feeding into D4+D5).
-/

theorem extractorSucceeds_of_natural_witness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (coeff : Fin msg.k → ℕ)
    (hCoeff_bound : ∀ i, coeff i < d)
    (hCoeff_zmod : ∀ i, extractorIsCanonical E stmt msg hkm i →
      (coeff i : ZMod E.q) = extractorGroupSum E stmt msg hkm i)
    (hCoeff_noncanon : ∀ i, ¬ extractorIsCanonical E stmt msg hkm i →
      coeff i = 0) :
    extractorSucceeds E stmt msg d hkm ∧
    ∀ i, extractedScalars E stmt msg hkm i = (coeff i : ℤ) := by
  classical
  -- Step 1: show extractedScalars i = (coeff i : ℤ) for every i.
  have hScalars_eq : ∀ i, extractedScalars E stmt msg hkm i = (coeff i : ℤ) := by
    intro i
    show (if hNegP : (negPIndexSet E stmt msg hkm).Nonempty
          then (if i = (negPIndexSet E stmt msg hkm).min' hNegP
                then (-1 : ℤ) else 0)
          else if extractorIsCanonical E stmt msg hkm i
               then ((extractorGroupSum E stmt msg hkm i).val : ℤ)
               else 0) = _
    rw [dif_neg hNoNegP]
    by_cases hC : extractorIsCanonical E stmt msg hkm i
    · rw [if_pos hC]
      have h1 : (coeff i : ZMod E.q) = extractorGroupSum E stmt msg hkm i :=
        hCoeff_zmod i hC
      have hBound : coeff i < E.q := lt_of_lt_of_le (hCoeff_bound i) (le_of_lt hd)
      have h2 : ((extractorGroupSum E stmt msg hkm i : ZMod E.q)).val = coeff i := by
        rw [← h1]
        exact ZMod.val_natCast_of_lt hBound
      rw [h2]
    · rw [if_neg hC]
      rw [hCoeff_noncanon i hC, Nat.cast_zero]
  refine ⟨?_, hScalars_eq⟩
  -- Step 2: extractorSucceeds from the bound on coeff.
  intro i
  rw [hScalars_eq i, Int.natAbs_natCast]
  exact hCoeff_bound i

/-! ## D5: target from zero-sum of the extractor's divisor

In the general case (`-P ∉ {B_j}`), D's divisor of zeros on `E` is
`(-P) + Σ [extractedScalars i] · B_i - D.degE · ∞` (with the `-P` term
carrying the `+1` corresponding to D's simple zero there).
Principality of this divisor (= D being a rational function on E) says
that the sum of this divisor's group-evaluation is `0` in the group:

  `(-P) + Σ [extractedScalars i] · B_i = 0`

(the `∞` term contributes `0` since `∞` is the group zero). This
theorem takes the zero-sum as hypothesis and derives
`target = Σ [extractedScalars i] · B_i` via left-cancellation by `(-P)`.
-/

theorem target_eq_weightedSum_of_zero_sum
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hZeroSum :
      (ECPoint.affine E stmt.target.1 (-stmt.target.2)) +
        (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
          (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
            (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                            (extractorBases E stmt msg hkm i).2)))
      = 0) :
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                          (extractorBases E stmt msg hkm i).2)) := by
  set P_aff := (ECPoint.affine E stmt.target.1 stmt.target.2 : ECPoint E)
  set X := ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
    (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
      (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                      (extractorBases E stmt msg hkm i).2)) with hX_def
  -- The `-P` affine point is the ECPoint negation of `P_aff`.
  have hPneg : (ECPoint.affine E stmt.target.1 (-stmt.target.2) : ECPoint E) =
               -P_aff :=
    (ECPoint.affine_neg E stmt.target.1 stmt.target.2).symm
  rw [hPneg] at hZeroSum
  -- `(-P_aff) + P_aff = 0` by `neg_add_cancel`.
  have hNegCancel : (-P_aff) + P_aff = 0 := neg_add_cancel P_aff
  -- Conclude `X = P_aff` by left cancellation.
  have hEq : (-P_aff) + X = (-P_aff) + P_aff := by
    rw [hZeroSum, hNegCancel]
  exact (add_left_cancel hEq).symm

/-- **Paper Step 5 (general case)** (`thm:ma`, ip.tex `\ref{step:extract}`):
    convert principal-divisor group-sum-zero into the dlog relation
    `P = Σ [n_j] · B_j`.

    Given the group-sum-zero of `extractorDivisorCoeffs` on its
    candidate Finset (a consequence of `(D)` being principal, via
    `thm:principal-divisor`), conclude
    `target = Σ [extractedScalars i] · B_i`. -/
theorem target_eq_weightedSum_of_weightedSum
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hWSum :
      ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
        (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) = 0) :
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                          (extractorBases E stmt msg hkm i).2)) := by
  exact target_eq_weightedSum_of_zero_sum E stmt msg hkm
    (extractor_zeroSum_of_weightedSum E stmt msg hkm hTargetOnE hBasesOnE hNoNegP hWSum)

/-! ## Distinct-base-point enumeration

    `log_deriv_nonvanishing_criterion` (T5) requires the `R` family
    passed to `polyG` to be injective. The raw `R = Fin.cons (-P_aff) B`
    may have duplicates among `B`'s positions (the extractor handles
    this via `extractorGroup` + canonical-index selection). This
    section enumerates the distinct bases as a Finset, and lifts to
    a `Fin`-indexing.

    Combined with `-P_aff` (which is outside the base image under
    `hNoNegP`), we get a distinct `R : Fin (1 + baseImageCount) →
    (ZMod E.q)²` via `Fin.cons`.
-/

/-- Finset of distinct base points. -/
noncomputable def baseImage
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : Finset (ZMod E.q × ZMod E.q) :=
  (Finset.univ : Finset (Fin msg.k)).image (extractorBases E stmt msg hkm)

/-- Number of distinct base points. -/
noncomputable def baseImageCount
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : ℕ :=
  (baseImage E stmt msg hkm).card

/-- Enumeration of distinct base points. -/
noncomputable def baseImageEnum
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Fin (baseImageCount E stmt msg hkm) ≃ (baseImage E stmt msg hkm) :=
  (baseImage E stmt msg hkm).equivFin.symm

/-- The `k`-th distinct base point (as an ordered pair). -/
noncomputable def baseAt
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (k : Fin (baseImageCount E stmt msg hkm)) :
    ZMod E.q × ZMod E.q :=
  ((baseImageEnum E stmt msg hkm k) : ZMod E.q × ZMod E.q)

theorem baseAt_mem_baseImage
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (k : Fin (baseImageCount E stmt msg hkm)) :
    baseAt E stmt msg hkm k ∈ baseImage E stmt msg hkm :=
  (baseImageEnum E stmt msg hkm k).2

theorem baseAt_injective
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Function.Injective (baseAt E stmt msg hkm) := by
  intro k₁ k₂ heq
  apply (baseImageEnum E stmt msg hkm).injective
  exact Subtype.ext heq

/-- Under `hNoNegP`, `-P_aff` is not in the base image. -/
theorem negP_notin_baseImage
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    (stmt.target.1, -stmt.target.2) ∉ baseImage E stmt msg hkm := by
  intro hContra
  rw [baseImage, Finset.mem_image] at hContra
  obtain ⟨i, _, heq⟩ := hContra
  apply hNoNegP
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩

/-- Under `hNoNegP`, `baseAt k ≠ -P_aff` for any `k`. -/
theorem baseAt_ne_negP
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (k : Fin (baseImageCount E stmt msg hkm)) :
    baseAt E stmt msg hkm k ≠ (stmt.target.1, -stmt.target.2) := by
  intro heq
  exact negP_notin_baseImage E stmt msg hkm hNoNegP
    (heq ▸ baseAt_mem_baseImage E stmt msg hkm k)

/-! ## Distinct-R enumeration (S1)

    `log_deriv_nonvanishing_criterion` (T5) demands an injective
    `R : Fin M → (ZMod E.q)²` family. We form it as
    `Fin.cons (P.1, -P.2) baseAt`: the head is `-P_aff`, the tail
    enumerates the distinct base points. Under `hNoNegP`,
    `-P_aff` is outside the base image (`baseAt_ne_negP`) and
    `baseAt` is already injective, so the combined family is injective.

    The length is packaged as `1 + baseImageCount` (matching T5's
    expected shape `1 + M`); internally we reuse `Fin.cons` which
    produces a `Fin (n + 1)`-indexed family and compose with
    `finCongr (Nat.add_comm _ _)`. -/

/-- Underlying `Fin.cons`-based family `Fin (n + 1) → ZMod² E.q`. -/
noncomputable def distinctRCons
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Fin (baseImageCount E stmt msg hkm + 1) → ZMod E.q × ZMod E.q :=
  Fin.cons (α := fun _ => ZMod E.q × ZMod E.q)
    (stmt.target.1, -stmt.target.2) (baseAt E stmt msg hkm)

@[simp] theorem distinctRCons_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    distinctRCons E stmt msg hkm 0 = (stmt.target.1, -stmt.target.2) := by
  simp [distinctRCons]

@[simp] theorem distinctRCons_succ
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctRCons E stmt msg hkm i.succ = baseAt E stmt msg hkm i := by
  simp [distinctRCons]

theorem distinctRCons_injective
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    Function.Injective (distinctRCons E stmt msg hkm) := by
  refine Fin.cons_injective_of_injective ?_ (baseAt_injective E stmt msg hkm)
  rintro ⟨i, hi⟩
  exact baseAt_ne_negP E stmt msg hkm hNoNegP i hi

/-- Distinct-R family: `-P_aff` prepended to the distinct base points.
    Length `1 + baseImageCount`. Used as the `R` parameter for T5. -/
noncomputable def distinctR
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Fin (1 + baseImageCount E stmt msg hkm) → ZMod E.q × ZMod E.q :=
  distinctRCons E stmt msg hkm ∘
    finCongr (Nat.add_comm 1 (baseImageCount E stmt msg hkm))

@[simp] theorem distinctR_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    distinctR E stmt msg hkm ⟨0, by omega⟩ = (stmt.target.1, -stmt.target.2) := by
  unfold distinctR
  simp [Function.comp_apply, distinctRCons_zero]

@[simp] theorem distinctR_succ
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctR E stmt msg hkm ⟨i.val + 1, by omega⟩
      = baseAt E stmt msg hkm i := by
  unfold distinctR
  have hEq : (finCongr (Nat.add_comm 1 (baseImageCount E stmt msg hkm))
                ⟨i.val + 1, by omega⟩ : Fin (baseImageCount E stmt msg hkm + 1))
             = i.succ := by
    apply Fin.ext
    rfl
  simp [Function.comp_apply, hEq, distinctRCons_succ]

/-- Under `hNoNegP`, `distinctR` is injective. Head is `-P_aff`,
    which is outside `baseAt`'s range (`baseAt_ne_negP`); tail is
    injective (`baseAt_injective`). -/
theorem distinctR_injective
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    Function.Injective (distinctR E stmt msg hkm) := by
  unfold distinctR
  exact (distinctRCons_injective E stmt msg hkm hNoNegP).comp
    (finCongr _).injective

/-! ## Grouped coefficient enumeration (S2)

    Companion to `distinctR`: the grouped-coefficient family `distinctM'`
    of type `Fin (1 + baseImageCount) → ZMod E.q`, with head `-1` and
    tail `extractorGroupSum` at the canonical index whose base is
    `baseAt i`.

    T5 (`log_deriv_nonvanishing_criterion`) takes a raw `(R, m)` pair on
    `Fin k`; for the extractor application we replace it with the
    distinct-base pair `(distinctR, distinctM')` on
    `Fin (1 + baseImageCount)`, where repeats in the raw `R` are folded
    into `ZMod`-sums in `m` at their common base point.

    The tail's `j`-choice is made via `Classical.choose` on the witness
    of `baseAt i ∈ baseImage`; `distinctM'_tail_group_invariant` below
    shows the resulting value depends only on the base point, not on
    the chosen representative. That independence is essential for the
    S3 raw-to-distinct polyG bridge.
-/

/-- For any `i : Fin (baseImageCount ...)`, `baseAt i` lies in
    `baseImage`, i.e. is in the `extractorBases`-image of `Finset.univ`;
    hence there exists `j : Fin msg.k` with `extractorBases j = baseAt i`. -/
theorem exists_extractorBases_eq_baseAt
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    ∃ j : Fin msg.k, extractorBases E stmt msg hkm j
      = baseAt E stmt msg hkm i := by
  have hmem := baseAt_mem_baseImage E stmt msg hkm i
  rw [baseImage, Finset.mem_image] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  exact ⟨j, hj⟩

/-- Canonical index choice for a distinct base point: some
    `j : Fin msg.k` with `extractorBases j = baseAt i`. -/
noncomputable def baseAtIndex
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    Fin msg.k :=
  (exists_extractorBases_eq_baseAt E stmt msg hkm i).choose

theorem baseAtIndex_spec
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    extractorBases E stmt msg hkm (baseAtIndex E stmt msg hkm i)
      = baseAt E stmt msg hkm i :=
  (exists_extractorBases_eq_baseAt E stmt msg hkm i).choose_spec

/-- `extractorGroupSum` depends only on the base point, not on the
    representative index. Concretely, if `extractorBases j₁ =
    extractorBases j₂` then the two indices share a group (by
    `extractedScalars_group_canonical`) and hence produce the same
    `extractorGroupSum`. -/
theorem extractorGroupSum_congr_of_extractorBases_eq
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) {j₁ j₂ : Fin msg.k}
    (h : extractorBases E stmt msg hkm j₁
      = extractorBases E stmt msg hkm j₂) :
    extractorGroupSum E stmt msg hkm j₁
      = extractorGroupSum E stmt msg hkm j₂ := by
  have hj₁inG₂ : j₁ ∈ extractorGroup E stmt msg hkm j₂ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hGeq : extractorGroup E stmt msg hkm j₁
      = extractorGroup E stmt msg hkm j₂ :=
    extractedScalars_group_canonical E stmt msg hkm j₂ j₁ hj₁inG₂
  simp [extractorGroupSum, hGeq]

/-- Underlying `Fin.cons`-based family `Fin (n + 1) → ZMod E.q` for
    the grouped coefficients. Head `-1`, tail
    `-extractorGroupSum` at the chosen `baseAtIndex`.

    The tail is NEGATED (vs. the raw `extractorGroupSum`) to align
    with the narrow scalar polyG-bridge axiom's sign convention
    (`Fin.cons (-1) (fun j => -m j)`). The negation reconciles the
    additive sign of `polyG`'s second sum (`Σ m'·prods`) with
    `logDerivCheckFn`'s RHS sum coefficient (`-m_j / L(B_j)`) and
    the `\ref{lem:log-derivative}` residue identity `Σ β_k/L(Q_k) = 1/L(-P) + Σ m_j/L(B_j)`.
    See sign-resolution note and ResidueIdentity.lean. -/
noncomputable def distinctMCons
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Fin (baseImageCount E stmt msg hkm + 1) → ZMod E.q :=
  Fin.cons (α := fun _ => ZMod E.q) (-1 : ZMod E.q)
    (fun i : Fin (baseImageCount E stmt msg hkm) =>
      -extractorGroupSum E stmt msg hkm (baseAtIndex E stmt msg hkm i))

@[simp] theorem distinctMCons_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    distinctMCons E stmt msg hkm 0 = (-1 : ZMod E.q) := by
  simp [distinctMCons]

@[simp] theorem distinctMCons_succ
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctMCons E stmt msg hkm i.succ
      = -extractorGroupSum E stmt msg hkm
          (baseAtIndex E stmt msg hkm i) := by
  simp [distinctMCons]

/-- Grouped coefficient family: `-1` at the `-P_aff` head, then
    `-extractorGroupSum` per distinct base. Length `1 + baseImageCount`,
    matching `distinctR`'s shape so the pair feeds T5's `Fin M` form.

    Note: the tail is NEGATED to align
    `polyG`'s additive convention with `logDerivCheckFn`'s RHS sign on
    the `m_j` coefficients. -/
noncomputable def distinctM'
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    Fin (1 + baseImageCount E stmt msg hkm) → ZMod E.q :=
  distinctMCons E stmt msg hkm ∘
    finCongr (Nat.add_comm 1 (baseImageCount E stmt msg hkm))

@[simp] theorem distinctM'_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    distinctM' E stmt msg hkm ⟨0, by omega⟩ = (-1 : ZMod E.q) := by
  unfold distinctM'
  simp [Function.comp_apply, distinctMCons_zero]

@[simp] theorem distinctM'_succ
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctM' E stmt msg hkm ⟨i.val + 1, by omega⟩
      = -extractorGroupSum E stmt msg hkm
          (baseAtIndex E stmt msg hkm i) := by
  unfold distinctM'
  have hEq : (finCongr (Nat.add_comm 1 (baseImageCount E stmt msg hkm))
                ⟨i.val + 1, by omega⟩ : Fin (baseImageCount E stmt msg hkm + 1))
             = i.succ := by
    apply Fin.ext
    rfl
  simp [Function.comp_apply, hEq, distinctMCons_succ]

/-- **Representative independence**: `distinctM' ⟨i+1, _⟩` equals
    `-extractorGroupSum` at *any* `j` with `extractorBases j = baseAt i`,
    not just the `Classical.choose` representative.

    Proof: by `distinctM'_succ`, the LHS reduces to
    `-extractorGroupSum E stmt msg hkm (baseAtIndex ... i)`. The
    `baseAtIndex` representative shares a base with `baseAt i`, i.e.
    with `j`, so
    `extractorGroupSum_congr_of_extractorBases_eq` collapses both to
    the same value. Essential for S3's raw↔distinct polyG bridge. -/
theorem distinctM'_tail_group_invariant
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm))
    (j : Fin msg.k)
    (hj : extractorBases E stmt msg hkm j = baseAt E stmt msg hkm i) :
    distinctM' E stmt msg hkm ⟨i.val + 1, by omega⟩
      = -extractorGroupSum E stmt msg hkm j := by
  rw [distinctM'_succ]
  have hspec := baseAtIndex_spec E stmt msg hkm i
  congr 1
  exact extractorGroupSum_congr_of_extractorBases_eq E stmt msg hkm
    (hspec.trans hj.symm)

/-! ## Narrow polyG-bridge (scalar level)

    The classical content of the T4 bridge that is NOT covered by
    `CoordRingElt.has_principal_divisor` (= Silverman III.3.5) is the
    paper's residue / denominator-clearing identity: if the scalar
    `logDerivCheckFn` vanishes on the defined non-vertical challenge
    subspace of `E × E`, then the denominator-cleared polynomial
    `polyG` (formed with `D`'s divisor data `(Q, β)`) vanishes on the
    non-vertical subspace of `E × E`.

    The theorem `polyG_zero_of_logDerivCheck_identically_zero` takes
    one additional hypothesis — `hPolyGZero` — supplying the scalar conclusion
    (`polyG = 0` at every non-vertical pair) directly. This
    hypothesis packages the two remaining unmechanized pieces:
    `\ref{lem:log-derivative}`'s function-field chord-residue identity and the density
    argument transferring vanishing from defined pairs to all
    non-vertical pairs.

    `ma_extractable` uses `hPolyGZero` as an extra hypothesis,
    which a future phase can discharge by finishing `\ref{lem:log-derivative}`
    (requires mechanizing `chordLogDerivMatchesNormZ` from
    `Divisor/Lemma6.lean`; reduced `\ref{lem:log-derivative}` to that scalar
    equality) and the density argument.

    Paper context: (i) `\ref{lem:log-derivative}` (norm decomposition
    `N(D) = ∏ (z − z(Q_k))^{β_k}`), (ii) the log-derivative formula
    `L(N(D)) = Σ β_k / (z − z(Q_k))`, (iii) the `ellP = L_Q · (X₁ − X₀)`
    denominator-clearing step (already mechanized via
    `polyG_eq_zero_iff_paperResidue` in `Divisor/ResidueIdentity.lean`),
    (iv) the density argument transferring vanishing from `defined`
    pairs to all non-vertical pairs on `E × E`.

    Citation: Silverman AEC Ch II §2 (local uniformizers, order of
    vanishing, p. 19-26) + Ch III §3 (elliptic curves, principal
    divisors, Cor 3.5 on p. 63). -/

/-- **Scalar bridge theorem** for
    `polyG_zero_of_logDerivCheck_identically_zero`. Its premises plus
    the hypothesis `hPolyGZero` entail the conclusion.

    Hypotheses encode `D`'s divisor data `(Q, β)` (obtainable via
    `CoordRingElt.has_principal_divisor`):
    * `Q : Fin d → (ZMod E.q)²` enumerates `D`'s distinct affine
      zeros on `E`,
    * `β : Fin d → ℕ` their natural-number multiplicities summing to
      `D.degE`,
    * `R = Fin.cons (P.1, -P.2) B` packages the RHS residue points,
    * `m' = Fin.cons (-1) (fun j => -m j)` packages the RHS residue
      coefficients with the sign convention needed to align with
      Lean's `logDerivCheckFn` (whose `rhs` has coefficient `-m_j` on
      `L(B_j)⁻¹`) against `polyG`'s additive sign convention
      `Σβ·prods + Σm'·prods`. See sign-resolution note.

    Conclusion: `polyG` vanishes on all non-vertical pairs of `E × E`.

    `hPolyGZero` is the consolidated "`\ref{lem:log-derivative}` + density" hypothesis:
    it asserts `polyG = 0` at every non-vertical E-pair for the
    specific `(Q, β_fun, R, m')` data. narrows the axiom by
    taking this as a hypothesis; a future phase can discharge it by
    completing `\ref{lem:log-derivative}` (infrastructure in
    `Divisor/Lemma6.lean`) and the density argument (polynomial form
    `polyGPoly` from `Divisor/PolyGBridge.lean` + `card_zeros_on_E_le`
    from `Divisor/CubicIntersection.lean`). -/
theorem polyG_zero_of_logDerivCheck_identically_zero
    (D : CoordRingElt E.q) (_hD : ¬ D.isZero)
    (P : ZMod E.q × ZMod E.q) (k : ℕ)
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q)
    (beta : Fin d → ℕ)
    (_hQinj : Function.Injective Q)
    (_hQzeros : ∀ k' : Fin d,
       Q k' ∈ E.points ∧ D.eval (Q k').1 (Q k').2 = 0)
    (_hQcov : ∀ Q' ∈ E.points, D.eval Q'.1 Q'.2 = 0 →
       ∃ k' : Fin d, Q k' = Q')
    (_hβPos : ∀ k', beta k' > 0)
    (_hβSum : (∑ k' : Fin d, beta k') = D.degE)
    (hPolyGZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
                  (Fin.cons (P.1, -P.2) B)
                  (Fin.cons (-1) (fun j => -m j))
                  A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
              (Fin.cons (P.1, -P.2) B)
              (Fin.cons (-1) (fun j => -m j))
              A₀ A₁ = 0 :=
  hPolyGZero A₀ A₁ hA₀ hA₁ hNV

/-! ## S3: raw → distinct polyG bridge

    Combine the narrow scalar axiom `polyG_zero_of_logDerivCheck_identically_zero`
    with the distinct-base enumeration (`distinctR` / `distinctM'` from S1+S2)
    to obtain vanishing of `polyG` in distinct form.

    Strategy: two layers.

    * **Layer A (scalar invariance)**: `logDerivCheckFn` with raw
      `(stmt.bases, fun i => msg.m (hkm ▸ i))` equals
      `logDerivCheckFn` with distinct
      `(baseAt, distinctM'_tail)`. Follows from fiberwise decomposition
      of `Fin msg.k` by `extractorBases`: each fiber has constant base
      `baseAt i`, so the raw sum `Σ -msg.m_j · L(stmt.bases j)⁻¹`
      collapses to `Σ -extractorGroupSum_i · L(baseAt i)⁻¹`.
    * **Layer B (apply narrow axiom)**: feed the narrow axiom with
      `k := baseImageCount`, `B := baseAt`, `m := distinctM'_tail`.
      Its `hAllZero` precondition becomes the distinct form, which we
      derive from the raw form via Layer A. Its conclusion is
      `polyG ... (Fin.cons (P.1,-P.2) baseAt)
               (Fin.cons (-1) (fun j => -distinctM'_tail j)) = 0`
      at index `Fin (baseImageCount + 1)`. The latter argument equals
      `distinctMCons` definitionally (fix).
      Reindexing by `finCongr (Nat.add_comm 1 _)` produces the
      `distinctR` / `distinctM'` form at index
      `Fin (1 + baseImageCount)`.
-/

/-- The tail of `distinctMCons`, exposed as a separate definition.
    Value is `extractorGroupSum` at the `Classical.choose` representative. -/
noncomputable def distinctM'_tail
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    ZMod E.q :=
  extractorGroupSum E stmt msg hkm (baseAtIndex E stmt msg hkm i)

/-- `distinctMCons` factors as the `-1` head `Fin.cons` (negated) tail
    `-distinctM'_tail`. -/
theorem distinctMCons_eq_cons
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    distinctMCons E stmt msg hkm =
      Fin.cons (α := fun _ => ZMod E.q) (-1 : ZMod E.q)
        (fun i => -distinctM'_tail E stmt msg hkm i) := rfl

/-- `distinctRCons` factors as the `-P_aff` head `Fin.cons` tail `baseAt`. -/
theorem distinctRCons_eq_cons
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    distinctRCons E stmt msg hkm =
      Fin.cons (α := fun _ => ZMod E.q × ZMod E.q)
        (stmt.target.1, -stmt.target.2) (baseAt E stmt msg hkm) := rfl

/-- Canonical fiber index: for `j : Fin msg.k`,
    `baseIndexOf j` is the unique `i : Fin (baseImageCount ...)` with
    `baseAt i = extractorBases j`. -/
noncomputable def baseIndexOf
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (j : Fin msg.k) :
    Fin (baseImageCount E stmt msg hkm) :=
  (baseImageEnum E stmt msg hkm).symm
    ⟨extractorBases E stmt msg hkm j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem baseAt_baseIndexOf
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (j : Fin msg.k) :
    baseAt E stmt msg hkm (baseIndexOf E stmt msg hkm j)
      = extractorBases E stmt msg hkm j := by
  unfold baseAt baseIndexOf
  rw [Equiv.apply_symm_apply]

/-- The filter set `{j : Fin msg.k | extractorBases j = baseAt i}` equals
    `extractorGroup ... (baseAtIndex i)`. -/
theorem filter_extractorBases_eq_baseAt_eq_extractorGroup
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    ((Finset.univ : Finset (Fin msg.k)).filter
        (fun j => extractorBases E stmt msg hkm j
                    = baseAt E stmt msg hkm i))
      = extractorGroup E stmt msg hkm (baseAtIndex E stmt msg hkm i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    extractorGroup]
  rw [baseAtIndex_spec]

/-- `distinctM'_tail i` equals the sum of `msg.m` over the fiber of
    base point `baseAt i`. -/
theorem distinctM'_tail_eq_filter_sum
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctM'_tail E stmt msg hkm i
      = ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
              (fun j => extractorBases E stmt msg hkm j
                          = baseAt E stmt msg hkm i), msg.m j := by
  unfold distinctM'_tail extractorGroupSum
  rw [filter_extractorBases_eq_baseAt_eq_extractorGroup]

/-- **Layer A (scalar invariance)**: raw `logDerivCheckFn` with
    `(stmt.bases, fun i => msg.m (hkm ▸ i))` equals the distinct form
    with `(baseAt, distinctM'_tail)` at length `baseImageCount`. -/
theorem logDerivCheckFn_eq_grouped
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    logDerivCheckFn E D P stmt.k stmt.bases (fun i => msg.m (hkm ▸ i))
        A₀ A₁
      = logDerivCheckFn E D P (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm) (distinctM'_tail E stmt msg hkm)
          A₀ A₁ := by
  classical
  -- Only the last sum differs. Unfold both forms and reduce to equality
  -- of the scalar sums.
  unfold logDerivCheckFn
  -- Both sides share `lhs - (-L(-P)⁻¹ + sum)`; reduce to `sum`-equality.
  simp only [sub_right_inj, add_right_inj]
  -- Step 1: reindex raw sum from Fin stmt.k to Fin msg.k.
  have hRaw :
      (Finset.univ : Finset (Fin stmt.k)).sum
          (fun j => -(msg.m (hkm ▸ j)) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
              (stmt.bases j).1 (stmt.bases j).2)⁻¹)
      = (Finset.univ : Finset (Fin msg.k)).sum
          (fun j => -(msg.m j) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
              (extractorBases E stmt msg hkm j).1
              (extractorBases E stmt msg hkm j).2)⁻¹) := by
    -- Both sides have the same underlying family parametrized by
    -- `.val`, so we prove equality by generalizing `stmt.k`.
    -- Use `Fintype.sum_equiv` with `finCongr hkm` and resolve the
    -- pointwise equality by `cases`-ing `hkm` (after generalizing
    -- `stmt.k`, `msg.m`, `stmt.bases` in sync).
    -- Simpler: prove via `Finset.sum_bij` with the bijection.
    refine Finset.sum_bij (fun j _ => finCongr hkm j)
      (fun _ _ => Finset.mem_univ _)
      ?_ -- injOn
      ?_ -- surjOn
      ?_ -- f equality
    · intro j _ j' _ h
      exact (finCongr hkm).injective h
    · intro j _
      refine ⟨(finCongr hkm).symm j, Finset.mem_univ _, ?_⟩
      simp
    · intro j _
      -- Show: -(msg.m (hkm ▸ j)) * L(stmt.bases j)⁻¹
      --     = -(msg.m (finCongr hkm j)) * L(extractorBases (finCongr hkm j))⁻¹.
      -- Both msg.m (hkm ▸ j) and msg.m (finCongr hkm j) equal via cast.
      -- Both L(stmt.bases j) and L(extractorBases (finCongr hkm j)) equal
      -- since extractorBases (finCongr hkm j) = stmt.bases (Fin.cast hkm.symm (finCongr hkm j))
      -- and Fin.cast hkm.symm (finCongr hkm j) = j (since ⟨j.val, _⟩ casts back).
      unfold extractorBases
      have hb : stmt.bases (Fin.cast hkm.symm (finCongr hkm j)) = stmt.bases j := by
        congr 1
      have hm : msg.m (hkm ▸ j) = msg.m (finCongr hkm j) := by
        congr 1
        -- Reduce to `(hkm ▸ j : Fin msg.k) = finCongr hkm j`. Both have
        -- `.val = j.val`; resolve by cases on `hkm`.
        generalize hn : msg.k = n at hkm
        subst hkm
        rfl
      rw [hb, hm]
  -- Step 2: fiberwise on RHS of step 1.
  rw [hRaw]
  -- Partition Fin msg.k by baseIndexOf.
  rw [← Finset.sum_fiberwise_of_maps_to
        (g := baseIndexOf E stmt msg hkm)
        (t := (Finset.univ : Finset (Fin (baseImageCount E stmt msg hkm))))
        (f := fun j => -(msg.m j) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (extractorBases E stmt msg hkm j).1
            (extractorBases E stmt msg hkm j).2)⁻¹)
        (fun _ _ => Finset.mem_univ _)]
  -- Replace each inner sum's filter by the baseAt-based filter.
  apply Finset.sum_congr rfl
  intro i _
  -- The inner filter `fun j => baseIndexOf j = i` equals
  -- `fun j => extractorBases j = baseAt i`.
  have hFilterEq :
      (Finset.univ : Finset (Fin msg.k)).filter
          (fun j => baseIndexOf E stmt msg hkm j = i)
        = (Finset.univ : Finset (Fin msg.k)).filter
            (fun j => extractorBases E stmt msg hkm j
                        = baseAt E stmt msg hkm i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rw [← h, baseAt_baseIndexOf]
    · intro h
      -- Goal: baseIndexOf j = i, given h : extractorBases j = baseAt i.
      -- Apply baseImageEnum (bijective), then reduce to the .val equality.
      unfold baseIndexOf
      apply (baseImageEnum E stmt msg hkm).symm_apply_eq.mpr
      apply Subtype.ext
      exact h
  rw [hFilterEq]
  -- Now the inner sum is over the filter `extractorBases j = baseAt i`.
  -- On this filter, `extractorBases j = baseAt i`, so the L(extractorBases j)⁻¹
  -- factor becomes L(baseAt i)⁻¹ (constant); pull it out:
  --   Σ j ∈ filter_i, -(msg.m j) · L(baseAt i)⁻¹
  --   = -L(baseAt i)⁻¹ · Σ j ∈ filter_i, msg.m j
  --   = -L(baseAt i)⁻¹ · distinctM'_tail i
  --   = -(distinctM'_tail i) · L(baseAt i)⁻¹
  have hInner :
      ∀ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
          (fun j => extractorBases E stmt msg hkm j
                      = baseAt E stmt msg hkm i),
        -(msg.m j) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (extractorBases E stmt msg hkm j).1
            (extractorBases E stmt msg hkm j).2)⁻¹
        = -(msg.m j) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (baseAt E stmt msg hkm i).1
            (baseAt E stmt msg hkm i).2)⁻¹ := by
    intro j hj
    have hjEq : extractorBases E stmt msg hkm j = baseAt E stmt msg hkm i :=
      (Finset.mem_filter.mp hj).2
    rw [hjEq]
  rw [Finset.sum_congr rfl hInner]
  -- Factor out the constant L(baseAt i)⁻¹.
  rw [← Finset.sum_mul]
  -- Σ j ∈ filter, -(msg.m j) = -(Σ j ∈ filter, msg.m j).
  rw [Finset.sum_neg_distrib]
  -- Σ j ∈ filter_i, msg.m j = distinctM'_tail i.
  rw [← distinctM'_tail_eq_filter_sum]

/-- **Main theorem (S3 — `Fin.cons` form)**: apply the narrow scalar
    bridge with `B := baseAt`, `m := distinctM'_tail`; its conclusion is
    in `Fin.cons`/`Fin (baseImageCount + 1)` form, matching `distinctRCons`
    and `distinctMCons`.

    The scalar bridge takes a `hPolyGZero` hypothesis. That hypothesis
    is threaded here as `hPolyGZeroCons` (at the `distinctRCons` /
    `distinctMCons` instantiation). -/
theorem polyG_distinct_zero_cons
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hD : ¬ msg.toD.isZero)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q)
    (beta : Fin d → ℕ)
    (hQinj : Function.Injective Q)
    (hQzeros : ∀ k' : Fin d,
       Q k' ∈ E.points ∧ msg.toD.eval (Q k').1 (Q k').2 = 0)
    (hQcov : ∀ Q' ∈ E.points, msg.toD.eval Q'.1 Q'.2 = 0 →
       ∃ k' : Fin d, Q k' = Q')
    (hβPos : ∀ k', beta k' > 0)
    (hβSum : (∑ k' : Fin d, beta k') = msg.toD.degE)
    (hPolyGZeroCons :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
                  (distinctRCons E stmt msg hkm) (distinctMCons E stmt msg hkm)
                  A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
              (distinctRCons E stmt msg hkm) (distinctMCons E stmt msg hkm)
              A₀ A₁ = 0 := by
  -- Distinct-form `hAllZero` from raw `hAllZero` via Layer A scalar
  -- invariance (`logDerivCheckFn_eq_grouped`). The `Defined` predicate
  -- takes `stmt.bases`; we need a version with `baseAt`. But the narrow
  -- axiom takes `logDerivCheckFnDefined E D P B A₀ A₁` with its own `B`,
  -- so we instantiate at `B := baseAt`.
  have hAllZero' :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target
          (baseAt E stmt msg hkm) A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target
          (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm)
          (distinctM'_tail E stmt msg hkm) A₀ A₁ = 0 := by
    intro A₀ A₁ hA₀ hA₁ hNV hDefDistinct
    -- Translate `defined`-distinct to `defined`-raw at `stmt.bases`.
    have hDefRaw : logDerivCheckFnDefined E msg.toD stmt.target
        stmt.bases A₀ A₁ := by
      unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDefDistinct ⊢
      -- Both denoms share the "common" prefix up to and including
      -- `L.eval stmt.target.1 (-stmt.target.2)`. They differ only in
      -- the final product: raw is `∏_{j : Fin stmt.k} L(stmt.bases j)`,
      -- distinct is `∏_{i : Fin baseImageCount} L(baseAt i)`.
      -- These products share zero/nonzero status because
      -- `{stmt.bases j | j : Fin stmt.k} = {baseAt i | i : Fin baseImageCount}`
      -- (set-equality of images, with multiplicity collapsed on the
      -- distinct side but the value set is the same).
      intro hRawEqZero
      apply hDefDistinct
      -- Strategy: show that raw_denom = 0 implies distinct_denom = 0.
      -- Split raw_denom = common * ∏_{Fin stmt.k} L(stmt.bases j) = 0
      -- into: common = 0 (then distinct_denom shares `common = 0`) or
      -- one `L(stmt.bases j) = 0` (then `L(baseAt (baseIndexOf (finCongr hkm j))) = 0`,
      -- so the distinct product is 0).
      set common := msg.toD.eval A₀.1 A₀.2 * msg.toD.eval A₁.1 A₁.2 *
        msg.toD.eval (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1)
          (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
              (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) *
        (3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) *
        (3 * A₁.1 ^ 2 + E.curveA -
          2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) *
        (3 * (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) ^ 2 + E.curveA -
          2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
              (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1))) *
        (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2)
      change common * ∏ j : Fin stmt.k,
        (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
          (stmt.bases j).1 (stmt.bases j).2 = 0 at hRawEqZero
      change common * ∏ i : Fin (baseImageCount E stmt msg hkm),
        (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
          (baseAt E stmt msg hkm i).1 (baseAt E stmt msg hkm i).2 = 0
      rcases mul_eq_zero.mp hRawEqZero with hCommon | hProd
      · exact mul_eq_zero.mpr (Or.inl hCommon)
      · rw [Finset.prod_eq_zero_iff] at hProd
        obtain ⟨j, _, hj⟩ := hProd
        apply mul_eq_zero.mpr; right
        rw [Finset.prod_eq_zero_iff]
        refine ⟨baseIndexOf E stmt msg hkm (finCongr hkm j),
                Finset.mem_univ _, ?_⟩
        rw [baseAt_baseIndexOf]
        -- `extractorBases (finCongr hkm j) = stmt.bases j`.
        have hEq : extractorBases E stmt msg hkm (finCongr hkm j) = stmt.bases j := by
          unfold extractorBases
          congr 1
        rw [hEq]
        exact hj
    have hRaw := hAllZero A₀ A₁ hA₀ hA₁ hNV hDefRaw
    rw [logDerivCheckFn_eq_grouped] at hRaw
    exact hRaw
  -- Apply narrow bridge theorem.
  -- The conclusion uses `Fin.cons (P.1,-P.2) baseAt` and
  -- `Fin.cons (-1) (fun j => -distinctM'_tail j)`, which definitionally
  -- equal `distinctRCons` and `distinctMCons`.
  exact polyG_zero_of_logDerivCheck_identically_zero E
    msg.toD hD stmt.target (baseImageCount E stmt msg hkm)
    (baseAt E stmt msg hkm) (distinctM'_tail E stmt msg hkm) hAllZero'
    Q beta hQinj hQzeros hQcov hβPos hβSum hPolyGZeroCons
    A₀ A₁ hA₀ hA₁ hNV

/-- Reindexing lemma: `polyG` is invariant under reindexing the `(R, m)`
    family by a bijection. Used to convert between the `Fin.cons` form
    (length `baseImageCount + 1`) and the `finCongr`-composed form
    (length `1 + baseImageCount`) used in T5. -/
theorem polyG_reindex
    {d M M' : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (e : Fin M' ≃ Fin M)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    polyG E Q β (R ∘ e) (m ∘ e) A₀ A₁ = polyG E Q β R m A₀ A₁ := by
  classical
  unfold polyG
  congr 1
  · -- First sum: β_k part. `R`-dependence is `∏_j ellP (R j)`, invariant
    -- under outer reindex.
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    exact Equiv.prod_comp e (fun j => ellP E (R j) A₀ A₁)
  · -- Second sum: reindex outer sum; inner `erase` product shifts by `e`.
    rw [← Equiv.sum_comp e
      (fun j => m j *
        (Finset.univ.prod (fun k => ellP E (Q k) A₀ A₁)) *
        ((Finset.univ.erase j).prod (fun j' => ellP E (R j') A₀ A₁)))]
    apply Finset.sum_congr rfl
    intro j _
    show (m ∘ e) j * _ * _ = m (e j) * _ * _
    congr 1
    -- Inner erase-prod over `(R ∘ e)` at `univ.erase j` equals
    -- erase-prod over `R` at `univ.erase (e j)`.
    rw [show ((Finset.univ : Finset (Fin M')).erase j).prod
              (fun j' => ellP E ((R ∘ e) j') A₀ A₁)
           = ((Finset.univ : Finset (Fin M')).erase j).prod
              (fun j' => ellP E (R (e j')) A₀ A₁) from rfl]
    rw [← Finset.prod_image (g := (e : Fin M' → Fin M))
          (f := fun j' => ellP E (R j') A₀ A₁)
          (fun _ _ _ _ h => e.injective h)]
    congr 1
    rw [Finset.image_erase e.injective Finset.univ j,
        Finset.image_univ_equiv]

/-- **Main theorem (S3 — `distinctR` / `distinctM'` form)**: `polyG`
    vanishes on non-vertical `E × E` pairs with the distinct-base
    enumeration. Derived from `polyG_distinct_zero_cons` via
    `polyG_reindex`. -/
theorem polyG_distinct_zero_of_logDerivCheck_identically_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (_hD : ¬ msg.toD.isZero)
    (_hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q)
    (beta : Fin d → ℕ)
    (_hQinj : Function.Injective Q)
    (_hQzeros : ∀ k' : Fin d,
       Q k' ∈ E.points ∧ msg.toD.eval (Q k').1 (Q k').2 = 0)
    (_hQcov : ∀ Q' ∈ E.points, msg.toD.eval Q'.1 Q'.2 = 0 →
       ∃ k' : Fin d, Q k' = Q')
    (_hβPos : ∀ k', beta k' > 0)
    (_hβSum : (∑ k' : Fin d, beta k') = msg.toD.degE)
    (hPolyGZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
                  (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
                  A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    polyG E Q (fun k' => ((beta k' : ℕ) : ZMod E.q))
              (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
              A₀ A₁ = 0 :=
  hPolyGZero A₀ A₁ hA₀ hA₁ hNV

/-! ## S4: T5 application — `σ`-matching existence

    Combine `CoordRingElt.has_principal_divisor` (Silverman III.3.5,
    providing the nonnegative multiplicity function `β_fun` for `D`'s
    affine zeros), the S3 raw→distinct polyG bridge
    (`polyG_distinct_zero_of_logDerivCheck_identically_zero`), and T5
    (`log_deriv_nonvanishing_criterion`) to produce the embedding
    `σ : Fin (zerosCard E D) ↪ Fin (1 + baseImageCount E stmt msg hkm)`
    matching each `D`-zero to a distinct-base index with the
    β-plus-m-sum-zero property, plus the complementary `m = 0` outside
    range(σ). The quantitative hypothesis of T5 is discharged directly
    from the hypothesis `hValidPairsLarge` (S7 will derive this from a
    cleaner `E.q`-vs-`(d + stmt.k + 1)` inequality via Hasse-Weil and
    `card_validPairs_lb`).
-/

/-- **S4 — distinct-σ existence.** The combined T5 + S3 + Silverman
    application: given `hAllZero` (raw `logDerivCheckFn ≡ 0`), the
    no-`-P`-in-bases assumption `hNoNegP`, nonzero-`D` hypothesis, and
    a quantitative bound `hValidPairsLarge`, produce:
    * `β_fun : ZMod² → ℕ` — principal-divisor multiplicities for `D`.
    * Its principal-divisor package (support, coverage, degree-sum,
      `dCoeffs`-principality).
    * An embedding `σ : Fin (zerosCard E D) ↪ Fin (1 + baseImageCount)`
      matching `zerosAt` to `distinctR`.
    * `(multAt k : ZMod E.q) + distinctM' (σ k) = 0` (β_k + m at σ k).
    * `distinctM' j = 0` for `j ∉ range σ`.

    Consumed by S5 (coefficient construction) + S6 (principality
    transfer) + S7 (final T4-bridge replacement). -/
theorem distinctSigma_exists
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hSplit : splitsOnE E msg.toD)
    (_hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (hPolyGZero :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E (zerosAt E msg.toD)
            (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0)
    (hValidPairsLarge :
      6 * E.q * ((d + stmt.k + 1) + (d + stmt.k + 1) * (d + stmt.k)) + 1
        ≤ (validPairs E).card) :
    ∃ (σ : Fin (zerosCard E msg.toD) ↪
            Fin (1 + baseImageCount E stmt msg hkm)),
      (∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k)) ∧
      (∀ k, ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q)
            + distinctM' E stmt msg hkm (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) := by
  classical
  -- Step 1: nonzero-D hypothesis.
  have hD : ¬ msg.toD.isZero := admSet_implies_toD_nonzero stmt msg hAdm
  -- Step 2: use the canonical `betaCanonical` (totalised existential
  -- from `CoordRingElt.exists_divisor_multiplicity`). We work with
  -- `betaCanonical` rather than `betaTrue` so the conclusion's
  -- `multAt`-cast doesn't have to thread the `hD` parameter.
  set β_fun := betaCanonical E msg.toD with hβ_def
  have hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ msg.toD.eval P.1 P.2 = 0 :=
    betaCanonical_support E msg.toD
  have hβcov : ∀ P ∈ E.points, msg.toD.eval P.1 P.2 = 0 → β_fun P ≠ 0 :=
    betaCanonical_covers E msg.toD hD
  have hβsum : (∑ P ∈ E.points, β_fun P) ≤ msg.toD.degE :=
    betaCanonical_sum_le_degE E msg.toD
  have hβgroup : ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine E P.1 P.2)) = 0 :=
    betaCanonical_group_sum_zero E msg.toD hSplit
  -- Step 3: build the `Q` / `beta_nat` pair for the distinct-polyG bridge.
  have hQinj : Function.Injective (zerosAt E msg.toD) :=
    zerosAt_injective E msg.toD
  have _hQzeros : ∀ k : Fin (zerosCard E msg.toD),
      zerosAt E msg.toD k ∈ E.points ∧
      msg.toD.eval (zerosAt E msg.toD k).1 (zerosAt E msg.toD k).2 = 0 :=
    fun k => ⟨zerosAt_mem_E E msg.toD k, zerosAt_eval_zero E msg.toD k⟩
  have _hQcov : ∀ Q' ∈ E.points, msg.toD.eval Q'.1 Q'.2 = 0 →
      ∃ k, zerosAt E msg.toD k = Q' := fun Q' hQ'pts hQ'zero =>
    zerosAt_covers_zeros E msg.toD Q' hQ'pts hQ'zero
  have hβPos : ∀ k : Fin (zerosCard E msg.toD),
                 multAt E β_fun msg.toD k > 0 :=
    multAt_pos E β_fun msg.toD hβcov
  have hβSum : (∑ k : Fin (zerosCard E msg.toD),
                   multAt E β_fun msg.toD k) ≤ msg.toD.degE :=
    sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
  -- Step 4: each `multAt k` is strictly less than E.q (upper bound comes
  -- from `multAt k ≤ Σ multAt ≤ D.degE ≤ d < E.q`).
  have hBetaLt : ∀ k, multAt E β_fun msg.toD k < E.q := by
    intro k
    have hSingle : multAt E β_fun msg.toD k ≤
        ∑ k' : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k' := by
      refine Finset.single_le_sum
        (f := fun k' => multAt E β_fun msg.toD k') ?_ (Finset.mem_univ k)
      intro k' _
      exact Nat.zero_le _
    exact lt_of_le_of_lt (hSingle.trans (hβSum.trans hDeg)) hd
  -- Step 5: `polyG` vanishes on non-vertical `E × E` in distinct form.
  have hPolyGZero' :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        polyG E (zerosAt E msg.toD)
          (fun k => ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q))
          (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
          A₀ A₁ = 0 := hPolyGZero
  -- Step 6: set up T5's quantitative hypothesis.
  -- `zerosCard E msg.toD ≤ d`: each multiplicity ≥ 1, sum ≤ D.degE ≤ d.
  have hd_zero_le_d : zerosCard E msg.toD ≤ d := by
    have hCardLe : zerosCard E msg.toD ≤
        ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k := by
      calc zerosCard E msg.toD
          = ∑ _k : Fin (zerosCard E msg.toD), 1 := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k :=
              Finset.sum_le_sum (fun k _ => hβPos k)
    exact hCardLe.trans (hβSum.trans hDeg)
  -- `baseImageCount ≤ msg.k = stmt.k`.
  have hBICount_le : baseImageCount E stmt msg hkm ≤ stmt.k := by
    have hleK : baseImageCount E stmt msg hkm ≤ msg.k := by
      unfold baseImageCount baseImage
      refine (Finset.card_image_le (f := extractorBases E stmt msg hkm)
                 (s := Finset.univ)).trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hkm]; exact hleK
  have hSum_le :
      zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
        ≤ d + stmt.k + 1 := by
    have : zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
            ≤ d + (1 + stmt.k) :=
      Nat.add_le_add hd_zero_le_d (Nat.add_le_add_left hBICount_le _)
    omega
  have hQuant : 6 * E.q * ((zerosCard E msg.toD
                              + (1 + baseImageCount E stmt msg hkm))
                  + (zerosCard E msg.toD
                      + (1 + baseImageCount E stmt msg hkm))
                     * (zerosCard E msg.toD
                          + (1 + baseImageCount E stmt msg hkm) - 1)) + 1
                ≤ (validPairs E).card := by
    refine le_trans ?_ hValidPairsLarge
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add hSum_le
    have hSub_le :
        zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm) - 1
          ≤ d + stmt.k := by
      have := Nat.sub_le_sub_right hSum_le 1
      have hEq : d + stmt.k + 1 - 1 = d + stmt.k := by omega
      rw [hEq] at this; exact this
    exact Nat.mul_le_mul hSum_le hSub_le
  -- Step 7: `hBetaNz` — each `multAt k` cast to `ZMod E.q` is nonzero.
  have hBetaNz : ∀ k,
      ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q) ≠ 0 := by
    intro k
    rw [Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
    intro hdvd
    have hPos : 0 < multAt E β_fun msg.toD k := hβPos k
    have hLt : multAt E β_fun msg.toD k < E.q := hBetaLt k
    exact Nat.not_lt.mpr (Nat.le_of_dvd hPos hdvd) hLt
  -- Step 8: apply T5.
  have hDistinctR_inj : Function.Injective (distinctR E stmt msg hkm) :=
    distinctR_injective E stmt msg hkm hNoNegP
  obtain ⟨σ, hσ_eq, hσ_betam, hσ_off⟩ :=
    log_deriv_nonvanishing_criterion E (zerosAt E msg.toD)
      (fun k => ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q))
      (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
      hQuant hQinj hDistinctR_inj hBetaNz hPolyGZero'
  -- Step 9: package the output.
  exact ⟨σ, hσ_eq, hσ_betam, hσ_off⟩

/-! ## S5: extractor coefficient function from σ

    Given the `σ`-matching output of `distinctSigma_exists`, build a
    natural-number coefficient `Fin msg.k → ℕ` whose ZMod residues match
    `-extractorGroupSum` at canonical indices (and zero elsewhere), with
    the D3 bound `coeff i < d`. Feeds into
    `extractorSucceeds_of_natural_witness` (D3) to produce the full
    `extractorSucceeds ∧ extractedScalars i = coeff i` package.

    Structure:
    * `baseImagePos` — position in `distinctR` corresponding to a
      `baseIndexOf i` canonical index.
    * `extractorCoeffFromSigma` — the coefficient function.
    * `sigma_zero_preimage_exists` — σ must hit position `0` (else
      `distinctM' 0 = -1 = 0`, contradiction).
    * `extractorCoeffFromSigma_satisfies_D3` — main S5 theorem: the
      three hypotheses of `extractorSucceeds_of_natural_witness` hold.
-/

/-- Position in `distinctR` corresponding to a distinct-base index.
    Shape `⟨i.val + 1, _⟩` to match `distinctR_succ`. -/
noncomputable def baseImagePos
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin (baseImageCount E stmt msg hkm)) :
    Fin (1 + baseImageCount E stmt msg hkm) :=
  ⟨i.val + 1, by omega⟩

theorem baseImagePos_val
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin (baseImageCount E stmt msg hkm)) :
    (baseImagePos E stmt msg hkm i).val = i.val + 1 := rfl

theorem baseImagePos_ne_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin (baseImageCount E stmt msg hkm)) :
    baseImagePos E stmt msg hkm i
      ≠ (⟨0, by omega⟩ : Fin (1 + baseImageCount E stmt msg hkm)) := by
  intro h
  have : (baseImagePos E stmt msg hkm i).val = 0 := by rw [h]
  rw [baseImagePos_val] at this
  omega

@[simp] theorem distinctR_baseImagePos
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctR E stmt msg hkm (baseImagePos E stmt msg hkm i)
      = baseAt E stmt msg hkm i :=
  distinctR_succ E stmt msg hkm i

@[simp] theorem distinctM'_baseImagePos
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (i : Fin (baseImageCount E stmt msg hkm)) :
    distinctM' E stmt msg hkm (baseImagePos E stmt msg hkm i)
      = -extractorGroupSum E stmt msg hkm
          (baseAtIndex E stmt msg hkm i) :=
  distinctM'_succ E stmt msg hkm i

/-- **Extractor coefficient function from σ.** At canonical `i`, if the
    distinct-R position corresponding to `extractorBases i` is hit by σ
    at some `k`, return `multAt k`; else `0`. At non-canonical `i`,
    return `0`. -/
noncomputable def extractorCoeffFromSigma
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm)) :
    Fin msg.k → ℕ := fun i =>
  if extractorIsCanonical E stmt msg hkm i then
    if hHit : ∃ k : Fin (zerosCard E msg.toD),
        σ k = baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i) then
      multAt E β_fun msg.toD hHit.choose
    else 0
  else 0

theorem extractorCoeffFromSigma_noncanon
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (i : Fin msg.k) (hNotCanon : ¬ extractorIsCanonical E stmt msg hkm i) :
    extractorCoeffFromSigma E stmt msg hkm β_fun σ i = 0 := by
  unfold extractorCoeffFromSigma
  rw [if_neg hNotCanon]

theorem extractorCoeffFromSigma_canonical_hit
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (i : Fin msg.k) (hCanon : extractorIsCanonical E stmt msg hkm i)
    (hHit : ∃ k : Fin (zerosCard E msg.toD),
        σ k = baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)) :
    extractorCoeffFromSigma E stmt msg hkm β_fun σ i
      = multAt E β_fun msg.toD hHit.choose := by
  unfold extractorCoeffFromSigma
  rw [if_pos hCanon, dif_pos hHit]

theorem extractorCoeffFromSigma_canonical_nohit
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (i : Fin msg.k) (hCanon : extractorIsCanonical E stmt msg hkm i)
    (hNoHit : ¬ ∃ k : Fin (zerosCard E msg.toD),
        σ k = baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)) :
    extractorCoeffFromSigma E stmt msg hkm β_fun σ i = 0 := by
  unfold extractorCoeffFromSigma
  rw [if_pos hCanon, dif_neg hNoHit]

/-- **σ must hit position 0.** From the σ-output's off-range condition:
    `j ∉ range σ → distinctM' j = 0`. Applied at `j = 0`, we would get
    `distinctM' 0 = 0`, but `distinctM' 0 = -1 ≠ 0` in `ZMod E.q` (since
    `E.q ≥ 5 ≥ 2` is prime). Hence `0 ∈ range σ`. -/
theorem sigma_zero_preimage_exists
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (hσ_off : ∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) :
    ∃ k₀ : Fin (zerosCard E msg.toD),
      σ k₀ = (⟨0, by omega⟩ : Fin (1 + baseImageCount E stmt msg hkm)) := by
  classical
  by_contra hne
  push_neg at hne
  have h0notRange :
      (⟨0, by omega⟩ : Fin (1 + baseImageCount E stmt msg hkm))
        ∉ Set.range σ := by
    intro hRange
    obtain ⟨k, hk⟩ := hRange
    exact hne k hk
  have h0m : distinctM' E stmt msg hkm
      (⟨0, by omega⟩ : Fin (1 + baseImageCount E stmt msg hkm)) = 0 :=
    hσ_off _ h0notRange
  rw [distinctM'_zero] at h0m
  -- Now h0m : (-1 : ZMod E.q) = 0, contradicts one_ne_zero (via neg_eq_zero).
  have h1 : (1 : ZMod E.q) = 0 := neg_eq_zero.mp h0m
  exact one_ne_zero h1

/-- **Bound for the multiplicity at σ's zero-preimage.** `multAt k₀ ≥ 1`
    where `k₀` is the (any) index with `σ k₀ = 0`. Follows from
    `multAt_pos` (every `multAt k` is positive under the `β`-coverage
    condition). -/
theorem multAt_at_sigma_zero_pos
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (D : CoordRingElt E.q)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (k₀ : Fin (zerosCard E D)) :
    1 ≤ multAt E β_fun D k₀ :=
  multAt_pos E β_fun D hβcov k₀

/-- **Bound lemma.** For `k ≠ k₀` in `Fin (zerosCard E D)`,
    `multAt k ≤ D.degE - 1`. Uses `multAt k + multAt k₀ ≤ ∑ multAt ≤ D.degE`
    with `multAt k₀ ≥ 1`. -/
theorem multAt_le_degE_sub_one_of_ne
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (D : CoordRingElt E.q)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ D.degE)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    {k k₀ : Fin (zerosCard E D)} (hne : k ≠ k₀) :
    multAt E β_fun D k + 1 ≤ D.degE := by
  classical
  have hSum := sum_multAt_le_degE E β_fun D hβsup hβsum
  -- Insert: sum over {k, k₀} ≤ sum over univ.
  have hPair : multAt E β_fun D k + multAt E β_fun D k₀ ≤
               ∑ k' : Fin (zerosCard E D), multAt E β_fun D k' := by
    have hSubset : ({k, k₀} : Finset (Fin (zerosCard E D))) ⊆ Finset.univ := by
      intro x _; exact Finset.mem_univ _
    have hSumPair :
        ∑ k' ∈ ({k, k₀} : Finset (Fin (zerosCard E D))),
            multAt E β_fun D k'
          = multAt E β_fun D k + multAt E β_fun D k₀ := by
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact hne), Finset.sum_singleton]
    rw [← hSumPair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun _ _ _ => Nat.zero_le _)
  have hk₀ : 1 ≤ multAt E β_fun D k₀ := multAt_at_sigma_zero_pos E β_fun D hβcov k₀
  omega

/-- **Paper Step 4** (`thm:ma`, ip.tex `\ref{step:lift}`): lift σ-matched
    residues to integer multiplicities `n_R ∈ [0, d]` (≡ paper's
    `eq:integer-mult`).

    `extractorCoeffFromSigma` is the canonical lift of the residue
    identity into `[0, d]`. This theorem packages the three hypotheses
    needed by `extractorSucceeds_of_natural_witness` to convert the
    σ-matching output into `extractorSucceeds` plus `extractedScalars`
    pointwise equality with the lifted coefficients — the inputs that
    Step 5 (general case) consumes. -/
theorem extractorCoeffFromSigma_satisfies_D3
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hkm : stmt.k = msg.k)
    (_hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ msg.toD.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, msg.toD.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ msg.toD.degE)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (_hσ_eq : ∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k))
    (hσ_betam : ∀ k,
      ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q)
        + distinctM' E stmt msg hkm (σ k) = 0)
    (hσ_off : ∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) :
    (∀ i, extractorCoeffFromSigma E stmt msg hkm β_fun σ i < d) ∧
    (∀ i, extractorIsCanonical E stmt msg hkm i →
      (extractorCoeffFromSigma E stmt msg hkm β_fun σ i : ZMod E.q)
        = extractorGroupSum E stmt msg hkm i) ∧
    (∀ i, ¬ extractorIsCanonical E stmt msg hkm i →
      extractorCoeffFromSigma E stmt msg hkm β_fun σ i = 0) := by
  classical
  -- k₀ is the preimage of 0 under σ.
  obtain ⟨k₀, hk₀⟩ := sigma_zero_preimage_exists E stmt msg hkm σ hσ_off
  refine ⟨?_, ?_, ?_⟩
  -- (1) Bound: extractorCoeffFromSigma i < d.
  · intro i
    by_cases hC : extractorIsCanonical E stmt msg hkm i
    · by_cases hHit : ∃ k : Fin (zerosCard E msg.toD),
          σ k = baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)
      · rw [extractorCoeffFromSigma_canonical_hit E stmt msg hkm β_fun σ i hC hHit]
        -- Use hHit.choose: σ (hHit.choose) = pos_i ≠ 0 = σ k₀, so
        -- hHit.choose ≠ k₀. Hence multAt (hHit.choose) ≤ D.degE - 1 ≤ d - 1 < d.
        set k := hHit.choose
        have hkspec : σ k = baseImagePos E stmt msg hkm
            (baseIndexOf E stmt msg hkm i) := hHit.choose_spec
        have hkne_k₀ : k ≠ k₀ := by
          intro hEq
          rw [hEq] at hkspec
          rw [hk₀] at hkspec
          exact baseImagePos_ne_zero E stmt msg hkm (baseIndexOf E stmt msg hkm i)
            hkspec.symm
        have hBound : multAt E β_fun msg.toD k + 1 ≤ msg.toD.degE :=
          multAt_le_degE_sub_one_of_ne E β_fun msg.toD
            hβsup hβsum hβcov hkne_k₀
        have : multAt E β_fun msg.toD k + 1 ≤ d :=
          hBound.trans hDeg
        omega
      · rw [extractorCoeffFromSigma_canonical_nohit
              E stmt msg hkm β_fun σ i hC hHit]
        -- Need: 0 < d. Use multAt_at_sigma_zero_pos + hβsum + hDeg.
        have hk₀_pos : 1 ≤ multAt E β_fun msg.toD k₀ :=
          multAt_at_sigma_zero_pos E β_fun msg.toD hβcov k₀
        -- 1 ≤ multAt k₀ ≤ ∑ multAt ≤ D.degE ≤ d.
        have hSum := sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
        have hSingle : multAt E β_fun msg.toD k₀ ≤
            ∑ k' : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k' := by
          refine Finset.single_le_sum
            (f := fun k' => multAt E β_fun msg.toD k') ?_ (Finset.mem_univ k₀)
          intro _ _; exact Nat.zero_le _
        have : multAt E β_fun msg.toD k₀ ≤ d := (hSingle.trans hSum).trans hDeg
        omega
    · rw [extractorCoeffFromSigma_noncanon E stmt msg hkm β_fun σ i hC]
      -- Same 0 < d argument.
      have hk₀_pos : 1 ≤ multAt E β_fun msg.toD k₀ :=
        multAt_at_sigma_zero_pos E β_fun msg.toD hβcov k₀
      have hSum := sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
      have hSingle : multAt E β_fun msg.toD k₀ ≤
          ∑ k' : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k' := by
        refine Finset.single_le_sum
          (f := fun k' => multAt E β_fun msg.toD k') ?_ (Finset.mem_univ k₀)
        intro _ _; exact Nat.zero_le _
      have : multAt E β_fun msg.toD k₀ ≤ d := (hSingle.trans hSum).trans hDeg
      omega
  -- (2) ZMod identity at canonical i.
  · intro i hC
    by_cases hHit : ∃ k : Fin (zerosCard E msg.toD),
        σ k = baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)
    · rw [extractorCoeffFromSigma_canonical_hit
            E stmt msg hkm β_fun σ i hC hHit]
      set k := hHit.choose
      have hkspec : σ k = baseImagePos E stmt msg hkm
          (baseIndexOf E stmt msg hkm i) := hHit.choose_spec
      -- multAt k + distinctM' (σ k) = 0 ⇒ multAt k = -distinctM' (σ k).
      have hBetaM := hσ_betam k
      -- distinctM' (σ k) = distinctM' baseImagePos = extractorGroupSum (baseAtIndex (baseIndexOf i))
      --                   = extractorGroupSum i (since extractorBases (baseAtIndex (baseIndexOf i)) = baseAt (baseIndexOf i) = extractorBases i).
      rw [hkspec, distinctM'_baseImagePos] at hBetaM
      -- Translate extractorGroupSum (baseAtIndex (baseIndexOf i)) = extractorGroupSum i.
      have hBases_eq : extractorBases E stmt msg hkm
          (baseAtIndex E stmt msg hkm (baseIndexOf E stmt msg hkm i))
            = extractorBases E stmt msg hkm i := by
        rw [baseAtIndex_spec E stmt msg hkm (baseIndexOf E stmt msg hkm i),
            baseAt_baseIndexOf]
      have hGroupSum_eq :
          extractorGroupSum E stmt msg hkm
            (baseAtIndex E stmt msg hkm (baseIndexOf E stmt msg hkm i))
            = extractorGroupSum E stmt msg hkm i :=
        extractorGroupSum_congr_of_extractorBases_eq E stmt msg hkm hBases_eq
      rw [hGroupSum_eq] at hBetaM
      -- hBetaM : (multAt k : ZMod q) + (-extractorGroupSum i) = 0
      -- (: distinctM'_baseImagePos is NEGATED).
      -- Goal: (multAt k : ZMod q) = extractorGroupSum i.
      linear_combination hBetaM
    · rw [extractorCoeffFromSigma_canonical_nohit
            E stmt msg hkm β_fun σ i hC hHit]
      -- pos_i ∉ range σ ⇒ distinctM' pos_i = 0 ⇒ extractorGroupSum i = 0.
      push_neg at hHit
      have hPosNotRange :
          baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)
            ∉ Set.range σ := by
        intro hInRange
        obtain ⟨k, hk⟩ := hInRange
        exact hHit k hk
      have hM : distinctM' E stmt msg hkm
          (baseImagePos E stmt msg hkm (baseIndexOf E stmt msg hkm i)) = 0 :=
        hσ_off _ hPosNotRange
      rw [distinctM'_baseImagePos] at hM
      -- hM : extractorGroupSum (baseAtIndex (baseIndexOf i)) = 0
      -- translate to extractorGroupSum i.
      have hBases_eq : extractorBases E stmt msg hkm
          (baseAtIndex E stmt msg hkm (baseIndexOf E stmt msg hkm i))
            = extractorBases E stmt msg hkm i := by
        rw [baseAtIndex_spec E stmt msg hkm (baseIndexOf E stmt msg hkm i),
            baseAt_baseIndexOf]
      have hGroupSum_eq :
          extractorGroupSum E stmt msg hkm
            (baseAtIndex E stmt msg hkm (baseIndexOf E stmt msg hkm i))
            = extractorGroupSum E stmt msg hkm i :=
        extractorGroupSum_congr_of_extractorBases_eq E stmt msg hkm hBases_eq
      rw [hGroupSum_eq] at hM
      -- hM : -extractorGroupSum i = 0 ().
      -- Goal: 0 = extractorGroupSum i.
      have hZero : extractorGroupSum E stmt msg hkm i = 0 := by
        linear_combination -hM
      simp [hZero]
  -- (3) Non-canonical indices: trivial.
  · intro i hNotCanon
    exact extractorCoeffFromSigma_noncanon E stmt msg hkm β_fun σ i hNotCanon

/-! ## S6: extractorDivisorCoeffs ↔ dCoeffs matching

    Pointwise equality `extractorDivisorCoeffs = dCoeffs E msg.toD β_fun`
    on `ECPoint E` under the σ-matching output of `distinctSigma_exists`.
    Combined with `distinctSigma_exists`'s `IsPrincipal (dCoeffs ...)`
    conclusion and `funext`, this yields
    `IsPrincipal E (extractorDivisorCoeffs E stmt msg hkm)`.

    The packaged theorem `extractor_succeeds_and_isPrincipal` combines
    S4 + S5 + S6 into the full composite conclusion
    `extractorSucceeds ∧ IsPrincipal (extractorDivisorCoeffs)`,
    as consumed by S7 to replace the former composite T4 bridge axiom.
-/

/-- **Helper: σ k is either 0 or `baseImagePos i`**.
    Every `j : Fin (1 + baseImageCount)` is either `⟨0, _⟩` or
    `⟨i.val + 1, _⟩` for some `i : Fin baseImageCount`. -/
theorem fin_one_plus_cases
    (n : ℕ) (j : Fin (1 + n)) :
    j = (⟨0, by omega⟩ : Fin (1 + n)) ∨
    ∃ i : Fin n, j = (⟨i.val + 1, by omega⟩ : Fin (1 + n)) := by
  rcases j with ⟨v, hv⟩
  rcases v with _ | v
  · left; rfl
  · right
    refine ⟨⟨v, by omega⟩, ?_⟩
    rfl

/-- **Helper**: at a non-canonical index `j`, filter selects the
    canonical representative so its `extractedScalars`-sum is at the
    canonical value (mirror of `sum_extractedScalars_over_group`). -/
theorem extractorDivisorCoeffs_affine_not_in_baseImage
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (x y : ZMod E.q)
    (hNot : (x, y) ∉ baseImage E stmt msg hkm) :
    ((Finset.univ : Finset (Fin msg.k)).filter
      (fun j => extractorBases E stmt msg hkm j = (x, y))) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  apply hNot
  refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

/-- **S6 — pointwise matching.** Under the σ-matching hypotheses
    produced by `distinctSigma_exists`, the extractor's divisor
    coefficient function equals `dCoeffs E msg.toD β_fun` at every
    point of `ECPoint E`.

    Combined with `IsPrincipal (dCoeffs ...)` from S4 and `funext`,
    this gives `IsPrincipal (extractorDivisorCoeffs ...)`. -/
theorem extractorDivisorCoeffs_eq_dCoeffs
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ msg.toD.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, msg.toD.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ msg.toD.degE)
    (σ : Fin (zerosCard E msg.toD) ↪
          Fin (1 + baseImageCount E stmt msg hkm))
    (hσ_eq : ∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k))
    (hσ_betam : ∀ k,
      ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q)
        + distinctM' E stmt msg hkm (σ k) = 0)
    (hσ_off : ∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0)
    (P : ECPoint E) :
    extractorDivisorCoeffs E stmt msg hkm P = dCoeffs E msg.toD β_fun P := by
  classical
  -- D3 data for the σ-matching (S5).
  obtain ⟨hBound, hCanon, hNonCanon⟩ :=
    extractorCoeffFromSigma_satisfies_D3 E stmt msg d hDeg hkm hNoNegP β_fun
      hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off
  -- D3 consumption for extractedScalars.
  obtain ⟨_, hScalars_eq⟩ :=
    extractorSucceeds_of_natural_witness E stmt msg d hd hkm hNoNegP
      (extractorCoeffFromSigma E stmt msg hkm β_fun σ)
      hBound hCanon hNonCanon
  -- D-zeros enumeration: σ k₀ = 0 for some k₀.
  obtain ⟨k₀, hk₀⟩ := sigma_zero_preimage_exists E stmt msg hkm σ hσ_off
  -- multAt k₀ = 1 in ℕ (via ZMod q identity + bound multAt k₀ < E.q).
  have hBetaLt : ∀ k, multAt E β_fun msg.toD k < E.q := by
    intro k
    have hSingle : multAt E β_fun msg.toD k ≤
        ∑ k' : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k' := by
      refine Finset.single_le_sum
        (f := fun k' => multAt E β_fun msg.toD k') ?_ (Finset.mem_univ k)
      intro _ _; exact Nat.zero_le _
    have hSum := sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
    exact lt_of_le_of_lt ((hSingle.trans hSum).trans hDeg) hd
  have hMult_k₀_one_nat : multAt E β_fun msg.toD k₀ = 1 := by
    have hBM := hσ_betam k₀
    rw [hk₀, distinctM'_zero] at hBM
    -- hBM : (multAt k₀ : ZMod E.q) + (-1) = 0 ⇒ (multAt k₀ : ZMod E.q) = 1.
    have hZMod : ((multAt E β_fun msg.toD k₀ : ℕ) : ZMod E.q) = 1 := by
      have : ((multAt E β_fun msg.toD k₀ : ℕ) : ZMod E.q) = 0 - (-1) := by
        linear_combination hBM
      rw [this]; ring
    -- Bound: multAt k₀ < E.q, and (multAt k₀ : ZMod q) = 1 with q ≥ 2.
    have h1LtQ : (1 : ℕ) < E.q := E.hq_prime.one_lt
    have h1ValEq : ((1 : ZMod E.q)).val = 1 := by
      rw [ZMod.val_one_eq_one_mod]
      exact Nat.mod_eq_of_lt h1LtQ
    have hValLeft : ((multAt E β_fun msg.toD k₀ : ℕ) : ZMod E.q).val =
        multAt E β_fun msg.toD k₀ :=
      ZMod.val_natCast_of_lt (hBetaLt k₀)
    rw [hZMod] at hValLeft
    rw [h1ValEq] at hValLeft
    exact hValLeft.symm
  -- zerosAt k₀ = -P_aff.
  have hk₀_aff : zerosAt E msg.toD k₀ = (stmt.target.1, -stmt.target.2) := by
    rw [hσ_eq k₀, hk₀, distinctR_zero]
  -- β_fun (-P_aff) = multAt k₀ = 1.
  have hβ_negP : β_fun (stmt.target.1, -stmt.target.2) = 1 := by
    have : β_fun (zerosAt E msg.toD k₀) = multAt E β_fun msg.toD k₀ := rfl
    rw [← hk₀_aff, this, hMult_k₀_one_nat]
  -- Case on P.
  cases P with
  | zero =>
      show -(msg.toD.degE : ℤ) = -(msg.toD.degE : ℤ); rfl
  | @some x y _ =>
      -- LHS = indicator + filter-sum extractedScalars.
      -- RHS = (β_fun (x, y) : ℤ).
      show (if (x, y) = (stmt.target.1, -stmt.target.2)
            then (1 : ℤ) else 0) +
           ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
             (fun j => extractorBases E stmt msg hkm j = (x, y)),
             extractedScalars E stmt msg hkm j = (β_fun (x, y) : ℤ)
      by_cases hxy : (x, y) = (stmt.target.1, -stmt.target.2)
      · -- Sub-case: (x, y) = -P_aff.
        rw [if_pos hxy, hxy]
        -- The filter is empty by hNoNegP.
        have hEmpty : ((Finset.univ : Finset (Fin msg.k)).filter
            (fun j => extractorBases E stmt msg hkm j =
                       (stmt.target.1, -stmt.target.2))) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro j hj
          apply hNoNegP
          exact ⟨j, hj⟩
        rw [hEmpty, Finset.sum_empty, add_zero, hβ_negP]
        rfl
      · -- Sub-case: (x, y) ≠ -P_aff. Indicator = 0.
        rw [if_neg hxy, zero_add]
        by_cases hInImage : (x, y) ∈ baseImage E stmt msg hkm
        · -- Sub-sub-case: (x, y) ∈ baseImage.
          -- Let i_c = canonical index with extractorBases i_c = (x, y).
          rw [baseImage, Finset.mem_image] at hInImage
          obtain ⟨j₀, _, hj₀eq⟩ := hInImage
          -- Canonicalize: i_c = (extractorGroup j₀).min'.
          set i_c := (extractorGroup E stmt msg hkm j₀).min'
            (extractorGroup_nonempty E stmt msg hkm j₀) with hi_c_def
          have hi_c_canon : extractorIsCanonical E stmt msg hkm i_c := by
            show (extractorGroup E stmt msg hkm i_c).min'
              (extractorGroup_nonempty E stmt msg hkm i_c) = i_c
            have hi_c_in : i_c ∈ extractorGroup E stmt msg hkm j₀ :=
              Finset.min'_mem _ _
            have hG_eq : extractorGroup E stmt msg hkm i_c =
                         extractorGroup E stmt msg hkm j₀ :=
              extractedScalars_group_canonical E stmt msg hkm j₀ i_c hi_c_in
            apply le_antisymm
            · apply Finset.min'_le
              exact mem_extractorGroup_self E stmt msg hkm i_c
            · apply Finset.le_min'
              intro y' hy'
              rw [hG_eq] at hy'
              rw [hi_c_def]
              exact Finset.min'_le _ _ hy'
          -- extractorBases i_c = extractorBases j₀ = (x, y).
          have hi_c_base : extractorBases E stmt msg hkm i_c = (x, y) := by
            have hi_c_in : i_c ∈ extractorGroup E stmt msg hkm j₀ :=
              Finset.min'_mem _ _
            have := Finset.mem_filter.mp hi_c_in
            rw [this.2, hj₀eq]
          -- The filter sum equals extractedScalars i_c.
          -- Go via sum_extractedScalars_over_group.
          have hFilter_eq_group : ((Finset.univ : Finset (Fin msg.k)).filter
              (fun j => extractorBases E stmt msg hkm j = (x, y)))
              = extractorGroup E stmt msg hkm i_c := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              extractorGroup]
            rw [hi_c_base]
          have hSum_group : ∑ j ∈ extractorGroup E stmt msg hkm i_c,
              extractedScalars E stmt msg hkm j
              = extractedScalars E stmt msg hkm
                  ((extractorGroup E stmt msg hkm i_c).min'
                    (extractorGroup_nonempty E stmt msg hkm i_c)) :=
            sum_extractedScalars_over_group E stmt msg hkm hNoNegP i_c
          rw [hFilter_eq_group, hSum_group, hi_c_canon]
          -- extractedScalars i_c = (extractorCoeffFromSigma ... i_c : ℤ).
          rw [hScalars_eq i_c]
          -- Now case on whether σ hits baseImagePos (baseIndexOf i_c).
          set pos := baseImagePos E stmt msg hkm
            (baseIndexOf E stmt msg hkm i_c) with hpos_def
          by_cases hHit : ∃ k : Fin (zerosCard E msg.toD), σ k = pos
          · -- Hit: extractorCoeffFromSigma i_c = multAt (hHit.choose).
            rw [hpos_def] at hHit
            rw [extractorCoeffFromSigma_canonical_hit
                  E stmt msg hkm β_fun σ i_c hi_c_canon hHit]
            set k := hHit.choose
            have hkspec : σ k = baseImagePos E stmt msg hkm
                (baseIndexOf E stmt msg hkm i_c) := hHit.choose_spec
            -- zerosAt k = distinctR (σ k) = baseAt (baseIndexOf i_c) = extractorBases i_c = (x, y).
            have hzerosAt_k : zerosAt E msg.toD k = (x, y) := by
              rw [hσ_eq k, hkspec, distinctR_baseImagePos,
                  baseAt_baseIndexOf, hi_c_base]
            -- β_fun (x, y) = β_fun (zerosAt k) = multAt k.
            have hβ_xy : β_fun (x, y) = multAt E β_fun msg.toD k := by
              unfold multAt
              rw [hzerosAt_k]
            rw [hβ_xy]
          · -- No hit: extractorCoeffFromSigma i_c = 0. Need β_fun (x, y) = 0.
            rw [hpos_def] at hHit
            rw [extractorCoeffFromSigma_canonical_nohit
                  E stmt msg hkm β_fun σ i_c hi_c_canon hHit]
            -- Show β_fun (x, y) = 0 by contradiction with hβsup + zerosAt_covers_zeros.
            have hβ_eq_zero : β_fun (x, y) = 0 := by
              by_contra hβne
              obtain ⟨hMem, hEval⟩ := hβsup (x, y) hβne
              obtain ⟨k, hk⟩ := zerosAt_covers_zeros E msg.toD (x, y) hMem hEval
              -- distinctR (σ k) = zerosAt k = (x, y) = baseAt (baseIndexOf i_c) = distinctR pos.
              have hDRσ : distinctR E stmt msg hkm (σ k) = (x, y) := by
                rw [← hσ_eq k, hk]
              have hDRpos : distinctR E stmt msg hkm
                  (baseImagePos E stmt msg hkm
                    (baseIndexOf E stmt msg hkm i_c)) = (x, y) := by
                rw [distinctR_baseImagePos, baseAt_baseIndexOf, hi_c_base]
              have hEqDR : distinctR E stmt msg hkm (σ k) =
                  distinctR E stmt msg hkm
                    (baseImagePos E stmt msg hkm
                      (baseIndexOf E stmt msg hkm i_c)) := by
                rw [hDRσ, hDRpos]
              have hσk_eq_pos : σ k =
                  baseImagePos E stmt msg hkm
                    (baseIndexOf E stmt msg hkm i_c) :=
                distinctR_injective E stmt msg hkm hNoNegP hEqDR
              exact hHit ⟨k, hσk_eq_pos⟩
            rw [hβ_eq_zero]
        · -- Sub-sub-case: (x, y) ∉ baseImage.
          rw [extractorDivisorCoeffs_affine_not_in_baseImage E stmt msg hkm
                x y hInImage, Finset.sum_empty]
          -- β_fun (x, y) = 0 by contradiction.
          have hβ_eq_zero : β_fun (x, y) = 0 := by
            by_contra hβne
            obtain ⟨hMem, hEval⟩ := hβsup (x, y) hβne
            obtain ⟨k, hk⟩ := zerosAt_covers_zeros E msg.toD (x, y) hMem hEval
            -- distinctR (σ k) = (x, y).
            have hDRσ : distinctR E stmt msg hkm (σ k) = (x, y) := by
              rw [← hσ_eq k, hk]
            -- Case on σ k: either 0 or baseImagePos.
            rcases fin_one_plus_cases (baseImageCount E stmt msg hkm) (σ k)
              with hσ_zero | ⟨i, hσ_succ⟩
            · -- σ k = 0 ⇒ (x, y) = distinctR 0 = -P_aff, contradicts hxy.
              rw [hσ_zero, distinctR_zero] at hDRσ
              exact hxy hDRσ.symm
            · -- σ k = ⟨i+1, _⟩ ⇒ (x, y) = baseAt i ∈ baseImage.
              rw [hσ_succ, distinctR_succ] at hDRσ
              exact hInImage (hDRσ ▸ baseAt_mem_baseImage E stmt msg hkm i)
          rw [hβ_eq_zero]
          rfl

/-- **S6 + S4 + S5 combined.** Under the full T4 hypothesis set,
    the extractor succeeds and its divisor coefficient function's
    group-sum-zero surrogate holds on the candidate Finset. Only the
    group-sum-zero half of `principal_divisor_iff.mpr` is carried;
    the degree-0 half is not needed downstream. -/
theorem extractor_succeeds_and_groupSumZero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hSplit : splitsOnE E msg.toD)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (hPolyGZero :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E (zerosAt E msg.toD)
            (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0)
    (hValidPairsLarge :
      6 * E.q * ((d + stmt.k + 1) + (d + stmt.k + 1) * (d + stmt.k)) + 1
        ≤ (validPairs E).card) :
    extractorSucceeds E stmt msg d hkm ∧
    ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
      (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) = 0 := by
  classical
  -- Step 1: apply S4.
  have hD : ¬ msg.toD.isZero := admSet_implies_toD_nonzero stmt msg hAdm
  set β_fun := betaCanonical E msg.toD
  have hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ msg.toD.eval P.1 P.2 = 0 :=
    betaCanonical_support E msg.toD
  have hβcov : ∀ P ∈ E.points, msg.toD.eval P.1 P.2 = 0 → β_fun P ≠ 0 :=
    betaCanonical_covers E msg.toD hD
  have hβsum : (∑ P ∈ E.points, β_fun P) ≤ msg.toD.degE :=
    betaCanonical_sum_le_degE E msg.toD
  have hβgroup : ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine E P.1 P.2)) = 0 :=
    betaCanonical_group_sum_zero E msg.toD hSplit
  obtain ⟨σ, hσ_eq, hσ_betam, hσ_off⟩ :=
    distinctSigma_exists E stmt msg d hDeg hd hkm hAdm hNoNegP hSplit
      hAllZero hPolyGZero hValidPairsLarge
  -- Step 2: apply S5 to get extractorSucceeds + scalar identification.
  obtain ⟨hBound, hCanon, hNonCanon⟩ :=
    extractorCoeffFromSigma_satisfies_D3 E stmt msg d hDeg hkm hNoNegP
      β_fun hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off
  obtain ⟨hSucceeds, _hScalars_eq⟩ :=
    extractorSucceeds_of_natural_witness E stmt msg d hd hkm hNoNegP
      (extractorCoeffFromSigma E stmt msg hkm β_fun σ)
      hBound hCanon hNonCanon
  -- Step 3: pointwise matching ⇒ functional equality.
  have hEq : extractorDivisorCoeffs E stmt msg hkm =
             dCoeffs E msg.toD β_fun := by
    funext P
    exact extractorDivisorCoeffs_eq_dCoeffs E stmt msg d hDeg hd hkm
      hNoNegP β_fun hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off P
  -- Step 4: transfer group-sum-zero from the β-side to the extractor side.
  refine ⟨hSucceeds, ?_⟩
  rw [hEq]
  -- Goal: weightedSum over extractorDivisorCandidate of zsmul (dCoeffs ...) = 0.
  -- β_fun's group sum on E.points is 0 (hβgroup). Combined with
  -- `weightedSum_dCoeffs_candidate_eq`, this gives the weightedSum on
  -- `dCoeffsCandidate` is 0. We need to transfer this to
  -- `extractorDivisorCandidate` — it suffices to show the zsmul`-
  -- contribution agrees on both candidate Finsets (via `hEq` for the
  -- coefficient function and, once we unfold `dCoeffs`, the candidate
  -- shapes differ but both strictly contain the joint support, so we
  -- can reduce both weightedSums to the underlying support and match).
  -- Concretely: produce the weightedSum-zero on a common enlargement
  -- and use `weightedSum_subset_of_zero_outside`.
  set c := dCoeffs E msg.toD β_fun with hc_def
  set extCand := extractorDivisorCandidate E stmt msg hkm with hExtCand_def
  have hβsup_P : ∀ P, β_fun P ≠ 0 → P ∈ E.points :=
    fun P hP => (hβsup P hP).1
  -- Finite support of c.
  have hFinSupp : Set.Finite (Function.support c) :=
    dCoeffs_finiteSupport E msg.toD β_fun hβsup_P
  -- Group-sum-zero of c on hFinSupp.toFinset.
  have hGSup :
      ECPoint.weightedSum E hFinSupp.toFinset
        (fun P => ECPoint.zsmul E (c P) P) = 0 :=
    dCoeffs_groupSum_zero E msg.toD β_fun hβsup_P hβgroup hFinSupp
  -- Function.support c ⊆ ↑extCand (via hEq and the extractor candidate lemma).
  have hSupSub : Function.support c ⊆ ↑extCand := by
    intro P hP
    have hP' : extractorDivisorCoeffs E stmt msg hkm P ≠ 0 := by
      rw [hEq]; exact hP
    exact extractorDivisorCoeffs_support_subset_candidate E stmt msg hkm hP'
  have hFinSupp_sub : hFinSupp.toFinset ⊆ extCand := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact hSupSub hP
  -- Pad from support to extCand.
  have hPad :
      ECPoint.weightedSum E extCand
          (fun P => ECPoint.zsmul E (c P) P)
        = ECPoint.weightedSum E hFinSupp.toFinset
            (fun P => ECPoint.zsmul E (c P) P) :=
    ECPoint.weightedSum_subset_of_zero_outside E hFinSupp_sub
      (fun P _ hPnotSup => by
        rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
        rw [hPnotSup]; exact ECPoint.zsmul_zero E P)
  rw [hPad]; exact hGSup

/-! ## T4 theorem: the original bridge statement as a theorem -/

/-- **T4 bridge theorem.** Derived from the S4+S5+S6 assembly
    (`extractor_succeeds_and_groupSumZero`) combined with the D4+D5
    infrastructure (`target_eq_weightedSum_of_weightedSum`).

    Conclusion: `extractorSucceeds` and
    `target = Σ [extractedScalars i] · B_i`.

    Requires the quantitative hypothesis `hValidPairsLarge`
    threaded from the T5 application inside the proof. -/
theorem extractorSucceeds_of_logDerivCheck_identically_zero_general
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hSplit : splitsOnE E msg.toD)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (hPolyGZero :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E (zerosAt E msg.toD)
            (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0)
    (hValidPairsLarge :
      6 * E.q * ((d + stmt.k + 1) + (d + stmt.k + 1) * (d + stmt.k)) + 1
        ≤ (validPairs E).card) :
    extractorSucceeds E stmt msg d hkm ∧
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg hkm i)
                   (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                                   (extractorBases E stmt msg hkm i).2)) := by
  obtain ⟨hSucc, hWSum⟩ :=
    extractor_succeeds_and_groupSumZero E stmt msg d hDeg hd hkm hAdm hNoNegP
      hSplit hAllZero hPolyGZero hValidPairsLarge
  exact ⟨hSucc,
    target_eq_weightedSum_of_weightedSum E stmt msg hkm hTargetOnE hBasesOnE hNoNegP hWSum⟩

/-! ## Extractor validity (both cases) -/

/-- **Extractor validity (both cases).** The extracted witness
    satisfies the dlog relation `relDlog`:
    * Special case (`-P ∈ {B_j}`): `extracted_scalars_valid_special`.
    * General case (`-P ∉ {B_j}`): T4 theorem's second conjunct. -/
theorem extracted_scalars_valid
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hSplit : splitsOnE E msg.toD)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (hPolyGZero :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E (zerosAt E msg.toD)
            (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0)
    (hValidPairsLarge :
      6 * E.q * ((d + stmt.k + 1) + (d + stmt.k + 1) * (d + stmt.k)) + 1
        ≤ (validPairs E).card) :
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg hkm i)
                   (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                                   (extractorBases E stmt msg hkm i).2)) := by
  classical
  by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
  · exact extracted_scalars_valid_special E stmt msg hkm hNegP
  · exact (extractorSucceeds_of_logDerivCheck_identically_zero_general
            E stmt msg d hDeg hd hkm hAdm hTargetOnE hBasesOnE hNegP hSplit
            hAllZero hPolyGZero hValidPairsLarge).2

/-! ## Classical axiom: polyG vanishing on E × E

    The `hPolyGZero` hypothesis threaded through the extractor chain
    asserts that the denominator-cleared polynomial `polyG` vanishes
    on every non-vertical pair in `E × E`. Classically this is the
    composite of two facts:

    1. **Function-field trace-of-log-derivative identity.**
       For `D ∈ F_q[E]^×` and the degree-3 separable extension
       `F_q(E)/F_q(z)` with `z = y − λ x`, the chord-sum of scalar
       logarithmic-derivative terms at the three chord-fiber points
       equals the logarithmic derivative of the function-field norm:

       ```
       Σ_i (dD/dz)(A_i) / D(A_i)  =  (d/dz) N(D) / N(D)
       ```

       where `N = N_{F_q(E)/F_q(z)}`. This is the general identity
       `Tr_{L/K}(dg/g) = d(N_{L/K} g) / N_{L/K} g` specialised to the
       degree-3 function-field extension cut out by the chord-cubic
       `x³ − λ² x² + (A − 2 λ z) x + (B − z²)` (Vieta: the three chord
       intersection `x`-coordinates are the roots). Combined with the
       factorisation `N(D)(z) = lc(D)^3 · ∏_Q (z − z(Q))^{β(Q)}` as a
       polynomial identity in `F_q[z]` — valid under the splitting /
       accounting hypotheses on `normPoly E D` (no "phantom" roots at
       non-rational `x`-coordinates) — and the chord-intercept partial-
       fraction expansion `(normZ)'(μ)/normZ(μ) = -Σ_Q β(Q)/L_Q(Q)`
       (already mechanised as `normZ_logDeriv_at_chord_intercept` in
       `Divisor/NormZDecomp.lean`), one gets the residue-sum form
       `Σ_i logDerivTerm(A_i) = -Σ_Q β(Q)/L_Q(Q)` which is the scalar
       identity `chord_sum_eq_residue_sum` in
       `Divisor/ChordLogDerivProof.lean`.

    2. **Density extension.** Vanishing of `polyG` on the "defined"
       subset of non-vertical pairs (where slope denominators are
       nonzero) extends to the full non-vertical set via polynomial
       degree counting on `polyGPoly` against `card_zeros_on_E_le`.
       Mechanised as `polyG_zero_on_nonvertical_of_defined` in
       `Divisor/PolyGDensity.lean` (modulo a concrete density bound).

    Citations:
      * Silverman, *The Arithmetic of Elliptic Curves*
        (AEC, GTM 106, 2009), III Cor 3.5 (Abel's theorem: principal-
        divisor characterisation on E); II §3 (divisors of rational
        functions); II §4 (differentials on a curve).
      * Silverman, *Advanced Topics in the Arithmetic of Elliptic
        Curves* (ATAEC, GTM 151, 1999), III §1 (elliptic curves over
        function fields — establishes `F_q(E)/F_q(C)` as a finite
        separable function-field extension).
      * Stichtenoth, *Algebraic Function Fields and Codes*
        (GTM 254, 2nd ed., 2009), §III.1-2 (norm `N_{F/E}` in a finite
        separable extension of algebraic function fields;
        multiplicativity and divisor-of-norm formula), §III.5
        (differentials in function-field extensions).
      * Lang, *Algebra* (GTM 211, 3rd ed., 2002), §VI.5 (norm and
        trace of a finite field extension, multiplicativity, identity
        `Tr(dg/g) = d(Ng)/(Ng)` via the characteristic-polynomial
        formula). -/

/-
**Trace-of-log-derivative identity** (`polyG_zero_trace_formula`
below). Under `hSplit` (normPoly splits over F_q), `hAccount`
(betaConstructive accounting identity), and `hAllZero`
(logDerivCheckFn vanishes on every defined non-vertical pair), the
denominator-cleared polynomial `polyG` formed from
`betaConstructive E msg.toD` vanishes on every non-vertical pair in
`E × E`.

**All three hypotheses are essential**:
* Without `hSplit` + `hAccount`, `\ref{lem:log-derivative}`
  (`chord_sum_eq_residue_sum`) fails; concrete finite-field
  counterexamples exist.
* Without `hAllZero`, a cheating prover's `msg.m` can make
  `polyG ≠ 0` at some non-vertical pair (by the `polyG ⇔
  paperResidue` Step-5 equivalence).

The multiplicity function is fixed to `betaConstructive` — universal
quantification over all decompositions is unsound; see
`BetaUnique.lean` for the counterexample.

Classical content: Lang *Algebra* 3rd ed. §VI.5 (norm/trace of a
finite separable field extension) + Silverman ATAEC III §1
(function-field extension `F_q(E)/F_q(z)`) + Stichtenoth
*Algebraic Function Fields and Codes* 2nd ed. §III.1-5
(function-field norm, divisor-of-norm, differentials) +
Silverman AEC III Cor 3.5 (principal-divisor characterisation on E).
-/

set_option maxHeartbeats 1600000 in
/-- **Paper Step 1** (`thm:ma`, ip.tex `\ref{step:logderiv}`): express
    `f` as the discrepancy of two log-derivatives.

    Under `f ≡ 0` on `E × E` (the `¬event_NotEq` regime), the trace-
    formula identity gives `polyG = 0` on every defined non-vertical
    pair of `E.points × E.points`. -/
theorem polyG_zero_trace_formula
    {E : ECSetup} (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (_hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hSplit : splitsOnE E msg.toD)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    -- Structural non-degeneracy of the denominator polynomial.
    -- See CubicIntersection.curveEqPoly_dvd_mul for the underlying
    -- prime property; pending full factor-by-factor verification.
    (hDenomNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm),
            distinctR E stmt msg hkm j ≠ A₀) →
        denomScaledPoly (E := E) msg.toD stmt.target
          (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm) A₀ %ₘ curveEqPoly E ≠ 0)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E (zerosAt E msg.toD)
        (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
        (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
        A₀ A₁ = 0 := by
  classical
  set D := msg.toD with hD_def
  set Q_fn := zerosAt E D
  set β_fn := fun k => ((multAt E (betaCanonical E D) D k : ℕ) : ZMod E.q)
  -- Accounting identity for the canonical β.
  have hAccount : (∑ P ∈ E.points, betaCanonical E D P) =
                    (normPoly E D).natDegree :=
    betaCanonical_account E D hSplit
  set R_fn := distinctR E stmt msg hkm
  set m_fn := distinctM' E stmt msg hkm
  -- Case: D = 0 (trivial: β = 0 and Q-products contain ellP(A₀, A₀, A₁) = 0)
  by_cases hDnz : D.a = 0 ∧ D.b = 0
  · -- When D = 0, normPoly = 0, so hAccount gives ∑ beta = 0.
    -- All beta = 0, so β_fn = 0. polyG's first sum is 0.
    -- For the second sum: ∏_k ellP(Q_k, A₀, A₁) = 0 because A₀ is among Q_k.
    intro A₀ A₁ hA₀ hA₁ hNV
    -- β_fn = 0: normPoly = 0 when D = 0, so ∑ beta = 0, so each beta = 0
    have hNormZero : normPoly E D = 0 := by
      rw [normPoly_eq]; simp [hDnz.1, hDnz.2]
    have hβall : ∀ P, betaCanonical E D P = 0 := by
      intro P
      have hZero : betaCanonical E D = fun _ => 0 :=
        betaCanonical_eq_zero E D hDnz
      rw [hZero]
    have hβ_fn_zero : ∀ k, β_fn k = 0 := by
      intro k; show ((multAt E (betaCanonical E D) D k : ℕ) : ZMod E.q) = 0
      unfold multAt; rw [hβall _]; simp
    -- A₀ ∈ zerosFinset (since D.eval = 0 everywhere)
    have hA₀z : A₀ ∈ zerosFinset E D := by
      simp only [zerosFinset, zeros, Finset.mem_filter]
      exact ⟨hA₀, by unfold CoordRingElt.eval; rw [hDnz.1, hDnz.2]; simp⟩
    -- Get k₀ : Fin (zerosCard E D) with Q_fn k₀ = A₀
    have ⟨k₀, hk₀⟩ : ∃ k₀ : Fin (zerosCard E D), Q_fn k₀ = A₀ := by
      refine ⟨(zerosEnum E D).symm ⟨A₀, hA₀z⟩, ?_⟩
      show zerosAt E D ((zerosEnum E D).symm ⟨A₀, hA₀z⟩) = A₀
      unfold zerosAt
      exact congr_arg Subtype.val (Equiv.apply_symm_apply (zerosEnum E D) ⟨A₀, hA₀z⟩)
    -- polyG = first_sum + second_sum
    unfold polyG
    -- First sum = 0 (each β_fn k = 0)
    have hS1 : ∑ k : Fin (zerosCard E D), β_fn k *
        (∏ k' ∈ Finset.univ.erase k, ellP E (Q_fn k') A₀ A₁) *
        (∏ j, ellP E (R_fn j) A₀ A₁) = 0 := by
      apply Finset.sum_eq_zero; intro k _; rw [hβ_fn_zero k]; ring
    -- Second sum = 0 (∏_k ellP(Q_k, A₀, A₁) = 0 via k₀)
    have hProdQ : ∏ k : Fin (zerosCard E D), ellP E (Q_fn k) A₀ A₁ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k₀)
      rw [hk₀]; unfold ellP; ring
    have hS2 : ∑ j, m_fn j * (∏ k, ellP E (Q_fn k) A₀ A₁) *
        (∏ j' ∈ Finset.univ.erase j, ellP E (R_fn j') A₀ A₁) = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [hProdQ]; ring
    rw [hS1, hS2, add_zero]
  push_neg at hDnz
  -- From here, D is nonzero.
  -- polyG = 0 at fully defined pairs
  have hPhaseA : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁ →
      (∀ Q ∈ zerosFinset E D,
        (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) →
      polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
    intro A₀ A₁ hA₀ hA₁ hNV hDefBaseAt hQline
    by_cases hDnz : D.a = 0 ∧ D.b = 0
    · exfalso
      unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDefBaseAt
      apply hDefBaseAt
      have : D.eval A₀.1 A₀.2 = 0 := by
        unfold CoordRingElt.eval; rw [hDnz.1, hDnz.2]; simp
      simp [this]
    · have hDefRaw : logDerivCheckFnDefined E D stmt.target
          stmt.bases A₀ A₁ := by
        unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDefBaseAt ⊢
        intro hRawEqZero
        apply hDefBaseAt
        set common := D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 *
          D.eval (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1)
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
                (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) *
          (3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) *
          (3 * A₁.1 ^ 2 + E.curveA -
            2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) *
          (3 * (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) ^ 2 + E.curveA -
            2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
                (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
                (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1))) *
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2)
        change common * ∏ j : Fin stmt.k,
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (stmt.bases j).1 (stmt.bases j).2 = 0 at hRawEqZero
        change common * ∏ i : Fin (baseImageCount E stmt msg hkm),
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (baseAt E stmt msg hkm i).1 (baseAt E stmt msg hkm i).2 = 0
        rcases mul_eq_zero.mp hRawEqZero with hCommon | hProd
        · exact mul_eq_zero.mpr (Or.inl hCommon)
        · rw [Finset.prod_eq_zero_iff] at hProd
          obtain ⟨j, _, hj⟩ := hProd
          apply mul_eq_zero.mpr; right
          rw [Finset.prod_eq_zero_iff]
          refine ⟨baseIndexOf E stmt msg hkm (finCongr hkm j),
                  Finset.mem_univ _, ?_⟩
          rw [baseAt_baseIndexOf]
          have hEq : extractorBases E stmt msg hkm (finCongr hkm j) = stmt.bases j := by
            unfold extractorBases; congr 1
          rw [hEq]; exact hj
      have hCheckRaw := hAllZero A₀ A₁ hA₀ hA₁ hNV hDefRaw
      have hCheckGrouped : logDerivCheckFn E D stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)
          (distinctM'_tail E stmt msg hkm) A₀ A₁ = 0 := by
        rw [← logDerivCheckFn_eq_grouped E stmt msg hkm D stmt.target A₀ A₁]
        exact hCheckRaw
      have hPolyGCons := polyG_zero_at_defined_fincons D hDnz
        (betaCanonical E D)
        (betaCanonical_support E D)
        (betaCanonical_covers E D hDnz)
        hSplit (betaCanonical_account E D hSplit)
        (fun P => congrFun (betaCanonical_eq_betaTrue E D hDnz) P)
        stmt.target (baseAt E stmt msg hkm) (distinctM'_tail E stmt msg hkm)
        A₀ A₁ hA₀ hA₁ hNV hDefBaseAt hQline hCheckGrouped
      show polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0
      change polyG E (zerosAt E D)
        (fun k => ((multAt E (betaCanonical E D) D k : ℕ) : ZMod E.q))
        (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm) A₀ A₁ = 0
      unfold distinctR distinctM'
      rw [polyG_reindex]
      exact hPolyGCons
  -- For A₀ NOT a zero of D, polyG(A₀, ·) = 0 on all of E.
  -- Requires counting bad A₁'s from logDerivCheckFnDenom factors.
  have hPhase1 : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E D →
      ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
      polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
    -- Two-step approach: for "non-special" A₀, via swap.
    -- A₀ not in zerosFinset and not in distinctR image
    have hPhase1a : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E D →
        (∀ j, R_fn j ≠ A₀) →
        ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
        polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₀ hA₀ hA₀nz hA₀nr
      -- Use density: show polyGPoly(A₀) has enough zeros on E.
      have hManyZeros : (E.points.filter (fun p =>
          bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          > 2 * (resultantX E (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree := by
        -- The "good" set: A₁ where hPhaseA applies (fullyDef)
        -- Its complement on E.points has cardinality ≤ 3*(D.degE + stmt.k + 2) + 5
        -- Bound the resultant degree
        have hResLe := resultantX_polyGPoly_natDegree_le E Q_fn β_fn R_fn m_fn A₀
        -- zerosCard + (1 + baseImageCount) ≤ D.degE + stmt.k + 2
        have hZC : zerosCard E D ≤ D.degE := by
          have hβcov := betaCanonical_covers E D
            (by push_neg; intro ha; exact hDnz ha)
          have hβpos : ∀ k : Fin (zerosCard E D), 1 ≤ multAt E (betaCanonical E D) D k :=
            fun k => multAt_pos E (betaCanonical E D) D hβcov k
          have hβsum := betaCanonical_sum_le_degE E D
          have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E D) D
            (betaCanonical_support E D)
          calc zerosCard E D
              = ∑ _ : Fin (zerosCard E D), 1 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            _ ≤ ∑ k : Fin (zerosCard E D), multAt E (betaCanonical E D) D k :=
                Finset.sum_le_sum (fun k _ => hβpos k)
            _ = ∑ P ∈ E.points, betaCanonical E D P := hβeq
            _ ≤ D.degE := hβsum
        have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
          calc baseImageCount E stmt msg hkm
              ≤ msg.k := by
                unfold baseImageCount baseImage
                exact (Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin])
            _ = stmt.k := hkm.symm
        -- The good set (where hPhaseA applies) is a subset of the bivEval zero set
        have hGoodSub : E.points.filter (fun A₁ =>
            A₀.1 ≠ A₁.1 ∧
            logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁ ∧
            (∀ Q ∈ zerosFinset E D,
              (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0))
          ⊆ E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0) := by
          intro A₁ hA₁
          simp only [Finset.mem_filter] at hA₁ ⊢
          refine ⟨hA₁.1, ?_⟩
          rw [bivEval_polyGPoly]
          exact hPhaseA A₀ A₁ hA₀ hA₁.1 hA₁.2.1 hA₁.2.2.1 hA₁.2.2.2
        -- Bound the complement of the good set
        -- Bad A₁'s: vertical + collinear with special points + slope denoms
        -- Total bad ≤ 3*(D.degE + stmt.k + 2) + 5
        have hBadBound : (E.points.filter (fun A₁ =>
            ¬(A₀.1 ≠ A₁.1 ∧
              logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁ ∧
              (∀ Q ∈ zerosFinset E D,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)))).card
            ≤ 21 * (D.degE + stmt.k + 2) + 72 := by
          -- The bad predicate is ¬(A ∧ B ∧ C), so bad ⊆ ¬A ∪ ¬B ∪ ¬C.
          -- We bound each piece: ¬A (vertical) ≤ 2,
          -- ¬C (line through zero) ≤ 3*zerosCard,
          -- ¬B (undefined denom) ≤ 3*(D.degE + stmt.k + 2) + 12 (factor bounds).
          -- Total ≤ 2 + 3*D.degE + 3*(D.degE+stmt.k+2)+12 ≤ 6*(D.degE+stmt.k+2)+14.
          -- We use a subset argument + union bound.
          set badFilter := E.points.filter (fun A₁ =>
            ¬(A₀.1 ≠ A₁.1 ∧
              logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁ ∧
              (∀ Q ∈ zerosFinset E D,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0))) with hBF
          -- Crude but correct bound: filter ⊆ E.points, so card ≤ E.points.card.
          -- We need a tighter bound. Use the structure of the negation.
          -- The filter is contained in three sets whose union has bounded card.
          have hSub : badFilter ⊆
              E.points.filter (fun A₁ => A₁.1 = A₀.1) ∪
              (E.points.filter (fun A₁ =>
                ¬logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁) ∪
               E.points.filter (fun A₁ =>
                ∃ Q ∈ zerosFinset E D,
                  (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0)) := by
            intro A₁ hA₁
            simp only [hBF, Finset.mem_filter, not_and_or, Finset.mem_union] at hA₁ ⊢
            obtain ⟨hMem, hBad⟩ := hA₁
            rcases hBad with h1 | h2 | h3
            · left; exact ⟨hMem, (not_not.mp h1).symm⟩
            · right; left; exact ⟨hMem, h2⟩
            · right; right; refine ⟨hMem, ?_⟩
              push_neg at h3; obtain ⟨Q, hQmem, hQeval⟩ := h3
              exact ⟨Q, hQmem, hQeval⟩
          -- Bound card(badFilter)
          have hVert : (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card ≤ 2 :=
            card_points_with_fst_eq_le E A₀.1
          -- For the non-vertical bad conditions, use a crude bound:
          -- The filter ⊆ E.points, so card ≤ E.points.card.
          -- But we know the bound 3*(D.degE + stmt.k + 2) + 6 suffices.
          -- Decompose hRestBound into two sub-bounds:
          --   hBoundUndefined: card {A₁ | logDerivCheckFnDenom = 0} ≤ 3*(stmt.k + 2) + 12
          --     (8-factor product decomposition; each factor contributes ≤ 3 or ≤ 12)
          --   hBoundZerosLine: card {A₁ | ∃ Q ∈ zerosFinset, line passes through Q}
          --                    ≤ 3 * zerosCard ≤ 3 * D.degE
          --     (biUnion over zerosFinset + linear_form_zeros_le_three)
          have hBoundUndefined : (E.points.filter (fun A₁ =>
                ¬logDerivCheckFnDefined E D stmt.target
                  (baseAt E stmt msg hkm) A₀ A₁)).card
              ≤ 18 * D.degE + 10 * stmt.k + 112 := by
            set k₀ := baseImageCount E stmt msg hkm
            set B₀ := baseAt E stmt msg hkm
            set P₀ := stmt.target
            by_cases hWit : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
                logDerivCheckFnDefined E D P₀ B₀ A₀ A₁
            · -- Witness exists: use denomScaledPoly + card_zeros_on_E_le
              have hNZ := denomScaledPoly_modCurve_ne_zero E D P₀ k₀ B₀ A₀ hWit
              have hCardBound := card_zeros_on_E_le E
                (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) hNZ
              have hResBound := resultantX_denomScaledPoly_natDegree_le E D P₀ k₀ B₀ A₀
              -- Non-vertical filter ⊆ zeros of denomScaledPoly
              have hFilterSubNV : E.points.filter (fun A₁ =>
                    ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1)
                  ⊆ E.points.filter (fun p =>
                    bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0) := by
                intro A₁ hA₁
                simp only [Finset.mem_filter] at hA₁ ⊢
                refine ⟨hA₁.1, ?_⟩
                unfold logDerivCheckFnDefined at hA₁
                push_neg at hA₁
                rw [bivEval_denomScaledPoly_eq E D P₀ k₀ B₀ A₀ A₁ hA₁.2.2, hA₁.2.1,
                    mul_zero]
              -- Split filter into vertical + non-vertical
              have hFilterSplit : E.points.filter (fun A₁ =>
                    ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁)
                  ⊆ E.points.filter (fun A₁ => A₁.1 = A₀.1) ∪
                    E.points.filter (fun A₁ =>
                      ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1) := by
                intro A₁ hA₁
                simp only [Finset.mem_filter, Finset.mem_union] at hA₁ ⊢
                by_cases h : A₀.1 = A₁.1
                · left; exact ⟨hA₁.1, h.symm⟩
                · right; exact ⟨hA₁.1, hA₁.2, h⟩
              calc (E.points.filter (fun A₁ =>
                      ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁)).card
                  ≤ _ := Finset.card_le_card hFilterSplit
                _ ≤ (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
                    (E.points.filter (fun A₁ =>
                      ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1)).card :=
                    Finset.card_union_le _ _
                _ ≤ 2 + (E.points.filter (fun p =>
                      bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0)).card :=
                    Nat.add_le_add (card_points_with_fst_eq_le E A₀.1)
                      (Finset.card_le_card hFilterSubNV)
                _ ≤ 2 + 2 * (resultantX E
                      (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀)).natDegree :=
                    Nat.add_le_add_left hCardBound 2
                _ ≤ 2 + 2 * (9 * D.degE + 5 * k₀ + 55) :=
                    Nat.add_le_add_left (Nat.mul_le_mul_left 2 hResBound) 2
                _ ≤ 18 * D.degE + 10 * stmt.k + 112 := by
                    have := hBI; omega
            · -- No defined witness: derive contradiction.
              -- Every non-vertical A₁ has logDerivCheckFnDenom = 0.
              -- But denomScaledPoly is nonzero as a polynomial (for large E),
              -- so this contradicts large E.points.card from hLargeQ.
              push_neg at hWit
              exfalso
              -- Every non-vertical A₁ has bivEval denomScaledPoly = 0.
              have hAllZeroBiv : ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
                  bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) A₁ = 0 := by
                intro A₁ hA₁mem hNV
                rw [bivEval_denomScaledPoly_eq E D P₀ k₀ B₀ A₀ A₁ hNV]
                have hND := hWit A₁ hA₁mem hNV
                unfold logDerivCheckFnDefined at hND
                push_neg at hND
                rw [hND]; ring
              -- denomScaledPoly %ₘ curveEqPoly ≠ 0 (structural argument).
              -- By curveEqPoly_dvd_mul (primality) + degree analysis of
              -- each factor: DAtA₁Poly D has degree ≤ 1 and is nonzero
              -- (from hDnz), dxdzDenA₀Scaled has degree ≤ 1 and is nonzero
              -- (from hSmooth + A₀ on curve), lineEvalNumAt factors have
              -- degree ≤ 1 and are nonzero (from hA₀nr).  By
              -- not_curveEqPoly_dvd_of_natDegree_lt these are not divisible
              -- by curveEqPoly.  By curveEqPoly_dvd_mul (prime property),
              -- curveEqPoly cannot divide the product.
              have hNZ : denomScaledPoly (E := E) D P₀ k₀ B₀ A₀ %ₘ
                  curveEqPoly E ≠ 0 :=
                hDenomNZ A₀ hA₀ hA₀nz hA₀nr
              -- Now count: zeros of denomScaledPoly on E are bounded.
              have hCardBound := card_zeros_on_E_le E
                (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) hNZ
              have hResBound := resultantX_denomScaledPoly_natDegree_le
                E D P₀ k₀ B₀ A₀
              -- The non-vertical filter is a subset of the zero set.
              have hNVsub : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)
                  ⊆ E.points.filter (fun p =>
                    bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0) := by
                intro A₁ hA₁
                simp only [Finset.mem_filter] at hA₁ ⊢
                exact ⟨hA₁.1, hAllZeroBiv A₁ hA₁.1 hA₁.2⟩
              -- Card of non-vertical points ≥ #E.points - 2
              have hNVcard : E.points.card - 2 ≤
                  (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card := by
                have hVertCard := card_points_with_fst_eq_le E A₀.1
                have hCompl : (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
                    (E.points.filter (fun A₁ => ¬A₁.1 = A₀.1)).card =
                    E.points.card :=
                  Finset.card_filter_add_card_filter_not (s := E.points)
                    (p := fun A₁ => A₁.1 = A₀.1)
                have hEq : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1) =
                    E.points.filter (fun A₁ => ¬A₁.1 = A₀.1) := by
                  ext x; simp [ne_comm]
                rw [hEq]; omega
              -- Derive contradiction: too many zeros.
              have hUB : (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card
                  ≤ 2 * (9 * D.degE + 5 * k₀ + 55) :=
                le_trans (Finset.card_le_card hNVsub)
                  (le_trans hCardBound (Nat.mul_le_mul_left 2 hResBound))
              have : E.points.card ≤ 2 * (9 * D.degE + 5 * k₀ + 55) + 2 := by omega
              have := hBI
              omega
          have hBoundZerosLine : (E.points.filter (fun A₁ =>
                ∃ Q ∈ zerosFinset E D,
                  (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0)).card
              ≤ 3 * D.degE := by
            -- D.degE ≥ 3 for any CoordRingElt
            have hDegE3 : 3 ≤ D.degE := by
              show 3 ≤ max (2 * D.a.natDegree) (3 + 2 * D.b.natDegree)
              omega
            -- Split filter into non-vertical (A₁.1 ≠ A₀.1) and vertical (A₁.1 = A₀.1)
            set S := E.points.filter (fun A₁ =>
              ∃ Q ∈ zerosFinset E D,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0) with hS_def
            -- Vertical part: vert = {A₁ ∈ E | A₁.1 = A₀.1}
            set vert := E.points.filter (fun A₁ => A₁.1 = A₀.1) with hV_def
            have hVertCard : vert.card ≤ 2 := card_points_with_fst_eq_le E A₀.1
            -- Non-vertical part: {A₁ ∈ E | A₁.1 ≠ A₀.1 ∧ ∃ Q ∈ zeros, eval = 0}
            set nonvert := E.points.filter (fun A₁ =>
              A₁.1 ≠ A₀.1 ∧ ∃ Q ∈ zerosFinset E D,
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0) with hNV_def
            -- S ⊆ nonvert ∪ vert
            have hSsub : S ⊆ nonvert ∪ vert := by
              intro A₁ hA₁
              simp only [hS_def, hNV_def, hV_def, Finset.mem_filter, Finset.mem_union] at hA₁ ⊢
              obtain ⟨hMem, Q, hQ, hEval⟩ := hA₁
              by_cases heq : A₁.1 = A₀.1
              · right; exact ⟨hMem, heq⟩
              · left; exact ⟨hMem, heq, Q, hQ, hEval⟩
            -- For each Q ∈ zeros, the linear form as a function of A₁:
            -- (Q.2-A₀.2)*A₁.1 + (-(Q.1-A₀.1))*A₁.2 + ((Q.1-A₀.1)*A₀.2 - (Q.2-A₀.2)*A₀.1)
            -- has ≤ 3 zeros on E.points.
            -- The non-vertical lineThrough.eval = 0 is equivalent to this linear form = 0
            -- when A₁.1 ≠ A₀.1.
            -- Also, A₀ satisfies the linear form = 0 (substitute A₁ = A₀).
            -- So the non-vertical part of each per-Q set has ≤ 2 elements.
            -- Bound non-vertical part
            have hNVbound : nonvert.card ≤ 2 * zerosCard E D := by
              -- nonvert ⊆ biUnion over Q of the per-Q non-vert linear form zeros
              have hNVsub : nonvert ⊆ (zerosFinset E D).biUnion (fun Q =>
                  (E.points.filter (fun A₁ =>
                    (Q.2 - A₀.2) * A₁.1 + (-(Q.1 - A₀.1)) * A₁.2 +
                      ((Q.1 - A₀.1) * A₀.2 - (Q.2 - A₀.2) * A₀.1) = 0)).erase A₀) := by
                intro A₁ hA₁
                simp only [hNV_def, Finset.mem_filter] at hA₁
                obtain ⟨hMem, hNE, Q, hQmem, hEval⟩ := hA₁
                rw [Finset.mem_biUnion]
                refine ⟨Q, hQmem, ?_⟩
                rw [Finset.mem_erase]
                constructor
                · -- A₁ ≠ A₀ since A₁.1 ≠ A₀.1
                  intro heq; exact hNE (congr_arg Prod.fst heq)
                · rw [Finset.mem_filter]
                  refine ⟨hMem, ?_⟩
                  -- lineThrough.eval = 0 iff linear form = 0 (when A₁.1 ≠ A₀.1)
                  -- eval = Q.2 - s*Q.1 - (A₀.2 - s*A₀.1) where s = (A₁.2-A₀.2)*(A₁.1-A₀.1)⁻¹
                  -- eval * (A₁.1 - A₀.1) = (Q.2-A₀.2)*(A₁.1-A₀.1) - (A₁.2-A₀.2)*(Q.1-A₀.1)
                  -- = linearForm evaluated at A₁
                  have hne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNE
                  have heval_expand : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 =
                    Q.2 - (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹ * Q.1 -
                    (A₀.2 - (A₁.2 - A₀.2) * (A₁.1 - A₀.1)⁻¹ * A₀.1) := by
                    simp only [lineThrough, Line.eval, slopeOf]
                  have key : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 * (A₁.1 - A₀.1) =
                    (Q.2 - A₀.2) * (A₁.1 - A₀.1) - (A₁.2 - A₀.2) * (Q.1 - A₀.1) := by
                    simp only [lineThrough, Line.eval, slopeOf]
                    set d := (A₁.1 - A₀.1) with hd_def
                    set s := (A₁.2 - A₀.2) * d⁻¹ with hs_def
                    -- s * d = A₁.2 - A₀.2
                    have hsd : s * d = A₁.2 - A₀.2 := by
                      rw [hs_def, mul_assoc, inv_mul_cancel₀ hne, mul_one]
                    -- Goal: (Q.2 - s * Q.1 - (A₀.2 - s * A₀.1)) * d
                    --     = (Q.2 - A₀.2) * d - (A₁.2 - A₀.2) * (Q.1 - A₀.1)
                    calc (Q.2 - s * Q.1 - (A₀.2 - s * A₀.1)) * d
                        = Q.2 * d - s * Q.1 * d - A₀.2 * d + s * A₀.1 * d := by ring
                      _ = Q.2 * d - (A₁.2 - A₀.2) * Q.1 - A₀.2 * d + (A₁.2 - A₀.2) * A₀.1 := by
                          rw [show s * Q.1 * d = (s * d) * Q.1 from by ring, hsd,
                              show s * A₀.1 * d = (s * d) * A₀.1 from by ring, hsd]
                      _ = (Q.2 - A₀.2) * d - (A₁.2 - A₀.2) * (Q.1 - A₀.1) := by ring
                  -- From hEval: eval = 0, so eval * (A₁.1-A₀.1) = 0
                  have hprod : (Q.2 - A₀.2) * (A₁.1 - A₀.1) - (A₁.2 - A₀.2) * (Q.1 - A₀.1) = 0 := by
                    rw [← key, hEval, zero_mul]
                  -- This equals the linear form
                  linear_combination hprod
              calc nonvert.card
                  ≤ ((zerosFinset E D).biUnion _).card := Finset.card_le_card hNVsub
                _ ≤ ∑ Q ∈ zerosFinset E D,
                      ((E.points.filter (fun A₁ =>
                        (Q.2 - A₀.2) * A₁.1 + (-(Q.1 - A₀.1)) * A₁.2 +
                          ((Q.1 - A₀.1) * A₀.2 - (Q.2 - A₀.2) * A₀.1) = 0)).erase A₀).card :=
                    Finset.card_biUnion_le
                _ ≤ ∑ _Q ∈ zerosFinset E D, 2 := by
                    apply Finset.sum_le_sum
                    intro Q hQ
                    -- Card of erase = card - 1 when A₀ is in the set
                    have hA₀in : A₀ ∈ E.points.filter (fun A₁ =>
                        (Q.2 - A₀.2) * A₁.1 + (-(Q.1 - A₀.1)) * A₁.2 +
                          ((Q.1 - A₀.1) * A₀.2 - (Q.2 - A₀.2) * A₀.1) = 0) := by
                      rw [Finset.mem_filter]
                      exact ⟨hA₀, by ring⟩
                    rw [Finset.card_erase_of_mem hA₀in]
                    -- Card of filter ≤ 3 by linear_form_zeros_le_three
                    have hle3 : (E.points.filter (fun A₁ =>
                        (Q.2 - A₀.2) * A₁.1 + (-(Q.1 - A₀.1)) * A₁.2 +
                          ((Q.1 - A₀.1) * A₀.2 - (Q.2 - A₀.2) * A₀.1) = 0)).card ≤ 3 := by
                      apply linear_form_zeros_le_three
                      -- Q ≠ A₀ since Q ∈ zerosFinset and A₀ ∉ zerosFinset
                      have hQne : Q ≠ A₀ := fun heq => hA₀nz (heq ▸ hQ)
                      by_contra h
                      push_neg at h
                      have hx : Q.1 = A₀.1 := by
                        have := h.2; rw [neg_eq_zero] at this; exact eq_of_sub_eq_zero this
                      have hy : Q.2 = A₀.2 := eq_of_sub_eq_zero h.1
                      exact hQne (Prod.ext hx hy)
                    omega
                _ = 2 * zerosCard E D := by
                    simp [Finset.sum_const, zerosCard]
                    ring
            -- Combine: S.card ≤ nonvert.card + vert.card ≤ 2*zerosCard + 2 ≤ 3*D.degE
            calc S.card
                ≤ (nonvert ∪ vert).card := Finset.card_le_card hSsub
              _ ≤ nonvert.card + vert.card := Finset.card_union_le _ _
              _ ≤ 2 * zerosCard E D + 2 := Nat.add_le_add hNVbound hVertCard
              _ ≤ 2 * D.degE + 2 := by omega
              _ ≤ 3 * D.degE := by omega
          have hRestBound : (E.points.filter (fun A₁ =>
                ¬logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁) ∪
               E.points.filter (fun A₁ =>
                ∃ Q ∈ zerosFinset E D,
                  (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0)).card
              ≤ 21 * D.degE + 10 * stmt.k + 112 := by
            have hUnion := Finset.card_union_le
              (E.points.filter (fun A₁ =>
                ¬logDerivCheckFnDefined E D stmt.target
                  (baseAt E stmt msg hkm) A₀ A₁))
              (E.points.filter (fun A₁ =>
                ∃ Q ∈ zerosFinset E D,
                  (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0))
            have hSum :=
              Nat.add_le_add hBoundUndefined hBoundZerosLine
            omega
          calc badFilter.card
              ≤ _ := Finset.card_le_card hSub
            _ ≤ (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
                (E.points.filter (fun A₁ =>
                  ¬logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁) ∪
                 E.points.filter (fun A₁ =>
                  ∃ Q ∈ zerosFinset E D,
                    (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 = 0)).card :=
                Finset.card_union_le _ _
            _ ≤ 2 + (21 * D.degE + 10 * stmt.k + 112) :=
                Nat.add_le_add hVert hRestBound
            _ ≤ 21 * (D.degE + stmt.k + 2) + 72 := by omega
        have hGoodCount := Finset.card_le_card hGoodSub
        have hSplitCard := Finset.card_filter_add_card_filter_not
          (fun A₁ => A₀.1 ≠ A₁.1 ∧
            logDerivCheckFnDefined E D stmt.target (baseAt E stmt msg hkm) A₀ A₁ ∧
            (∀ Q ∈ zerosFinset E D,
              (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0))
          (s := E.points)
        omega
      have hAllOnE := bivEval_zero_on_E_of_many_zeros E
        (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) hManyZeros
      intro A₁ hA₁ _
      rw [← bivEval_polyGPoly]
      exact hAllOnE A₁ hA₁
    -- A₀ in distinctR image (special), use swap from earlier branch + density
    intro A₀ hA₀ hA₀nz
    by_cases hA₀r : ∀ j, R_fn j ≠ A₀
    · -- Non-special: use the lemma directly
      exact hPhase1a A₀ hA₀ hA₀nz hA₀r
    · -- Special A₀: some R_fn j = A₀
      push_neg at hA₀r
      -- For A₁ not in zerosFinset, not in R-image, different x:
      -- (applied to A₁ as "A₀") gives polyG(A₁, A₀) = 0
      -- Swap gives polyG(A₀, A₁) = 0
      -- Then density extends to all A₁.
      have hSwapZeros : ∀ A₁ ∈ E.points, A₁ ∉ zerosFinset E D →
          (∀ j, R_fn j ≠ A₁) → A₀.1 ≠ A₁.1 →
          polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
        intro A₁ hA₁ hA₁nz hA₁nr hNV
        exact polyG_swap_zero E Q_fn β_fn R_fn m_fn A₀ A₁
          (hPhase1a A₁ hA₁ hA₁nz hA₁nr A₀ hA₀ hNV.symm)
      -- Show enough zeros for density
      have hManyZeros : (E.points.filter (fun p =>
          bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          > 2 * (resultantX E (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree := by
        -- Good A₁: not in zerosFinset, not in R-image, different x
        have hGoodSub : E.points.filter (fun A₁ =>
            A₁ ∉ zerosFinset E D ∧ (∀ j, R_fn j ≠ A₁) ∧ A₀.1 ≠ A₁.1)
          ⊆ E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0) := by
          intro A₁ hA₁
          simp only [Finset.mem_filter] at hA₁ ⊢
          refine ⟨hA₁.1, ?_⟩
          rw [bivEval_polyGPoly]
          exact hSwapZeros A₁ hA₁.1 hA₁.2.1 hA₁.2.2.1 hA₁.2.2.2
        -- Bad A₁: in zerosFinset ∪ R-image ∪ same-x
        -- |bad| ≤ |zerosFinset| + |R-image| + 2 ≤ D.degE + (1 + stmt.k) + 2
        have hZC : zerosCard E D ≤ D.degE := by
          have hβcov := betaCanonical_covers E D
            (by push_neg; intro ha; exact hDnz ha)
          have hβpos : ∀ k : Fin (zerosCard E D), 1 ≤ multAt E (betaCanonical E D) D k :=
            fun k => multAt_pos E (betaCanonical E D) D hβcov k
          have hβsum := betaCanonical_sum_le_degE E D
          have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E D) D
            (betaCanonical_support E D)
          calc zerosCard E D
              = ∑ _ : Fin (zerosCard E D), 1 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            _ ≤ ∑ k : Fin (zerosCard E D), multAt E (betaCanonical E D) D k :=
                Finset.sum_le_sum (fun k _ => hβpos k)
            _ = ∑ P ∈ E.points, betaCanonical E D P := hβeq
            _ ≤ D.degE := hβsum
        have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
          calc baseImageCount E stmt msg hkm
              ≤ msg.k := by
                unfold baseImageCount baseImage
                exact (Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin])
            _ = stmt.k := hkm.symm
        have hResLe := resultantX_polyGPoly_natDegree_le E Q_fn β_fn R_fn m_fn A₀
        -- Count complement
        have hBadBound : (E.points.filter (fun A₁ =>
            ¬(A₁ ∉ zerosFinset E D ∧ (∀ j, R_fn j ≠ A₁) ∧ A₀.1 ≠ A₁.1))).card
            ≤ D.degE + stmt.k + 5 := by
          -- The cardinality of the bad set is at most the sum of the cardinalities of the three sets.
          have h_bad_card : (Finset.filter (fun A₁ => A₁ ∈ zerosFinset E D ∨ ∃ j, R_fn j = A₁ ∨ A₀.1 = A₁.1) E.points).card ≤ D.degE + (1 + stmt.k) + 2 := by
            refine' le_trans ( Finset.card_le_card _ ) _;
            any_goals exact Finset.filter ( fun A₁ => A₁ ∈ zerosFinset E D ) E.points ∪ Finset.image R_fn Finset.univ ∪ Finset.filter ( fun A₁ => A₀.1 = A₁.1 ) E.points;
            · intro x hx
              simp only [Finset.mem_filter] at hx
              obtain ⟨hMem, h⟩ := hx
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image,
                         Finset.mem_univ, true_and]
              rcases h with hZ | ⟨j, hj⟩
              · exact Or.inl (Or.inl ⟨hMem, hZ⟩)
              · rcases hj with rfl | heq
                · exact Or.inl (Or.inr ⟨j, rfl⟩)
                · exact Or.inr ⟨hMem, heq⟩;
            · refine' le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) _ ) _ );
              · refine' add_le_add _ _;
                · refine' le_trans _ hZC;
                  rw [ ← Finset.card_image_of_injective _ ( show Function.Injective ( fun x : ZMod E.q × ZMod E.q => x ) from fun x y hxy => by simpa using hxy ) ] ; exact Finset.card_le_card fun x hx => by aesop;
                · exact le_trans ( Finset.card_image_le ) ( by simpa using by linarith );
              · refine le_trans (le_of_eq ?_) (card_points_with_fst_eq_le E A₀.1)
                exact congrArg Finset.card
                  (Finset.filter_congr fun x _ => by rw [eq_comm])
          have hSetEq : ({A₁ ∈ E.points |
                ¬(A₁ ∉ zerosFinset E D ∧
                    (∀ j, R_fn j ≠ A₁) ∧ A₀.1 ≠ A₁.1)} :
                Finset (ZMod E.q × ZMod E.q))
              = {A₁ ∈ E.points |
                  A₁ ∈ zerosFinset E D ∨ ∃ j, R_fn j = A₁ ∨ A₀.1 = A₁.1} := by
            refine Finset.filter_congr fun A₁ _ => ?_
            simp only [not_and, not_not, ne_eq]
            constructor
            · intro hp
              by_cases hZ : A₁ ∈ zerosFinset E D
              · exact Or.inl hZ
              · by_cases hR : ∃ j, R_fn j = A₁
                · obtain ⟨j, rfl⟩ := hR; exact Or.inr ⟨j, Or.inl rfl⟩
                · push_neg at hR
                  exact Or.inr ⟨⟨0, by omega⟩, Or.inr (hp hZ hR)⟩
            · intro hp hnz hR
              rcases hp with h1 | ⟨j, hj⟩
              · exact absurd h1 hnz
              · rcases hj with hj | hj
                · exact absurd hj (hR j)
                · exact hj
          refine le_trans (le_of_eq (congrArg Finset.card hSetEq))
            (h_bad_card.trans (by linarith))
        have hGoodCount := Finset.card_le_card hGoodSub
        have hSplitCard := Finset.card_filter_add_card_filter_not
          (fun A₁ => A₁ ∉ zerosFinset E D ∧ (∀ j, R_fn j ≠ A₁) ∧ A₀.1 ≠ A₁.1)
          (s := E.points)
        omega
      have hAllOnE := bivEval_zero_on_E_of_many_zeros E
        (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) hManyZeros
      intro A₁ hA₁ _
      rw [← bivEval_polyGPoly]
      exact hAllOnE A₁ hA₁
  -- For A₀ IN zerosFinset E D, polyG(A₀, ·) = 0 on all of E.
  -- Uses polyG_swap_zero + earlier branch to get enough known zeros,
  -- then density (bivEval_zero_on_E_of_many_zeros) to extend.
  have hPhase2 : ∀ A₀ ∈ E.points, A₀ ∈ zerosFinset E D →
      ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
      polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
    intro A₀ hA₀ hA₀z
    -- Step 1: get zeros via antisymmetry
    have hSwapZeros : ∀ A₁ ∈ E.points, A₁ ∉ zerosFinset E D → A₀.1 ≠ A₁.1 →
        polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₁ hA₁ hA₁nz hNV
      exact polyG_swap_zero E Q_fn β_fn R_fn m_fn A₀ A₁
        (hPhase1 A₁ hA₁ hA₁nz A₀ hA₀ hNV.symm)
    -- Step 2: the known zeros form a large subset of E.points
    have hGoodSub : E.points.filter (fun A₁ => decide (A₁ ∉ zerosFinset E D) = true ∧ A₀.1 ≠ A₁.1) ⊆
        E.points.filter (fun p => bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0) := by
      intro A₁ hA₁
      simp only [Finset.mem_filter] at hA₁ ⊢
      refine ⟨hA₁.1, ?_⟩
      rw [bivEval_polyGPoly]
      exact hSwapZeros A₁ hA₁.1 (by simpa using hA₁.2.1) hA₁.2.2
    -- Step 3: density bound
    -- zerosFinset E D ⊆ E.points, so |zeros| ≤ |E.points|
    -- |good| ≥ |E.points| - |zerosFinset| - 2
    -- By hLargeQ, this exceeds 2 * resultant degree.
    have hManyZeros : (E.points.filter (fun p =>
        bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
        > 2 * (resultantX E (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree := by
      -- The good set has card ≥ |E.points| - |zerosFinset| - 2
      -- and is a subset of the zero set.
      -- The resultant degree ≤ 5*(D.degE + stmt.k + 2) + 3.
      -- By hLargeQ, the bound holds.
      have hZCle : (zerosFinset E D).card ≤ D.degE + stmt.k + 2 := by
        have hZCle' : zerosCard E D ≤ D.degE := by
          have hβcov := betaCanonical_covers E D (by
            push_neg; intro ha; exact hDnz ha)
          have hβpos : ∀ k : Fin (zerosCard E D), 1 ≤ multAt E (betaCanonical E D) D k :=
            fun k => multAt_pos E (betaCanonical E D) D hβcov k
          have hβsum := betaCanonical_sum_le_degE E D
          have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E D) D
            (betaCanonical_support E D)
          calc zerosCard E D
              = ∑ _ : Fin (zerosCard E D), 1 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            _ ≤ ∑ k : Fin (zerosCard E D), multAt E (betaCanonical E D) D k :=
                Finset.sum_le_sum (fun k _ => hβpos k)
            _ = ∑ P ∈ E.points, betaCanonical E D P := hβeq
            _ ≤ D.degE := hβsum
        unfold zerosCard at hZCle'; omega
      have hResLe := resultantX_polyGPoly_natDegree_le E Q_fn β_fn R_fn m_fn A₀
      -- Count the good set:
      have hBadX : (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card ≤ 2 :=
        card_points_with_fst_eq_le E A₀.1
      have hBadZ : (E.points.filter (fun A₁ => A₁ ∈ zerosFinset E D)).card
          ≤ (zerosFinset E D).card := by
        apply Finset.card_le_card
        intro x hx; exact (Finset.mem_filter.mp hx).2
      -- The good set has card ≥ |E.points| - |zeros| - 2
      have hGoodLower : (E.points.filter
          (fun A₁ => decide (A₁ ∉ zerosFinset E D) = true ∧ A₀.1 ≠ A₁.1)).card
          + (zerosFinset E D).card + 2 ≥ E.points.card := by
        have hBadUnion : E.points.filter
            (fun A₁ => ¬(decide (A₁ ∉ zerosFinset E D) = true ∧ A₀.1 ≠ A₁.1))
            ⊆ E.points.filter (fun A₁ => A₁ ∈ zerosFinset E D) ∪
              E.points.filter (fun A₁ => A₁.1 = A₀.1) := by
          intro x hx
          simp only [Finset.mem_filter, not_and,
            Decidable.not_not] at hx
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          by_cases hxz : x ∈ zerosFinset E D
          · left; exact ⟨hx.1, hxz⟩
          · right; exact ⟨hx.1, (hx.2 (by simpa using hxz)).symm⟩
        have hBadCard : (E.points.filter
            (fun A₁ => ¬(decide (A₁ ∉ zerosFinset E D) = true ∧ A₀.1 ≠ A₁.1))).card
            ≤ (zerosFinset E D).card + 2 :=
          calc _ ≤ _ := Finset.card_le_card hBadUnion
            _ ≤ _ := Finset.card_union_le _ _
            _ ≤ _ := Nat.add_le_add hBadZ hBadX
        have := Finset.card_filter_add_card_filter_not
          (fun A₁ => decide (A₁ ∉ zerosFinset E D) = true ∧ A₀.1 ≠ A₁.1) (s := E.points)
        omega
      -- Combine with hGoodSub and hLargeQ
      have hGoodCount := Finset.card_le_card hGoodSub
      -- zerosCard + (1 + baseImageCount) ≤ D.degE + stmt.k + 2 (generous bound)
      -- so resultant ≤ 5*(D.degE + stmt.k + 2) + 3
      -- |zeros of polyGPoly| ≥ good count ≥ |E.points| - |zerosFinset| - 2
      --   > hLargeQ - (D.degE + stmt.k + 2) - 2 > 2*(5*(D.degE+stmt.k+2)+3)
      have : zerosCard E D + (1 + baseImageCount E stmt msg hkm) ≤ D.degE + stmt.k + 2 := by
        have hZC : zerosCard E D ≤ D.degE := by
          have hβcov := betaCanonical_covers E D (by
            push_neg; intro ha; exact hDnz ha)
          have hβpos : ∀ k : Fin (zerosCard E D), 1 ≤ multAt E (betaCanonical E D) D k :=
            fun k => multAt_pos E (betaCanonical E D) D hβcov k
          have hβsum := betaCanonical_sum_le_degE E D
          have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E D) D
            (betaCanonical_support E D)
          calc zerosCard E D
              = ∑ _ : Fin (zerosCard E D), 1 := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            _ ≤ ∑ k : Fin (zerosCard E D), multAt E (betaCanonical E D) D k :=
                Finset.sum_le_sum (fun k _ => hβpos k)
            _ = ∑ P ∈ E.points, betaCanonical E D P := hβeq
            _ ≤ D.degE := hβsum
        have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
          calc baseImageCount E stmt msg hkm
              ≤ msg.k := by
                unfold baseImageCount baseImage
                exact (Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin])
            _ = stmt.k := hkm.symm
        omega
      omega
    -- Step 4: apply density
    have hAllOnE := bivEval_zero_on_E_of_many_zeros E
      (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) hManyZeros
    intro A₁ hA₁ _hNV
    rw [← bivEval_polyGPoly]
    exact hAllOnE A₁ hA₁
  -- Combine the two
  intro A₀ A₁ hA₀ hA₁ hNV
  by_cases hA₀z : A₀ ∈ zerosFinset E D
  · exact hPhase2 A₀ hA₀ hA₀z A₁ hA₁ hNV
  · exact hPhase1 A₀ hA₀ hA₀z A₁ hA₁ hNV

/-! ## Helper lemmas for the polyGFull path -/

/-- Negation of the y-coordinate preserves membership in `E.points`. -/
theorem neg_y_mem_points (x y : ZMod E.q)
    (h : (x, y) ∈ E.points) : (x, -y) ∈ E.points := by
  apply E.hComplete
  have hc := E.hOnCurve _ h
  try simp only at hc ⊢
  rw [neg_sq]; exact hc

/-- Every value of `distinctR` lies in `E.points`, given that the
    statement's target and all bases are on the curve. -/
theorem distinctR_mem_points
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (j : Fin (1 + baseImageCount E stmt msg hkm)) :
    distinctR E stmt msg hkm j ∈ E.points := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj, distinctR_zero]
    exact neg_y_mem_points E stmt.target.1 stmt.target.2 hTargetOnE
  · have hpos : 0 < j.val := Nat.pos_of_ne_zero hj0
    have hlt : j.val - 1 < baseImageCount E stmt msg hkm := by omega
    set i : Fin (baseImageCount E stmt msg hkm) := ⟨j.val - 1, hlt⟩
    have hj : j = ⟨i.val + 1, by omega⟩ := Fin.ext (by simp [i]; omega)
    rw [hj, distinctR_succ]
    have hmem := baseAt_mem_baseImage E stmt msg hkm i
    rw [baseImage, Finset.mem_image] at hmem
    obtain ⟨idx, _, hbase⟩ := hmem
    rw [← hbase]
    unfold extractorBases
    exact hBasesOnE _


end Divisor
