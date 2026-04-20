/-
  Divisor/ExtractorBridge.lean

  T4 extractor bridge theorems (D3, D4, D5 of the axiom elimination plan).

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
import Divisor.Soundness

namespace Divisor

open Finset Classical

variable (E : ECSetup)

/-! ## D4: extractor's divisor principality ⇒ zero-sum

The extractor's divisor (as a coefficient function on `ECPoint E.q`)
equals `+1` at `-P`, `extractedScalars i` at each base point
`B_i` (aggregating duplicates), and `-D.degE` at `∞`. Mirror of
`honestDivisorCoeffs` with `extractedScalars` in place of `wit.scalars`.
-/

/-- Extractor-side divisor coefficient function. -/
noncomputable def extractorDivisorCoeffs
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : ECPoint E.q → ℤ :=
  fun P => match P with
    | .infinity => -(msg.toD.degE : ℤ)
    | .affine x y =>
        (if (x, y) = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ j ∈ (Finset.univ : Finset (Fin msg.k)).filter
          (fun j => extractorBases E stmt msg hkm j = (x, y)),
          extractedScalars E stmt msg hkm j

/-- Candidate finite superset of the support: `{∞, -P, all base points}`. -/
noncomputable def extractorDivisorCandidate
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) : Finset (ECPoint E.q) :=
  insert (ECPoint.infinity : ECPoint E.q)
    (insert (ECPoint.affine stmt.target.1 (-stmt.target.2))
      ((Finset.univ : Finset (Fin msg.k)).image
        (fun j => ECPoint.affine (extractorBases E stmt msg hkm j).1
                                 (extractorBases E stmt msg hkm j).2)))

/-- Value of `extractorDivisorCoeffs` at `∞`. -/
theorem extractorDivisorCoeffs_infinity
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    extractorDivisorCoeffs E stmt msg hkm ECPoint.infinity =
      -(msg.toD.degE : ℤ) := rfl

/-- Value of `extractorDivisorCoeffs` at `-P` (general case). -/
theorem extractorDivisorCoeffs_negP
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    extractorDivisorCoeffs E stmt msg hkm
        (ECPoint.affine stmt.target.1 (-stmt.target.2)) = 1 := by
  classical
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
    rw [Finset.eq_empty_iff_forall_not_mem]
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
             then ((-(extractorGroupSum E stmt msg hkm i)).val : ℤ)
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

/-- `ECPoint.affine (extractorBases j)` as a function `Fin msg.k → ECPoint E.q`. -/
noncomputable def basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (j : Fin msg.k) : ECPoint E.q :=
  ECPoint.affine (extractorBases E stmt msg hkm j).1
                 (extractorBases E stmt msg hkm j).2

/-- Injectivity of `basesAffineEC` on the canonical Finset: two canonical
    indices with the same affine base point are equal (they're both the
    min of the same group). -/
theorem basesAffineEC_injOn_canonical
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
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
    have h12 := ECPoint.affine.injEq .. |>.mp heq
    exact Prod.ext h12.1 h12.2
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
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (i : Fin msg.k) :
    extractorDivisorCoeffs E stmt msg hkm
        (ECPoint.affine (extractorBases E stmt msg hkm i).1
                        (extractorBases E stmt msg hkm i).2) =
      extractedScalars E stmt msg hkm
        ((extractorGroup E stmt msg hkm i).min'
          (extractorGroup_nonempty E stmt msg hkm i)) := by
  classical
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
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (j : Fin msg.k) (hCanon : extractorIsCanonical E stmt msg hkm j) :
    extractorDivisorCoeffs E stmt msg hkm (basesAffineEC E stmt msg hkm j) =
      extractedScalars E stmt msg hkm j := by
  unfold basesAffineEC
  have h1 := extractorDivisorCoeffs_affine_bases E stmt msg hkm hNoNegP j
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
  -- Step B: fold_image with injectivity on canonical.
  have hInj : ∀ x ∈ canFs, ∀ y ∈ canFs, bEC x = bEC y → x = y :=
    basesAffineEC_injOn_canonical E stmt msg hkm
  show (canFs.image bEC).fold (ECPoint.add E) 0
        (fun P => ECPoint.zsmul E (c P) P) = _
  rw [Finset.fold_image hInj]
  -- After fold_image: canFs.fold (ECPoint.add E) 0 ((fun P => zsmul (c P) P) ∘ bEC).
  -- Step C: rewrite summand at canonical positions.
  have hFoldCongr :
      canFs.fold (ECPoint.add E) 0
        ((fun P => ECPoint.zsmul E (c P) P) ∘ bEC)
      = canFs.fold (ECPoint.add E) 0
        (fun j => ECPoint.zsmul E (extractedScalars E stmt msg hkm j) (bEC j)) := by
    apply Finset.fold_congr
    intro j hj
    simp only [hcanFs_def, canonicalFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    show ECPoint.zsmul E (c (bEC j)) (bEC j) = _
    rw [hc_def, hbEC_def,
        extractorDivisorCoeffs_basesAffineEC_of_canonical E stmt msg hkm hNoNegP j hj]
  rw [hFoldCongr]
  -- Step D: extend canonical sum to univ via zero-padding.
  show canFs.fold (ECPoint.add E) 0 _ = ECPoint.weightedSum E _ _
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
  | infinity =>
      exact Finset.mem_insert_self _ _
  | affine x y =>
      refine Finset.mem_insert_of_mem ?_
      by_cases hxy : (x, y) = (stmt.target.1, -stmt.target.2)
      · rw [Prod.mk.injEq] at hxy
        rcases hxy with ⟨hx, hy⟩
        rw [hx, hy]
        exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        -- Indicator = 0, so filter-sum ≠ 0, so filter is nonempty.
        have hEval : extractorDivisorCoeffs E stmt msg hkm
                        (ECPoint.affine x y) =
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
        by_contra hNotInImage
        apply hP
        have hEmpty : ((Finset.univ : Finset (Fin msg.k)).filter
            (fun j => extractorBases E stmt msg hkm j = (x, y))) = ∅ := by
          rw [Finset.eq_empty_iff_forall_not_mem]
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          apply hNotInImage
          refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
          simp only [hj]
        rw [hEmpty, Finset.sum_empty]

/-- `∞` is not an affine point, so not in the `basesAffineEC` image. -/
theorem infinity_notin_image_basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    ECPoint.infinity ∉
    ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨j, _, heq⟩ := hContra
  unfold basesAffineEC at heq
  exact ECPoint.noConfusion heq

/-- Under general case, `-P_aff` is not in the image of base points. -/
theorem negP_notin_image_basesAffineEC
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty) :
    (ECPoint.affine stmt.target.1 (-stmt.target.2) : ECPoint E.q) ∉
    ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨j, _, heq⟩ := hContra
  apply hNoNegP
  refine ⟨j, ?_⟩
  simp only [negPIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold basesAffineEC at heq
  have hprod : (extractorBases E stmt msg hkm j).1 = stmt.target.1 ∧
               (extractorBases E stmt msg hkm j).2 = -stmt.target.2 := by
    have := ECPoint.affine.injEq .. |>.mp heq
    exact this
  exact Prod.ext hprod.1 hprod.2

/-- `∞ ≠ -P_aff`. -/
theorem infinity_ne_negP_aff
    (stmt : DlogStatement E.q) :
    (ECPoint.infinity : ECPoint E.q) ≠
    ECPoint.affine stmt.target.1 (-stmt.target.2) := fun h => ECPoint.noConfusion h

/-- `∞` is not in `insert (-P_aff) (image basesAffineEC)`. -/
theorem infinity_notin_insert_negP_image
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k) :
    (ECPoint.infinity : ECPoint E.q) ∉
    insert (ECPoint.affine stmt.target.1 (-stmt.target.2))
      ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm)) := by
  intro hContra
  rw [Finset.mem_insert] at hContra
  rcases hContra with h | h
  · exact infinity_ne_negP_aff E stmt h
  · exact infinity_notin_image_basesAffineEC E stmt msg hkm h

/-- **D4 main theorem.** If `extractorDivisorCoeffs` is the divisor of a
    rational function on `E` (i.e., `IsPrincipal`), then the group-law
    equation `(-P) + Σ [extractedScalars i] · B_i = 0` holds.

    Combined with D5 (`target_eq_weightedSum_of_zero_sum`), this gives
    the full group-law conclusion `target = Σ [extractedScalars i] · B_i`. -/
theorem extractor_zeroSum_of_principal
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hPrincipal : IsPrincipal E (extractorDivisorCoeffs E stmt msg hkm)) :
    ECPoint.add E
      (ECPoint.affine stmt.target.1 (-stmt.target.2))
      (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (basesAffineEC E stmt msg hkm i)))
    = 0 := by
  classical
  set c := extractorDivisorCoeffs E stmt msg hkm with hc_def
  set candFs := extractorDivisorCandidate E stmt msg hkm
  -- Step 1-2: finite support.
  have hSupSub : Function.support c ⊆ ↑candFs :=
    extractorDivisorCoeffs_support_subset_candidate E stmt msg hkm
  have hFinSupp : Set.Finite (Function.support c) :=
    (Finset.finite_toSet candFs).subset hSupSub
  -- Step 3: principal_divisor_iff.
  have ⟨_, hGroup⟩ := (principal_divisor_iff E c hFinSupp).mp hPrincipal
  -- Step 4: extend group-sum from support to candidate Finset.
  have hFinSupp_sub_candFs : hFinSupp.toFinset ⊆ candFs := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact hSupSub hP
  have hCandSum :
      ECPoint.weightedSum E candFs (fun P => ECPoint.zsmul E (c P) P) = 0 := by
    rw [ECPoint.weightedSum_subset_of_zero_outside E hFinSupp_sub_candFs ?_]
    · exact hGroup
    · intro P _ hPnotSup
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
      rw [hPnotSup]
      exact ECPoint.zsmul_zero E P
  -- Step 5: expand weightedSum over candidate Finset.
  have hCandExpand :
      ECPoint.weightedSum E candFs (fun P => ECPoint.zsmul E (c P) P) =
      ECPoint.add E
        (ECPoint.affine stmt.target.1 (-stmt.target.2))
        (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
          (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
            (basesAffineEC E stmt msg hkm i))) := by
    show ECPoint.weightedSum E
      (insert (ECPoint.infinity : ECPoint E.q)
        (insert (ECPoint.affine stmt.target.1 (-stmt.target.2))
          ((Finset.univ : Finset (Fin msg.k)).image (basesAffineEC E stmt msg hkm))))
      (fun P => ECPoint.zsmul E (c P) P) = _
    rw [ECPoint.weightedSum_insert E (infinity_notin_insert_negP_image E stmt msg hkm)]
    have h_f_inf : ECPoint.zsmul E (c ECPoint.infinity) ECPoint.infinity = 0 := by
      rw [hc_def]
      rw [extractorDivisorCoeffs_infinity]
      exact ECPoint.zsmul_infinity E _
    rw [h_f_inf, ECPoint.zero_add_curve]
    rw [ECPoint.weightedSum_insert E (negP_notin_image_basesAffineEC E stmt msg hkm hNoNegP)]
    have h_f_negP :
        ECPoint.zsmul E (c (ECPoint.affine stmt.target.1 (-stmt.target.2)))
          (ECPoint.affine stmt.target.1 (-stmt.target.2))
        = ECPoint.affine stmt.target.1 (-stmt.target.2) := by
      rw [hc_def, extractorDivisorCoeffs_negP E stmt msg hkm hNoNegP]
      exact ECPoint.zsmul_one E _
    rw [h_f_negP]
    congr 1
    exact weightedSum_imageBases_eq_univ_zsmul_extractedScalars E stmt msg hkm hNoNegP
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
      (coeff i : ZMod E.q) = -(extractorGroupSum E stmt msg hkm i))
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
               then ((-(extractorGroupSum E stmt msg hkm i)).val : ℤ)
               else 0) = _
    rw [dif_neg hNoNegP]
    by_cases hC : extractorIsCanonical E stmt msg hkm i
    · rw [if_pos hC]
      have h1 : (coeff i : ZMod E.q) = -(extractorGroupSum E stmt msg hkm i) :=
        hCoeff_zmod i hC
      have hBound : coeff i < E.q := lt_of_lt_of_le (hCoeff_bound i) (le_of_lt hd)
      have h2 : ((-(extractorGroupSum E stmt msg hkm i) : ZMod E.q)).val = coeff i := by
        rw [← h1]
        exact ZMod.val_natCast_of_lt hBound
      rw [h2]
    · rw [if_neg hC]
      rw [hCoeff_noncanon i hC, Nat.cast_zero]
  refine ⟨?_, hScalars_eq⟩
  -- Step 2: extractorSucceeds from the bound on coeff.
  intro i
  rw [hScalars_eq i, Int.natAbs_ofNat]
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
      ECPoint.add E
        (ECPoint.affine stmt.target.1 (-stmt.target.2))
        (ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
          (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
            (ECPoint.affine (extractorBases E stmt msg hkm i).1
                            (extractorBases E stmt msg hkm i).2)))
      = 0) :
    ECPoint.affine stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (ECPoint.affine (extractorBases E stmt msg hkm i).1
                          (extractorBases E stmt msg hkm i).2)) := by
  set P_aff := (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q)
  set X := ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
    (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
      (ECPoint.affine (extractorBases E stmt msg hkm i).1
                      (extractorBases E stmt msg hkm i).2)) with hX_def
  -- The `-P` affine point is the ECPoint negation of `P_aff`.
  have hPneg : (ECPoint.affine stmt.target.1 (-stmt.target.2) : ECPoint E.q) =
               -P_aff := rfl
  rw [hPneg] at hZeroSum
  -- `add (-P_aff) P_aff = 0` by `neg_add_cancel`.
  have hNegCancel : ECPoint.add E (-P_aff) P_aff = 0 :=
    ECPoint.neg_add_cancel E P_aff
  -- Conclude `X = P_aff` by left cancellation.
  have hEq : ECPoint.add E (-P_aff) X = ECPoint.add E (-P_aff) P_aff := by
    rw [hZeroSum, hNegCancel]
  exact (ECPoint.add_left_cancel E hEq).symm

/-- **D4+D5 combined.** Given principality of the extractor's divisor
    coefficient function (`extractorDivisorCoeffs`), conclude
    `target = Σ [extractedScalars i] · B_i`. -/
theorem target_eq_weightedSum_of_principal
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hPrincipal : IsPrincipal E (extractorDivisorCoeffs E stmt msg hkm)) :
    ECPoint.affine stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E (extractedScalars E stmt msg hkm i)
          (ECPoint.affine (extractorBases E stmt msg hkm i).1
                          (extractorBases E stmt msg hkm i).2)) := by
  exact target_eq_weightedSum_of_zero_sum E stmt msg hkm
    (extractor_zeroSum_of_principal E stmt msg hkm hNoNegP hPrincipal)

/-! ## Narrow bridge axiom (TEMPORARY — composite)

    This axiom is a *composite* that bundles two separate pieces of
    classical AG content together. It is NOT a single textbook
    result; it is a stopgap pending full mechanization.

    * **Derivable piece (not actually axiomatic):** that
      `logDerivCheckFn ≡ 0 on defined non-vertical pairs` implies the
      extractor's combinatorial matching. This follows from
      Silverman III.3.5 (D's principal divisor) combined with
      denominator-clearing (mechanized at scalar level), Bezout on
      E × E (mechanized via T1/T2/T3), and partial-fraction uniqueness
      (mechanized in `simple_pole_fraction_zero`). Estimated ~500-800
      LOC of function-field infrastructure to mechanize.
    * **Missing axiomatic content (Silverman III.3.5):** every
      non-zero CoordRingElt `D` has a principal divisor
      `Σ β_k · Q_k − D.degE · ∞` on E, where `(Q, β)` are its
      distinct affine zeros with multiplicities summing to `D.degE`.

    The target end-state is to replace this composite axiom with a
    single narrow Silverman III.3.5 axiom
    (`CoordRingElt.has_principal_divisor`) plus full mechanization of
    the bridge. See `docs/axiom-elimination-plan.md` for the citation
    policy (axioms cite Silverman/Hasse only) and the remaining path. -/

/-- **Bridge axiom (composite, temporary).** See docstring above for
    the split into Silverman III.3.5 + derivation; that split is
    planned future work. -/
axiom weil_reciprocity_soundness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    extractorSucceeds E stmt msg d hkm ∧
    IsPrincipal E (extractorDivisorCoeffs E stmt msg hkm)

/-! ## T4 theorem: the original bridge statement as a theorem -/

/-- **T4 bridge theorem.** Previously an axiom; now derived from the
    narrow `weil_reciprocity_soundness` axiom combined with the
    D4+D5 infrastructure (`target_eq_weightedSum_of_principal`).

    Conclusion: `extractorSucceeds` and
    `target = Σ [extractedScalars i] · B_i`. -/
theorem extractorSucceeds_of_logDerivCheck_identically_zero_general
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    extractorSucceeds E stmt msg d hkm ∧
    ECPoint.affine stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg hkm i)
                   (ECPoint.affine (extractorBases E stmt msg hkm i).1
                                   (extractorBases E stmt msg hkm i).2)) := by
  obtain ⟨hSucc, hPrincipal⟩ :=
    weil_reciprocity_soundness E stmt msg d hDeg hd hkm hAdm hNoNegP hAllZero
  exact ⟨hSucc,
    target_eq_weightedSum_of_principal E stmt msg hkm hNoNegP hPrincipal⟩

/-! ## Extractor validity (both cases) -/

/-- **Extractor validity (both cases).** The extracted witness
    satisfies the dlog relation `dlogHolds`:
    * Special case (`-P ∈ {B_j}`): `extracted_scalars_valid_special`.
    * General case (`-P ∉ {B_j}`): T4 theorem's second conjunct. -/
theorem extracted_scalars_valid
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ECPoint.affine stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg hkm i)
                   (ECPoint.affine (extractorBases E stmt msg hkm i).1
                                   (extractorBases E stmt msg hkm i).2)) := by
  classical
  by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
  · exact extracted_scalars_valid_special E stmt msg hkm hNegP
  · exact (extractorSucceeds_of_logDerivCheck_identically_zero_general
            E stmt msg d hDeg hd hkm hAdm hNegP hAllZero).2

/-! ## Theorem 6: Extractable MA protocol -/

/-- **Theorem 6 (MA extractability) — upgraded form with valid witness.**

    Knowledge soundness of the MA protocol. For every first-round message,
    one of the two branches holds:

    * **Witness branch**: there exists a witness `wit` satisfying the
      dlog relation `dlogHolds E stmt wit hkm` such that the extractor
      returns `some wit`; or

    * **Bound branch**: the set of accepting challenges in `validPairs`
      has cardinality at most
      `(72 · (d + stmt.k + 6) + 4) · |E.points|`. -/
theorem ma_extractable
    (stmt : DlogStatement E.q) (d : ℕ) (hd : d < E.q) (hd2 : 2 ≤ d)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ d)
    (hkm : stmt.k = msg.k) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg d hd hkm = some wit
        ∧ dlogHolds E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (72 * (d + stmt.k + 6) + 4) * E.points.card := by
  classical
  by_cases hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
     logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ ∧
     logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
       (fun i => msg.m (hkm ▸ i)) A₀ A₁ ≠ 0
  · -- Nonvanishing on defined subset: `log_deriv_sz` bounds the NotEq bad set.
    right
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      (validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
    set badSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      badChallengesNotEq E msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) with hBS
    have hSub : acceptSet ⊆ badSet := by
      intro p hp
      simp only [hAS, Finset.mem_filter] at hp
      simp only [hBS, badChallengesNotEq, Finset.mem_filter]
      exact ⟨hp.1, hp.2.2.2⟩
    have hCardLe : acceptSet.card ≤ badSet.card := Finset.card_le_card hSub
    have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt hDeg hd
    have hBound :=
      log_deriv_sz E msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) hDegLt hNV
    have hMono : (72 * (msg.toD.degE + stmt.k + 6) + 4) * E.points.card
                 ≤ (72 * (d + stmt.k + 6) + 4) * E.points.card := by
      apply Nat.mul_le_mul_right
      have : msg.toD.degE + stmt.k + 6 ≤ d + stmt.k + 6 := by
        exact Nat.add_le_add_right (Nat.add_le_add_right hDeg _) _
      omega
    exact le_trans hCardLe (le_trans hBound hMono)
  · push_neg at hNV
    by_cases hAdm : stmt.admSet (msg.polyA, msg.polyB)
    · left
      classical
      by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
      · have hSucc : extractorSucceeds E stmt msg d hkm :=
          extractorSucceeds_special E stmt msg d hkm hNegP hd2
        have hRelation := extracted_scalars_valid_special E stmt msg hkm hNegP
        let wit : DlogWitness E.q :=
          ⟨msg.k, extractedScalars E stmt msg hkm, d, hSucc⟩
        refine ⟨wit, ?_, ?_⟩
        · show (if h : extractorSucceeds E stmt msg d hkm
                then some (⟨msg.k, extractedScalars E stmt msg hkm, d, h⟩ : DlogWitness E.q)
                else none) = _
          rw [dif_pos hSucc]
        · refine ⟨hkm, ?_⟩
          show (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q) =
            ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
              (fun i => ECPoint.zsmul E (wit.scalars i)
                (ECPoint.affine
                  (stmt.bases (Fin.cast hkm.symm i)).1
                  (stmt.bases (Fin.cast hkm.symm i)).2))
          convert hRelation using 1
      · obtain ⟨hSucc, hRelation⟩ :=
          extractorSucceeds_of_logDerivCheck_identically_zero_general E stmt msg d
            hDeg hd hkm hAdm hNegP
            (fun A₀ A₁ hA₀ hA₁ hDef => hNV A₀ A₁ hA₀ hA₁ hDef)
        let wit : DlogWitness E.q :=
          ⟨msg.k, extractedScalars E stmt msg hkm, d, hSucc⟩
        refine ⟨wit, ?_, ?_⟩
        · show (if h : extractorSucceeds E stmt msg d hkm
                then some (⟨msg.k, extractedScalars E stmt msg hkm, d, h⟩ : DlogWitness E.q)
                else none) = _
          rw [dif_pos hSucc]
        · refine ⟨hkm, ?_⟩
          show (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q) =
            ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
              (fun i => ECPoint.zsmul E (wit.scalars i)
                (ECPoint.affine
                  (stmt.bases (Fin.cast hkm.symm i)).1
                  (stmt.bases (Fin.cast hkm.symm i)).2))
          convert hRelation using 1
    · right
      set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
        (validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
      have hEmpty : acceptSet = ∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro p hp
        simp only [hAS, Finset.mem_filter] at hp
        exact hAdm hp.2.2.1
      rw [hEmpty]
      simp

/-! ## Theorem 7: Knowledge-Sound IP -/

/-- **Theorem 7 (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (d : ℕ) (hd : d < E.q) (hd2 : 2 ≤ d)
    (msg1 : MAProverMsg E.q) (hDeg : msg1.toD.degE ≤ d)
    (hkm : stmt.k = msg1.k) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 d hd hkm = some wit
         ∧ dlogHolds E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ (72 * (d + stmt.k + 6) + 4) * E.points.card)
    ∧ ∀ (chal : MAChallenge E.q) (A₂ : ZMod E.q × ZMod E.q)
        (msg3 msg3' : IPProverMsg3 E.q),
        msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0 →
        msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0 →
        msg1.toD.eval A₂.1 A₂.2 ≠ 0 →
        (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
            stmt.target.1 (-stmt.target.2) ≠ 0 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3' →
        msg3 = msg3' := by
  refine ⟨?_, ?_⟩
  · exact ma_extractable E stmt d hd hd2 msg1 hDeg hkm
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

end Divisor
