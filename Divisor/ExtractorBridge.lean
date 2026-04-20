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

/-! ## weightedSum subset helper

Adding zero-valued entries to a `weightedSum` over an `ECPoint`-valued
family doesn't change the sum. Dual to `Finset.sum_subset` for
`Finset.sum`; proved by induction on the outer Finset. -/

theorem ECPoint.weightedSum_subset_of_zero_outside
    {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t)
    {f : α → ECPoint E.q} (h0 : ∀ a ∈ t, a ∉ s → f a = 0) :
    ECPoint.weightedSum E t f = ECPoint.weightedSum E s f := by
  revert s
  induction t using Finset.induction_on with
  | empty =>
      intro s hs _
      rw [Finset.subset_empty.mp hs]
  | @insert a t' ha ih =>
      intro s hs h0
      rw [ECPoint.weightedSum_insert E ha]
      by_cases hain : a ∈ s
      · have hs_erase_sub : s.erase a ⊆ t' := by
          intro x hx
          have hxs : x ∈ s := Finset.mem_of_mem_erase hx
          have hxt : x ∈ insert a t' := hs hxs
          have hxne : x ≠ a := Finset.ne_of_mem_erase hx
          exact (Finset.mem_insert.mp hxt).resolve_left hxne
        have hs_insert : s = insert a (s.erase a) := (Finset.insert_erase hain).symm
        have h0' : ∀ x ∈ t', x ∉ s.erase a → f x = 0 := by
          intro x hxt hxne
          by_cases hxs : x ∈ s
          · have hxeq : x = a := by
              by_contra hxa
              exact hxne (Finset.mem_erase.mpr ⟨hxa, hxs⟩)
            exact absurd (hxeq ▸ hxt) ha
          · exact h0 x (Finset.mem_insert_of_mem hxt) hxs
        have hrec : ECPoint.weightedSum E t' f = ECPoint.weightedSum E (s.erase a) f :=
          ih hs_erase_sub h0'
        rw [hs_insert, ECPoint.weightedSum_insert E (Finset.not_mem_erase _ _), hrec]
      · rw [h0 a (Finset.mem_insert_self _ _) hain, ECPoint.zero_add_curve]
        have hs_t' : s ⊆ t' := by
          intro x hx
          have hxt : x ∈ insert a t' := hs hx
          have hxne : x ≠ a := fun heq => hain (heq ▸ hx)
          exact (Finset.mem_insert.mp hxt).resolve_left hxne
        have h0' : ∀ x ∈ t', x ∉ s → f x = 0 :=
          fun x hxt hxs => h0 x (Finset.mem_insert_of_mem hxt) hxs
        exact ih hs_t' h0'

/-! ## Zsmul on `ECPoint.infinity` -/

theorem ECPoint.nsmul_infinity (E : ECSetup) (n : ℕ) :
    ECPoint.nsmul E n (ECPoint.infinity : ECPoint E.q) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show ECPoint.add E ECPoint.infinity (ECPoint.nsmul E n ECPoint.infinity) = 0
      rw [ih]
      rfl

theorem ECPoint.zsmul_infinity (E : ECSetup) (n : ℤ) :
    ECPoint.zsmul E n (ECPoint.infinity : ECPoint E.q) = 0 := by
  cases n with
  | ofNat m => exact ECPoint.nsmul_infinity E m
  | negSucc m =>
      show -(ECPoint.nsmul E (m + 1) ECPoint.infinity) = 0
      rw [ECPoint.nsmul_infinity]
      rfl

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

end Divisor
