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
-/
import Divisor.Soundness

namespace Divisor

open Finset Classical

variable (E : ECSetup)

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

end Divisor
