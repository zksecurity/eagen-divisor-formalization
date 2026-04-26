/-
  Divisor/PolyGTraceFormula.lean

  Sub-theorems toward converting the `polyG_zero_trace_formula` axiom
  (in `Divisor/ExtractorBridge.lean`) into a theorem.

  **Proof chain (betaConstructive case)**:
  1. `chord_sum_eq_residue_sum` (axiom, ChordLogDerivProof.lean):
     scalar chord-sum = −Σ betaConstructive(Q)/L(Q) over zerosFinset.
  2. Convert Finset sum → Fin-indexed sum so hLemma6 applies.
  3. `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (ResidueIdentity.lean):
     hLemma6 + logDerivCheckFn = 0  ⟹  polyG = 0 at defined pair.
  4. `polyG_zero_on_nonvertical_of_defined` (PolyGDensity.lean):
     polyG = 0 on "defined" pairs extends to all non-vertical pairs.

  **Gap analysis** (see comments in `ExtractorBridge.lean` at the axiom):
  The axiom `polyG_zero_trace_formula` quantifies over *arbitrary*
  `β_fun` satisfying Silverman III.3.5-style conditions, while
  `chord_sum_eq_residue_sum` is proved (as an axiom) for the specific
  `betaConstructive`. We prove the chain for `betaConstructive` below
  and note that the general case requires a uniqueness lemma
  (`multAt_eq_of_conditions`) that is not currently available.
-/
import Divisor.ChordLogDerivProof
import Divisor.ResidueIdentity
import Divisor.PolyGDensity
import Divisor.DivisorPrincipal

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Step 1–2: Convert chord_sum_eq_residue_sum Finset sum to Fin-indexed form

    `chord_sum_eq_residue_sum` yields a sum over `zerosFinset E D`;
    `polyG_zero_of_Lemma6_and_logDerivCheck_zero` needs a Fin-indexed sum.
    The canonical enumeration `zerosAt` / `zerosEnum` provides the
    bijection. -/

/-- The Finset sum `Σ_{Q ∈ zerosFinset E D} f(Q)` equals the
    Fin-indexed sum `Σ_{k : Fin (zerosCard E D)} f(zerosAt E D k)`. -/
theorem sum_zerosFinset_eq_sum_fin
    (D : CoordRingElt E.q) (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    ∑ Q ∈ zerosFinset E D, f Q =
    ∑ k : Fin (zerosCard E D), f (zerosAt E D k) := by
  symm
  apply Finset.sum_bij (fun k _ => zerosAt E D k)
  · intro k _
    exact Finset.mem_filter.mpr
      ⟨zerosAt_mem_E E D k, zerosAt_eval_zero E D k⟩
  · intro k₁ _ k₂ _ heq
    exact zerosAt_injective E D heq
  · intro Q hQ
    obtain ⟨k, hk⟩ := zerosAt_surjective_on_zeros E D Q hQ
    exact ⟨k, Finset.mem_univ _, hk⟩
  · intro k _; rfl

/-- The chord-sum identity restated with Fin-indexed sums for
    `betaConstructive`. This is the `hLemma6` input needed by
    `polyG_zero_of_Lemma6_and_logDerivCheck_zero`. -/
theorem chord_sum_eq_residue_sum_fin
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = -∑ k' : Fin (zerosCard E D),
        (betaConstructive E D (zerosAt E D k') : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ := by
  have hOrig := chord_sum_eq_residue_sum E D A₀ A₁
    hA₀ hA₁ hNV hD hSplit hAccount hA₀def hA₁def hA₂def hQline hDen
  rw [sum_zerosFinset_eq_sum_fin] at hOrig
  exact hOrig

/-- `hQline` for `zerosAt`-indexed zeros: if the Finset version holds,
    the Fin-indexed version holds too. -/
theorem hQline_fin_of_finset
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    ∀ k' : Fin (zerosCard E D),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
        (zerosAt E D k').1 (zerosAt E D k').2 ≠ 0 := by
  intro k'
  apply hQline
  exact Finset.mem_filter.mpr
    ⟨zerosAt_mem_E E D k', zerosAt_eval_zero E D k'⟩

/-! ## Step 3: polyG = 0 for betaConstructive at defined pairs

    Combine `chord_sum_eq_residue_sum_fin` (`\ref{lem:log-derivative}` for betaConstructive)
    with `polyG_zero_of_Lemma6_and_logDerivCheck_zero` to get polyG = 0
    at defined non-vertical pairs. -/

/-- **Key sub-theorem**: at a defined non-vertical pair where the
    chord-sum hypotheses hold AND `logDerivCheckFn = 0`, the `polyG`
    formed from `betaConstructive` multiplicities vanishes.

    This is the `\ref{lem:log-derivative}` → polyG bridge instantiated at
    `β = betaConstructive`, `Q = zerosAt`, using
    `chord_sum_eq_residue_sum` for the `hLemma6` input. -/
theorem polyG_zero_betaConstructive_at_defined
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    -- Non-degeneracy for chord_sum_eq_residue_sum:
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    -- Non-degeneracy for polyG bridge:
    (hNegPline : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0)
    (hBline : ∀ j, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0)
    -- logDerivCheckFn vanishes:
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    polyG E (zerosAt E D)
      (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B)
      (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0 := by
  -- Get `\ref{lem:log-derivative}` identity from chord_sum_eq_residue_sum
  have hLemma6 := chord_sum_eq_residue_sum_fin E D A₀ A₁
    hA₀ hA₁ hNV hD hSplit hAccount hA₀def hA₁def hA₂def hQline hDen
  -- The `\ref{lem:log-derivative}` identity uses betaConstructive, which equals
  -- multAt E (betaConstructive E D) D k' at zerosAt E D k'.
  -- This is definitional: multAt E β D k = β (zerosAt E D k).
  have hLemma6' :
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
                ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                  + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
      = -∑ k' : Fin (zerosCard E D),
          ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
              (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ := by
    convert hLemma6 using 2
  -- Apply the bridge theorem
  exact polyG_zero_of_Lemma6_and_logDerivCheck_zero E D P B m
    (zerosAt E D)
    (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
    A₀ A₁ hNV
    (hQline_fin_of_finset E D A₀ A₁ hQline)
    hNegPline hBline hLemma6' hCheck

end Divisor
