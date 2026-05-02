/-
  Divisor/PolyGTraceFormula.lean

  Sub-theorems toward proving polyG vanishing at defined non-vertical
  pairs, parameterised over a multiplicity function β_fun that is
  pointwise the true local-order multiplicity.

  **Proof chain (β_fun case)**:
  1. `chord_sum_eq_residue_sum` (theorem in ChordLogDerivProof.lean):
     scalar chord-sum = −Σ β_fun(Q)/L(Q) over zerosFinset.
  2. Convert Finset sum → Fin-indexed sum so hLemma6 applies.
  3. `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (ResidueIdentity.lean):
     hLemma6 + logDerivCheckFn = 0  ⟹  polyG = 0 at defined pair.
  4. `polyG_zero_on_nonvertical_of_defined` (PolyGDensity.lean):
     polyG = 0 on "defined" pairs extends to all non-vertical pairs.
-/
import Divisor.ChordLogDerivProof
import Divisor.ResidueIdentity
import Divisor.PolyGDensity
import Divisor.DivisorPrincipal

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Step 1–2: Convert chord_sum_eq_residue_sum Finset sum to Fin-indexed form -/

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

/-- The chord-sum identity restated with Fin-indexed sums. This is the
    `hLemma6` input needed by
    `polyG_zero_of_Lemma6_and_logDerivCheck_zero`. -/
theorem chord_sum_eq_residue_sum_fin
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD  : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) = (normPoly E D).natDegree)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P)
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
        (β_fun (zerosAt E D k') : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ := by
  have hOrig := chord_sum_eq_residue_sum E D β_fun A₀ A₁
    hA₀ hA₁ hNV hD hSplit hβsup hβcov hAccount hβtrue
    hA₀def hA₁def hA₂def hQline hDen
  rw [sum_zerosFinset_eq_sum_fin] at hOrig
  exact hOrig

/-- `hQline` for `zerosAt`-indexed zeros. -/
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

/-! ## Step 3: polyG = 0 for an arbitrary β_fun at defined pairs -/

/-- **Key sub-theorem**: at a defined non-vertical pair where the
    chord-sum hypotheses hold AND `logDerivCheckFn = 0`, the `polyG`
    formed from `β_fun` multiplicities vanishes. -/
theorem polyG_zero_at_defined
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hSplit : splitsOnE E D)
    (hAccount : (∑ P ∈ E.points, β_fun P) = (normPoly E D).natDegree)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
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
    (hNegPline : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0)
    (hBline : ∀ j, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    polyG E (zerosAt E D)
      (fun k' => ((multAt E β_fun D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B)
      (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0 := by
  have hLemma6 := chord_sum_eq_residue_sum_fin E D β_fun A₀ A₁
    hA₀ hA₁ hNV hD hSplit hβsup hβcov hAccount hβtrue
    hA₀def hA₁def hA₂def hQline hDen
  have hLemma6' :
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
                ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                  + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
      = -∑ k' : Fin (zerosCard E D),
          ((multAt E β_fun D k' : ℕ) : ZMod E.q) *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
              (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ := by
    convert hLemma6 using 2
  exact polyG_zero_of_Lemma6_and_logDerivCheck_zero E D P B m
    (zerosAt E D)
    (fun k' => ((multAt E β_fun D k' : ℕ) : ZMod E.q))
    A₀ A₁ hNV
    (hQline_fin_of_finset E D A₀ A₁ hQline)
    hNegPline hBline hLemma6' hCheck

end Divisor
