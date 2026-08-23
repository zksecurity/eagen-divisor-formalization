/-
  Divisor/WeilReciprocityDescent.lean

  Protocol-level Weil-reciprocity descent under explicit divisor data:
  the trace of chord-fiber log-derivative terms vanishes when an
  explicit multiplicity function matching `D`'s zero divisor is
  supplied. The chord-residue identity is derived from the project's
  chord-resultant infrastructure plus protocol-specific algebra.

  ## Structure

  **`logDerivCheckFn_eq_residue_sum_form`** /
  **`logDerivCheckFn_zero_of_chord_residue_match`**: protocol algebra
  rewrites of `logDerivCheckFn`.

  **`logDerivCheckFn_zero_of_explicit_divisor_data`** (the external
  entry point, consumed by `EagenBuildRecursive` and
  `LogDerivEagenLength4`): `logDerivCheckFn = 0` given an explicit
  divisor multiplicity function `β_fun` matching `D`'s zero divisor,
  plus the per-challenge geometric side conditions.

  The completeness path goes through `MACompletenessCore`; the
  honest-divisor identification is supplied by the
  `MAProverMsg.isHonestFor` contract.
-/
import Divisor.Defs
import Divisor.LogDeriv
import Divisor.Protocol
import Divisor.SupportDisjoint
import Divisor.ChordLogDerivProof

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Lemma 1: protocol algebra rewrite of `logDerivCheckFn` -/

theorem logDerivCheckFn_eq_residue_sum_form
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hDenomNZ : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 ↔
      logDerivCheckFnCleared E D P k B m A₀ A₁ = 0 :=
  logDerivCheckFn_eq_zero_iff_cleared E D P B m A₀ A₁ hDenomNZ

/-! ## Intermediate completeness theorem under explicit divisor data

Decouples the chord-residue side from the protocol-level identification
of `msg.toD`'s actual zero divisor with `(-P) + Σⱼ wit.scalars(j) · (Bⱼ)`.

Inputs:
* an explicit divisor multiplicity function `β_fun : E.points → ℕ`
  matching `D`'s zero divisor (`hβsup`, `hβcov`, `hAccount`, `hSplit`),
* the per-`(A₀, A₁)` geometric non-vanishing side conditions consumed by
  `chord_sum_eq_residue_sum` (`hNV`, `hA*def`, `hQline`, `hDen`),
* the residue-support identity `hResidueMatch` that converts the sum
  over `zerosFinset E D` into the protocol RHS at `(-P)` and `(Bⱼ, mⱼ)`.

Output: `logDerivCheckFn = 0`.

Proof: `chord_sum_eq_residue_sum` gives
`LT₀ + LT₁ + LT₂ = -∑_{Q ∈ zerosFinset E D} β(Q) · L(Q)⁻¹`;
substituting `hResidueMatch` rewrites the right hand side into
`-L(-P)⁻¹ + Σⱼ -mⱼ · L(Bⱼ)⁻¹`, which is exactly the RHS used by
`logDerivCheckFn`. The result is `lhs = rhs`, hence `lhs - rhs = 0`.

This isolates the genuinely missing protocol-level identification
(`hResidueMatch`) — discharging it from `MAProverMsg.isHonestFor` is
the remaining blocker for `weil_residue_identity` proper. -/
theorem logDerivCheckFn_zero_of_chord_residue_match
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    -- divisor data for `D`:
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (hβsup : ∀ Q, β_fun Q ≠ 0 → Q ∈ E.points ∧ D.eval Q.1 Q.2 = 0)
    (hβcov : ∀ Q ∈ E.points, D.eval Q.1 Q.2 = 0 → β_fun Q ≠ 0)
    (hAccount : (∑ Q ∈ E.points, β_fun Q) = (normPoly E D).natDegree)
    (hβtrue : ∀ Q, β_fun Q = betaTrue E D hD Q)
    -- per-pair geometric data:
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
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
    -- protocol-level residue match (the explicit divisor identification):
    (hResidueMatch :
      (∑ Q ∈ zerosFinset E D, (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
          + (Finset.univ : Finset (Fin k)).sum
              (fun j => (m j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  classical
  -- Apply the chord-sum identity from `chord_sum_eq_residue_sum`.
  have hChord :=
    chord_sum_eq_residue_sum E D β_fun A₀ A₁ hA₀ hA₁ hNV hD hSplit
      hβsup hβcov hAccount hβtrue hA₀def hA₁def hA₂def hQline hDen
  unfold logDerivCheckFn
  simp only []
  rw [sub_eq_zero, hChord, hResidueMatch]
  -- Goal: -(L(-P)⁻¹ + Σ m j · L(B j)⁻¹) = -L(-P)⁻¹ + Σ -(m j) · L(B j)⁻¹.
  rw [neg_add, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ### `hGood`-driven wrapper around the explicit-data theorem

Wraps `logDerivCheckFn_zero_of_chord_residue_match` so that the
per-pair side conditions `hA*def` are extracted from the "non-bad"
hypothesis `hGood` automatically.

The two genuinely-protocol-level obligations that *cannot* be
discharged from `hGood + hA*` alone — `hQline` (D's other zeros not on
the chord) and `hDen` (the `3·x² + A − 2λ·y` factors at the three
chord points are nonzero) — are surfaced as explicit hypotheses so
they can be discharged separately. The residue-support identity
`hResidueMatch` remains explicit. -/
theorem logDerivCheckFn_zero_of_explicit_divisor_data
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D)
    (hβsup : ∀ Q, β_fun Q ≠ 0 → Q ∈ E.points ∧ D.eval Q.1 Q.2 = 0)
    (hβcov : ∀ Q ∈ E.points, D.eval Q.1 Q.2 = 0 → β_fun Q ≠ 0)
    (hAccount : (∑ Q ∈ E.points, β_fun Q) = (normPoly E D).natDegree)
    (hβtrue : ∀ Q, β_fun Q = betaTrue E D hD Q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E D)
    -- Genuinely protocol-level side conditions (not implied by hGood):
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hResidueMatch :
      (∑ Q ∈ zerosFinset E D, (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
          + (Finset.univ : Finset (Fin k)).sum
              (fun j => (m j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  classical
  -- Extract per-pair non-vanishing facts from `hGood` + `hA*`.
  have hMem : (A₀, A₁) ∈ E.points ×ˢ E.points :=
    Finset.mk_mem_product hA₀ hA₁
  have h_unbad : ¬ badPairCompletenessPred E D (A₀, A₁) := fun hbad =>
    hGood (Finset.mem_filter.mpr ⟨hMem, hbad⟩)
  -- `thirdPoint` on a non-vertical pair returns the chord formula.
  have hThirdEq :
      thirdPoint E A₀ A₁ =
        some (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
              slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
                (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
              (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) := by
    unfold thirdPoint slopeOf
    rw [if_neg hNV]
  have hA₀def : D.eval A₀.1 A₀.2 ≠ 0 := fun h =>
    h_unbad (Or.inl h)
  have hA₁def : D.eval A₁.1 A₁.2 ≠ 0 := fun h =>
    h_unbad (Or.inr (Or.inl h))
  have hA₂def :
      let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
      let x₂  := lam ^ 2 - A₀.1 - A₁.1
      let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
      D.eval x₂ y₂ ≠ 0 := by
    intro lam x₂ y₂ h
    apply h_unbad
    refine Or.inr (Or.inr (Or.inl ?_))
    show (match thirdPoint E (A₀, A₁).1 (A₀, A₁).2 with
      | none => True
      | some (x, y) => D.eval x y = 0)
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq]
    exact h
  exact logDerivCheckFn_zero_of_chord_residue_match E D P B m β_fun
    hD hSplit hβsup hβcov hAccount hβtrue A₀ A₁ hA₀ hA₁ hNV
    hA₀def hA₁def hA₂def hQline hDen hResidueMatch

end Divisor
