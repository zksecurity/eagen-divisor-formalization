/-
  Divisor/WeilReciprocityDescent.lean

  Descent of the project-specific `weil_reciprocity_honest` axiom
  (in `Divisor/Axioms/AxiomWeilReciprocityHonest.lean`) to a *theorem*
  derived from textbook Weil reciprocity (`weil_reciprocity_textbook`
  in `Divisor/Axioms/AxiomWeilReciprocity.lean`) plus protocol-specific
  algebra.

  ## Structure

  **`weil_residue_identity`** (sorry'd bridge lemma): under the
  honest-prover hypothesis, the trace of log-derivative terms at the
  three chord-fiber points `(A₀, A₁, A₂)` equals the evaluation sum
  `−1/L(−P) + Σⱼ −mⱼ/L(Bⱼ)`. This is the core content of Weil
  reciprocity applied to `D` and the chord line `L`.

  **`weil_pairing_zero_under_honest`**: proved from
  `weil_residue_identity` by observing that `logDerivCheckFn` is
  exactly `lhs − rhs` where `lhs = rhs` by the residue identity.

  **`weil_reciprocity_honest_descent`**: re-exports
  `weil_pairing_zero_under_honest`.
-/
import Divisor.Defs
import Divisor.LogDeriv
import Divisor.Protocol
import Divisor.SupportDisjoint
import Divisor.ChordLogDerivProof
import Divisor.Axioms.AxiomWeilReciprocity

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
    refine Or.inr (Or.inr ?_)
    show (match thirdPoint E A₀ A₁ with
      | none => True
      | some (x, y) => D.eval x y = 0)
    rw [hThirdEq]
    exact h
  exact logDerivCheckFn_zero_of_chord_residue_match E D P B m β_fun
    hD hSplit hβsup hβcov hAccount hβtrue A₀ A₁ hA₀ hA₁ hNV
    hA₀def hA₁def hA₂def hQline hDen hResidueMatch

/-! ## Bridge lemma: the Weil residue identity

This is the mathematical heart of the descent. Under the honest-prover
hypothesis, the trace of `logDerivTerm`s at the three chord-fiber
points equals the evaluation-sum RHS:

    logDerivTerm(D, λ, A₀) + logDerivTerm(D, λ, A₁) + logDerivTerm(D, λ, A₂)
    = −(L(−P))⁻¹ + Σⱼ −mⱼ · (L(Bⱼ))⁻¹

i.e. `logDerivCheckFn E D P k B m A₀ A₁ = 0`.

Proof sketch (to be mechanized):
1. By `chord_sum_eq_chord_fiber_product_logDeriv`, the LHS equals
   `(N(D))'(μ) / N(D)(μ)` where `N = chord_fiber_product` and
   `μ = zLambda λ A₀`.
2. By `chord_fiber_product_eq_normZ_under_split`, `N(D) = c · normZ`
   for some nonzero `c`, so the log-derivative simplifies to
   `(normZ)'(μ) / normZ(μ)`.
3. `normZ = ∏ (z − zₖ)^{βₖ}`, so by the partial-fraction expansion
   of its log-derivative:
     `(normZ)'(μ)/normZ(μ) = Σₖ βₖ / (μ − zₖ)`.
4. Converting `μ − zₖ` to `L(Qₖ) · (x₁ − x₀)` and using the
   honest-prover divisor coefficients (`β(-P) = 1` and `β(Bⱼ) = nⱼ`
   with `mⱼ = nⱼ mod q`) yields exactly the RHS.
5. Textbook Weil reciprocity (`weil_reciprocity_textbook`) justifies
   the product-to-sum conversion and ensures the identity holds
   when the supports are disjoint (guaranteed by `¬ bad`).

The statement is intentionally restricted to `A₀, A₁ ∈ E.points`,
matching the completeness consumer and the geometric hypotheses needed
by the chord-residue identity.

This lemma requires importing and chaining several axioms
(`weil_reciprocity_textbook`, `chord_sum_eq_chord_fiber_product_logDeriv`,
`chord_fiber_product_eq_normZ_under_split`, `principal_divisor_iff`).
The remaining formal gap is the honest-divisor identification:
`msg.isHonestFor E stmt wit hk hkm` currently proves that the formal
honest divisor is principal, but it does not directly identify
`msg.toD`'s actual zero divisor and multiplicities with
`(-P) + Σᵢ wit.scalars(i) · (Bᵢ)`. That bridge is needed to rewrite the
partial-fraction sum over `msg.toD`'s zeros into the protocol RHS. -/
theorem weil_residue_identity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (_hA₀ : A₀ ∈ E.points) (_hA₁ : A₁ ∈ E.points)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let x₂ := lam ^ 2 - A₀.1 - A₁.1
    let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
    let L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2
    let negP := (stmt.target.1, -stmt.target.2)
    logDerivTerm E msg.toD E.curveA lam A₀ +
    logDerivTerm E msg.toD E.curveA lam A₁ +
    logDerivTerm E msg.toD E.curveA lam (x₂, y₂) =
    -(L.eval negP.1 negP.2)⁻¹ +
    (Finset.univ (α := Fin stmt.k)).sum
      (fun j => -(msg.m (hkm ▸ j)) * (L.eval (stmt.bases j).1 (stmt.bases j).2)⁻¹) := by
  sorry

/-! ## Main theorem: `weil_pairing_zero_under_honest`

Proved by observing that `logDerivCheckFn` is defined as exactly
`lhs − rhs` where `lhs = rhs` is established by `weil_residue_identity`. -/

theorem weil_pairing_zero_under_honest
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 := by
  -- logDerivCheckFn is defined as lhs - rhs; show lhs = rhs.
  have hId := weil_residue_identity E stmt wit hk msg hkm hHonestDivisor
    A₀ A₁ hA₀ hA₁ hGood
  simp only [] at hId
  -- logDerivCheckFn = lhs - rhs, so logDerivCheckFn = 0 ↔ lhs = rhs
  show logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
    (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0
  unfold logDerivCheckFn
  simp only []
  exact sub_eq_zero.mpr hId

/-! ## Top-level: the honest-prover Weil-reciprocity theorem -/
theorem weil_reciprocity_honest_descent
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 :=
  weil_pairing_zero_under_honest E stmt wit hk msg hkm hHonestDivisor
    A₀ A₁ hA₀ hA₁ hGood

end Divisor
