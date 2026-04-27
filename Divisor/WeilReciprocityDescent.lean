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

This lemma requires importing and chaining several axioms
(`weil_reciprocity_textbook`, `chord_sum_eq_chord_fiber_product_logDeriv`,
`chord_fiber_product_eq_normZ_under_split`, `principal_divisor_iff`).
The sorry records the gap between these axioms and the protocol-level
statement. -/
theorem weil_residue_identity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
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
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 := by
  -- logDerivCheckFn is defined as lhs - rhs; show lhs = rhs.
  have hId := weil_residue_identity E stmt wit hk msg hkm hHonestDivisor A₀ A₁ hGood
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
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 :=
  weil_pairing_zero_under_honest E stmt wit hk msg hkm hHonestDivisor A₀ A₁ hGood

end Divisor
