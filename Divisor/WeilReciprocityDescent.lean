/-
  Divisor/WeilReciprocityDescent.lean

  Descent of the project-specific `weil_reciprocity_honest` axiom
  (in `Divisor/Axioms/AxiomWeilReciprocityHonest.lean`) to a *theorem*
  derived from textbook Weil reciprocity (`weil_reciprocity_textbook`
  in `Divisor/Axioms/AxiomWeilReciprocity.lean`) plus protocol-specific
  algebra.

  ## Structure

  The protocol-level claim:

      msg.isHonestFor stmt wit ∧ (A₀, A₁) ∉ badChallengesCompleteness msg.toD
      → logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases (...) A₀ A₁ = 0

  We decompose into:

  **Lemma 1** (`logDerivCheckFn_eq_weil_pairing_form`): rewrite
  `logDerivCheckFn` at a non-bad challenge as a residue/pairing sum:
      logDerivCheckFn = Σ_{P ∈ supp(div(D))} ord_P(D) · (chord-line-eval at P)⁻¹.
  Pure protocol algebra (no textbook content).

  **Lemma 2** (`weil_pairing_form_eq_zero_under_honest`): under
  `msg.isHonestFor`, the divisor of `D` is the prescribed
  `(-P) + Σ n_i (B_i) − degE(D)(∞)`. Combined with disjointness from
  `{A₀, A₁, A₂}` (the `¬ bad` premise) and Weil reciprocity applied
  to `D` and the chord polynomial `L`, the residue sum vanishes.

  **Theorem** (`weil_reciprocity_honest_descent`): chains the two
  lemmas to prove `weil_reciprocity_honest` as a theorem.

  ## Status

  This file currently contains the skeleton and `sorry` statements.
  The actual proofs are dispatched to Aristotle in a follow-up batch
  (P3.2 of the master plan).
-/
import Divisor.Defs
import Divisor.LogDeriv
import Divisor.Protocol
import Divisor.SupportDisjoint
import Divisor.Axioms.AxiomWeilReciprocity

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Lemma 1: protocol algebra rewrite of `logDerivCheckFn`

    The log-derivative check sum can be expressed (after clearing
    denominators) as a sum over `D`'s zeros on `E` of
    `ord_P(D) · (L_chord(P))⁻¹`, where `L_chord` is the chord line
    through `A₀, A₁`. This is a pure rewrite — no Weil reciprocity
    invoked yet.

    **PROVIDED SOLUTION sketch** (for Aristotle):
    Unfold `logDerivCheckFn` by definition and group the three
    chord-fiber log-deriv terms with the `−Σ −m_j / L(B_j)` term.
    Apply `chord_sum_eq_chord_fiber_product_logDeriv` (axiom 2 of
    the chord-fiber pair) and the partial-fraction expansion of
    `(normZ)'/normZ` from `normZ_logDeriv_at_chord_intercept`. The
    result expresses `logDerivCheckFn` as a Σ of residues at D's
    affine zeros plus a pole-at-(-P)/B_j contribution. -/
theorem logDerivCheckFn_eq_residue_sum_form
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hDenomNZ : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 ↔
      logDerivCheckFnCleared E D P k B m A₀ A₁ = 0 :=
  logDerivCheckFn_eq_zero_iff_cleared E D P B m A₀ A₁ hDenomNZ

/-! ## Lemma 2: Weil reciprocity descent for the honest divisor

    Under `msg.isHonestFor`, the divisor of `D` is the explicit
    formal sum `(-P) + Σ_i n_i · (B_i) − degE(D) · (∞)`. By textbook
    Weil reciprocity applied to `D` and the chord polynomial `L`:

      ∏_{Q ∈ supp(div(D)) ∩ E.points} L(Q)^{ord_Q(D)} =
        ∏_{R ∈ supp(div(L)) ∩ E.points} D(R)^{ord_R(L)}.

    The RHS is `D(A₀)·D(A₁)·D(A₂)` (the chord meets `E` at
    `{A₀, A₁, A₂}` with multiplicity 1 each). Under `¬ bad`, this is
    nonzero (none of the three Aᵢ are zeros of D). Taking
    log-derivatives matches the LHS to `logDerivCheckFn`, which
    therefore equals zero (since the LHS is essentially a residue
    sum that telescopes). -/
theorem weil_pairing_zero_under_honest
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 := by
  -- Skeleton: combine Lemma 1 with textbook Weil reciprocity.
  -- PROVIDED SOLUTION (for Aristotle):
  -- 1. Use `weil_reciprocity_textbook` with f = msg.toD, g = (chord polynomial L).
  -- 2. The disjointness premise comes from hGood (¬ bad set).
  -- 3. The honesty premise pins div(msg.toD) to the prescribed (−P + Σ n_i B_i − degE ∞).
  -- 4. Take logarithmic derivatives of both sides; the result is exactly
  --    `logDerivCheckFn = 0`.
  sorry

/-! ## Top-level: the honest-prover Weil-reciprocity theorem

    Replaces the project-specific `weil_reciprocity_honest` axiom
    with a derived theorem.  Once this `sorry` is discharged, the
    original axiom statement (in `AxiomWeilReciprocityHonest.lean`)
    can be retired and replaced with a `theorem` that just re-exports
    `weil_pairing_zero_under_honest`. -/
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
