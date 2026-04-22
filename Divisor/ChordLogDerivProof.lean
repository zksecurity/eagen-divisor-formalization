/-
  Divisor/ChordLogDerivProof.lean

  Proof of `chordLogDerivMatchesNormZ` under splitting and norm-accounting
  hypotheses.

  ## Proof structure

  The target `chordLogDerivMatchesNormZ E D A₀ A₁` unfolds to:

      (LT₀ + LT₁ + LT₂) · normZ(μ) = normZ'(μ)

  where LTᵢ = logDerivTerm(Aᵢ, λ), μ = zLambda λ A₀.

  **Step 1.** Show `normZ(μ) ≠ 0` from `hQline` (the hypothesis that no
  zero of D lies on the chord line). This uses
  `normZ_eval_ne_zero_at_nonroot` and the bridge
  `L_eval_eq_zLambda_sub`. ✓ Proved.

  **Step 2.** Reduce to the ratio form via `chordLogDerivMatchesNormZ_of_ratio_eq`:

      LT₀ + LT₁ + LT₂ = normZ'(μ) / normZ(μ)

  ✓ Done (one-liner application).

  **Step 3.** Prove the ratio identity `trace_logDeriv_eq_normZ_logDeriv`
  (sorry'd; see below for the mathematical argument).

  ## Mathematical content of Step 3

  The ratio identity is the **function-field trace-of-log-derivative
  formula**: for D ∈ F_q[E]× and the degree-3 extension F_q(E)/F_q(z)
  with z = y − λx,

      Tr(D'/D) = N(D)'/N(D)

  where N is the extension norm and Tr is the trace. The proof goes:

  1. Define N(D)(z) = ∏ᵢ D(Aᵢ(z)) (the function-field norm), which is
     the resultant Resₓ(D(x, z+λx), chord_cubic(x, z)).

  2. By the product rule for algebraic functions:
     N(D)'(z)/N(D)(z) = Σᵢ (d/dz D(Aᵢ))/D(Aᵢ) = Σᵢ logDerivTerm(Aᵢ).

  3. Under the splitting + accounting hypotheses, N(D)(z) and normZ(z)
     have the same roots with the same multiplicities (both polynomials
     in z), hence N(D) = C · normZ for some nonzero constant C.

  4. Therefore N(D)'/N(D) = normZ'/normZ, giving the target.

  Step 3 requires either resultant infrastructure or a direct
  polynomial-root matching argument. This infrastructure is not
  currently available in the project or Mathlib.
-/
import Divisor.Lemma6
import Divisor.NormZDecomp
import Divisor.BivariateLogDeriv
import Divisor.ChordCubicSymmetric
import Divisor.PFHelper
import Mathlib

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Step 1: normZ(μ) ≠ 0 from hQline -/

/-- When no zero of D lies on the chord line (`hQline`), the norm
polynomial `normZ` is nonzero at the chord intercept μ = zLambda λ A₀.
This is because `L(Q) = z(Q) − μ`, so `L(Q) ≠ 0` implies `μ ≠ z(Q)`,
and `normZ` has no root at μ. -/
theorem normZ_eval_ne_zero_of_hQline
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0) :
    (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0 := by
  apply normZ_eval_ne_zero_at_nonroot E _ D hD
  intro Q hQ
  have hL := hQline Q hQ
  have hLsub := L_eval_eq_zLambda_sub E A₀ A₁ Q
  intro heq
  apply hL
  rw [hLsub, heq, sub_self]

/-! ## Step 3: The trace-of-log-derivative identity (core content)

This is the function-field content: the sum of logDerivTerms at the
three chord intersection points equals the logarithmic derivative of
normZ at the chord intercept.

Mathematically, this follows from:
1. The product rule: `∑ᵢ (dD/dz)(Aᵢ)/D(Aᵢ) = (d/dz ∏ D(Aᵢ))/∏ D(Aᵢ)`
2. The norm identity: `∏ D(Aᵢ(z)) = C · normZ(z)` (under splitting + accounting)
3. Log-derivative invariance: `(Cf)'/Cf = f'/f` for constant C ≠ 0.

The proof of (2) requires connecting the function-field norm
(a resultant / symmetric function in the chord fiber) to the
explicitly-defined normZ (product over zerosFinset with
betaConstructive multiplicities). Under the splitting hypothesis
(all roots of normPoly are F_q-rational) and the accounting
hypothesis (total betaConstructive sum equals normPoly degree),
the two polynomials have identical roots with identical
multiplicities, hence are proportional. -/

/-! ### Scalar identity (⋆)

The core algebraic content boiled down to a scalar equality in `F_q`:

  Σᵢ logDerivTerm(Aᵢ, λ) = -Σ_{Q ∈ zerosFinset} β(Q) / L_Q(Q)

This is the statement after applying `normZ_logDeriv_at_chord_intercept`
to the RHS of `chordLogDerivMatchesNormZ` and cancelling `normZ(μ) ≠ 0`.
Under the splitting + accounting hypotheses the identity holds because
the function-field norm `N(D)(z)` agrees as a polynomial with `normZ(z)`
(up to a constant), but the statement itself is a plain scalar equality
over `ZMod E.q`.
-/

/-- **Scalar log-derivative identity (⋆).** The sum of `logDerivTerm`
over the three chord fiber points equals the negative sum of
`β(Q) / L_Q(Q)` over the affine zeros of `D`.

**Status**: open. This is the remaining algebraic content. Under the
splitting + accounting hypotheses it reduces to a polynomial identity
in `(ZMod E.q)[z]` between the function-field norm of `D` and `normZ`.

PROVIDED SOLUTION
Under `hSplit` the three chord x-coordinates `x₀, x₁, x₂` are the
roots of a monic cubic whose elementary symmetric polynomials are
(see `Divisor/ChordCubicSymmetric.lean`):
  * `e₁ = λ²`                       (`chord_x_sum_eq_lam_sq`)
  * `e₂ = A − 2λμ`                  (`chord_x_pairwise_sum`)
  * `e₃ = μ² − B`                   (`chord_x_triple_product`)
The Lagrange partial-fraction identities over three distinct
field elements (see `Divisor/PFHelper.lean`) give
  * `∑ᵢ (c·xᵢ + d) / ∏_{j≠i}(xᵢ−xⱼ) = 0`         (`pf_affine_sum_zero`)
  * `∑ᵢ xᵢ² / ∏_{j≠i}(xᵢ−xⱼ) = 1`                  (`pf_quadratic_sum_one`)
  * `∑ᵢ (ax³+bx²+cx+d) / ∏_{j≠i}(xᵢ−xⱼ) = a·e₁+b` (`pf_cubic_sum`)

Strategy: unfold `logDerivTerm_eq_explicit`
(`Divisor/ClearedPolyForm.lean`) to get explicit rational form,
express the three-term chord sum as a Lagrange partial-fraction sum
over `x₀, x₁, x₂`, apply the PF identities with numerator polynomial
extracted from `D.a, D.b, A, B, λ, μ`, then match against the
residue-sum over `zerosFinset E D`.

Alternative: introduce a helper theorem for the case `D.b = 0`
(simpler — D is independent of y, normPoly = D.a², zerosFinset is
determined by roots of D.a together with the y-sign), prove by PF
identity + Vieta, then extend to `D.b ≠ 0` by a similar argument
on `(D.a + y·D.b) · (D.a − y·D.b) = normPoly` paired evaluation. -/
theorem chord_sum_eq_residue_sum
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
    = -∑ Q ∈ zerosFinset E D,
        (betaConstructive E D Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
  sorry

/-- **Trace-of-log-derivative identity.** The chord-sum of logDerivTerms
equals the logarithmic derivative of normZ at the chord intercept.

**Proof**: combines `chord_sum_eq_residue_sum` (scalar identity `(⋆)`)
with `normZ_logDeriv_at_chord_intercept` (partial-fraction expansion of
normZ's log-derivative into residue sum form) and cancels `normZ(μ) ≠ 0`. -/
theorem trace_logDeriv_eq_normZ_logDeriv
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
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = eval (zLambda E lam A₀)
        (derivative (normZ E lam D))
      / (normZ E lam D).eval (zLambda E lam A₀) := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  -- Scalar identity (⋆): Σ LT = -Σ β/L
  have hScalar := chord_sum_eq_residue_sum E D A₀ A₁
    hA₀ hA₁ hNV hD hSplit hAccount hA₀def hA₁def hA₂def hQline hDen
  -- PFE: eval μ (deriv normZ) = -(normZ(μ) · Σ β/L)
  have hPFE := normZ_logDeriv_at_chord_intercept E D A₀ A₁ hQline
  -- Abbreviations
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    with hLT
  set N : ZMod E.q := (normZ E lam D).eval μ with hN
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D)) with hNd
  set S : ZMod E.q :=
    ∑ Q ∈ zerosFinset E D,
      (betaConstructive E D Q : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ with hS
  -- hScalar: LT = -S
  change LT = -S at hScalar
  -- hPFE: Nd = -(N * S)
  change Nd = -(N * S) at hPFE
  -- Goal: LT = Nd / N
  show LT = Nd / N
  rw [hPFE, hScalar]
  field_simp

/-! ## Step 2 + Assembly: Main theorem -/

/-- **Main theorem: `chordLogDerivMatchesNormZ` under splitting and
accounting hypotheses.**

**Hypotheses:**
* `hSplit`: normPoly splits completely over F_q.
* `hAccount`: the total betaConstructive sum equals normPoly's natDegree.
  This ensures every root of normPoly corresponds to F_q-rational E-points
  with matching multiplicity (no "phantom" roots at non-rational points).
* Standard non-degeneracy: D nonzero, D nonvanishing at chord points,
  dx/dz denominators nonzero, zeros of D not on the chord line.

**Proof:** Reduces to `trace_logDeriv_eq_normZ_logDeriv` via the ratio
equivalence `chordLogDerivMatchesNormZ_of_ratio_eq`. -/
theorem chordLogDerivMatchesNormZ_holds
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
    chordLogDerivMatchesNormZ E D A₀ A₁ := by
  -- Step 1: normZ(μ) ≠ 0
  have hNormZne := normZ_eval_ne_zero_of_hQline E D A₀ A₁ hD hQline
  -- Step 2: reduce to ratio form
  apply chordLogDerivMatchesNormZ_of_ratio_eq E D A₀ A₁ hNormZne
  -- Step 3: apply the trace identity
  exact trace_logDeriv_eq_normZ_logDeriv E D A₀ A₁
    hA₀ hA₁ hNV hD hSplit hAccount hA₀def hA₁def hA₂def hQline hDen hNormZne

end Divisor
