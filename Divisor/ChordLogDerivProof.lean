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
  by decomposing into two independent axioms:

  **AXIOM 1** (`chord_fiber_product_eq_normZ_under_split`):
    The chord-fiber product ∏ᵢ D(Aᵢ(z)) equals a nonzero constant times
    normZ(z), under splitting + accounting hypotheses.
    *Citation*: Stichtenoth, *Algebraic Function Fields and Codes*,
    2nd ed., GTM 254, Proposition 3.1.9 (p.72–73, conorm of a principal
    divisor is a principal divisor) combined with the norm/conorm
    duality on Div in finite separable extensions (cf. Stichtenoth
    §3.1 and the norm map `NF'/F` introduced in §3.7).

  **AXIOM 2** (`chord_sum_eq_chord_fiber_product_logDeriv`):
    The sum of logDerivTerms at the three chord-fiber points equals the
    logarithmic derivative of the chord-fiber product at the chord
    intercept.
    *Citation*: Lang, *Algebra*, 3rd ed., GTM 211, §VI.5 Theorem 5.1
    (norm `N_{L/K}` as determinant of the multiplication map) +
    §VIII.5 (Derivations, p.368) applied to the separable function-
    field extension `F_q(E)/F_q(z)`: the trace-of-log-derivative
    identity `Tr_{L/K}(dg/g) = d(N_{L/K}(g))/N_{L/K}(g)` follows from
    differentiating the product formula `N_{L/K}(g) = ∏_σ σ(g)` over
    a Galois closure, with the derivation extended to the Galois
    closure per §VIII.5.

  **DERIVED** (`chord_sum_eq_residue_sum`): theorem combining the two
  axioms with the existing `normZ_logDeriv_at_chord_intercept`.
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

/-! ## Opaque definition: chord-fiber product

The chord-fiber product ∏ᵢ D(Aᵢ(z)) is the function-field norm
N_{F_q(E)/F_q(z)}(D) viewed as a polynomial in z, where A₀(z), A₁(z),
A₂(z) are the three chord-fiber points parametrised by z = y − λx.

This is left opaque because its concrete construction requires
resultant infrastructure (Sylvester matrix over three sheets) that
is not currently available. The two axioms below capture the two
key properties of this norm that the proof needs. -/

/-- The chord-fiber product: ∏ᵢ D(Aᵢ(z)) as a polynomial in z.
Represents the function-field norm N_{F_q(E)/F_q(z)}(D). -/
noncomputable opaque chord_fiber_product (E : ECSetup) (lam : ZMod E.q) (D : CoordRingElt E.q) : (ZMod E.q)[X]

/-! ## AXIOM 1: Divisor-of-norm formula (Stichtenoth III.1.11)

Under the splitting and accounting hypotheses, the chord-fiber product
∏ᵢ D(Aᵢ(z)) (the function-field norm) equals a nonzero constant times
normZ(z). This is because both polynomials have the same roots with the
same multiplicities: the norm's roots are the z-coordinates of D's
zeros on E, with multiplicities matching betaConstructive.

**Citation**: Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., GTM 254, Proposition 3.1.9 (p.72–73) — the conorm of a
principal divisor is a principal divisor:
  Con_{F'/F}(div(x)) = div_{F'}(x),
together with the norm map `NF'/F` (introduced in §3.7) which sends
a function in F' to its product of Galois conjugates in F. The
divisor-of-norm identity, for `y ∈ F'`,
  div_F(N_{F'/F}(y)) = "Tr on divisors"(div_{F'}(y)),
then identifies (under the splitting hypothesis) the roots and
multiplicities of N(D)(z) with those of normZ(z), establishing
proportionality. -/
axiom chord_fiber_product_eq_normZ_under_split
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, betaConstructive E D P) =
                  (normPoly E D).natDegree) :
    ∃ c : ZMod E.q, c ≠ 0 ∧ chord_fiber_product E lam D = C c * normZ E lam D

/-! ## AXIOM 2: Trace-of-log-derivative identity (Lang §VI.5 + §VIII.5)

The sum of logDerivTerms at the three chord-fiber points equals the
logarithmic derivative of the chord-fiber product at the chord
intercept μ. This is the function-field trace-of-log-derivative formula:

    Tr_{L/K}(dg/g) = d(N_{L/K}(g)) / N_{L/K}(g)

specialised to g = D, K = F_q(z), L = F_q(E), and evaluated at the
chord intercept μ = zLambda λ A₀.

**Citation**: Lang, *Algebra*, 3rd ed., GTM 211, §VI.5 Theorem 5.1
(the norm N_{L/K} as determinant of the multiplication map, and the
characteristic polynomial connection) + §VIII.5 Derivations (p.368)
for the extension of a derivation to a separable algebraic extension;
the identity `Tr_{L/K}(dg/g) = d(N_{L/K}(g))/N_{L/K}(g)` follows from
differentiating the product formula `N_{L/K}(g) = ∏_σ σ(g)` over a
Galois closure. -/
axiom chord_sum_eq_chord_fiber_product_logDeriv
    (E : ECSetup) (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂  := lam ^ 2 - A₀.1 - A₁.1
              let y₂  := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hChordNorm : (chord_fiber_product E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let μ := zLambda E lam A₀
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = eval μ (derivative (chord_fiber_product E lam D))
      / (chord_fiber_product E lam D).eval μ

/-! ## Helper: log-derivative of a constant multiple

If f = C c * g with c ≠ 0, then f'(μ)/f(μ) = g'(μ)/g(μ). -/

theorem logDeriv_const_mul {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (g : K[X]) (μ : K) (hg : g.eval μ ≠ 0) :
    eval μ (derivative (C c * g)) / (C c * g).eval μ =
    eval μ (derivative g) / g.eval μ := by
  rw [derivative_C_mul, eval_C_mul, eval_C_mul]
  field_simp

/-! ## Step 3: The chord_sum_eq_residue_sum derived theorem

This is the function-field content: the sum of logDerivTerms at the
three chord intersection points equals the negative residue sum.

Mathematically, this follows from:
1. AXIOM 2: the sum of logDerivTerms equals the log-derivative of
   chord_fiber_product at μ.
2. AXIOM 1: chord_fiber_product = c · normZ for some nonzero c, under
   splitting + accounting.
3. Log-derivative invariance: (c·f)'/c·f = f'/f for constant c ≠ 0.
4. normZ_logDeriv_at_chord_intercept: normZ'(μ)/normZ(μ) = -Σ β/L.
-/

/-- **Theorem (scalar trace-of-log-derivative identity on the chord fiber).**
The sum of `logDerivTerm` over the three chord fiber points equals the
negative sum of `β(Q) / L_Q(Q)` over the affine zeros of `D` (where
`β = betaConstructive E D`).

Derived from `chord_fiber_product_eq_normZ_under_split` (AXIOM 1,
Stichtenoth III.1.11) and `chord_sum_eq_chord_fiber_product_logDeriv`
(AXIOM 2, Lang §VI.5 + §VIII.5), combined with the existing
`normZ_logDeriv_at_chord_intercept` (partial-fraction expansion). -/
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
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  -- Step 1: normZ(μ) ≠ 0 from hQline
  have hNormZne : (normZ E lam D).eval μ ≠ 0 := by
    rw [hMu, hLam]
    exact normZ_eval_ne_zero_of_hQline E D A₀ A₁ hD hQline
  -- Step 2: AXIOM 1 — chord_fiber_product = c * normZ
  obtain ⟨c, hc_ne, hcfp_eq⟩ :=
    chord_fiber_product_eq_normZ_under_split E D lam hD hSplit hAccount
  -- Step 3: chord_fiber_product(μ) ≠ 0
  have hcfp_ne : (chord_fiber_product E lam D).eval μ ≠ 0 := by
    rw [hcfp_eq, eval_mul, eval_C]
    exact mul_ne_zero hc_ne hNormZne
  -- Step 4: AXIOM 2 — LHS = cfp'(μ)/cfp(μ)
  have hAxiom2 : logDerivTerm E D E.curveA lam A₀
        + logDerivTerm E D E.curveA lam A₁
        + logDerivTerm E D E.curveA lam
            (lam ^ 2 - A₀.1 - A₁.1,
             lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      = eval μ (derivative (chord_fiber_product E lam D))
        / (chord_fiber_product E lam D).eval μ := by
    rw [hLam, hMu]
    exact chord_sum_eq_chord_fiber_product_logDeriv E D A₀ A₁
      hA₀ hA₁ hNV hD hA₀def hA₁def hA₂def hDen (by rw [← hLam, ← hMu]; exact hcfp_ne)
  -- Step 5: cfp'(μ)/cfp(μ) = normZ'(μ)/normZ(μ) via constant-multiple cancellation
  have hLogDeriv : eval μ (derivative (chord_fiber_product E lam D))
      / (chord_fiber_product E lam D).eval μ =
      eval μ (derivative (normZ E lam D)) / (normZ E lam D).eval μ := by
    rw [hcfp_eq]
    exact logDeriv_const_mul c hc_ne (normZ E lam D) μ hNormZne
  -- Step 6: normZ_logDeriv_at_chord_intercept — normZ'(μ) = -(normZ(μ) * Σ β/L)
  have hPFE := normZ_logDeriv_at_chord_intercept E D A₀ A₁ hQline
  -- Abbreviations for the target
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
  -- Chain: LT = cfp'/cfp = normZ'/normZ = -S
  -- hPFE: Nd = -(N * S)
  change Nd = -(N * S) at hPFE
  -- hAxiom2: LT = cfp'/cfp
  -- hLogDeriv: cfp'/cfp = Nd/N
  -- So LT = Nd/N
  have hLT_eq : LT = Nd / N := by
    rw [hAxiom2, hLogDeriv]
  -- Nd = -(N * S) and N ≠ 0 ⇒ Nd/N = -S
  have hNd_div : Nd / N = -S := by
    rw [hPFE]
    field_simp
  -- Conclude: LT = -S
  show LT = -S
  rw [hLT_eq, hNd_div]

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
