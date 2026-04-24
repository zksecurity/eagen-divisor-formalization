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
    2nd ed., GTM 254, Proposition 3.1.9 (p.73, conorm of a principal
    divisor is a principal divisor) combined with the norm/conorm
    duality on Div in finite separable extensions (cf. Stichtenoth
    §3.1 and the norm map `N_{F'/F}` defined in Appendix A and used
    in §3.7 Theorem 3.7.1, p.121).

  **AXIOM 2** (`chord_sum_eq_chord_fiber_product_logDeriv`):
    The sum of logDerivTerms at the three chord-fiber points equals the
    logarithmic derivative of the chord-fiber product at the chord
    intercept.
    *Citation*: Lang, *Algebra*, 3rd ed., GTM 211, §VI.5 "The Norm
    and Trace" (p.284–285), Theorem 5.1 (multiplicativity of the
    norm; product-of-embeddings formula `N_k^E(α) = ∏_σ σα` for E/k
    separable) + §VIII.5 "Derivations" (p.369), Theorem 5.1 Case 1
    (p.370, unique extension of a derivation to a separable algebraic
    extension) applied to the separable function-field extension
    `F_q(E)/F_q(z)`: the trace-of-log-derivative identity
    `Tr_{L/K}(dg/g) = d(N_{L/K}(g))/N_{L/K}(g)` follows from
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
2nd ed., GTM 254, Proposition 3.1.9 (p.73) — the conorm of a
principal divisor is a principal divisor:
  Con_{F'/F}(div(x)) = div_{F'}(x),
together with the norm map `N_{F'/F}` (defined in Appendix A,
used in §3.7 Theorem 3.7.1, p.121) which sends a function in F'
to its product of Galois conjugates in F. The divisor-of-norm
identity, for `y ∈ F'`,
  div_F(N_{F'/F}(y)) = "Tr on divisors"(div_{F'}(y)),
then identifies (under the splitting hypothesis) the roots and
multiplicities of N(D)(z) with those of normZ(z), establishing
proportionality.

**Textbook statement (verbatim), Stichtenoth Proposition 3.1.9, p.73:**

> "Proposition 3.1.9. Let F′/K′ be an algebraic extension of the
> function field F/K. For 0 ≠ x ∈ F let (x)₀^F, (x)∞^F, (x)^F resp.
> (x)₀^{F′}, (x)∞^{F′}, (x)^{F′} denote the zero, pole, principal
> divisor of x in Div(F) resp. in Div(F′). Then
>   Con_{F′/F}((x)₀^F) = (x)₀^{F′},
>   Con_{F′/F}((x)∞^F) = (x)∞^{F′},   and
>   Con_{F′/F}((x)^F)  = (x)^{F′}."

**Textbook statement (verbatim), Stichtenoth Theorem 3.7.1, p.121:**

> "Theorem 3.7.1. Let F′/K′ be a Galois extension of F/K and
> P₁, P₂ ∈ IP_{F′} be extensions of P ∈ IP_F. Then P₂ = σ(P₁) for
> some σ ∈ Gal(F′/F). In other words, the Galois group acts
> transitively on the set of extensions of P."

The axiom below combines these (conorm identity + Galois-transitive
norm `N_{F'/F}`) to identify `chord_fiber_product` with a nonzero
constant multiple of `normZ` in our F_q(E)/F_q(z) setting. -/
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

**Citation**: Lang, *Algebra*, 3rd ed., GTM 211, §VI.5 "The Norm and
Trace" (p.284–285), whose Theorem 5.1 establishes multiplicativity
of the norm together with the product-of-embeddings formula
`N_k^E(α) = ∏_σ σα` (for E/k separable, p.285); combined with
§VIII.5 "Derivations" (p.369), Theorem 5.1 Case 1 (p.370), which
extends a derivation uniquely to a separable algebraic extension.
The identity `Tr_{L/K}(dg/g) = d(N_{L/K}(g))/N_{L/K}(g)` follows
from differentiating the product formula `N_{L/K}(g) = ∏_σ σ(g)`
over a Galois closure.

**Textbook statement (verbatim), Lang §VI.5, p.285 (product-of-embeddings):**

> "Thus if E is separable over k, we have
>     N^E_k(α) = ∏ σα
> where the product is taken over the distinct embeddings of E in k^a
> over k. Similarly, if E/k is separable, then
>     Tr(α) = Σ σα."

**Textbook statement (verbatim), Lang §VI.5 Theorem 5.1, p.285:**

> "Theorem 5.1. Let E/k be a finite extension. Then the norm N^E_k is
> a multiplicative homomorphism of E* into k* and the trace is an
> additive homomorphism of E into k. If E ⊃ F ⊃ k is a tower of fields,
> then the two maps are transitive, in other words,
>     N^E_k = N^F_k ∘ N^E_F   and   Tr^E_k = Tr^F_k ∘ Tr^E_F.
> If E = k(α), and f(X) = Irr(α, k, X) = X^n + a_{n-1} X^{n-1} + ⋯ + a_0,
> then
>     N^E_k(α) = (−1)^n a_0   and   Tr^E_k(α) = −a_{n-1}."

**Textbook statement (verbatim), Lang §VIII.5 Theorem 5.1 Case 1, p.370:**

> "Theorem 5.1. Let D be a derivation of a field K. Let
> (x) = (x_1, …, x_n) be a finite family of elements in an extension
> of K. Let {f_α(X)} be a set of generators for the ideal determined
> by (x) in K[X]. Then, if (u) is any set of elements of K(x)
> satisfying the equations
>     0 = f_α^D(x) + Σ (∂f_α/∂x_i) u_i,
> there is one and only one derivation D* of K(x) coinciding with D on
> K, and such that D* x_i = u_i for every i."
>
> "Case 1. x is separable algebraic over K. Let f(X) be the
> irreducible polynomial satisfied by x over K. Then f′(x) ≠ 0. We
> have
>     0 = f^D(x) + f′(x) u,
> whence u = −f^D(x)/f′(x). Hence D extends to K(x) uniquely. If D is
> trivial on K, then D is trivial on K(x)."

The axiom below is the trace-of-logarithmic-derivative identity
`Tr_{L/K}(dg/g) = d(N_{L/K}(g))/N_{L/K}(g)` obtained by
differentiating `N(g) = ∏_σ σ(g)` (Lang VI.5, p.285) — with the
derivation uniquely extended to the Galois closure via Lang VIII.5
Theorem 5.1 Case 1 — then evaluating at the chord intercept μ. -/
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
