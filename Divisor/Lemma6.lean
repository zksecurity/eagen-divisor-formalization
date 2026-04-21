/-
  Divisor/Lemma6.lean

  Phase 3 of the continuation plan (`docs/continuation-plan.md`). Paper's
  Lemma 6 (`~/paper/divisor/sections/ec.tex:557-579`) mechanized as a
  Lean theorem in the chord-sum form:

    Σᵢ logDerivTerm(Aᵢ, λ)
      = -Σ_{Q ∈ zerosFinset E D} β(Q) · L_Q(Q)⁻¹

  where `λ = slopeOf A₀ A₁`, `L_Q = lineThrough A₀ A₁`, A_i range over
  the three chord intersections, and β = betaConstructive E D.

  ## Strategy (Fallback C: scalar log-derivative match as hypothesis)

  The paper's proof proceeds via the function-field norm identity

    N(D)(z) = lc(D)^3 · ∏_k (z − z(Q_k))^(β_k)                    (*)

  as an equality in `F_q[z]` (the function-field norm being the
  determinant of multiplication by D on F_q(E) viewed as a rank-3
  module over F_q(z)). Mechanising (*) requires nontrivial
  function-field infrastructure (resultant computations, Sylvester
  matrix over three sheets, relative trace pairing) that is out of
  scope for Phase 3.

  Our Phase 1a *definition* of `normZ` is already the RHS of (*). What
  (*) provides — and what is the actual algebraic content of Lemma 6 —
  is the identity

    Σᵢ (dD/dz)(Aᵢ) / D(Aᵢ)  =  (normZ)'(μ) / normZ(μ)            (**)

  at the chord intercept μ = zLambda λ A₀. (Equivalently: the
  logarithmic derivatives of D(A₀(z))·D(A₁(z))·D(A₂(z)) and of
  normZ(z) coincide, because they differ by a nonzero constant.)

  Phase 3 takes (**) as a scalar *hypothesis* (paper-faithful
  logarithmic-derivative equality) and DERIVES Lemma 6 in one step
  from Phase 2's partial-fraction expansion
  (`normZ_logDeriv_at_chord_intercept`, which asserts exactly that
  the RHS of (**) equals `-Σ β · L⁻¹`). This turns Lemma 6 into a
  short, pure-algebra consequence of Phase 2.

  Phase 4's integration: the hypothesis (**) is narrower than the
  full Lemma 6 statement but is still function-field content. Phase 4
  either (a) discharges (**) via a new Mathlib-level resultant
  computation, or (b) absorbs (**) as a precondition into the
  narrowed form of `polyG_zero_of_logDerivCheck_identically_zero`.

  No new axioms, no `sorry` / `admit`. This module only needs the
  Phase 2 PFE and its neighbours.
-/
import Divisor.NormZDecomp
import Divisor.BivariateLogDeriv
import Divisor.LogDeriv

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Hypothesis form of Lemma 6's deep content

The paper's Lemma 6 proof uses the function-field norm identity
`N(D)(z) = lc(D)^3 · ∏ (z - z(Q))^β` (a *polynomial equality* in z).
This induces the scalar *logarithmic-derivative* equality

  Σᵢ logDerivTerm(Aᵢ, λ)  =  (normZ)'(μ) / normZ(μ)

at the chord intercept μ = zLambda λ A₀. We encapsulate that
scalar equality as `chordLogDerivMatchesNormZ` below. Phase 4 is
responsible for discharging (or narrowing the axiom scope around)
this hypothesis.
-/

/-- **Scalar log-derivative match.** At a chord (A₀, A₁) with
nonzero normZ(μ), the chord-sum Σᵢ logDerivTerm(Aᵢ) equals the
logarithmic derivative of normZ at the chord intercept
μ = zLambda λ A₀.

This is the algebraic content of paper's Lemma 6 boiled down to a
single scalar equality. Phase 2's
`normZ_logDeriv_at_chord_intercept` gives the RHS's partial-fraction
decomposition; combining the two yields Lemma 6 (see
`lemma6_chord_residue` below). -/
def chordLogDerivMatchesNormZ
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  let μ := zLambda E lam A₀
  (logDerivTerm E D E.curveA lam A₀
    + logDerivTerm E D E.curveA lam A₁
    + logDerivTerm E D E.curveA lam
        (lam ^ 2 - A₀.1 - A₁.1,
         lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
    * (normZ E lam D).eval μ
  = eval μ (derivative (normZ E lam D))

/-! ## Lemma 6, mechanized form

Under the scalar log-derivative match (above) and with normZ(μ)
nonzero (equivalently: every `L_Q(Q) ≠ 0`), Lemma 6 states

  Σᵢ logDerivTerm(Aᵢ, λ) = -Σ_Q β(Q) · L_Q(Q)⁻¹

with β = betaConstructive E D and the sum on the RHS indexed by
Q ∈ zerosFinset E D.
-/

/-- **Lemma 6 (chord residue identity).** The chord-sum
`Σᵢ logDerivTerm(Aᵢ, λ)` equals the partial-fraction expansion
of normZ's logarithmic derivative at the chord intercept, in the
line-evaluation basis.

**Proof**: the hypothesis `hMatch` is the scalar log-derivative
equality `Σᵢ logDerivTerm(Aᵢ) · normZ(μ) = (normZ)'(μ)`. Phase 2's
`normZ_logDeriv_at_chord_intercept` expresses the RHS (normZ)'(μ)
as `-normZ(μ) · Σ β · L⁻¹`. Dividing through by `normZ(μ) ≠ 0`
gives Lemma 6.

**Scope**: narrows the axiom
`polyG_zero_of_logDerivCheck_identically_zero` to the case where
the scalar log-derivative hypothesis holds. Phase 4 discharges (or
absorbs) this precondition. -/
theorem lemma6_chord_residue
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D A₀ A₁) :
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
           (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
             ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
             + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
    = -∑ Q ∈ zerosFinset E D,
        (betaConstructive E D Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set μ := zLambda E lam A₀
  -- Phase 2 PFE: eval μ (deriv normZ) = -normZ(μ) · Σ β · L⁻¹.
  have hPFE := normZ_logDeriv_at_chord_intercept E D A₀ A₁ hQline
  -- hPFE: eval μ (deriv (normZ E lam D)) =
  --    -(normZ(μ) · Σ β · L⁻¹)
  -- Abbreviations matching hMatch.
  set A₂ : ZMod E.q × ZMod E.q :=
    (lam ^ 2 - A₀.1 - A₁.1,
     lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam A₂
  set N : ZMod E.q := (normZ E lam D).eval μ
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D))
  set S : ZMod E.q :=
    ∑ Q ∈ zerosFinset E D,
      (betaConstructive E D Q : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹
  -- hPFE in abbreviated form: Nd = -(N · S).
  change Nd = -(N * S) at hPFE
  -- hMatch in abbreviated form: LT · N = Nd.
  change LT * N = Nd at hMatch
  -- Combine: LT · N = -(N · S), so LT = -S (given N ≠ 0).
  have hNne : N ≠ 0 := hNormZne
  -- LT * N = -(N * S)  ⇒  LT * N = N * (-S)  ⇒  LT = -S.
  have hEq : LT * N = N * (-S) := by rw [hMatch, hPFE]; ring
  have hDiv : LT = -S := by
    have hEq' : LT * N = (-S) * N := by rw [hEq]; ring
    exact mul_right_cancel₀ hNne hEq'
  -- Conclude.
  show LT = -S
  exact hDiv

/-! ## Corollary: the form consumed by ResidueIdentity.lean:644

The Phase 3 target (the theorem `polyG_zero_of_Lemma6_and_logDerivCheck_zero`
at `Divisor/ResidueIdentity.lean:644`) expects the chord-sum hypothesis
exactly in the form above. `lemma6_chord_residue` produces it directly. -/

/-- **Convenience corollary.** The form of Lemma 6 that matches the
Phase 3 bridge theorem `polyG_zero_of_Lemma6_and_logDerivCheck_zero`
verbatim. -/
theorem lemma6_as_bridge_hypothesis
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D A₀ A₁) :
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
              ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
    = -∑ Q ∈ zerosFinset E D,
        (betaConstructive E D Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ :=
  lemma6_chord_residue E D A₀ A₁ hQline hNormZne hMatch

/-! ## Fin-indexed form for use with the bridge theorem

The `polyG_zero_of_Lemma6_and_logDerivCheck_zero` bridge at
`Divisor/ResidueIdentity.lean:644` indexes its `beta` and `Q` arrays
by `Fin d`, not by the `zerosFinset E D` Finset. The next
adaptation expresses Lemma 6 in that form when the Fin-indexed
family enumerates `zerosFinset E D`. -/

/-- **Fin-indexed form of Lemma 6.** When `Q : Fin d → ...`
enumerates distinct affine E-zeros of D with multiplicities
`beta : Fin d → ℕ` matching `betaConstructive`, the chord-sum
`Σᵢ logDerivTerm(Aᵢ, λ)` equals the negative Fin-sum
`-Σ_{k'} beta(k') · L_Q(Q k')⁻¹`.

Hypotheses:
* `hQinj`: Q is injective.
* `hQzeros`: every Q k' is an affine E-zero of D.
* `hQcov`: every affine E-zero of D equals some Q k'.
* `hβMatch`: `beta k' = betaConstructive E D (Q k')`. -/
theorem lemma6_fin_indexed
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D A₀ A₁)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ℕ)
    (hQinj : Function.Injective Q)
    (hQzeros : ∀ k' : Fin d,
       Q k' ∈ E.points ∧ D.eval (Q k').1 (Q k').2 = 0)
    (hQcov : ∀ Q' ∈ E.points, D.eval Q'.1 Q'.2 = 0 →
       ∃ k' : Fin d, Q k' = Q')
    (hβMatch : ∀ k' : Fin d, beta k' = betaConstructive E D (Q k')) :
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
              ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
    = -∑ k' : Fin d, (beta k' : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (Q k').1 (Q k').2)⁻¹ := by
  classical
  rw [lemma6_chord_residue E D A₀ A₁ hQline hNormZne hMatch]
  -- Reindex the Finset sum to the Fin sum.
  congr 1
  -- Direction: show Fin sum = Finset sum. Use Finset.sum_bij with forward Q : Fin d → zerosFinset.
  have hQ_mem : ∀ k' : Fin d, Q k' ∈ zerosFinset E D := by
    intro k'
    unfold zerosFinset zeros
    rw [Finset.mem_filter]
    exact hQzeros k'
  symm
  apply Finset.sum_bij (fun k' (_ : k' ∈ (Finset.univ : Finset (Fin d))) => Q k')
  · intro k' _
    exact hQ_mem k'
  · intro i _ j _ h
    exact hQinj h
  · intro Q' hQ'
    have hQ'mem : Q' ∈ E.points ∧ D.eval Q'.1 Q'.2 = 0 := by
      unfold zerosFinset zeros at hQ'
      exact Finset.mem_filter.mp hQ'
    obtain ⟨k', hk'⟩ := hQcov Q' hQ'mem.1 hQ'mem.2
    exact ⟨k', Finset.mem_univ k', hk'⟩
  · intro k' _
    rw [hβMatch k']

/-! ## Alternative reduction: from a polynomial product-norm identity

The `chordLogDerivMatchesNormZ` hypothesis encodes the scalar
log-derivative equality at a single chord. It is implied by (but
does not imply) the stronger polynomial identity

  D.eval A₀(z) · D.eval A₁(z) · D.eval A₂(z) = C · normZ(z)

where A_i(z) are the chord-point coordinates as symbolic functions
of z, and C is a nonzero constant. Directly mechanising the
polynomial form requires function-field infrastructure that Phase 3
defers, but we provide below a direct scalar reduction: given the
aggregate identity form (from `chord_aggregate_identity`), Lemma 6
reduces to a polynomial equality between the aggregate RHS and
`(normZ)'(μ) · chordDenomProd / normZ(μ)`.

The following helper simply restates `chordLogDerivMatchesNormZ`
as an equivalent form with the product moved to the other side
(useful when building the hypothesis from downstream proofs). -/

/-- Equivalent form of `chordLogDerivMatchesNormZ`: when
`normZ(μ) ≠ 0`, the hypothesis is equivalent to
`Σᵢ logDerivTerm(Aᵢ) = eval μ (deriv normZ) / normZ(μ)`. -/
theorem chordLogDerivMatchesNormZ_iff_ratio
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    chordLogDerivMatchesNormZ E D A₀ A₁ ↔
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
               ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
               + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
      = eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D))
        / (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
            (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) := by
  unfold chordLogDerivMatchesNormZ
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set μ := zLambda E lam A₀
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
  set N : ZMod E.q := (normZ E lam D).eval μ
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D))
  have hNne : N ≠ 0 := hNormZne
  show LT * N = Nd ↔ LT = Nd / N
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp

/-! ## Alternate interface: `chordLogDerivMatchesNormZ` from a polynomial identity

The following theorem packages the chord-log-deriv match in a form
that a Phase-4 proof could discharge via a polynomial identity: if
`normZ(z) · chordDenomProd(z) = (normZ)'(z) · [some polynomial in z]`
holds, the scalar form follows by evaluation at μ. (Not used
internally; exported for downstream callers.) -/

/-- If the chord aggregate identity's LHS ratio matches normZ's
log-derivative ratio, the chord-log-deriv match holds. A trivial
encapsulation; the nontrivial content lives in the hypothesis. -/
theorem chordLogDerivMatchesNormZ_of_ratio_eq
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hRatio : logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
               ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
               + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
      = eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D))
        / (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
            (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)) :
    chordLogDerivMatchesNormZ E D A₀ A₁ :=
  (chordLogDerivMatchesNormZ_iff_ratio E D A₀ A₁ hNormZne).mpr hRatio

end Divisor
