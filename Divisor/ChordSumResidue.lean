/-
  Divisor/ChordSumResidue.lean

  Paper's `\ref{lem:log-derivative}` (`ec.tex`) in chord-sum form:

    Σᵢ logDerivTerm(Aᵢ, λ)
      = -Σ_{Q ∈ zerosFinset E D} β_fun(Q) · L_Q(Q)⁻¹

  where `λ = slopeOf A₀ A₁`, `L_Q = lineThrough A₀ A₁`, A_i range over
  the three chord intersections, and β_fun is an arbitrary
  multiplicity function (the existential from
  `CoordRingElt.exists_divisor_multiplicity` / `has_principal_divisor`).

  The function-field norm identity
    N(D)(z) = lc(D)^3 · ∏_k (z − z(Q_k))^(β_k)
  induces the scalar log-derivative equality
    Σᵢ (dD/dz)(Aᵢ) / D(Aᵢ)  =  (normZ)'(μ) / normZ(μ)
  at the chord intercept μ = zLambda λ A₀. Combined with the
  partial-fraction expansion `normZ_logDeriv_at_chord_intercept`
  (which gives the RHS = `-Σ β_fun · L⁻¹`), this yields
  `\ref{lem:log-derivative}`. The scalar log-derivative equality is
  taken here as a hypothesis (`chordLogDerivMatchesNormZ`).
-/
import Divisor.NormZDecomp

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Hypothesis form of `\ref{lem:log-derivative}`'s deep content -/

/-- **Scalar log-derivative match.** Parameterised on β_fun. At a
chord (A₀, A₁) with nonzero `normZ E λ D β_fun (μ)`, the chord-sum
Σᵢ logDerivTerm(Aᵢ) equals the logarithmic derivative of
`normZ E λ D β_fun` at the chord intercept μ = zLambda λ A₀. -/
def chordLogDerivMatchesNormZ
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  let μ := zLambda E lam A₀
  (logDerivTerm E D E.curveA lam A₀
    + logDerivTerm E D E.curveA lam A₁
    + logDerivTerm E D E.curveA lam
        (lam ^ 2 - A₀.1 - A₁.1,
         lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
    * (normZ E lam D β_fun).eval μ
  = eval μ (derivative (normZ E lam D β_fun))

/-! ## `\ref{lem:log-derivative}`, mechanized form -/

/-- **`\ref{lem:log-derivative}` (chord residue identity).** -/
theorem lemma6_chord_residue
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D β_fun A₀ A₁) :
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
           (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
             ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
             + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
    = -∑ Q ∈ zerosFinset E D,
        (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set μ := zLambda E lam A₀
  have hPFE := normZ_logDeriv_at_chord_intercept E D β_fun A₀ A₁ hQline
  set A₂ : ZMod E.q × ZMod E.q :=
    (lam ^ 2 - A₀.1 - A₁.1,
     lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
  set LT : ZMod E.q :=
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam A₂
  set N : ZMod E.q := (normZ E lam D β_fun).eval μ
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D β_fun))
  set S : ZMod E.q :=
    ∑ Q ∈ zerosFinset E D,
      (β_fun Q : ZMod E.q) *
        ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹
  change Nd = -(N * S) at hPFE
  change LT * N = Nd at hMatch
  have hNne : N ≠ 0 := hNormZne
  have hEq : LT * N = N * (-S) := by rw [hMatch, hPFE]; ring
  have hDiv : LT = -S := by
    have hEq' : LT * N = (-S) * N := by rw [hEq]; ring
    exact mul_right_cancel₀ hNne hEq'
  show LT = -S
  exact hDiv

/-! ## Corollary: the form consumed by ResidueIdentity.lean -/

/-- **Convenience corollary.** -/
theorem lemma6_as_bridge_hypothesis
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D β_fun A₀ A₁) :
    logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
      + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
              ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
    = -∑ Q ∈ zerosFinset E D,
        (β_fun Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹ :=
  lemma6_chord_residue E D β_fun A₀ A₁ hQline hNormZne hMatch

/-! ## Fin-indexed form for use with the bridge theorem -/

/-- **Fin-indexed form of `\ref{lem:log-derivative}`.** -/
theorem lemma6_fin_indexed
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hMatch : chordLogDerivMatchesNormZ E D β_fun A₀ A₁)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ℕ)
    (hQinj : Function.Injective Q)
    (hQzeros : ∀ k' : Fin d,
       Q k' ∈ E.points ∧ D.eval (Q k').1 (Q k').2 = 0)
    (hQcov : ∀ Q' ∈ E.points, D.eval Q'.1 Q'.2 = 0 →
       ∃ k' : Fin d, Q k' = Q')
    (hβMatch : ∀ k' : Fin d, beta k' = β_fun (Q k')) :
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
  rw [lemma6_chord_residue E D β_fun A₀ A₁ hQline hNormZne hMatch]
  congr 1
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

/-! ## Auxiliary equivalences -/

/-- Equivalent form of `chordLogDerivMatchesNormZ` as a ratio. -/
theorem chordLogDerivMatchesNormZ_iff_ratio
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    chordLogDerivMatchesNormZ E D β_fun A₀ A₁ ↔
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
               ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
               + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
      = eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun))
        / (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
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
  set N : ZMod E.q := (normZ E lam D β_fun).eval μ
  set Nd : ZMod E.q := eval μ (derivative (normZ E lam D β_fun))
  have hNne : N ≠ 0 := hNormZne
  show LT * N = Nd ↔ LT = Nd / N
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp

/-- If the chord aggregate identity's LHS ratio matches normZ's
log-derivative ratio, the chord-log-deriv match holds. -/
theorem chordLogDerivMatchesNormZ_of_ratio_eq
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNormZne : (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
      (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0)
    (hRatio : logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
               ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
               + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1))
      = eval (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          (derivative (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun))
        / (normZ E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D β_fun).eval
            (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)) :
    chordLogDerivMatchesNormZ E D β_fun A₀ A₁ :=
  (chordLogDerivMatchesNormZ_iff_ratio E D β_fun A₀ A₁ hNormZne).mpr hRatio

end Divisor
