/-
  Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean

  Trace-of-log-derivative identity. The exported API
  `chord_sum_eq_chord_fiber_product_logDeriv` is now a *theorem* derived
  from a strictly narrower axiom
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` plus the
  chord-cubic factorisation lemmas in `Divisor/Sketch/ChordFiberGeometry`.

  The narrower axiom is the textbook trace-of-log-derivative formula
  applied to the chord projection: at any chord intercept `μ` where the
  chord cubic splits, the log-derivative of the chord-fiber product
  (= function-field norm of `D`) equals the multiset sum of the
  per-chord-root `logDerivTerm`'s. This is the citable Lang fact.

  The exported `chord_sum_eq_chord_fiber_product_logDeriv` is the
  specialisation to the chord intercept `μ = zLambda lam A₀`, where the
  three chord roots are exactly the chord-fiber points
  `A₀, A₁, A₂`. The conversion is pure plumbing: chord-cubic
  factorisation (`Sketch.intersectionPoly_factor_at_zLambda`,
  `Sketch.intersectionPoly_splits_at_zLambda`) plus the slope identity.

  Reference: Lang, *Algebra* (3rd ed., GTM 211), §VI.5 Theorem 5.1
  (p. 285) + §VIII.5 Theorem 5.1 Case 1 (p. 370). See
  `axioms/chord_sum_eq_chord_fiber_product_logDeriv.md`.
-/
import Divisor.Defs
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.BivariateLogDeriv
import Divisor.FunctionFieldZ
import Divisor.Sketch.ChordFiberGeometry

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Narrower trace-of-log-derivative axiom

This is the Lang-citable form of the chord-fiber log-derivative
identity, abstracted over the chord intercept `μ`.

For `D : CoordRingElt E.q`, `lam : ZMod E.q`, and any chord intercept
`μ : ZMod E.q` at which the chord cubic `intersectionPoly E lam μ`
splits over `ZMod E.q`, the formal logarithmic derivative of
`chord_fiber_product E lam D` (the function-field norm of `D`,
viewed as a polynomial in `μ`) equals the multiset sum of per-root
`logDerivTerm`'s, indexed by `(intersectionPoly E lam μ).roots` and
evaluated at the chord-line points `(x, λ·x + μ)`.

The corresponding textbook identity is Lang's
`Tr_{L/K}(dα/α) = d N_{L/K}(α) / N_{L/K}(α)`
(L = function field of E over K = base specialised at μ). The trace
is the multiset sum over the chord roots; the norm is the chord-fiber
product. The right-hand-side per-root term has been pre-collapsed to
the project's `logDerivTerm` via the curve-residual identity (see
`logDerivTerm_denom_cleared_pointwise`). -/
axiom chord_fiber_product_logDeriv_eq_logDerivTerm_trace
    (E : ECSetup) (D : CoordRingElt E.q) (lam μ : ZMod E.q)
    (hSplit : (intersectionPoly E lam μ).Splits)
    (hCfpNe : (chord_fiber_product E lam D).eval μ ≠ 0)
    (hRootsDef : ∀ x ∈ (intersectionPoly E lam μ).roots,
        D.eval x (lam * x + μ) ≠ 0)
    (hChordCone : ∀ x ∈ (intersectionPoly E lam μ).roots,
        3 * x ^ 2 + E.curveA - 2 * lam * (lam * x + μ) ≠ 0) :
    eval μ (derivative (chord_fiber_product E lam D))
      / (chord_fiber_product E lam D).eval μ
    = ((intersectionPoly E lam μ).roots.map
        (fun x => logDerivTerm E D E.curveA lam (x, lam * x + μ))).sum

/-! ## Exported API: specialisation to the chord intercept

`chord_sum_eq_chord_fiber_product_logDeriv` is the chord-specific form
of the trace identity: under the project's per-chord-point side
conditions (`hA*def`, `hDen`), the sum
`logDerivTerm(A₀) + logDerivTerm(A₁) + logDerivTerm(A₂)` equals the
log-derivative of the chord-fiber product at `μ = zLambda lam A₀`.

Derived from `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` by
chord-cubic factorisation: the three roots of `intersectionPoly` at
the chord intercept are exactly `{A₀.1, A₁.1, x₂}`, and the slope
identity `λ·(A₁.1 − A₀.1) = A₁.2 − A₀.2` makes the per-root
`logDerivTerm` evaluations land at `A₀, A₁, A₂` respectively. -/
theorem chord_sum_eq_chord_fiber_product_logDeriv
    (E : ECSetup) (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0))
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
      / (chord_fiber_product E lam D).eval μ := by
  intro lam μ
  set x₂ : ZMod E.q := lam ^ 2 - A₀.1 - A₁.1 with hx₂
  set y₂ : ZMod E.q := lam * x₂ + (A₀.2 - lam * A₀.1) with hy₂
  -- Slope identity: λ · (A₁.1 − A₀.1) = A₁.2 − A₀.2.
  have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    show slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2
    have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
    rw [slopeOf]
    field_simp
  -- y-coordinate identities at the three chord roots.
  have h_y_A₀ : lam * A₀.1 + μ = A₀.2 := by
    show lam * A₀.1 + zLambda E lam A₀ = A₀.2
    unfold zLambda; ring
  have h_y_A₁ : lam * A₁.1 + μ = A₁.2 := by
    show lam * A₁.1 + zLambda E lam A₀ = A₁.2
    unfold zLambda
    linear_combination hSlope
  have h_y_x₂ : lam * x₂ + μ = y₂ := by
    show lam * x₂ + zLambda E lam A₀ = y₂
    unfold zLambda
    show _ = lam * x₂ + (A₀.2 - lam * A₀.1); ring
  -- Roots of `intersectionPoly E lam μ` form the multiset {A₀.1, A₁.1, x₂}.
  have hFact := Sketch.intersectionPoly_factor_at_zLambda E A₀ A₁ hA₀ hA₁ hNV
  have h₁_ne : (Polynomial.X - Polynomial.C A₀.1) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h₂_ne : (Polynomial.X - Polynomial.C A₁.1) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have h₃_ne : (Polynomial.X - Polynomial.C x₂) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have hProd_ne :
      (Polynomial.X - Polynomial.C A₀.1) * (Polynomial.X - Polynomial.C A₁.1) ≠ 0 :=
    mul_ne_zero h₁_ne h₂_ne
  have hRoots : (intersectionPoly E lam μ).roots = {A₀.1, A₁.1, x₂} := by
    rw [hFact, Polynomial.roots_mul (mul_ne_zero hProd_ne h₃_ne),
        Polynomial.roots_mul hProd_ne,
        Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C,
        Polynomial.roots_X_sub_C]
    rfl
  -- Splits.
  have hSplit := Sketch.intersectionPoly_splits_at_zLambda E A₀ A₁ hA₀ hA₁ hNV
  -- hRootsDef.
  have hRootsDef : ∀ x ∈ (intersectionPoly E lam μ).roots,
      D.eval x (lam * x + μ) ≠ 0 := by
    rw [hRoots]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
               Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [h_y_A₀]; exact hA₀def
    · rw [h_y_A₁]; exact hA₁def
    · rw [h_y_x₂]; exact hA₂def
  -- hChordCone.
  have hChordCone : ∀ x ∈ (intersectionPoly E lam μ).roots,
      3 * x ^ 2 + E.curveA - 2 * lam * (lam * x + μ) ≠ 0 := by
    rw [hRoots]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
               Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rw [h_y_A₀]; exact hDen A₀ (Or.inl rfl)
    · rw [h_y_A₁]; exact hDen A₁ (Or.inr (Or.inl rfl))
    · rw [h_y_x₂]; exact hDen (x₂, y₂) (Or.inr (Or.inr rfl))
  -- Apply the narrow axiom.
  have hTrace := chord_fiber_product_logDeriv_eq_logDerivTerm_trace E D lam μ
                  hSplit hChordNorm hRootsDef hChordCone
  rw [hTrace, hRoots]
  -- Compute the multiset .map .sum.
  show _ = (((A₀.1 ::ₘ A₁.1 ::ₘ {x₂}).map
              (fun x => logDerivTerm E D E.curveA lam (x, lam * x + μ))).sum : ZMod E.q)
  simp only [Multiset.map_cons, Multiset.map_singleton,
             Multiset.sum_cons, Multiset.sum_singleton]
  rw [h_y_A₀, h_y_A₁, h_y_x₂]
  ring

end Divisor
