/-
  Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean

  Trace-of-log-derivative identity. The exported API
  `chord_sum_eq_chord_fiber_product_logDeriv` is now a *theorem* derived
  from the chord-specific theorem
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace`, which in turn
  derives from the **strictly narrower generic axiom**
  `Polynomial.resultant_logDeriv_at_split_specialization`
  (in `AxiomResultantLogDerivAtSplit.lean`) plus chord-cubic-specific
  algebra.

  The chord-specific identity is now a *theorem*: the only axiom in its
  closure is the generic resultant log-derivative formula. The
  chord-cubic plumbing — computing `f_X`, `f_T`, `g_X`, `g_T`, `g_val`
  for `f := chordCubicBiv` and `g := DLineBiv` and matching to
  `logDerivTerm` — is mechanised in this file.

  Reference: Lang, *Algebra* (3rd ed., GTM 211), §VI.5 Theorem 5.1
  (p. 285) + §VIII.5 Theorem 5.1 Case 1 (p. 370). The README links
  the archived snippets for these source statements.
-/
import Divisor.Defs
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomResultantLogDerivAtSplit
import Divisor.BivariateLogDeriv
import Divisor.FunctionFieldZ
import Divisor.Sketch.ChordFiberGeometry

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Helper: pointwise bivariate evaluations of `chordCubicBiv` and
`DLineBiv`

These helper lemmas compute the partial derivatives of the bivariate
chord cubic `f := chordCubicBiv` and the bivariate D-on-line lift
`g := DLineBiv` at a chord-curve point `(x, lam·x + μ)` in terms of
the project's existing scalar functions.

Combined with the generic resultant log-derivative axiom
`Polynomial.resultant_logDeriv_at_split_specialization`, they let us
identify each per-root term in the resultant log-derivative formula
with the project's `logDerivTerm`. -/

/-- For `p : K[X]`, `(p.map C).eval (C x) = C (p.eval x)` (the
"polynomial-as-constant-coefficient pullback then evaluate" identity).
Standard induction over `Polynomial.induction_on'`. -/
private lemma eval_map_C_eval_C
    (p : Polynomial (ZMod E.q)) (x : ZMod E.q) :
    (p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).eval (Polynomial.C x)
      = Polynomial.C (p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, Polynomial.eval_add, hp, hq, Polynomial.eval_add,
        Polynomial.C_add]
  | monomial n c =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.eval_monomial, ← Polynomial.C_pow, ← Polynomial.C_mul]

/-- **Outer X-derivative of the bivariate chord cubic at `(x, μ)`.**

After specialising the inner variable to `μ`, the X-derivative of
`chordCubicBiv` at `x` equals the chord-cone factor
`3x² + A − 2λ·(λx + μ)`. This is the denominator factor in
`logDerivTerm`. -/
private lemma chordCubicBiv_map_derivative_eval
    (lam μ x : ZMod E.q) :
    ((chordCubicBiv E lam).map (Polynomial.evalRingHom μ)).derivative.eval x
      = 3 * x ^ 2 + E.curveA - 2 * lam * (lam * x + μ) := by
  rw [chordCubicBiv_map_evalRingHom]
  unfold Divisor.intersectionPoly
  simp [Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- **Inner T-derivative of the bivariate chord cubic at `(x, μ)`.**

Substituting outer `X = x` and taking the inner derivative, then
evaluating at `T = μ`, gives `-2λx − 2μ = -2·(λx + μ)`. This is the
implicit-function-theorem `f_T` value. -/
private lemma chordCubicBiv_eval_C_derivative_eval
    (lam μ x : ZMod E.q) :
    ((chordCubicBiv E lam).eval (Polynomial.C x)).derivative.eval μ
      = -2 * lam * x - 2 * μ := by
  unfold chordCubicBiv
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.derivative_add, Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_C]
  ring

/-- **D-on-line specialization at intercept `μ`, evaluated at chord
x-coordinate `x`.** Recovers the affine evaluation
`D.eval x (lam·x + μ)` on the chord line `y = lam·x + μ`. -/
private lemma DLineBiv_map_eval_at_root
    (D : CoordRingElt E.q) (lam μ x : ZMod E.q) :
    ((DLineBiv E lam D).map (Polynomial.evalRingHom μ)).eval x
      = D.eval x (lam * x + μ) := by
  rw [DLineBiv_map_evalRingHom]
  unfold CoordRingElt.eval
  simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]

/-- **Outer X-derivative of `DLineBiv` at `(x, μ)`.**

After inner specialisation `T = μ` and outer differentiation in X,
evaluation at `x` gives the chord-line slope correction. -/
private lemma DLineBiv_map_derivative_eval
    (D : CoordRingElt E.q) (lam μ x : ZMod E.q) :
    ((DLineBiv E lam D).map (Polynomial.evalRingHom μ)).derivative.eval x
      = D.a.derivative.eval x
        - D.b.derivative.eval x * (lam * x + μ)
        - lam * D.b.eval x := by
  rw [DLineBiv_map_evalRingHom]
  rw [Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_C]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
             Polynomial.eval_C, Polynomial.eval_X, zero_mul,
             zero_add, add_zero, mul_one]
  ring

/-- **Inner T-derivative of `DLineBiv` at `(x, μ)`.**

Substituting outer `X = x` and taking the inner derivative, then
evaluating at `T = μ`, gives `-D.b.eval x`. This is the
implicit-function-theorem `g_T` value. -/
private lemma DLineBiv_eval_C_derivative_eval
    (D : CoordRingElt E.q) (lam μ x : ZMod E.q) :
    ((DLineBiv E lam D).eval (Polynomial.C x)).derivative.eval μ
      = -D.b.eval x := by
  unfold DLineBiv
  rw [Polynomial.eval_sub]
  rw [eval_map_C_eval_C E D.a x]
  rw [Polynomial.eval_mul]
  rw [eval_map_C_eval_C E D.b x]
  rw [Polynomial.eval_add]
  rw [Polynomial.eval_mul]
  rw [Polynomial.eval_C]
  rw [Polynomial.eval_C]
  rw [Polynomial.eval_X]
  rw [show (Polynomial.C lam : Polynomial (ZMod E.q)) * Polynomial.C x
        = Polynomial.C (lam * x) from (Polynomial.C_mul).symm]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_X]
  simp only [Polynomial.eval_neg, Polynomial.eval_C, zero_mul, zero_sub, zero_add, mul_one]

/-! ## Chord-specific log-derivative identity (theorem)

The narrow project-shaped axiom that used to live here is now a
theorem, derived from the strictly narrower generic axiom
`Polynomial.resultant_logDeriv_at_split_specialization` plus the five
explicit-evaluation lemmas above. -/

/-- **Theorem (was axiom): chord-specific log-derivative identity at the
chord intercept.**

For `D : CoordRingElt E.q`, slope `lam`, and intercept `μ : ZMod E.q`
where the chord cubic `intersectionPoly E lam μ` splits over
`ZMod E.q`, the formal logarithmic derivative of the chord-fiber
product equals the multiset sum of per-chord-root `logDerivTerm`
values evaluated at the chord-line points `(x, λ·x + μ)`.

Proof: apply the generic resultant log-derivative formula
`Polynomial.resultant_logDeriv_at_split_specialization` to
`f := chordCubicBiv E lam` and `g := DLineBiv E lam D`, then identify
each per-root contribution with `logDerivTerm` via direct
chord-cubic-specific algebra (see helper lemmas above).

Reference: Lang, *Algebra* GTM 211, §VI.5 Theorem 5.1 + §VIII.5
Theorem 5.1 Case 1 — specialised through the resultant. -/
theorem chord_fiber_product_logDeriv_eq_logDerivTerm_trace
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
        (fun x => logDerivTerm E D E.curveA lam (x, lam * x + μ))).sum := by
  classical
  -- 1. Unfold `chord_fiber_product` to expose the underlying resultant.
  unfold chord_fiber_product chord_fiber_product_concrete
  -- 2. The roots of the inner-specialised chord cubic coincide with
  --    `(intersectionPoly E lam μ).roots`.
  have hMap_eq :
      (chordCubicBiv E lam).map (Polynomial.evalRingHom μ)
        = intersectionPoly E lam μ :=
    chordCubicBiv_map_evalRingHom E lam μ
  -- 3. Translate the four hypotheses to the generic axiom's form.
  have hSplit' :
      ((chordCubicBiv E lam).map (Polynomial.evalRingHom μ)).Splits := by
    rw [hMap_eq]; exact hSplit
  have hF_ne :
      (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)
        (chordCubicBiv E lam).natDegree (DLineBiv E lam D).natDegree).eval μ
        ≠ 0 := hCfpNe
  have hg_def' : ∀ x ∈ ((chordCubicBiv E lam).map (Polynomial.evalRingHom μ)).roots,
      ((DLineBiv E lam D).map (Polynomial.evalRingHom μ)).eval x ≠ 0 := by
    intro x hx
    rw [DLineBiv_map_eval_at_root]
    rw [hMap_eq] at hx
    exact hRootsDef x hx
  have hf_X_def' : ∀ x ∈ ((chordCubicBiv E lam).map (Polynomial.evalRingHom μ)).roots,
      (((chordCubicBiv E lam).map (Polynomial.evalRingHom μ)).derivative).eval x
        ≠ 0 := by
    intro x hx
    rw [chordCubicBiv_map_derivative_eval]
    rw [hMap_eq] at hx
    exact hChordCone x hx
  -- 4. Apply the generic resultant log-derivative axiom.
  have hAxiom :=
    Polynomial.resultant_logDeriv_at_split_specialization
      (chordCubicBiv E lam) (DLineBiv E lam D) μ
      (chordCubicBiv_monic E lam) hF_ne hSplit' hg_def' hf_X_def'
  rw [hAxiom, hMap_eq]
  -- 5. Match per-root expressions to `logDerivTerm` (`.sum` propagates).
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro x hx
  -- 5a. Compute the five partial-derivative scalar values at `(x, μ)`.
  have hfX := chordCubicBiv_map_derivative_eval E lam μ x
  have hfX' :
      (intersectionPoly E lam μ).derivative.eval x
        = 3 * x ^ 2 + E.curveA - 2 * lam * (lam * x + μ) := by
    rw [← hMap_eq]
    exact hfX
  have hfT := chordCubicBiv_eval_C_derivative_eval E lam μ x
  have hgX := DLineBiv_map_derivative_eval E D lam μ x
  have hgT := DLineBiv_eval_C_derivative_eval E D lam μ x
  have hgV := DLineBiv_map_eval_at_root E D lam μ x
  -- 5b. Side-conditions: all denominators nonzero.
  have hChordCone_x := hChordCone x hx
  have hRootsDef_x := hRootsDef x hx
  -- 5c. Substitute scalar partials, unfold logDerivTerm, and finish via algebra.
  simp only [hfX', hfT, hgX, hgT, hgV]
  unfold logDerivTerm
  -- Goal is now a rational equality in (a, b, a', b', x, lam, μ, A);
  -- both sides share the denominator `(D.eval x (lam*x+μ))·(3x² + A − 2λ·(λx+μ))`,
  -- and the numerators agree as polynomials in x, lam, μ (via `lam*x + μ = y`).
  -- Cross-multiply via `field_simp` and close with `ring`.
  have hden_ne : D.eval x (lam * x + μ) ≠ 0 := hRootsDef_x
  have hcone_ne :
      (3 : ZMod E.q) * x ^ 2 + E.curveA - 2 * lam * (lam * x + μ) ≠ 0 :=
    hChordCone_x
  field_simp
  ring

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
  -- Apply the chord-specific theorem.
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
