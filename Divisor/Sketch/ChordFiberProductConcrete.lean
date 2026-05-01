/-
  Divisor/Sketch/ChordFiberProductConcrete.lean

  PROTOTYPE — concrete candidate for `chord_fiber_product`.

  The current `chord_fiber_product E lam D : (ZMod E.q)[X]` is opaque
  (declared as `noncomputable opaque` in
  `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`) and
  pinned only via two axioms:

    chord_fiber_product_eq_normZ_under_split  -- proportionality to normZ
    chord_fiber_product_bar_eq_geom_prod      -- bar-level factored form

  plus a third axiom for the log-derivative identity
  (`chord_sum_eq_chord_fiber_product_logDeriv`).

  This file provides a **concrete candidate** built from `mathlib`'s
  `Polynomial.resultant`, restated as the resultant in the chord
  x-variable of the chord cubic and the D-on-line polynomial. Each of
  the four downstream obligations is restated against the concrete
  candidate as a `theorem … := by sorry`. The accompanying note
  `docs/chord-fiber-product-concrete-sketch.md` categorises each sorry
  as plumbing or genuine mathematics.

  No existing source file is touched; this prototype lives in its own
  `Divisor.Sketch` namespace and depends only on `Divisor.Defs`,
  `Divisor.SlopeDist`, `Divisor.FunctionFieldZ`, `Divisor.GeomBase`,
  `Divisor.GeomLocalOrder`, `Divisor.LogDeriv`, and mathlib's
  `Polynomial.resultant` API.
-/
import Divisor.Defs
import Divisor.SlopeDist
import Divisor.FunctionFieldZ
import Divisor.GeomBase
import Divisor.GeomLocalOrder
import Divisor.LogDeriv
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open Polynomial

namespace Divisor.Sketch

variable (E : ECSetup)

/-! ## Bivariate setup

We work in `(ZMod E.q)[Z][X]` where:
* outer `Polynomial.X` (in `(ZMod E.q)[Z][X]`) = chord x-variable;
* inner `Polynomial.X` (in `(ZMod E.q)[Z]`) = chord intercept `Z = μ`.

The chord cubic over the inner `Z`-ring:
  `f(X, Z) = X³ − λ² X² + (A − 2λZ) X + (B − Z²)`

The D-on-line lift:
  `g(X, Z) = D.a(X) − D.b(X) (λX + Z)`

The candidate chord-fiber product is `Res_X(f, g) ∈ (ZMod E.q)[Z]`,
which reads as a polynomial in the chord-intercept `μ`. -/

/-- The chord cubic `X³ − λ² X² + (A − 2λZ) X + (B − Z²)` in the bivariate
ring `(ZMod E.q)[Z][X]`. The outer `X` is the chord x-variable; the inner
`Polynomial.X` is the chord intercept `Z`. -/
noncomputable def chordCubicBiv (lam : ZMod E.q) :
    Polynomial (Polynomial (ZMod E.q)) :=
  Polynomial.X ^ 3
    - Polynomial.C (Polynomial.C (lam ^ 2)) * Polynomial.X ^ 2
    + Polynomial.C (Polynomial.C E.curveA - Polynomial.C (2 * lam) * Polynomial.X)
        * Polynomial.X
    + Polynomial.C (Polynomial.C E.curveB - Polynomial.X ^ 2)

/-- The D-on-line polynomial `D.a(X) − D.b(X) · (λX + Z)` in
`(ZMod E.q)[Z][X]`. -/
noncomputable def DLineBiv (lam : ZMod E.q) (D : CoordRingElt E.q) :
    Polynomial (Polynomial (ZMod E.q)) :=
  D.a.map Polynomial.C
    - D.b.map Polynomial.C *
        (Polynomial.C (Polynomial.C lam) * Polynomial.X
          + Polynomial.C Polynomial.X)

/-- **Concrete chord-fiber-product candidate.** The X-resultant of the
chord cubic and the D-on-line lift, viewed as a polynomial in the
chord-intercept variable `μ`. -/
noncomputable def chord_fiber_product_concrete
    (lam : ZMod E.q) (D : CoordRingElt E.q) : Polynomial (ZMod E.q) :=
  Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)

/-! ## Obligations against the concrete candidate

Each `theorem` below mirrors a downstream consumer of the opaque
`chord_fiber_product`. The proofs are stubbed with `sorry`; the
accompanying doc note categorises them. -/

/-! ### Map of bivariate polynomials under `evalRingHom μ` -/

/-- The composition `(evalRingHom μ) ∘ C` is the identity on the inner
ring. -/
private lemma evalRingHom_comp_C_eq_id (μ : ZMod E.q) :
    (Polynomial.evalRingHom μ).comp (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))
      = RingHom.id (ZMod E.q) := by
  ext r
  simp [Polynomial.coe_evalRingHom]

/-- `(p.map C).map (evalRingHom μ) = p` for any base-field polynomial `p`. -/
private lemma mapC_map_evalRingHom (μ : ZMod E.q) (p : Polynomial (ZMod E.q)) :
    (p.map (Polynomial.C : ZMod E.q →+* Polynomial (ZMod E.q))).map
        (Polynomial.evalRingHom μ) = p := by
  rw [Polynomial.map_map, evalRingHom_comp_C_eq_id, Polynomial.map_id]

/-- Specialising `chordCubicBiv` at `Z = μ` recovers the project's
`intersectionPoly`. -/
lemma chordCubicBiv_map_evalRingHom (lam μ : ZMod E.q) :
    (chordCubicBiv E lam).map (Polynomial.evalRingHom μ)
      = Divisor.intersectionPoly E lam μ := by
  unfold chordCubicBiv Divisor.intersectionPoly
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C]
  simp [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]

/-- Specialising `DLineBiv` at `Z = μ` recovers the rational
"D evaluated on the chord line `y = λx + μ`" polynomial. -/
lemma DLineBiv_map_evalRingHom (lam μ : ZMod E.q) (D : CoordRingElt E.q) :
    (DLineBiv E lam D).map (Polynomial.evalRingHom μ)
      = D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ) := by
  unfold DLineBiv
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add,
             Polynomial.map_C, Polynomial.map_X,
             mapC_map_evalRingHom, Polynomial.coe_evalRingHom,
             Polynomial.eval_C, Polynomial.eval_X]

/-- Pointwise specialisation: evaluating `chord_fiber_product_concrete`
at a base-field intercept `μ ∈ ZMod E.q` reduces to the resultant of the
chord cubic at `μ` (which is `intersectionPoly E lam μ`) against the
D-on-line polynomial at `μ`.

*Plumbing*: instance of `Polynomial.resultant_map_map` for the evaluation
hom `Polynomial.X ↦ μ`, plus normalisation of the bivariate `chordCubicBiv`
and `DLineBiv` under that homomorphism. The natDegrees are kept as the
*bivariate* natDegrees (rather than the post-specialisation natDegrees,
which would generally differ when the leading coefficient happens to vanish
at `μ`). -/
theorem chord_fiber_product_concrete_eval (lam μ : ZMod E.q)
    (D : CoordRingElt E.q) :
    (chord_fiber_product_concrete E lam D).eval μ
      = Polynomial.resultant (Divisor.intersectionPoly E lam μ)
          (D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ))
          (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree := by
  unfold chord_fiber_product_concrete
  rw [show ((Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D)).eval μ
        = (Polynomial.evalRingHom μ)
            (Polynomial.resultant (chordCubicBiv E lam) (DLineBiv E lam D))) by
        rw [Polynomial.coe_evalRingHom]]
  have hMap := Polynomial.resultant_map_map (φ := Polynomial.evalRingHom μ)
    (f := chordCubicBiv E lam) (g := DLineBiv E lam D)
    (m := (chordCubicBiv E lam).natDegree) (n := (DLineBiv E lam D).natDegree)
  rw [← hMap, chordCubicBiv_map_evalRingHom E lam μ,
      DLineBiv_map_evalRingHom E lam μ D]

/-- The chord cubic `intersectionPoly` is monic of degree 3. -/
private lemma intersectionPoly_natDegree (lam μ : ZMod E.q) :
    (Divisor.intersectionPoly E lam μ).natDegree = 3 := by
  refine le_antisymm (Divisor.natDegree_intersectionPoly_le E lam μ) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  show (Divisor.intersectionPoly E lam μ).coeff 3 ≠ 0
  unfold Divisor.intersectionPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
             Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
             Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

/-- The chord cubic `intersectionPoly` is monic. -/
private lemma intersectionPoly_leadingCoeff (lam μ : ZMod E.q) :
    (Divisor.intersectionPoly E lam μ).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff, intersectionPoly_natDegree]
  unfold Divisor.intersectionPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
             Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
             Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num

/-- The bivariate chord cubic also has natDegree 3. -/
private lemma chordCubicBiv_natDegree (lam : ZMod E.q) :
    (chordCubicBiv E lam).natDegree = 3 := by
  -- Same coefficient inspection over the inner ring `(ZMod E.q)[X]`.
  refine le_antisymm ?_ ?_
  · -- natDegree ≤ 3
    unfold chordCubicBiv
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact (Polynomial.natDegree_X_pow_le 3)
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (Polynomial.natDegree_X_pow_le 2 |>.trans (by omega))
      · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        exact Polynomial.natDegree_X_le.trans (by omega)
    · exact (Polynomial.natDegree_C _).le.trans (by omega)
  · -- natDegree ≥ 3 via coeff at 3 = 1
    refine Polynomial.le_natDegree_of_ne_zero ?_
    show (chordCubicBiv E lam).coeff 3 ≠ 0
    unfold chordCubicBiv
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
               Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
               Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num

/-- Specialising `DLineBiv` cannot raise the natDegree (mapping a polynomial
through a `RingHom` is degree-non-increasing). -/
private lemma DLine_specialized_natDegree_le (lam μ : ZMod E.q)
    (D : CoordRingElt E.q) :
    (D.a - D.b * (Polynomial.C lam * Polynomial.X + Polynomial.C μ)).natDegree
      ≤ (DLineBiv E lam D).natDegree := by
  rw [← DLineBiv_map_evalRingHom E lam μ D]
  exact Polynomial.natDegree_map_le

/-- Resultant-as-product: when the chord cubic at `μ` splits, the
specialised resultant equals the product of `D`-on-line evaluations at
each chord root.

*Plumbing*: direct call to mathlib's `Polynomial.resultant_eq_prod_eval`
on `intersectionPoly E lam μ` (monic of degree 3). -/
theorem chord_fiber_product_concrete_eval_eq_prod_split
    (lam μ : ZMod E.q) (D : CoordRingElt E.q)
    (hSplit : (Divisor.intersectionPoly E lam μ).Splits) :
    (chord_fiber_product_concrete E lam D).eval μ
      = ((Divisor.intersectionPoly E lam μ).roots.map
          (fun x => D.eval x (lam * x + μ))).prod := by
  rw [chord_fiber_product_concrete_eval E lam μ D]
  -- Align the chord cubic's natDegree with intersectionPoly's.
  rw [show (chordCubicBiv E lam).natDegree = (Divisor.intersectionPoly E lam μ).natDegree by
        rw [chordCubicBiv_natDegree, intersectionPoly_natDegree]]
  -- Apply mathlib's resultant_eq_prod_eval; the leading coefficient is 1.
  rw [Polynomial.resultant_eq_prod_eval _ _ _
        (DLine_specialized_natDegree_le E lam μ D) hSplit,
      intersectionPoly_leadingCoeff, one_pow, one_mul]
  -- The `g.eval x` simplifies to the chord-line evaluation.
  congr 1
  refine Multiset.map_congr rfl ?_
  intro x _
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, CoordRingElt.eval]

/-- Bar-level evaluation specialisation. Same as above but over `Fqbar E`,
where the chord cubic always splits (algebraically closed). -/
theorem chord_fiber_product_concrete_bar_eval_eq_prod
    (lam : ZMod E.q) (D : CoordRingElt E.q) (μ : Fqbar E) :
    Polynomial.eval μ
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D))
      =
        ((Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
            (Divisor.intersectionPoly E lam (0 : ZMod E.q)) -- placeholder,
            -- conceptually: chord cubic at μ — but μ ∈ Fqbar so we
            -- need a slightly different specialisation route via
            -- coefficient base-change first.
            ).roots.map
          (fun _ => (1 : Fqbar E))).prod := by
  sorry

/-- **Non-vanishing.** The candidate is nonzero whenever `D` is.

*Math (medium)*: a polynomial in `μ` is nonzero iff some specialisation is.
By Hasse-Weil + finiteness of `D`'s zero locus on `E`, there exists a
rational `μ` (after extending to `Fqbar` if necessary) such that the
chord cubic at `μ` splits with three distinct roots, none of which is
killed by `D` on the corresponding line. The resultant at that `μ` is then
a nonzero product, so the polynomial is nonzero. -/
theorem chord_fiber_product_concrete_ne_zero
    (lam : ZMod E.q) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    chord_fiber_product_concrete E lam D ≠ 0 := by
  sorry

/-- **Bar-level factored form** (replacement of
`chord_fiber_product_bar_eq_geom_prod`).

*Math (deepest)*: combine `bar_eval_eq_prod` (resultant ↦ ∏ chord-root
evaluations) with the geometric divisor data: each `D`-zero `Q` in
`gd.support` contributes `gd.mult Q` factors of `(X − zLambdaBar Q)`,
because for `μ` near `zLambdaBar Q` the chord-line `y = λx + μ` passes
through `Q` (with the prescribed local order). The leading coefficient
matches `(normPoly E D).leadingCoeff` after passing through Hasse +
geom-divisor accounting. This is the divisor-of-norm formula
`div(N(D)) = π_*(div D)` for the cover
`F_qbar(E) / F_qbar(zLambdaBar lam)` (Stichtenoth Prop 3.1.9 +
Thm 3.7.1). Provable in mathlib once we have:
  (a) the inertial-degree / ramification computation for the chord
      projection (already encoded by `gd.mult` via the local-order
      machinery in `GeomLocalOrder`);
  (b) a finite product expansion for the resultant.
The hardest sub-step is (a): linking `gd.mult Q` to the multiplicity of
`zLambdaBar Q` as a root of the resultant. -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod
    (lam : ZMod E.q) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = Polynomial.C c * ∏ Q ∈ gd.support,
            (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  sorry

/-- **Proportionality to `normZ` under splitting** (replacement of
`chord_fiber_product_eq_normZ_under_split`).

*Plumbing once `bar_eq_geom_prod` is in hand.*

Both sides are polynomials in `(ZMod E.q)[X]`. Pass to `Fqbar`; the
left factors via `bar_eq_geom_prod`, the right factors directly via the
splitting hypothesis (rational `D`-zeros = `gd.support` over the bar).
The two factored forms agree up to a leading scalar, which descends to
`ZMod E.q` since both originals do. -/
theorem chord_fiber_product_concrete_eq_normZ_under_split
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      chord_fiber_product_concrete E lam D = Polynomial.C c * normZ E lam D β_fun := by
  sorry

/-- **Log-derivative identity** (replacement of
`chord_sum_eq_chord_fiber_product_logDeriv`).

*Math (medium)*: from the resultant-as-product form
`F(μ) = ∏_{i=0,1,2} D.eval(x_i(μ), λx_i(μ) + μ)`, take the logarithmic
derivative. The implicit-function derivatives `dx_i/dμ` are determined
by differentiating the chord cubic `x_i³ − λ²x_i² + (A−2λμ)x_i + (B−μ²) = 0`,
giving `dx_i/dμ = (2λx_i + 2μ) / (3x_i² + A − 2λx_i·(dy_i/dx_i)) `; the
chain-rule combination of `D` then collapses to the `logDerivTerm`
formula already encoded in the project. The non-degeneracy hypothesis
`hDen` rules out the cusp where the implicit-function step would fail. -/
theorem chord_fiber_product_concrete_logDeriv
    (D : CoordRingElt E.q) (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hA₀def : D.eval A₀.1 A₀.2 ≠ 0)
    (hA₁def : D.eval A₁.1 A₁.2 ≠ 0)
    (hA₂def : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
              let x₂ := lam ^ 2 - A₀.1 - A₁.1
              let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
              D.eval x₂ y₂ ≠ 0)
    (hDen : let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
            ∀ pt : ZMod E.q × ZMod E.q,
              pt = A₀ ∨ pt = A₁ ∨
              pt = (lam ^ 2 - A₀.1 - A₁.1,
                    lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
              → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0)
    (hChordNorm :
      (chord_fiber_product_concrete E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) D).eval
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let μ := zLambda E lam A₀
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam
          (lam ^ 2 - A₀.1 - A₁.1,
           lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
    = Polynomial.eval μ
        (Polynomial.derivative (chord_fiber_product_concrete E lam D))
      / (chord_fiber_product_concrete E lam D).eval μ := by
  sorry

end Divisor.Sketch
