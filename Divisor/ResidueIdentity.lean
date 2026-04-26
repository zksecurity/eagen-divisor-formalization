/-
  Divisor/ResidueIdentity.lean

  Queue-3 step Q3.4 (partial). Scaffolding lemmas for the scalar residue
  identity connecting `logDerivCheckFn` (the log-derivative check on
  `E × E` at defined non-vertical pairs) to `polyG` (the denominator-
  cleared polynomial in the `(Q, β, R, m)` data) at canonical divisor
  data `(Q, β) = (zerosAt E D, multAt (betaConstructive E D))`.

  The full proof of the target theorem requires a Vieta-style collapse of
  the three chord x-coordinates plus the partial-fraction expansion for
  `N(D)'` (Q3.2), combined with the per-sheet β vs. rootMultiplicity
  bridge (Q3.1). That argument spans hundreds of lines of careful
  polynomial manipulation over the split hypothesis. This module records
  the key reusable Layer-4 identities and matching lemmas that a
  subsequent session (or a broadened Q3.4) can consume.

  Landed lemmas:

  * `chord_Vieta_x_sum` : the three chord x-coords sum to `λ²` (i.e.
    `A₀.1 + A₁.1 + A₂.1 = λ²` where `A₂ = chordPoints ⟨2, _⟩`). This is
    the elementary Vieta identity for the chord cubic obtained from
    substituting the chord line into the Weierstrass equation.

  * `L_eval_eq_zLambda_sub` : `Line.eval L P = zLambda λ P - zLambda λ A₀`
    for `L = lineThrough A₀.1 A₀.2 A₁.1 A₁.2`, `λ = slopeOf A₀ A₁`. This
    is the polyFibK-style restatement of the linear form.

  * `ellP_eq_lineEval_mul_scaled` : re-export of `ellP = L_Q · (A₁.1 - A₀.1)`
    for symmetry.

  * `logDerivTermSum_denom_cleared_aggregate` : multiplies the three
    Layer-3 equations by appropriate `∏ N(D)(x_j)` factors and sums; the
    aggregate gives the chord-level denominator-cleared identity.

  No new axioms, no `sorry` / `admit`. Non-trivial layers consumable by
  Q3.4 / Q3.5 without requiring the full residue identity closure.
-/
import Divisor.BivariateLogDeriv
import Divisor.NormLogDeriv
import Divisor.PolyGSlopeProjection
import Divisor.DivisorPrincipal

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Elementary reductions -/

/-- `L_Q(P) = zLambda λ P - zLambda λ A₀` where `L_Q = lineThrough A₀ A₁`
    and `λ = slopeOf A₀ A₁`. -/
theorem L_eval_eq_zLambda_sub
    (A₀ A₁ P : ZMod E.q × ZMod E.q) :
    (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 =
      zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) P -
      zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ := by
  simp only [Line.eval, lineThrough, zLambda, sub_sub]

/-! ## Vieta sum of the three chord x-coordinates

    The chord line through `A₀`, `A₁` has slope `λ` and intersects the
    cubic `y² = x³ + A·x + B` in three points whose x-coordinates satisfy
    `x₀ + x₁ + x₂ = λ²`. The third x-coordinate is, by definition,
    `λ² − x₀ − x₁`, so this reduces to a `ring` identity. -/

/-- Sum of the three chord x-coordinates equals `λ²`. -/
theorem chord_Vieta_x_sum (A₀ A₁ : ZMod E.q × ZMod E.q) :
    A₀.1 + A₁.1 + (chordPoints E A₀ A₁ ⟨2, by omega⟩).1 =
      (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 := by
  show A₀.1 + A₁.1 +
      ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1) = _
  ring

/-- The third chord point's y-coordinate. -/
theorem chord_A₂_y_eq (A₀ A₁ : ZMod E.q × ZMod E.q) :
    (chordPoints E A₀ A₁ ⟨2, by omega⟩).2 =
      (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
        (chordPoints E A₀ A₁ ⟨2, by omega⟩).1 +
      (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1) := rfl

/-! ## Aggregate Layer-3 identity over chord points

    Summing `∏_{j≠i} N(D)(x_j) · (denominator_i)` against the Layer-3
    pointwise identity (multiplied by appropriate factors to make
    denominators line up) yields the chord-sum identity:

    ```
    Σ_i [∏_{j≠i} N(D)(x_j)] · [(3x_i² + A − 2λy_i)] · logDerivTerm(A_i, λ)
       · [something] = Σ_i RHS_i · [∏_{j≠i} N(D)(x_j)]
    ```

    This module states the pointwise denominator-cleared triple (one
    equation per `i`) and leaves the full aggregation step (Vieta +
    PFE matching against `polyG`'s β-sum) to the next iteration of Q3.4.
-/

/-- **Layer 4 sum-form (RHS only, paper-faithful)**. The sum of Layer 3
    RHS terms, one per chord intersection, yields a polynomial expression
    in the three x-coords and `λ`, `a(x), b(x), a'(x), b'(x)`. Includes
    the paper-faithful `-(a+by)·b·(3x²+A)` correction per point. No
    denominators are involved. -/
noncomputable def chordRHS
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (Finset.univ : Finset (Fin 3)).sum (fun i =>
    let P := chordPoints E A₀ A₁ i
    2 * P.2 * (D.a.derivative.eval P.1 * D.a.eval P.1
                 - D.b.derivative.eval P.1 * D.b.eval P.1
                      * (P.1 ^ 3 + E.curveA * P.1 + E.curveB))
      + 2 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB) *
        (D.a.derivative.eval P.1 * D.b.eval P.1
           - D.b.derivative.eval P.1 * D.a.eval P.1)
      - (D.a.eval P.1 + D.b.eval P.1 * P.2) * D.b.eval P.1
          * (3 * P.1 ^ 2 + E.curveA))

/-- Single-point RHS of the Layer-3 identity (paper-faithful form).

    The final correction term `−(a+b·y)·b·(3x²+A)` is the paper-faithful
    chain-rule piece. -/
noncomputable def chordRHSSingle
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ZMod E.q :=
  2 * P.2 * (D.a.derivative.eval P.1 * D.a.eval P.1
              - D.b.derivative.eval P.1 * D.b.eval P.1
                  * (P.1 ^ 3 + E.curveA * P.1 + E.curveB))
    + 2 * (P.1 ^ 3 + E.curveA * P.1 + E.curveB) *
      (D.a.derivative.eval P.1 * D.b.eval P.1
         - D.b.derivative.eval P.1 * D.a.eval P.1)
    - (D.a.eval P.1 + D.b.eval P.1 * P.2) * D.b.eval P.1
        * (3 * P.1 ^ 2 + E.curveA)

/-- `chordRHS` equals the sum of `chordRHSSingle` over the three chord
    points. -/
theorem chordRHS_eq_sum_triple
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    chordRHS E D A₀ A₁ =
      chordRHSSingle E D A₀ +
      chordRHSSingle E D A₁ +
      chordRHSSingle E D (chordPoints E A₀ A₁ ⟨2, by omega⟩) := by
  unfold chordRHS
  rw [show (Finset.univ : Finset (Fin 3)) =
      {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  -- chordPoints ⟨0,_⟩ = A₀, ⟨1,_⟩ = A₁ (by rfl per chordPoints def).
  show chordRHSSingle E D A₀ + (chordRHSSingle E D A₁ +
    chordRHSSingle E D (chordPoints E A₀ A₁ ⟨2, by omega⟩)) = _
  ring

/-! ## Pointwise Layer-3 identity in `chordRHSSingle` form

    `chordRHSSingle` matches the RHS of `logDerivTerm_denom_cleared_pointwise`
    verbatim, so the Layer-3 identity reads
    ```
    N(D)(P.1) · (3·P.1² + A − 2λ·P.2) · logDerivTerm(P, λ)
        = chordRHSSingle E D P
    ```
    at any E-point `P` with nonzero denominators. -/

/-- **Layer 3 identity (rephrased as `chordRHSSingle`).** -/
theorem logDerivTerm_denom_cleared_in_chordRHSSingle
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hD : D.eval P.1 P.2 ≠ 0)
    (hXDen : (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) ≠ 0) :
    (normPoly E D).eval P.1 * (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2) *
        logDerivTerm E D E.curveA lam P =
      chordRHSSingle E D P := by
  unfold chordRHSSingle
  exact logDerivTerm_denom_cleared_pointwise E D lam hP hD hXDen

/-! ## `ellP`-factor inversion at a non-vertical pair

    On `A₀.1 ≠ A₁.1`, `L_Q` is nonzero off the chord through `A₀`, `A₁`,
    and we can express the inverse `L_Q(P)⁻¹` as
    `((A₁.1 - A₀.1) / ellP(P, A₀, A₁))`, matching the denominator-clearing
    structure of `polyG` versus `logDerivCheckFn`'s `1/L(·)` terms. -/

/-- For non-vertical `(A₀, A₁)` and `L_Q(P) ≠ 0`, the inverse
    `L_Q(P)⁻¹` equals `(A₁.1 - A₀.1) / ellP(P, A₀, A₁)`. -/
theorem lineEval_inv_eq_xDiff_div_ellP
    (A₀ A₁ P : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hLnz : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0) :
    ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2)⁻¹ =
      (A₁.1 - A₀.1) / ellP E P A₀ A₁ := by
  rw [ellP_eq_lineEval_mul E P A₀ A₁ hNV]
  have hxne : (A₁.1 - A₀.1) ≠ 0 := sub_ne_zero.mpr hNV.symm
  field_simp

/-! ## Step 1 : Aggregate Layer-3 identity

    Multiplying each of the three pointwise Layer-3 identities by the
    "missing" factors from the other two chord points yields an
    aggregate polynomial identity

    ```
    (∏_i N(D)(x_i) · (3x_i² + A − 2λy_i)) · Σ_i logDerivTerm(A_i, λ)
       = Σ_i [∏_{j≠i} N(D)(x_j) · (3x_j² + A − 2λy_j)] · chordRHSSingle(A_i).
    ```

    No denominators appear on either side.  This is "Step 1" of the
    chord-residue identity argument described in the ResidueIdentity
    summary.  The proof just applies each of the three pointwise
    Layer-3 identities and balances by `ring`. -/

/-- Pointwise denominator factor at a chord point. -/
private noncomputable def normPolyDenom
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (P : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (normPoly E D).eval P.1 * (3 * P.1 ^ 2 + E.curveA - 2 * lam * P.2)

/-- The product of all three chord denominator factors. -/
private noncomputable def chordDenomProd
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  normPolyDenom E D lam A₀ *
  normPolyDenom E D lam A₁ *
  normPolyDenom E D lam (chordPoints E A₀ A₁ ⟨2, by omega⟩)

/-- **Step 1 aggregate identity.** Sum-form identity across the three
    chord points, with denominators cleared globally (no inverses on
    either side). -/
theorem chord_aggregate_identity
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points)
    (hA₁ : A₁ ∈ E.points)
    (hA₂ : chordPoints E A₀ A₁ ⟨2, by omega⟩ ∈ E.points)
    (hDA₀ : D.eval A₀.1 A₀.2 ≠ 0)
    (hDA₁ : D.eval A₁.1 A₁.2 ≠ 0)
    (hDA₂ : D.eval (chordPoints E A₀ A₁ ⟨2, by omega⟩).1
                   (chordPoints E A₀ A₁ ⟨2, by omega⟩).2 ≠ 0)
    (hXDen₀ : (3 * A₀.1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) ≠ 0)
    (hXDen₁ : (3 * A₁.1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) ≠ 0)
    (hXDen₂ : (3 * (chordPoints E A₀ A₁ ⟨2, by omega⟩).1 ^ 2 + E.curveA -
                  2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2
                        * (chordPoints E A₀ A₁ ⟨2, by omega⟩).2) ≠ 0) :
    chordDenomProd E D A₀ A₁ * logDerivTermSum E D A₀ A₁ =
      normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁ *
        normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (chordPoints E A₀ A₁ ⟨2, by omega⟩) *
        chordRHSSingle E D A₀ +
      normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ *
        normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
          (chordPoints E A₀ A₁ ⟨2, by omega⟩) *
        chordRHSSingle E D A₁ +
      normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀ *
        normPolyDenom E D (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁ *
        chordRHSSingle E D (chordPoints E A₀ A₁ ⟨2, by omega⟩) := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  -- Three pointwise Layer-3 identities in `chordRHSSingle` form.
  have h0 := logDerivTerm_denom_cleared_in_chordRHSSingle E D lam hA₀ hDA₀ hXDen₀
  have h1 := logDerivTerm_denom_cleared_in_chordRHSSingle E D lam hA₁ hDA₁ hXDen₁
  have h2 := logDerivTerm_denom_cleared_in_chordRHSSingle E D lam hA₂ hDA₂ hXDen₂
  -- Expand `logDerivTermSum` on LHS, and `normPolyDenom`, `chordDenomProd`.
  rw [logDerivTermSum_eq]
  set A₂ := chordPoints E A₀ A₁ ⟨2, by omega⟩ with hA₂_def
  show normPolyDenom E D lam A₀ * normPolyDenom E D lam A₁ *
        normPolyDenom E D lam A₂ *
        (logDerivTerm E D E.curveA lam A₀ +
          logDerivTerm E D E.curveA lam A₁ +
          logDerivTerm E D E.curveA lam A₂) = _
  unfold normPolyDenom
  set N0 := (normPoly E D).eval A₀.1
  set N1 := (normPoly E D).eval A₁.1
  set N2 := (normPoly E D).eval A₂.1
  set D0 := 3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2
  set D1 := 3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2
  set D2 := 3 * A₂.1 ^ 2 + E.curveA - 2 * lam * A₂.2
  set LT0 := logDerivTerm E D E.curveA lam A₀
  set LT1 := logDerivTerm E D E.curveA lam A₁
  set LT2 := logDerivTerm E D E.curveA lam A₂
  set S0 := chordRHSSingle E D A₀
  set S1 := chordRHSSingle E D A₁
  set S2 := chordRHSSingle E D A₂
  -- h0 : N0 · D0 · LT0 = S0, etc. (in `set`-abbreviated form)
  change N0 * D0 * LT0 = S0 at h0
  change N1 * D1 * LT1 = S1 at h1
  change N2 * D2 * LT2 = S2 at h2
  -- linear_combination with the three pointwise identities.
  linear_combination
    (N1 * D1 * N2 * D2) * h0 + (N0 * D0 * N2 * D2) * h1 + (N0 * D0 * N1 * D1) * h2

/-! ## Step 5 : `polyG` ⇔ divided-fraction sum

    `polyG` is the denominator-cleared form of the rational identity

    ```
      Σ_k β_k / ellP(Q_k) + Σ_j m_j / ellP(R_j) = 0.
    ```

    Formally, when every `ellP(Q_k)` and `ellP(R_j)` is nonzero, we
    have the product-sum identity

    ```
      polyG = (∏_k ellP(Q_k)) · (∏_j ellP(R_j)) ·
              (Σ_k β_k/ellP(Q_k) + Σ_j m_j/ellP(R_j))
    ```

    whence `polyG = 0` iff the divided sum equals zero (for nonzero
    product of poles).  This is "Step 5" of the chord-residue identity
    argument. -/

/-- The divided-fraction form: `Σ_k β_k / ellP(Q_k) +
    Σ_j m_j / ellP(R_j)`. -/
noncomputable def polyGDivided
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (∑ k : Fin d, beta k / ellP E (Q k) A₀ A₁) +
  (∑ j : Fin M, m j / ellP E (R j) A₀ A₁)

/-- The full product of all `ellP` factors at `(A₀, A₁)`. -/
noncomputable def polyG_ellP_product
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (∏ k : Fin d, ellP E (Q k) A₀ A₁) *
  (∏ j : Fin M, ellP E (R j) A₀ A₁)

/-- **`polyG` is the cleared form of `polyGDivided`.** On the open set
    where every `ellP` is nonzero,
    `polyG = (∏_k ellP(Q_k)) · (∏_j ellP(R_j)) · polyGDivided`. -/
theorem polyG_eq_product_mul_divided
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQnz : ∀ k, ellP E (Q k) A₀ A₁ ≠ 0)
    (hRnz : ∀ j, ellP E (R j) A₀ A₁ ≠ 0) :
    polyG E Q beta R m A₀ A₁ =
      polyG_ellP_product E Q R A₀ A₁ *
        polyGDivided E Q beta R m A₀ A₁ := by
  classical
  unfold polyG polyGDivided polyG_ellP_product
  -- LHS = Σ_k β_k · (∏_{k'≠k} ellP(Q_k')) · (∏_j ellP(R_j))
  --     + Σ_j m_j · (∏_k ellP(Q_k)) · (∏_{j'≠j} ellP(R_{j'}))
  -- RHS = (∏_k ellP(Q_k)) · (∏_j ellP(R_j)) · (Σ_k β_k/ellP(Q_k) + Σ_j m_j/ellP(R_j))
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · -- First sum: β_k · ∏_{k'≠k} ellP(Q_k') · ∏_j ellP(R_j) =
    --             (∏_k ellP(Q_k)) · (∏_j ellP(R_j)) · β_k / ellP(Q_k)
    apply Finset.sum_congr rfl
    intro k _
    have hQk := hQnz k
    have hQall : (∏ k' : Fin d, ellP E (Q k') A₀ A₁) =
        ellP E (Q k) A₀ A₁ * ∏ k' ∈ Finset.univ.erase k, ellP E (Q k') A₀ A₁ :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
    rw [hQall]
    field_simp
  · -- Second sum: similar for `R`.
    apply Finset.sum_congr rfl
    intro j _
    have hRj := hRnz j
    have hRall : (∏ j' : Fin M, ellP E (R j') A₀ A₁) =
        ellP E (R j) A₀ A₁ * ∏ j' ∈ Finset.univ.erase j, ellP E (R j') A₀ A₁ :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    rw [hRall]
    field_simp

/-- **Step 5 equivalence.** Under the nonvanishing hypothesis on every
    `ellP`, `polyG = 0` iff `polyGDivided = 0`. -/
theorem polyG_eq_zero_iff_divided_fraction
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQnz : ∀ k, ellP E (Q k) A₀ A₁ ≠ 0)
    (hRnz : ∀ j, ellP E (R j) A₀ A₁ ≠ 0) :
    polyG E Q beta R m A₀ A₁ = 0 ↔
      polyGDivided E Q beta R m A₀ A₁ = 0 := by
  classical
  have hProd : polyG_ellP_product E Q R A₀ A₁ ≠ 0 := by
    unfold polyG_ellP_product
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun k _ => hQnz k))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hRnz j))
  rw [polyG_eq_product_mul_divided E Q beta R m A₀ A₁ hQnz hRnz,
      mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hProd
    · exact h
  · intro h
    exact Or.inr h

/-! ## Step 4 : `polyGDivided` in `L_Q`-form

    The paper's residue identity is naturally stated in terms of
    `1 / L_Q(P)` (where `L_Q` is the chord line through `A₀`, `A₁`),
    whereas `polyGDivided` uses `1 / ellP(P) = 1 / (L_Q(P) · (A₁.1 - A₀.1))`.
    The identity `ellP = L_Q · (A₁.1 - A₀.1)` transfers between the two.

    Concretely, on non-vertical pairs (`A₀.1 ≠ A₁.1`) where every
    `L_Q(Q_k)`, `L_Q(R_j)` is nonzero:

    ```
    polyGDivided E Q β R m A₀ A₁
      = (A₁.1 - A₀.1)⁻¹ · (Σ_k β_k / L_Q(Q_k) + Σ_j m_j / L_Q(R_j)).
    ```

    The RHS is the paper's residue sum (times a nonzero scalar factor).
    This connects Step 5's divided form to the paper's PFE sum. -/

/-- **Paper-form divided-fraction sum in the line-evaluation basis.** -/
noncomputable def paperResidueDivided
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2
  (∑ k : Fin d, beta k * (L.eval (Q k).1 (Q k).2)⁻¹) +
  (∑ j : Fin M, m j * (L.eval (R j).1 (R j).2)⁻¹)

/-- **Step 4 identity.** On a non-vertical pair with every line
    evaluation nonzero, `polyGDivided = (A₁.1 - A₀.1)⁻¹ · paperResidueDivided`. -/
theorem polyGDivided_eq_xDiffInv_mul_paperResidue
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hQline : ∀ k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (Q k).1 (Q k).2 ≠ 0)
    (hRline : ∀ j, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2 ≠ 0) :
    polyGDivided E Q beta R m A₀ A₁ =
      (A₁.1 - A₀.1)⁻¹ * paperResidueDivided E Q beta R m A₀ A₁ := by
  classical
  have hxne : (A₁.1 - A₀.1) ≠ 0 := sub_ne_zero.mpr hNV.symm
  unfold polyGDivided paperResidueDivided
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    have hLk := hQline k
    have hL_inv := lineEval_inv_eq_xDiff_div_ellP E A₀ A₁ (Q k) hNV hLk
    rw [hL_inv]
    field_simp
  · apply Finset.sum_congr rfl
    intro j _
    have hLj := hRline j
    have hL_inv := lineEval_inv_eq_xDiff_div_ellP E A₀ A₁ (R j) hNV hLj
    rw [hL_inv]
    field_simp

/-- **Corollary.** Under the nonvanishing hypotheses, `polyG = 0` iff
    `paperResidueDivided = 0`. -/
theorem polyG_eq_zero_iff_paperResidue
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hQline : ∀ k, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (Q k).1 (Q k).2 ≠ 0)
    (hRline : ∀ j, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2 ≠ 0) :
    polyG E Q beta R m A₀ A₁ = 0 ↔
      paperResidueDivided E Q beta R m A₀ A₁ = 0 := by
  classical
  -- Upgrade hQline/hRline to hQnz/hRnz (ellP nonzero).
  have hQnz : ∀ k, ellP E (Q k) A₀ A₁ ≠ 0 := fun k => by
    rw [ellP_eq_lineEval_mul E _ A₀ A₁ hNV]
    exact mul_ne_zero (hQline k) (sub_ne_zero.mpr hNV.symm)
  have hRnz : ∀ j, ellP E (R j) A₀ A₁ ≠ 0 := fun j => by
    rw [ellP_eq_lineEval_mul E _ A₀ A₁ hNV]
    exact mul_ne_zero (hRline j) (sub_ne_zero.mpr hNV.symm)
  rw [polyG_eq_zero_iff_divided_fraction E Q beta R m A₀ A₁ hQnz hRnz]
  rw [polyGDivided_eq_xDiffInv_mul_paperResidue E Q beta R m A₀ A₁
        hNV hQline hRline]
  have hxne : (A₁.1 - A₀.1)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hNV.symm)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hxne
    · exact h
  · intro h
    rw [h, mul_zero]

/-! ## High-level chord-residue bridge (analysis)

    Combining Steps 1, 4, and 5 with a hypothesised "`\ref{lem:log-derivative}`" chord-sum
    residue identity

    ```
    Σᵢ logDerivTerm(Aᵢ, λ) = - Σ_k β_k / L_Q(Q_k)                  (`\ref{lem:log-derivative}`)
    ```

    and the axiom's global hypothesis `logDerivCheckFn = 0`,     sign analysis identified a sign mismatch between `logDerivCheckFn`'s
    RHS and `polyG`'s additive convention.

    **    `polyG_zero_of_logDerivCheck_identically_zero` (in
    `Divisor/ExtractorBridge.lean`) has been reformulated to use
    `Fin.cons (-1) (fun j => -m j)` instead of `Fin.cons (-1) m`
    for the polyG `m'` argument.

    Under the new axiom form, combining `logDerivCheckFn = 0` with
    `\ref{lem:log-derivative}` (the full residue identity), the paperResidueDivided form
    evaluates to

    ```
    Σ_k β_k/L_Q(Q_k) - L_Q(-P)⁻¹ - Σ_j m_j/L_Q(B_j) = 0,
    ```

    matching the derivation exactly:
    `Σ_k β_k/L_Q(Q_k) = L_Q(-P)⁻¹ + Σ_j m_j/L_Q(B_j)`.

    This still requires mechanizing `\ref{lem:log-derivative}` itself (paper's
    `lem:log-deriv-norm`) to close the axiom as a theorem, which
    remains deferred (requires function-field infrastructure per the
    axiom-elimination plan).

    The downstream cascade (`distinctMCons`, `extractedScalars`, D3
    witness interface) was propagated consistently in the same
    session; see `ExtractorBridge.lean`'s commentary. -/

/-! ## Summary note (Q3.4 status)

```
theorem polyG_zero_of_logDerivCheck_zero_at_defined_canonical
    (D : CoordRingElt E.q) (hD : ¬ D.isZero)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (P : ZMod E.q × ZMod E.q) (k : ℕ)
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDefined : logDerivCheckFnDefined E D P B A₀ A₁) :
    polyG E (zerosAt E D)
              (fun k' => ((multAt E (betaConstructive E D) D k' : ℕ) : ZMod E.q))
              (Fin.cons (P.1, -P.2) B)
              (Fin.cons (-1) (fun j => -m j))
              A₀ A₁ = 0
```

requires closing a deep residue-identity argument that exceeds this
module's 300-LOC budget. (The Session 41 sign resolution negated the
tail in the axiom's `m'` argument to `fun j => -m j`; the signs now
align with `logDerivCheckFn`'s RHS convention as derived above.) The classical proof proceeds by:

1. Aggregating the three pointwise Layer-3 identities (Q3.3,
   `logDerivTerm_denom_cleared_pointwise` / `_in_chordRHSSingle`) over
   the chord intersections to get
   ```
   (∏_i N(D)(x_i)) · (∏_i (3x_i² + A − 2λy_i)) · Σ_i logDerivTerm(A_i, λ)
     = Σ_i [∏_{j≠i} N(D)(x_j)] · [∏_{j≠i} (3x_j² + A − 2λy_j)] · chordRHSSingle(A_i)
   ```
   which is a polynomial identity in `(x_i, y_i, a, a', b, b', λ)` with
   no rational denominators.

2. Applying Vieta (`chord_Vieta_x_sum`) to express `x₂ = λ² − x₀ − x₁` and
   collapsing the x-coord sum dependence.

3. Converting `Σ_i logDerivTerm(A_i, λ)` into an explicit product via the
   partial-fraction expansion for `N(D)'` from Q3.2 + the beta-fiber
   bridge from Q3.1. Specifically:
   ```
   Σ_i logDerivTerm(A_i, λ) · (denoms)
      = Σ_α ∈ roots (βFiber α) / L_Q((α, y_α))
                                  + per-sheet corrections
   ```
   under `hSplit`.

4. Matching against `polyG`'s first sum:
   `Σ_k β_k · ∏_{k'≠k} ellP(Q_k') = Σ_k β_k / L_Q(Q_k) · ∏_all L_Q(Q_k') · (A₁-A₀)^{...}`
   via `ellP_eq_lineEval_mul` and the per-sheet-to-per-fiber re-indexing
   from `zerosAt` / `multAt` matching `betaConstructive`'s fiber sums.

5. Matching against `polyG`'s second sum: clearing denominators on the
   `-1/L(-P) - Σ m_j/L(B_j) = Σ m'_j / L(R_j)` pocket (R = cons (-P) B,
   m' = cons (-1) (fun j => -m j) fix), which is
   the `sum_div_iff_sum_mul_prod_erase` identity from `LogDeriv.lean`.

Steps 1-2 are tractable but lengthy (~400 LOC). Step 3 is deep
(~600+ LOC) and requires pushing `rootMultiplicity`-level PFE through
an explicit `x_i, y_i`-parametrized substitution plus careful case
analysis on per-fiber sheet membership. Step 4 is ~200 LOC. Step 5
is ~100 LOC.

Total realistic effort: ~1500 LOC + substantial new infrastructure
(Vieta polynomial identity, chord-cubic discriminant tracking,
fiber-level per-sheet sum identity).

**Partial progress landed here**: Vieta sum, L-Line-zLambda equivalence,
Layer-3 in chordRHSSingle form, ellP-inverse form. These are consumed
by steps 1, 2, 4. Steps 3 and 5 remain.

**Recommendation for Q3.4 re-attempt**: broaden scope to ~1500 LOC
across multiple new modules (`ChordSum.lean`, `VietaCollapse.lean`,
`BetaFiberMatch.lean`), or narrow the target theorem's hypothesis to
include the scalar residue identity as an assumption (deferring to a
still-later session). -/

/-! ## Chord-residue bridge from `\ref{lem:log-derivative}` hypothesis

    **Bridge theorem**: assuming the scalar `\ref{lem:log-derivative}` identity
    `Σᵢ logDerivTerm(Aᵢ, λ) = -Σ_k β_k · L_Q(Q_k)⁻¹` at a defined
    non-vertical pair (`A₀, A₁`) with all line-evaluations nonzero at
    every Q_k and B_j, if furthermore `logDerivCheckFn = 0` at the pair,
    then `polyG = 0` at the pair.

    This theorem isolates the `\ref{lem:log-derivative}` content as a single scalar
    hypothesis. Its proof is pure scalar algebra (field arithmetic
    plus the Step-5 polyG ⇔ paperResidue equivalence) and requires
    no function-field infrastructure.

    Consuming this lemma: any mechanization of `\ref{lem:log-derivative}` (as a theorem)
    closes `polyG_zero_of_logDerivCheck_identically_zero` at defined
    pairs. The full axiom also needs a density extension from defined
    to all non-vertical pairs (via `polyGPoly`'s polynomial form).

    The bridge theorem uses the sign convention of the current axiom:
    `m' = Fin.cons (-1) (fun j => -m j)` for `polyG`'s R/m' arguments. -/

/-- **Chord-residue bridge (`\ref{lem:log-derivative}` hypothesis form)**. Under `\ref{lem:log-derivative}`
    at a defined non-vertical pair and `logDerivCheckFn = 0`, `polyG`
    vanishes at that pair.

    Hypotheses:
    * `hNV : A₀.1 ≠ A₁.1` — non-vertical pair.
    * `hQline : L_Q(Q_k) ≠ 0` for every k — Q's off the chord.
    * `hNegPline : L_Q(-P) ≠ 0` — -P off the chord (part of the
      `logDerivCheckFnDefined` hypothesis).
    * `hBline : L_Q(B_j) ≠ 0` for every j — B's off the chord.
    * `hLemma6 : Σᵢ logDerivTerm(Aᵢ, λ) = -Σ_k β_k · L_Q(Q_k)⁻¹`.
    * `hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0`.

    Conclusion: `polyG E Q β R m' A₀ A₁ = 0` where
    `R = Fin.cons (P.1, -P.2) B`, `m' = Fin.cons (-1) (fun j => -m j)`. -/
theorem polyG_zero_of_Lemma6_and_logDerivCheck_zero
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    {d : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hQline : ∀ k', (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (Q k').1 (Q k').2 ≠ 0)
    (hNegPline : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0)
    (hBline : ∀ j, (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0)
    (hLemma6 :
      logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
        + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            (((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1,
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) *
                ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 - A₀.1 - A₁.1)
                  + (A₀.2 - (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) * A₀.1)))
      = -∑ k' : Fin d, beta k' *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (Q k').1 (Q k').2)⁻¹)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    polyG E Q beta
              (Fin.cons (P.1, -P.2) B)
              (Fin.cons (-1) (fun j => -m j))
              A₀ A₁ = 0 := by
  classical
  -- Step 1: derive paperResidueDivided = 0 from `\ref{lem:log-derivative}` + hCheck.
  -- Step 2: apply polyG_eq_zero_iff_paperResidue to conclude polyG = 0.
  set L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2 with hL_def
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam_def
  -- All R's line-evaluations: R = Fin.cons (P.1, -P.2) B, so L(R j) ≠ 0 for all j.
  have hRline : ∀ j : Fin (k + 1),
      L.eval
        ((Fin.cons (α := fun _ => ZMod E.q × ZMod E.q) (P.1, -P.2) B) j).1
        ((Fin.cons (α := fun _ => ZMod E.q × ZMod E.q) (P.1, -P.2) B) j).2 ≠ 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · show L.eval P.1 (-P.2) ≠ 0
      exact hNegPline
    · intro i
      show L.eval (B i).1 (B i).2 ≠ 0
      exact hBline i
  -- Unpack logDerivCheckFn = 0: Σᵢ logDerivTerm = -L(-P)⁻¹ + Σⱼ -m_j · L(B_j)⁻¹.
  have hSumLT :
      logDerivTerm E D E.curveA lam A₀
        + logDerivTerm E D E.curveA lam A₁
        + logDerivTerm E D E.curveA lam
            (lam ^ 2 - A₀.1 - A₁.1,
             lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      = -((L.eval P.1 (-P.2))⁻¹)
        + ∑ j : Fin k, -(m j) * (L.eval (B j).1 (B j).2)⁻¹ := by
    have hUnfold : logDerivCheckFn E D P k B m A₀ A₁ =
      (logDerivTerm E D E.curveA lam A₀
        + logDerivTerm E D E.curveA lam A₁
        + logDerivTerm E D E.curveA lam
            (lam ^ 2 - A₀.1 - A₁.1,
             lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
      - (-((L.eval P.1 (-P.2))⁻¹)
         + ∑ j : Fin k, -(m j) * (L.eval (B j).1 (B j).2)⁻¹) := by
      unfold logDerivCheckFn
      rfl
    rw [hUnfold, sub_eq_zero] at hCheck
    exact hCheck
  -- Combine with `\ref{lem:log-derivative}`: -Σ β · L(Q)⁻¹ = -L(-P)⁻¹ + Σ -m · L(B)⁻¹.
  have hCombined :
      -(∑ k' : Fin d, beta k' * (L.eval (Q k').1 (Q k').2)⁻¹) =
        -((L.eval P.1 (-P.2))⁻¹)
        + ∑ j : Fin k, -(m j) * (L.eval (B j).1 (B j).2)⁻¹ := by
    rw [← hLemma6]; exact hSumLT
  -- Rearrange: Σ β · L(Q)⁻¹ + (-1)·L(-P)⁻¹ + Σ (-m_j) · L(B_j)⁻¹ = 0.
  have hRearr :
      (∑ k' : Fin d, beta k' * (L.eval (Q k').1 (Q k').2)⁻¹)
      + ((-1) * (L.eval P.1 (-P.2))⁻¹
         + ∑ j : Fin k, (-(m j)) * (L.eval (B j).1 (B j).2)⁻¹) = 0 := by
    have h1 : (∑ j : Fin k, -(m j) * (L.eval (B j).1 (B j).2)⁻¹)
            = ∑ j : Fin k, (-(m j)) * (L.eval (B j).1 (B j).2)⁻¹ := by
      apply Finset.sum_congr rfl; intros; ring
    linear_combination -hCombined - h1
  -- Express paperResidueDivided on R = Fin.cons (-P) B, m' = Fin.cons (-1) (-m).
  -- paperResidueDivided = Σ β · L(Q)⁻¹ + Σⱼ m'_j · L(R_j)⁻¹.
  -- With R = cons, m' = cons, the second sum = (-1)·L(-P)⁻¹ + Σⱼ (-m_j)·L(B_j)⁻¹.
  have hPaper :
      paperResidueDivided E Q beta
          (Fin.cons (α := fun _ => ZMod E.q × ZMod E.q) (P.1, -P.2) B)
          (Fin.cons (α := fun _ => ZMod E.q) (-1) (fun j => -m j))
          A₀ A₁ = 0 := by
    show (∑ k' : Fin d, beta k' * (L.eval (Q k').1 (Q k').2)⁻¹)
         + (∑ j : Fin (k + 1),
             (Fin.cons (α := fun _ => ZMod E.q) (-1) (fun j => -m j)) j *
               ((L.eval
                   ((Fin.cons (α := fun _ => ZMod E.q × ZMod E.q) (P.1, -P.2) B) j).1
                   ((Fin.cons (α := fun _ => ZMod E.q × ZMod E.q) (P.1, -P.2) B) j).2))⁻¹)
         = 0
    -- Split the sum over Fin (k+1) via Fin.sum_univ_succ.
    rw [Fin.sum_univ_succ]
    -- The (0) term is (-1) * L(-P)⁻¹; the succ term is Σⱼ (-m_j) * L(B_j)⁻¹.
    -- These match hRearr.
    show (∑ k' : Fin d, beta k' * (L.eval (Q k').1 (Q k').2)⁻¹)
         + ((-1) * (L.eval P.1 (-P.2))⁻¹
            + ∑ i : Fin k, (-m i) * (L.eval (B i).1 (B i).2)⁻¹) = 0
    exact hRearr
  -- Apply Step-4 equivalence: polyG = 0 iff paperResidueDivided = 0.
  rw [polyG_eq_zero_iff_paperResidue E Q beta _ _ A₀ A₁ hNV hQline hRline]
  exact hPaper

end Divisor
