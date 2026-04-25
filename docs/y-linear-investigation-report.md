# Investigation Report: Y-Linear Lang-Weil Bound

## Question

Can `bivariate_poly_zeros_on_ExE_le_y_linear` (bound `(dX+dY)·|E|`)
be derived FROM the existing axiom `bivariate_poly_zeros_on_ExE_le`
(bound `2·(dX+dY)·|E|`)?

## Answer: NO — a new axiom is required.

### Obstruction (formal/logical)

The existing axiom is an opaque bound: for **any** polynomial `f`
satisfying the hypotheses, it returns

```
card ≤ 2 * (dX + dY) * E.points.card
```

The factor of 2 is baked into the axiom's **conclusion**. Adding
the hypothesis `bi_y_linear E f` gives us more information about
`f`, but this information is invisible to the axiom — the axiom's
output is always `2*(dX+dY)*|E|` regardless of any structural
property of `f`.

The Y-linear theorem requires `card ≤ (dX+dY)*|E|`, which is
**strictly tighter** than the axiom's bound (for `dX+dY > 0` and
`|E| > 0`). No amount of preprocessing the input polynomial can
change the constant factor in the axiom's output.

### Approaches considered and why they fail

#### 1. Direct application with reduced degree bounds

If we could show that Y-linearity implies the effective degree bounds
are half as large, we could apply the axiom with `(dX/2, dY/2)` and
get `2*(dX/2+dY/2)*|E| = (dX+dY)*|E|`. But Y-linearity constrains
the Y-degrees, not the X-degrees. The X-degree bounds `dX, dY` are
already tight.

#### 2. Product trick (f · f_σ eliminates Y-variables)

The strategy hint suggests forming `g = f · f_σ₀ · f_σ₂ · f_σ₀₂`
(where σ₀ negates Y₀, σ₂ negates Y₂). For Y-linear f, this product
is independent of Y₀ and Y₂ **on the curve** (since
`f·f_σ₀ = b² - a²·Y₀² = b² - a²·(X₀³+AX₀+B)`).

However:
- The product has X₀-degree ≤ 4·dX + 3 and X₂-degree ≤ 4·dY + 3
  (the curve substitution Y₀² → X₀³+AX₀+B adds degree 3).
- Applying the axiom to `g` gives `2*(4dX+3+4dY+3)*|E|`, which is
  **much worse** than `(dX+dY)*|E|`.
- The zero set of g on E×E strictly contains the zero set of f
  (g = 0 when any of the four factors vanish), making the bound
  even looser.
- Moreover, expressing "g is independent of Y on the curve" requires
  working modulo the curve ideal — the axiom takes raw polynomials,
  not equivalence classes modulo the curve.

#### 3. Decomposing zero set into sub-polynomials

For Y-linear f = a·Y₀·Y₂ + b·Y₀ + c·Y₂ + d, we could try to
decompose the zero set into cases and apply the axiom separately.
But each sub-case still produces a bound with the factor of 2.

#### 4. Counting argument via fiber bounds

The mathematical argument for the tighter bound is: for each
(X₀, X₂) pair, Y-linearity means there is at most 1 solution in
(Y₀, Y₂) vs. 2 in the general case. But this fiber-counting
argument is exactly what the **proof** of the Y-linear theorem would
use — it cannot be extracted from the **statement** of the existing
axiom.

### What would work

**Option A: New axiom.** Add a companion axiom:

```lean
axiom bivariate_poly_zeros_on_ExE_le_y_linear
    (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hYlinear : bi_y_linear E f)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ (dX + dY) * E.points.card
```

This is mathematically sound: the proof follows the same Lang-Weil
argument as the existing axiom, but with the tighter fiber count.
The factor of 2 in the original axiom comes from up-to-2 Y-branches
per X-value on the curve; Y-linearity reduces this to at most 1.

**Option B: Replace the existing axiom** with a more refined version
that takes an optional Y-degree bound and adjusts the constant
factor accordingly. This is cleaner but requires modifying the
existing axiom (which the constraints forbid).

**Option C: Prove from first principles** without any axiom, using
Mathlib's polynomial theory. This would require substantial
infrastructure (coordinate ring of E, Schwartz-Zippel for varieties,
etc.) that is not currently in Mathlib.

### Recommendation

Add the Y-linear axiom (Option A). The mathematical justification
is a strict refinement of the same Lang-Weil argument already
documented for the existing axiom. The provenance is identical
(Lang-Weil 1954, Theorem 1), with the additional observation that
Y-linear polynomials produce at most 1 root per fiber instead of 2.

### Impact on downstream bounds

With the Y-linear axiom:
- `log_deriv_sz_paper_core`: `36*(D.degE+k+6)*|E|` → `18*(D.degE+k+6)*|E|`
- `log_deriv_sz_paper`: `54*(D.degE+k+6)*|E|` → `36*(D.degE+k+6)*|E|`
  (the boundary term also uses the factor of 2 in one place)

This matches the paper's stated bound `18·(degE(D)+M−1)·|E|` more
closely (up to the +6 additive constant and boundary correction).
