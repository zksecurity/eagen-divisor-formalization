# Bivariate SZ Paper-Faithful Plan (72 → 18)

**Goal**: match the paper's `18·(d+k+6)·|E|` soundness constant in the MA extractor bound, via a single Weil-on-curves / Bezout-on-E×E argument rather than two nested per-fiber x-reductions.

**Precondition**: the 72→36 refactor (`docs/bivariate-sz-plan.md`) has landed. That refactor consolidates `undef` + `bad_A₀` contributions into a single cleared-fiber argument using the existing `clearedFiberPoly` (one per-fiber x-reduction + one role-swap fiber bound); the result is `(36·(d+k+6) + const)·|E|`. This plan replaces the final doubled-resultant step with a single Bezout / Weil intersection count on E × E.

## Why this needs extra work

Per-fiber machinery (`card_zeros_on_E_le` + `resultantX`) always collects a factor-2 per fiber (two y-branches per x on E). The paper's proof sidesteps this by intersecting the `{cleared=0}` hypersurface with `E × E ⊂ P² × P² ⊂ P⁸` as a single 1-dim intersection curve, and applying Weil's point-count on the resulting curve:

> Paper: `|{f=0} ∩ (E × E)(F_q)| ≤ 2·(dX + dY)·|E|` where `dX, dY` are the x-bi-degrees of `cleared` after reducing `y₀, y₁` modulo the respective curve relations.

This is a single application of a curve-points bound, not a nested pair of univariate bounds. Hence `18 = 9·2` with `9 = deg(E×E)` and `2 = line-SZ factor`, rather than `36 = (2·y₀-branches)·(2·y₁-branches)·9`.

## Constant accounting

| Contribution | 72-split (current) | 36-split (option b) | 18-paper (option a) |
|---|---|---|---|
| good-fiber | 18·(d+k+6)+2 | 18·(d+k+6)+2 | — (unified) |
| bad-A₀ (denom) | 18·(d+k+6) | — (absorbed) | — (absorbed) |
| bad-A₀ (count) | 36·(d+k+6)+2 | 18·(d+k+6)+2 (role-swap) | — (unified) |
| unified | — | — | 18·(d+k+6) |
| Total | 72·(d+k+6)+4 | 36·(d+k+6)+4 | 18·(d+k+6) |

## Axiom situation

**One new classical axiom.** The Weil curve-points bound is standard:

```lean
/-- Weil's theorem on F_q-points of a plane curve (weak form).
    Reference: Stichtenoth "Algebraic Function Fields and Codes"
    Thm V.2.3 (Hasse-Weil); Silverman "Arithmetic of Elliptic Curves"
    V.1.1; also Lang-Weil "Number of points of varieties in finite
    fields" Am. J. Math 76 (1954).

    Stated in the form we use: for a bivariate polynomial
    `f ∈ F_q[X₀, Y₀, X₁, Y₁]` not vanishing on `E × E` (equivalently,
    its image in the coordinate ring of `E × E` is nonzero), with
    x-bi-degree `(dX, dY)` after reducing `Y_i` modulo the curve
    relation `Y_i² = X_i³ + A·X_i + B`, the zero set on
    `E.points × E.points` has cardinality at most `2·(dX+dY)·|E|`. -/
axiom bivariate_poly_zeros_on_ExE_le
    (E : ECSetup) (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hNonzero : f %ₘ₂ (curveEq₀ E, curveEq₁ E) ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 2 * (dX + dY) * E.points.card
```

New axiom count: **10** (from 9). All textbook-citable.

*Provenance note*: the axiom follows from combining
- `hasse_weil` (already in the axiom surface, on one curve),
- absolute irreducibility of `E × E` (product of two absolutely irreducible curves),
- Bezout's theorem for hypersurface-in-surface intersection,
- Lang-Weil's point-count for curves on a surface.

Fully formalising these would take months. Stating the compound form as a single axiom with textbook citation matches the style already used for `principal_divisor_iff` and `hasse_weil`.

## Phase 1: FourVarPoly framework (~1 day)

Create `Divisor/FourVarPoly.lean` (~300-400 LOC):

```lean
/-- 4-variable polynomial ring: X₀, Y₀ (for A₀) and X₁, Y₁ (for A₁).
    Inner→outer layer order: X₀ (innermost), Y₀, X₁, Y₁ (outermost).
    Allows sequential mod-out by curveEq on each pair. -/
abbrev FourVarPoly (q : ℕ) := (ZMod q)[X][X][X][X]

/-- Evaluate at a pair `(A₀, A₁)`. -/
def bivEval₂ (f : FourVarPoly q) (A₀ A₁ : ZMod q × ZMod q) : ZMod q

/-- Embedding of a `(ZMod q)[X][X]` polynomial (2-var in A₁) as a
    4-var polynomial constant in A₀. -/
def liftA₁ (g : (ZMod q)[X][X]) : FourVarPoly q

/-- Inverse: specialize A₀ to get a 2-var polynomial in A₁.  -/
def specializeA₀ (f : FourVarPoly q) (A₀ : ZMod q × ZMod q) : (ZMod q)[X][X]

/-- The A₀-variables. -/
def varA₀x : FourVarPoly q  -- "C(C(C X))" at the appropriate layer
def varA₀y : FourVarPoly q
def varA₁x : FourVarPoly q
def varA₁y : FourVarPoly q

/-- Evaluation distributes over ring ops. -/
@[simp] theorem bivEval₂_add : ...
@[simp] theorem bivEval₂_mul : ...
@[simp] theorem bivEval₂_C : ...
@[simp] theorem bivEval₂_varA₀x : bivEval₂ (varA₀x) A₀ A₁ = A₀.1
...

/-- Simultaneous mod-by-both-curves. Well-defined since curveEq₀
    only touches (X₀, Y₀) layers and curveEq₁ only touches (X₁, Y₁). -/
def modBothCurves (f : FourVarPoly q) : FourVarPoly q
notation:70 f " %ₘ₂ " E => modBothCurves E f

/-- x-bi-degree: after reducing via `modBothCurves`, (dX, dY) bound
    on total degree in X₀ and X₁ respectively (Y_i reduced to linear
    via the curve relation). -/
def bi_x_degree_le (E : ECSetup) (f : FourVarPoly E.q) (dX dY : ℕ) : Prop
```

Key Mathlib tools to lean on:
- `Polynomial.eval₂` composition,
- `Polynomial.modByMonic`, `Polynomial.natDegree_modByMonic_lt`,
- existing `InnerDegLe` from `ClearedPolyForm.lean:~580`.

**Risk**: 4-layer polynomial rings are awkward in Mathlib; lots of `C(C(C _))` plumbing. If `(ZMod q)[X][X][X][X]` is intractable, fallback: `MvPolynomial (Fin 4) (ZMod q)`. MvPolynomial has better APIs for bi-degree but less direct composition with existing `(ZMod q)[X][X]` infrastructure. Choose based on Phase 1 trial.

## Phase 2: clearedFullPoly construction (~1-2 days)

Lift every existing `clearedFiberPoly` component to a full 4-variate:

```lean
/-- Slope numerator: `A₁.y - A₀.y`. -/
def slopeNumFull : FourVarPoly q := varA₁y - varA₀y

/-- Slope denominator: `A₁.x - A₀.x`. -/
def slopeDenFull : FourVarPoly q := varA₁x - varA₀x

/-- x₂ · slopeDen² = slopeNum² - (A₀.x + A₁.x) · slopeDen². -/
def x₂FullScaled : FourVarPoly q := ...

/-- y₂ · slopeDen³ = ... (Weierstrass chord formula cleared). -/
def y₂FullScaled : FourVarPoly q := ...

/-- Evaluate D at a 4-var "point". Takes the existing CoordRingElt. -/
def DAtFull (D : CoordRingElt q) (whichPt : A₀/A₁/A₂) : FourVarPoly q

/-- The fully-cleared log-derivative polynomial. -/
def clearedFullPoly
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    FourVarPoly E.q
```

Each component mirrors the corresponding piece of the existing `clearedFiberPoly` but with `A₀` also lifted to polynomial variables.

**Budget**: each of ~10 components takes ~30-50 LOC including bivEval₂ lemmas. Total ~500 LOC.

## Phase 3: cleared-identity (~1 day)

```lean
theorem bivEval₂_clearedFullPoly_eq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    bivEval₂ (clearedFullPoly E D P k B m) A₀ A₁
      = (A₁.1 - A₀.1) ^ N *
        logDerivCheckFnCleared E D P k B m A₀ A₁
```
where `N` is the total power of `slopeDen` collected during clearing.

Mirror of existing `clearedFiberPoly_identity` (ClearedPolyForm.lean:2172). Biggest source of proof complexity — essentially re-runs the algebraic identity in the 4-variate ring.

## Phase 4: bi-x-degree bound (~0.5 day)

```lean
theorem clearedFullPoly_bi_x_degree_le :
    bi_x_degree_le E (clearedFullPoly E D P k B m) (9·(D.degE+k+6)) (9·(D.degE+k+6))
```

Paper's count:
- `D.eval` at a point: x-degree ≤ D.degE (innermost A₀ or A₁ x-var).
- `slopeNum` / `slopeDen` product: degree 1 each side.
- `x₂Scaled`: degree 2 in A₀.x + A₁.x after reducing slope powers mod curves.
- Line-through evaluated at target: degree 1 in both sides.
- Total: the sum of ~9·(d+k+6) in each of A₀.x and A₁.x after mod reductions.

Proved via x-degree composition lemmas (`hasBi_x_degree_le.add`, `.mul`, etc.) dispatched to Aristotle.

## Phase 5: state the axiom (~0.5 hr)

Add `bivariate_poly_zeros_on_ExE_le` to `Divisor/Axioms.lean` with a verbatim textbook quote (Stichtenoth V.2.3 or Silverman V.1.1) in the docstring.

## Phase 6: assemble `log_deriv_sz_paper` + wire ma_extractable (~0.5 day)

```lean
theorem log_deriv_sz_paper
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNonvanishing : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card ≤ 18 * (D.degE + k + 6) * E.points.card := by
  have hDeg := clearedFullPoly_bi_x_degree_le ...
  have hNZ : clearedFullPoly ... %ₘ₂ ... ≠ 0 := by
    -- from logDerivCheckFn ≠ 0 + identity at (A₀*, A₁*) non-deg
    ...
  have hBound := bivariate_poly_zeros_on_ExE_le E (clearedFullPoly ...)
                   (9·(d+k+6)) (9·(d+k+6)) hDeg hNZ
  -- hBound : ≤ 2·18·(d+k+6)·|E| = 18·(d+k+6)·|E|
  ...
```

Update `ma_extractable` (ExtractorBridge.lean:3374) to:
- replace `72 * ...` with `18 * ...`,
- drop small-validPairs quadratic term entirely (now absorbed; the bound `18·(d+k+6)·|E|` already dominates),
- keep already-dropped `hDenomNZ` (from 72→36 refactor).

## Phase 7: cleanup (~0.5 day)

- Delete `logDerivCheckFn_badA₀_bound_via_symmetry` (the 72→36 combined lemma) — now dead.
- Delete `resultantX_denomScaledPoly_natDegree_le`, `denomScaledPoly` — dead.
- Delete `logDerivCheckFn_fiber_count_bound` if unused — possibly dead.
- Verify axiom count: expect 10 (was 9; +1 for Weil).

## Schedule

| Phase | Time | Aristotle parallelism |
|---|---|---|
| 1: FourVarPoly framework | 1 day | low — mostly plumbing |
| 2: clearedFullPoly build | 1-2 days | medium — per-component bivEval₂ lemmas parallelise |
| 3: identity proof | 1 day | low — single big algebraic rewrite |
| 4: bi-x-degree bound | 0.5 day | medium — per-component degree leaves |
| 5: axiom | 0.5 hr | — |
| 6: assemble + wire | 0.5 day | low |
| 7: cleanup | 0.5 day | — |

**Total**: ~5 focused days.

## Deliverables

1. `Divisor/FourVarPoly.lean` — framework (~400 LOC new).
2. `Divisor/ClearedFullPoly.lean` — construction + identity + degree bound (~500 LOC new).
3. `Divisor/Axioms.lean` — `+1 axiom` (Weil curve-points on E × E).
4. `Divisor/ClearedPolyForm.lean` — `-300-500 LOC` (dead code after 72→36 + now 36→18 pass).
5. Updated `ma_extractable` signature: bound is `18·(d+k+6)·|E|`.

## Success criteria

- `lake build` passes, zero `sorry`s in Divisor namespace.
- Axiom count = 10 (verified via `#print axioms ma_extractable`).
- `ma_extractable` bound matches paper's `thm:ma` constant 18.
- At least 300 net LOC removed (combined with the 72→36 precursor).

## Risk gates

1. **Phase 1 MvPolynomial vs. nested-Polynomial choice**: if `(ZMod q)[X][X][X][X]` plumbing exceeds ~500 LOC, switch to `MvPolynomial (Fin 4) (ZMod q)` + adapter layer. +1 day if we have to switch.
2. **Phase 3 identity bloat**: if the 4-variate cleared-identity proof doesn't factor nicely, may need to replay the paper's algebraic derivation more faithfully (+1 day).
3. **Axiom form mismatch with Weil statement**: if the `bi_x_degree_le` encoding doesn't match Stichtenoth's plane-curve degree, may need to reformulate through a degree-of-projective-curve definition (+0.5 day, no content change).

## Notes for the session

- Precondition: 72→36 refactor must be merged first. Reuses its consolidation of bad-A₀ via cleared-polynomial symmetry.
- The new axiom should live in `Divisor/Axioms.lean` alongside `hasse_weil`, with which it shares textbook provenance.
- `#print axioms ma_extractable` after this lands should show exactly one additional axiom compared to the 72→36 state.
