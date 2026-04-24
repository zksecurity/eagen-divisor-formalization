# Bivariate SZ Paper-Faithful Plan (current → paper)

**Session progress note (2026-04-24):** see `docs/session-progress.md`
for the state at end of this session. Achieved:
`54·(d+k+6)·|E| + quadratic` (linear coeff 72→54, quadratic unchanged).
The remaining gap to paper's exact `18·(d+k)·|E|` decomposes into:
(a) boundary unification (`+18·(…)` → 0 via unifying in Lang-Weil on
stronger polynomial), (b) chord-symmetry halving (`36 → 18`),
(c) uniform-clearing offset drop (`+6 → 0` via direct mod-curve
reduction), (d) T5 replacement to eliminate the quadratic. Each is a
separate follow-up Aristotle dispatch.



**Goal**: match the paper's bound on `ma_extractable` verbatim — `18·(degBound + k)·|E|`, as stated in `sections/ec.tex:763-779` (Lemma "Schwartz-Zippel for Log-Derivative of Norm Check") and `sections/ip.tex:410` (Theorem `thm:ma`, knowledge-soundness error).

Replace the current `(72·(d+k+6) + 4)·|E| + 6q·((d+k+1) + (d+k+1)(d+k))` with `18·(d+k)·|E|` via a single Weil/Bezout-on-E×E argument that obviates the λ-parametrisation + T5 pipeline.

**No precondition.** Executes directly from the current `72`-split; the intermediate `36` step is skipped.

**Hard discipline — no new axioms during the plan.** Every axiom this plan relies on must already exist in `Divisor/Axioms/*.lean` and `axioms/*.md` **before** Phase 1 begins. The plan is not allowed to introduce axioms as it goes — if Phase N discovers a gap, implementation stops and we re-do the preparation step.

See **Preconditions** below for the list of axioms that must be in place and for the Lean file layout (one file per axiom).

## Anatomy of the gap vs. the paper

Current Lean bound (`ExtractorBridge.lean:3396-3399`):

```
(72 · (d + k + 6) + 4) · |E|
  + 6q · ((d + k + 1) + (d + k + 1)·(d + k))   -- quadratic, small-validPairs
```

Paper target: `18·(d+k)·|E|`.

Four distinct slack sources, in decreasing order of size:

**(a) Quadratic `~6q·(d+k)²`** — from the **T5 case-split** (`log_deriv_nonvanishing_criterion`, `PolyFibK.lean:843`).

T5 demands `|validPairs| ≥ 6q·((d+M) + (d+M)(d+M-1)) + 1` to guarantee a "good λ" for the z-parametrisation of E×E → F_q. This requirement drives a case-split in `ma_extractable`: when `|validPairs|` is below the threshold, the proof bounds `acceptSet ⊆ validPairs` directly, tacking on the quadratic term.

**The paper never uses T5.** Weil/Bezout on E×E bounds zeros directly without any λ. The quadratic vanishes as a byproduct of routing through `bivariate_poly_zeros_on_ExE_le` instead.

**(b) Constant `72 → 18`** — from nested per-fiber decomposition (`ClearedPolyForm.lean:5394`).

```
72 = 18 (good-fiber) + 36 (bad-A₀ count) + 18 (undef/denom)
   = 2 · 2 · 18
```
Each `18 = 9·2` (9 = deg E×E, 2 = line-SZ factor). The redundant `×2·2` is two nested y-branch reductions. Weil on E×E does it once.

**(c) Offset `(d+k+6) → (d+k)`** — from the **uniform clearing scale** `N = d·1 + 4 + k·1 + 1` (`ClearedPolyForm.lean:1517`).

- `+1` for D's degree
- `+4` from `dxdzAllScaled` (three `dxdz` factors + corrections via `lamDen^4`)
- `+1` for the `-P` line factor (`linesProductScaled` has `lamDen^(k+1)`)

The `+6` is a formalisation artefact of the uniform-clearing strategy. The paper reduces mod the curve equation in the coordinate ring directly rather than multiplying through by `(A₁.1 − A₀.1)^N`. A tighter Phase 4 bi-x-degree count closes this (see below).

**(d) Constant `+4`** — `+2` from good-fiber `K`, `+2` from bad-A₀ `K'` (ClearedPolyForm.lean:5409-5411). Padding so bounds hold for degenerate `deg = 0` cases. Disappears with the unified Weil step.

## Constant accounting

| Contribution | Current | After plan | Paper |
|---|---|---|---|
| good-fiber | 18·(d+k+6)+2 | — (unified via Weil) | — |
| bad-A₀ (count) | 36·(d+k+6)+2 | — (unified via Weil) | — |
| undef/denom | 18·(d+k+6) | — (unified via Weil) | — |
| unified Weil/Bezout | — | 18·(d+k) | 18·(d+k) |
| quadratic (T5 fallback) | 6q·(d+k)²+ | — (T5 eliminated) | — |
| MA bound | (72·(d+k+6)+4)·\|E\| + ~6q·(d+k)² | 18·(d+k)·\|E\| | 18·(d+k)·\|E\| |

## Preconditions

Both must be satisfied before Phase 1 begins. If either fails, the plan stops and we fix the preparation step first.

### Precondition 1 — axiom restructure (one file per axiom)

Every axiom lives in its own Lean file under `Divisor/Axioms/`, with a docstring that mirrors the corresponding `axioms/*.md` file (verbatim textbook quote + snippet reference). Layout:

```
Divisor/Axioms.lean                           -- re-export hub (imports all below)
Divisor/Axioms/AxiomPrincipalDivisorIff.lean
Divisor/Axioms/AxiomHasseWeil.lean
Divisor/Axioms/AxiomECPointAddComm.lean
Divisor/Axioms/AxiomECPointAddAssoc.lean
Divisor/Axioms/AxiomECPointNegAddCancel.lean
Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean
Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean
Divisor/Axioms/AxiomWeilReciprocityHonest.lean
Divisor/Axioms/AxiomCoordRingEltDivisorGroupSumZero.lean
Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean
```

ECPoint group-law axioms currently embedded in `Divisor/Defs.lean` move out; `Defs.lean` then imports `Axioms.lean` (or the individual axiom files) for the instances that depend on them. All existing `axioms/*.md` files stay as-is and continue to serve as the textbook-provenance source of truth.

Net: **10 files, one axiom per file, all extracted up-front.** `#print axioms ma_extractable` after the full plan should report exactly these 10 names.

### Precondition 2 — FourVarPoly framework is already in place (no axioms, just definitions)

The Lang-Weil axiom's type signature mentions `FourVarPoly`, `bi_x_degree_le`, `bivEval₂`, `%ₘ₂`, `curveEq₀/₁`. These are pure definitions — no axioms — and must be created as part of the preparation so that the axiom file compiles without forward references. Goes in `Divisor/FourVarPoly.lean`.

Net preparatory shift from the original plan: the "FourVarPoly framework" section that was Phase 1 is now precondition work. Phase 1 of the execution plan changes to something else (see below).

### Precondition 3 — the `bivariate_poly_zeros_on_ExE_le` axiom is declared

Added as the 10th axiom file `Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`. Provenance already archived: `axioms/bivariate_poly_zeros_on_ExE_le.md` + `axioms/snippets/lang-weil-1954-thm-1-02.png` + `axioms/papers/lang-weil-1954.pdf`.

**Exact Lean declaration (single file, full content):**

```lean
import Divisor.FourVarPoly

namespace Divisor

/-- Weil / Lang-Weil curve-points bound on `E × E`.

    Reference: Lang & Weil, "Number of Points of Varieties in Finite
    Fields", Am. J. Math. 76 (1954), Theorem 1 (p. 819). See
    `axioms/bivariate_poly_zeros_on_ExE_le.md`.

    For a bivariate polynomial `f ∈ F_q[X₀, Y₀, X₁, Y₁]` whose image in
    the coordinate ring `F_q[E × E]` is nonzero (i.e. `f %ₘ₂ (curveEq₀,
    curveEq₁) ≠ 0`), with x-bi-degree `(dX, dY)` — the degrees of
    the Y-reduced form in X₀ and X₁ respectively — the F_q-zeros of
    `f` on `E × E` are bounded by `2·(dX + dY)·|E|`. -/
axiom bivariate_poly_zeros_on_ExE_le
    (E : ECSetup) (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hNonzero : f %ₘ₂ (curveEq₀ E, curveEq₁ E) ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 2 * (dX + dY) * E.points.card

end Divisor
```

After Precondition 3 lands, `#print axioms ma_extractable` remains unchanged (still lists only the 9 currently-used axioms) because `ma_extractable` doesn't invoke the new one yet — that happens in Phase 6. But the axiom file exists and the provenance is final. No axioms are added during any phase of the plan.

## Target theorem statement (exact)

```lean
theorem ma_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hSplit : normPoly_splits_over_Fq E msg.toD)
    (hAccount : (∑ P ∈ E.points, betaConstructive E msg.toD P) =
                  (normPoly E msg.toD).natDegree)
    (hLargeQ : q + 1 - 2 * Nat.sqrt E.q ≥ 4) :   -- enough for |E| ≥ 4
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ dlogHolds E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 18 * (stmt.degBound + stmt.k) * E.points.card
```

Four deletions from the current signature:

1. `(72·(d+k+6) + 4)` → `18·(d+k)`.
2. Quadratic summand `+ 6q·((d+k+1) + (d+k+1)(d+k))` → deleted.
3. `hDenomNZ` hypothesis → deleted (no denominator scaling once we work on E × E directly).
4. `hLargeQ` weakened from the current `2·(5·(d+k+2)+3) + 21·(d+k+2) + 72`-form to just the Hasse margin `|E| ≥ 4` (the Lang-Weil axiom carries the degree-in-(d+k) requirements internally via `bi_x_degree_le`).

Matches paper's `sections/ec.tex:776-779` and `sections/ip.tex:410` (after Hasse substitution `|E| ≥ q + 1 - 2√q`).

## Phase 1: FourVarPoly framework (moved to Precondition 2)

The 4-variate polynomial infrastructure (`FourVarPoly`, `bivEval₂`, `modBothCurves`, `bi_x_degree_le`, variable embeddings, evaluation lemmas) is **precondition work**, not part of the plan. It lives in `Divisor/FourVarPoly.lean` and is set up before Phase 1 so that the Lang-Weil axiom's signature typechecks.

Kept in the skeleton below for Aristotle's reference during Phase 2-3 proofs:

- `abbrev FourVarPoly (q : ℕ) := (ZMod q)[X][X][X][X]` — nested layers `X₀ → Y₀ → X₁ → Y₁`.
- `def bivEval₂`, `liftA₁`, `specializeA₀`, `varA₀x/y`, `varA₁x/y`.
- `modBothCurves : FourVarPoly q → FourVarPoly q` with notation `%ₘ₂`.
- `bi_x_degree_le E f dX dY : Prop` — post-mod-reduction bi-degree.
- `@[simp]` eval lemmas: `bivEval₂_add/mul/C/varA₀x/…`.

Mathlib tools: `Polynomial.eval₂`, `Polynomial.modByMonic`, existing `InnerDegLe` from `ClearedPolyForm.lean:~580`.

**Representation choice** (nested `Polynomial` vs. `MvPolynomial (Fin 4)`) is Aristotle's call during P2 — whichever yields cleaner eval/bi-degree lemmas wins.

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

## Phase 4: bi-x-degree bound (~1 day)

**Exact target (paper-tight degree count):**

```lean
theorem clearedFullPoly_bi_x_degree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    bi_x_degree_le E (clearedFullPoly E D P k B m)
      (9 * (D.degE + k)) (9 * (D.degE + k))
```

**Crucially, `9·(d+k)` — not `9·(d+k+6)`.** The `+6` offset in the current `clearedFiberPoly` pipeline comes from uniform clearing (`lamDen^N` with `N = d+k+6`). For the full 4-variate `clearedFullPoly` we do **not** clear uniformly — every `dxdz` denominator, slope power, and line factor is reduced mod `curveEq₀`/`curveEq₁` directly in the coordinate ring, collapsing the `+6` back into the effective X-degree.

Per-term contribution after mod-curve reduction:
- `D.eval` at each of the three chord points: total X-degree `≤ 3·D.degE`, reducing to `≤ D.degE` per side after symmetry + mod-reduction.
- Chord slope `λ = (y₁-y₀)/(x₁-x₀)`: numerator degree 1 in each Y, reduces to a non-multiplicative correction via `y_i² = x_i³ + …`; slope squared/cubed in `x₂`, `y₂` formulas absorbed into X-degree `≤ 3` per side.
- Line evaluations at `−P` and each `B_j`: degree 1 in each side, contributing `+(k+1)` to each axis after mod-reduction.
- Total per axis: `9·(d+k)` — the 9 is `deg(E×E)` from Lang-Weil, the `(d+k)` is X-degree of the reduced polynomial.

Proved via x-degree composition lemmas (`hasBi_x_degree_le.add`, `.mul`, `.modCurve`, etc.) dispatched to **Aristotle** for the mechanical degree-arithmetic steps. Per-component degree leaves parallelise well (~10-15 Aristotle queries).


## Phase 5: assemble `log_deriv_sz_paper` (~0.5 day)

Use the preconditioned Lang-Weil axiom to get the paper-faithful log-deriv bound:

```lean
theorem log_deriv_sz_paper
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNonvanishing : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card ≤ 18 * (D.degE + k) * E.points.card := by
  have hBideg := clearedFullPoly_bi_x_degree_le D P B m
  have hNZ    : clearedFullPoly E D P k B m %ₘ₂ … ≠ 0 := …
  have hBound := bivariate_poly_zeros_on_ExE_le E (clearedFullPoly …)
                   (9 * (D.degE + k)) (9 * (D.degE + k)) hBideg hNZ
  -- hBound : ≤ 2·(9·(d+k) + 9·(d+k))·|E| = 36·(d+k)·|E|
  -- Tighten via symmetry: axis reduction yields 18·(d+k)·|E|.
  …
```

**Open question — factor-of-2 between axiom and paper.** The axiom as stated gives `2·(dX+dY)·|E| = 36·(d+k)·|E|` for `dX = dY = 9·(d+k)`. The paper claims `18·(d+k)·|E|`. The factor of 2 discrepancy needs resolving; candidates during Phase 5:

- Tighten via chord symmetry `f(A₀, A₁) = f(A₁, A₀)` (if the log-deriv sum is symmetric in its argument roles). Bad pairs come in symmetric pairs → halve the count.
- Exploit the log-derivative's special structure (e.g., one axis is degenerate or handled by an earlier argument in the paper's proof).
- Accept `36·(d+k)·|E|` as the Lean-provable bound and file the tighter `18·(d+k)` as a follow-up — still eliminates the quadratic and beats the current `72·(d+k+6)+4` by ≥2×.

Decision deferred to Phase 5 execution; Aristotle + careful reading of paper's proof should pick the right path.

**Aristotle tasks**: nonzero-cleared-polynomial derivation (`hNZ`) — mechanical once the `clearedFullPoly` identity (Phase 3) is in place. Paper-exact tightening argument if attempted.

## Phase 6: wire `ma_extractable` (~0.5 day)

Rewrite `ma_extractable` body (`ExtractorBridge.lean:3396-3399`) to:

1. Invoke `log_deriv_sz_paper` in place of `log_deriv_sz` → bound is `18·(d+k)·|E|`.
2. **Delete the T5 case-split entirely.** The large-validPairs branch (currently calling `extractorSucceeds_of_logDerivCheck_identically_zero_general`) and the small-validPairs fallback branch both disappear. The `hAllZero` case is now handled by a direct σ-matching from Weil-on-E×E + principal-divisor characterisation (Silverman Cor III.3.5, existing axiom), not via T5's λ-good-injective argument.
3. **Remove `hLargeQ`** (currently `|E| > 2·(5·(d+k+2)+3) + 21·(d+k+2) + 72`). Replace with a minimal Hasse margin `|E| ≥ 4` or similar; the Lang-Weil axiom already handles q-sensitivity internally.
4. **Remove `hDenomNZ`** hypothesis — no denominator-scaling path remains.

Final signature matches the "Target theorem statement" block above.

**Aristotle tasks**: discharging the new σ-matching bridge — medium-complexity proof rewiring.

## Phase 7: cleanup + axiom audit (~1 day)

Dead code removal:
- `logDerivCheckFn_badA₀_bound` and related fiber-symmetry lemmas — dead.
- `resultantX_denomScaledPoly_natDegree_le`, `denomScaledPoly` — dead.
- `logDerivCheckFn_fiber_count_bound` — dead.
- `log_deriv_nonvanishing_criterion` (T5) — check all remaining callers; remove if no longer used. If T5 still has callers (e.g. in completeness), leave it in `PolyFibK.lean` with a comment noting MA extraction no longer needs it.
- `clearedFiberPoly` pipeline and the 3200+ LOC in `ClearedPolyForm.lean:3414-5534` — most becomes dead.

Axiom audit:
- `#print axioms ma_extractable` must list **exactly the 10 axioms** declared up-front. No new names, no added `sorryAx`.
- Diff check: `#print axioms ma_extractable` before/after the plan should differ by at most the addition of `bivariate_poly_zeros_on_ExE_le`.

If any new axiom accidentally gets pulled in (e.g. via a dependency on an `opaque` declaration that someone turned into an `axiom`), the plan halts and we re-plan.

## Schedule

### Preconditions (~1.5 days, before any plan phase runs)

| Step | Time | Aristotle parallelism |
|---|---|---|
| P1: split axioms into `Divisor/Axioms/Axiom*.lean` | 0.5 day | low — mechanical refactor |
| P2: FourVarPoly framework (`Divisor/FourVarPoly.lean`) | 1 day | medium — eval lemmas parallelise |
| P3: declare `AxiomBivariatePolyZerosOnExELe.lean` | 0.5 hr | — |
| Build + `#print axioms` sanity check | 0.5 hr | — |

### Plan phases (~5 days)

| Phase | Time | Aristotle parallelism |
|---|---|---|
| 1: (moved to P2 above) | — | — |
| 2: `clearedFullPoly` construction | 1-2 days | medium — per-component lemmas |
| 3: identity proof | 1 day | low — single big rewrite |
| 4: bi-x-degree bound `9·(d+k)` | 1 day | medium — degree-arithmetic leaves |
| 5: `log_deriv_sz_paper` | 0.5 day | low |
| 6: wire `ma_extractable` (delete T5 case-split) | 0.5 day | medium — bridge proof |
| 7: cleanup + axiom audit + full build | 1 day | — |

**Total**: ~6.5 days end-to-end (1.5 preconditions + 5 plan + cleanup buffer).

## Deliverables

1. `Divisor/Axioms/Axiom*.lean` — **10 files**, one axiom per file (precondition P1 + P3).
2. `Divisor/Axioms.lean` — re-export hub, importing all of the above.
3. `Divisor/FourVarPoly.lean` — 4-variate framework (~400 LOC new, precondition P2).
4. `Divisor/ClearedFullPoly.lean` — 4-variate construction + identity + degree bound (~500 LOC new, Phases 2-4).
5. `Divisor/ClearedPolyForm.lean` — **massive cleanup** (-2000 to -3000 LOC). Most of `Phase2` section becomes dead.
6. `Divisor/ExtractorBridge.lean` — `ma_extractable` signature tightened to `18·(d+k)·|E|`, no quadratic term, no `hDenomNZ`, `hLargeQ` weakened to Hasse margin only.
7. Updated `axioms/` — already complete; `bivariate_poly_zeros_on_ExE_le.md` is the 10th entry.

## Success criteria

- `lake build` passes at the end, zero `sorry`s in the `Divisor` namespace.
- `#print axioms ma_extractable` lists exactly 10 axioms, all with files under `Divisor/Axioms/`. Names stable across runs.
- `ma_extractable` bound is **exactly** `18·(stmt.degBound + stmt.k) · E.points.card` (matches paper `sections/ec.tex:776-779` via Hasse).
- Quadratic term `6q·((d+k+1) + (d+k+1)(d+k))` is gone.
- Net LOC: ≥ 1500 lines removed from `ClearedPolyForm.lean`, ≥ 900 lines added across `FourVarPoly.lean` + `ClearedFullPoly.lean`.

## Stop conditions

Stop and surface to the user only if there is genuinely no further avenue to explore within the constraints. Before stopping, exhaust:

- **Retrying Aristotle** with a fresh session (context drift, exhausted search, timeout all warrant a restart).
- **Reformulating the target theorem** — weaker hypothesis, alternative phrasing, a stepping-stone lemma — that still leads to the overall goal.
- **Adapting the phase's sub-structure** — splitting a proof into smaller pieces, rerouting via a different lemma, delegating a leaf to a manual fill-in.
- **Re-reading the paper's proof** for hints if a mathematical step is stuck.

Halt only if all of the following hold:

- An axiom not in the preconditioned list of 10 is genuinely required (not just convenient).
- `#print axioms` pulls in a name that wasn't there before Phase 1 (e.g. `sorryAx`), and no reformulation avoids it.
- A phase's target theorem cannot be proved by any formulation within the 10-axiom constraint, after multiple Aristotle rounds and manual exploration.

Phase-internal explorations (representation choice, proof factoring, degree-count tactics) are Aristotle's call during execution — not planning-time decisions, and not stop conditions.

## Notes for the session

- **Aristotle use**: per-component degree and identity lemmas parallelise well. Dispatch in batches of 5-10 at a time. Phase 4 is the biggest Aristotle-friendly chunk.
- **Build integrity**: run `lake build` (a) after each precondition step, (b) after each phase, (c) after the final cleanup. Full green build is the end-of-plan success gate — no broken references, no residual `sorry`, no axiom additions beyond the 10 planned ones.
- **No axiom additions during plan execution.** If an unanticipated gap needs a textbook fact not already axiomatised, STOP, surface the gap, and re-plan the precondition step.
- **Commit hygiene**: never sign commits (`--gpg-sign`, `-S`, `--no-gpg-sign`, or any GPG-related flag). Plain `git commit -m "…"`. Commit messages describe what the code change does, nothing else — no trailer lines, no co-authors, no attribution.
