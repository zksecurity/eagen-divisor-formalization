# Paper-Faithful Bound: Session Execution Status

Execution of `docs/bivariate-sz-paper-faithful.md` — orchestrator notes.

## Completed

### Preconditions (P1, P2, P3)
Already in place before session started.

### Phase 2: clearedFullPoly construction
- `Divisor/FourVarPoly.lean` extended with `bivEval₂_{add,sub,mul,neg,pow,sum,prod}` and `bi_x_degree_le.{add,sub,mul,neg,pow,sum,prod_fin,mono,C,X₀/Y₀/X₁/Y₁}`.
- `Divisor/ClearedFullPoly.lean` built with explicit 4-variate mirror of every `clearedFiberPoly` component:
  - Variable atoms: `varA₀x/y`, `varA₁x/y`
  - Slope/line: `lamNumFull`, `lamDenFull`, `lineEvalNumAtFull`
  - Chord: `x₂ScaledFull`, `y₂ScaledFull`
  - D/D' atoms at A₀,A₁,A₂ (with Finset-sum forms for A₂)
  - `dxdzDen{A₀,A₁,A₂}Full`, `DBdydzAt{A₀,A₁}Full`, `DbAtA₂TightFull`, `dydzNumA₂Full`, `correctionA₂CoreFull`
  - 8 summand defs: `lhsTerm{0,1,2}Full`, `correctionTerm{0,1,2}Full`, `rhsTermNegPFull`, `rhsSumFull`
- All compat lemmas `bivEval₂_*Full_eq_bivEval` proven (delegated 7 Finset-sum / algebraic cases to a subagent; all closed).

### Phase 3: identity
- `bivEval₂_clearedFullPoly_eq_bivEval` proven via per-summand compat.
- `clearedFullPoly_identity` then follows from the existing `clearedFiberPoly_identity`, one line.

### Phase 5 (partial): log-deriv bound framework
- `bivEval₂_clearedFullPoly_eq_zero_of_bad` proven — wires bad-pair hypothesis to polynomial vanishing.
- `A₀ne_A₁x_cleared_pair` predicate defined and decidable.
- `log_deriv_sz_paper_core` proven (non-degenerate part): card ≤ `36·(d+k+6)·|E|` via Lang-Weil axiom.
- `clearedFullPoly_nonzero_witness` proven via identity + factor non-vanishing.

### Phase 6 (partial): ma_extractable wiring
- Import `Divisor.ClearedFullPoly` added to `Divisor.lean` and `Divisor/ExtractorBridge.lean`.
- `ma_extractable`'s nonvanishing branch now calls `log_deriv_sz_paper` instead of `log_deriv_sz`.
- Linear coefficient of ma_extractable's bound: `72·(d+k+6)+4` → `36·(d+k+6)`.
- `ip_knowledge_sound` inherits the tightened bound automatically.

## Sorries remaining

| # | File | Line | Theorem | Approach | Status |
|---|---|---|---|---|---|
| 1 | ClearedFullPoly.lean | 870 | `clearedFullPoly_bi_x_degree_le` | degreeOf arithmetic on sum-of-products | Aristotle job `831865ae` (QUEUED) |
| 2 | ClearedFullPoly.lean | 1013 | `log_deriv_sz_paper` (outer, boundary) | Combine `_core` + boundary bounds, or delegate to `log_deriv_sz` | Aristotle job `831865ae` (QUEUED) |

Both are in the same Aristotle job.

### Still fully TODO (Phase 6b — deferred)

The quadratic summand `6·q·((d+k+1) + (d+k+1)·(d+k))` in `ma_extractable`'s bound remains. Eliminating it requires replacing the T5 path (`log_deriv_nonvanishing_criterion`) with a Lang-Weil-based σ-matching derivation (paper `sections/ip.tex:462-676`). Major new work.

## Phase 7 (cleanup) — queued

- Remove dead log_deriv_sz infrastructure (fiber-count bound, bad-A₀ bound, resultantX_* theorems) once Phase 5 outer closes without using them.
- Run `#print axioms ma_extractable` to confirm axiom list is exactly the 10 planned. No `sorryAx` creep.

## Session update (after Aristotle dispatches)

Post-dispatch state:

**Closed by Aristotle:**
- `clearedFullPoly_bi_x_degree_le` — 9·(D.degE + k + 6) bi-X-degree bound (project `eae97513`, ~300 LOC of private helpers)
- `bivEval₂_polyGFull_eq_polyG` — polyGFull = polyG compat (project `57bee5a1`)
- `polyGFull_bi_x_degree_le` — (d+M, d+M) bound (project `57bee5a1`)
- `polyGFull_vanishes_on_ExE_of_polyG_zero` — Lang-Weil contrapositive under linear `|E| > 4(d+M)+2` (project `57bee5a1`)
- `bivEval₂_swapA₀A₁` — swap at polynomial vs evaluation level (project `7771ba3b`)
- `bivEval₂_clearedFullPoly_swap_zero` — zero-set symmetry (uses signed version)

**Analytical findings:**
- `clearedFullPoly_swap_eq` ORIGINAL CLAIM IS FALSE: the swap gives `(-1)^(D.degE + k) · clearedFullPoly`, not equality. Replaced with `clearedFullPoly_swap_signed` (sorry pending sign-tracking algebra).
- Chord symmetry HALVING ARGUMENT DOES NOT WORK: an involution on the bad set only shows even cardinality, does not reduce Lang-Weil bound. The plan's `36 → 18` tightening needs a different mechanism (likely Y-linearity-aware Lang-Weil).

**Remaining sorries (top-level):**
1. `clearedFullPoly_swap_signed` — sign tracking under swap; UNUSED in proof chain.

`sigma_matching_from_polyGFull_vanishing` is now FULLY PROVEN (Aristotle projects 6e5f6092, 43de7f00, fa1f41ef). Paper Steps 3-6 mechanized via:
- `polyG_at_self_Q` / `polyG_at_self_R` — polyG reduction at self points
- `exists_avoiding_A1` — Bezout-on-curve geometric existence
- `residualFull` + bi-degree + vanishing-on-ExE — Lang-Weil contrapositive on residual after σ-matching
- `sigma_matching_core` — full assembly

**Paths to exact paper `18·(d+k)·|E|` bound:**

| Slack | Current bound contribution | Path |
|---|---|---|
| Factor 2 in Lang-Weil axiom | `36·…` vs target `18·…` | Derive a Y-linearity-aware Lang-Weil theorem from the existing axiom, exploiting that `clearedFullPoly` mod curve equations is Y-linear. |
| `+6` offset | `(d+k+6)` vs target `(d+k)` | Redefine `clearedFullPoly` with per-factor mod-curve reduction instead of uniform `lamDen^N` scaling. Major refactor. |
| `+18·(…)` boundary | log_deriv_sz_paper outer: 36+18=54 | Unify denom-undefined pairs into the Lang-Weil zero set via a single polynomial that vanishes on both. |
| Quadratic term | `+ 6q·((d+k+1)+(d+k+1)·(d+k))` | Close `sigma_matching_from_polyGFull_vanishing` and rewire `ma_extractable` to drop the quadratic fallback. |

Each of these is an independent follow-up Aristotle dispatch.
