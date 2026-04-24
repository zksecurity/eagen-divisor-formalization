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
