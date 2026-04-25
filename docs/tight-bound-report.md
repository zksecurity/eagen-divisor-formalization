# Tight Bound Report: `ma_extractable` Constant Improvement

## Summary

The bound on `ma_extractable` has been tightened from `84·(d+k+6)·|E|` to
`78·(d+k+6)·|E|`, a ~7% improvement. Additionally, a tight total-degree
bound `polyGFull_total_degree_le_tight` with `≤ 2·(d+M−1)` has been proven
(subgoal 1 from the task).

## Changes Made

### 1. `polyGFull_total_degree_le_tight` (Subgoal 1) — `ClearedFullPoly.lean`

New theorem proving that `polyGFull` has total degree `≤ 2·(d+M−1)`,
tightening the existing `polyGFull_total_degree_le'` bound of `≤ 2·(d+M)`.

The proof uses `Finset.card_erase_of_mem` to get the exact cardinality
`d−1` (resp. `M−1`) of the erased product factors, instead of the loose
`≤ d` (resp. `≤ M`) bound used by the previous version.

### 2. `log_deriv_sz_paper_core` tightening — `ClearedFullPoly.lean`

The core bound was tightened from `72·(d+k+6)·|E|` to
`36·(2d+k+6)·|E|`. The key observation: the DKL axiom applied to
`clearedFullPoly` of total degree `4d+2k+12` gives at most
`9·(4d+2k+12)·q` zero pairs. With Hasse (`q ≤ 2|E|`), this is
`18·(4d+2k+12)·|E| = 36·(2d+k+6)·|E|`. The previous bound rounded
`36·(2d+k+6)` up to `72·(d+k+6)`, losing precision in the `k`-dependent
term.

### 3. `log_deriv_sz_paper` tightening — `ClearedFullPoly.lean`

Combined bound: `36·(2d+k+6)·|E| + (6d+9k+71)·|E| ≤ 78·(d+k+6)·|E|`.
Previous: `84·(d+k+6)·|E|`.

### 4. `ma_extractable` and `ip_knowledge_sound` — `ExtractorBridge.lean`

Updated to use the tighter `78·(d+k+6)·|E|` bound.

## Verification

- `lake build` passes (8074 jobs).
- No `sorry` in the codebase.
- `#print axioms Divisor.ma_extractable` shows no `sorryAx`.
- Same axiom set as before (project-specific algebraic geometry axioms only).

## Analysis: Why 78, Not 46–54

The user's target of `~50·(d+k+6)·|E|` requires routing through
`polyGFull` (degree `2·(d+k+1)`) instead of `clearedFullPoly` (degree
`4d+2k+12`). This would give a DKL core bound of `36·(d+k+1)·|E|`
instead of `36·(2d+k+6)·|E|`.

However, the polyGFull route requires:

1. **Chord-failure pair counting**: At pairs where some zero `Q` of `D`
   lies on the chord through `(A₀, A₁)`, the `polyG = 0` implication from
   `polyG_zero_at_defined_fincons` does not apply. These pairs must be
   counted separately. The geometric bound is `≤ 4d·|E|` (Bezout: each
   zero Q contributes ≤ 4|E| collinear pairs), giving a total of
   `36·(d+k+1) + 4d + 6d+9k+71 = 46d+45k+107 ≤ 46·(d+k+6)·|E|`.

2. **polyGFull non-vanishing witness**: The `hNV` hypothesis must be
   strengthened to include `hQline` (no zeros on chord at the witness
   pair), creating a case split. When no witness with `hQline` exists,
   a density argument via DKL shows `polyGFull = 0` on all `E×E`,
   routing to extraction instead of the bound branch.

3. **Threshold strengthening**: The `hLargeQ` threshold would need to
   increase from `31·(d'+k+2)+78` to approximately `50·(d'+k+2)+100`
   to support the density argument.

These infrastructure additions (chord-failure counting, case split
restructuring, threshold propagation) represent ~500+ lines of new Lean
code and were beyond the scope of what could be completed with full
verification in this session.

### What the paper's exact bound `18·(d+k)·q + boundary` requires

The paper's argument uses `polyGFull` of degree `2·(d+k)` (i.e.,
`2·(d+M−1)`, proven as `polyGFull_total_degree_le_tight` in this session),
giving a DKL count of `18·(d+k)·q`. Combined with the Hasse bound
`q ≤ 2|E|` and the boundary `(6d+9k+71)·|E|`, this yields approximately
`42·(d+k)·|E| + boundary ≈ 48·(d+k+6)·|E|`.

The infrastructure for this tighter bound is partially in place:
- `polyGFull_total_degree_le_tight` ✓ (proven)
- `polyG_zero_at_defined_fincons` ✓ (existing)
- `polyG_eq_zero_iff_paperResidue` ✓ (existing)
- Chord-failure counting: NOT YET FORMALIZED
- Case-split restructuring of `ma_extractable`: NOT YET DONE
- Threshold strengthening: NOT YET DONE

## Bound Improvement Roadmap

| Approach | Constant | Status |
|----------|----------|--------|
| Current (clearedFullPoly, loose rounding) | 84 | Previous |
| Tightened rounding | **78** | **Done** |
| Product polynomial (polyGFull × ∏ lineEvalNumAtFull) | 78 | Same C |
| polyGFull + geometric chord-failure | **46** | Needs work |
| Paper's exact (polyGFull tight degree) | **~48** | Needs work |
