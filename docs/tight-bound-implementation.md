# Paper-Tight Bound Implementation

## Summary

The bound on `ma_extractable` (and `ip_knowledge_sound`) has been improved from:

```
78 · (d + k + 6) · |E|
```

to:

```
18 · (d + k) · E.q + (6·d + 9·k + 71) · |E|
```

where `d = stmt.degBound` and `k = stmt.k`.

This matches the paper's bound structure: the main `18·(d+k)·q` term comes from the DKL+Bezout
axiom applied to `polyGFull` (total degree `2·(d+k)`), and the `(6d+9k+71)·|E|` term is the
denominator-undefined boundary bound.

## Key Insight

The "chord failure" set from the user's plan turned out to be **empty**. When
`logDerivCheckFnDenom ≠ 0`, the Bezout argument shows the chord through `(A₀, A₁)`
automatically avoids all zeros of D on E, because:

1. The chord meets E in at most 3 affine points (by `linear_form_zeros_le_three`)
2. The three intersection points are `A₀`, `A₁`, and `(x₂, y₂)`
3. All three have `D ≠ 0` (extracted from `logDerivCheckFnDenom ≠ 0`)
4. So no zero of D on E can lie on the chord

This eliminates the `3·(d+k+1)·|E|` chord failure term entirely.

## New Files

- `Divisor/TightBound.lean`: Contains the paper-tight bound infrastructure:
  - `chord_avoids_D_zeros_of_denom_defined`: Bezout argument
  - `logDerivCheckFn_zero_of_polyG_zero`: Converse of `polyG_zero_at_defined_fincons`
  - `bad_pair_implies_polyGFull_zero`: Bad pair → polyGFull = 0
  - `polyGFull_nonzero_at_witness`: Nonvanishing witness
  - `log_deriv_sz_paper_core_tight`: Core bound `18·(d+k)·q`
  - `log_deriv_sz_paper_tight`: Full bound with undefined pairs

## Modified Files

- `Divisor/ExtractorBridge.lean`:
  - Added `import Divisor.TightBound`
  - Updated `ma_extractable` bound from `78·(d+k+6)·|E|` to `18·(d+k)·q + (6d+9k+71)·|E|`
  - Updated `ip_knowledge_sound` to match

- `Divisor.lean`: Added `import Divisor.TightBound`

## Verification

- `lake build` passes with no errors
- `#print axioms Divisor.ma_extractable` shows no `sorryAx`
- `#print axioms Divisor.ip_knowledge_sound` shows no `sorryAx`
- No `sorry` in `Divisor/TightBound.lean`
- All axioms are pre-existing project axioms

## Comparison

| Metric | Old | New |
|--------|-----|-----|
| Core bound | `36·(2d+k+6)·\|E\|` | `18·(d+k)·q` |
| Total bound | `78·(d+k+6)·\|E\|` | `18·(d+k)·q + (6d+9k+71)·\|E\|` |
| Via Hasse (q ≈ 2\|E\|) | `78·(d+k+6)·\|E\|` | `≈ (42d+45k+71)·\|E\|` |

The new bound is strictly tighter for all `d, k ≥ 0`.
