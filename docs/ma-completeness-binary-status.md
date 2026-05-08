# Status: ma_completeness_for_binary unconditional

## Achieved this session

`Divisor.ma_completeness_for_binary_unconditional` and
`Divisor.ma_completeness_clean_for_binary_unconditional` are committed
on `work/binary-completeness`, with axiom closure **identical** to the
existing `ma_completeness*` baseline:

```
{propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g}
```

(`_clean` adds `Divisor.hasse_weil`, same as the baseline.)

No new axioms. Verified by `Tests/AxiomClosurePin.lean` (commit `7a61b42`).

## What's gated and what's discharged

The new theorems take the same data as the old `ma_completeness_for_binary`:
`MAProverMsg.IsHonestForBinary` (binary witness, `Ps` support list,
`hSumZero`, `hNodup`, etc.). Hypothesis change:

| Old conditional             | New conditional           |
|-----------------------------|---------------------------|
| `Landmark.PairwiseCombineHyp E` (universal: `∀ xs ys a b ...`)  | `h_extras` (per-input: `LevelStepCombineExtras` at each iterate level) |

`h_extras` is strictly weaker:
- Only quantifies over the iterate states reachable from THIS specific
  `Ps`, not over arbitrary `(xs, ys, a, b)` quadruples.
- `LevelStepCombineExtras` is decidable (it's a finite product of
  affine-arithmetic conditions), so for concrete inputs it is
  dischargeable by `decide` / `native_decide`.

## Math infrastructure built

The chain that makes the unconditional version possible:

1. **m=3 cross-case multiplicativity** (commit `7759417`) — extends
   `cross_iterDivLin_invariant_at_m_eq_two` to the m=3 case via a
   second-derivative-vanishing argument. Axiom-free.
2. **m≤3 multiplicativity bridge** (commit `8ffdad1`) —
   `localMult_mulCoordRingElt_eq_add_when_rootMult_le_three_unconditional`
   with the cross-case dispatcher branching on `min(m₁, m₂)` ∈ {1,2,3}.
3. **m≤3 combine cases** (commit `941cd45`) — all 8 combine variants
   (oo / ol / or / vertical / distinct / tangent_torsion / tangent_smooth
   / unified) extended from rootMult ≤ 2 to ≤ 3.
4. **Iterate preservation** (commit `ae2f976`) —
   `landmarkInvStrong_eagenBuild_singletons`: starting from a Nodup
   affine sum-zero list of length ≥ 2, the iterate produces a single
   accumulator with `LandmarkInvStrong` over the full list and
   `point = 0`.
5. **Unconditional binary chain** (commit `4cacee9`) — wires the
   iterate-preservation into `MAProverMsg.IsHonestFor`, replacing
   `PairwiseCombineHyp` with `h_extras`.

## Remaining gap: discharging `h_extras`

`LevelStepCombineExtras` (defined in `Divisor/EagenBuildLandmark.lean`
around line 7805) requires:

For each adjacent accumulator pair `(a, b)` in an iterate state:
- **Branch 1 (xa ≠ xb, chord case)**: `ya ≠ 0`, `yb ≠ 0` (no 2-torsion),
  and the chord's third intersection x-coordinate differs from both
  parents.
- **Branch 2 (xa = xb, ya ≠ -yb, ya ≠ 0, smooth tangent doubling)**:
  divisibility conditions on the polynomial product.

**Genuine obstacle**: these geometric conditions can fail for specific
inputs. Examples:
- A 2-torsion point in `Ps` makes `ya = 0` or `yb = 0` at level 0.
- Two adjacent inputs `P, Q` with `Q = -2P` make the chord through
  `P, Q` tangent at `P`, so the third intersection has `x_3 = xa`.

For Nodup affine sum-zero inputs, these failures are non-generic but
not impossible. Discharging `h_extras` unconditionally requires either:

1. Adding input restrictions (e.g., "no 2-torsion in `Ps`", "no
   `Q = -2P` for adjacent pairs"), and propagating them through
   intermediate iterate states.
2. Proving these restrictions hold automatically for binary protocol
   inputs from the EC group structure. (This is plausible if the
   target/bases are sampled from a generic distribution, but that's a
   probabilistic rather than worst-case argument.)
3. Restructuring the protocol to handle degeneracies (e.g., perturb the
   pairing order so the accumulator points avoid degenerate configurations).

The `ma_completeness_for_binary_M_eq_3` constructive bridge through
`length-4-simple` (committed earlier) is fully unconditional for `k = 3`
because it bypasses iterate entirely.

## Path to fully unconditional general `ma_completeness_for_binary`

Two routes:

**Route A** — Discharge `h_extras` for binary inputs.
Requires showing that for any Nodup affine sum-zero list, the iterate
states never hit any of the geometric degeneracies. Likely needs
additional input genericity assumptions; may not hold uniformly.

**Route B** — Replace iterate with a non-recursive construction.
For binary inputs, an explicit closed-form `D` (e.g., the product over
`(P_i)` of chord lines through partial sums, with appropriate
cancellations) might avoid the recursion entirely. Closer to the
length-4-simple bridge, but for arbitrary `k`. Substantial new design.

## File map

- `Divisor/IncrementalConstruction.lean`: m=2 and m=3 cross-case
  multiplicativity proofs.
- `Divisor/EagenBuildLandmark.lean`: data model, `LandmarkInvStrong`,
  combine cases, iterate-preservation, unconditional landmark theorems.
- `Divisor/IsHonestForBinary.lean`: `IsHonestForBinary` structure,
  bridge to `MAProverMsg.isHonestFor`, ma_completeness_for_binary{,_clean}
  in two variants (old conditional, new unconditional).
- `Tests/AxiomClosurePin.lean`: regression test pinning closures.
