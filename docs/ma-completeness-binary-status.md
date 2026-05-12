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
`h_sum_zero`, `h_nodup`, etc.). Hypothesis change:

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

The `ma_completeness_for_binary_length2_unconditional` corollary
(commit `aab80bb`) is **fully unconditional** for `Ps = [P, Q]` with
`P + Q = 0` on `E` (i.e., `Q = -P`). `h_extras` is discharged by
`h_extras_holds_for_length2_sum_zero` because both branches of
`LandmarkInvStrongCombineAffineExtras` have failing hypotheses
(branch 1: `xa ≠ xb` fails since `Q.1 = P.1`; branch 2: `ya ≠ -yb`
fails since `Q.2 = -P.2`). The closure exactly matches
`ma_completeness*`.

### Reusable extras-vacuity helper

`affine_extras_vacuous_on_inverse_affine_points` (commit `6ca60f3`)
shows that for any two accumulators with `b.point = -a.point` and
`a.point ≠ 0` (i.e., the running sums are inverses on `E`), the
affine-affine extras are vacuous.

**Implication for length-4 sum-zero**: at iterate level 1, the two
accumulators have running sums `(P_0+P_1)` and `(P_2+P_3)` whose total
is zero (by sum-zero of the original `Ps`), so they're inverses. Level-1
extras therefore hold automatically.

**What's left for length 4**: only the level-0 extras for the two
adjacent pairs `(P_0, P_1)` and `(P_2, P_3)`. These are dischargeable
by `h_extras_holds_for_length2_sum_zero` if the pair is a vertical
pair (`P_1 = -P_0`), or by explicit chord conditions otherwise.

### Fully unconditional corollaries (all proven, closure matches `ma_completeness*`)

| Theorem                                                  | Configuration                                       | Conditions |
|----------------------------------------------------------|-----------------------------------------------------|------------|
| `ma_completeness_for_binary_length2_unconditional`       | `Ps = [P, -P]`                                      | 0 (vacuous)|
| `ma_completeness_for_binary_length4_unconditional`       | `Ps = [P_0, -P_0, P_2, -P_2]` (two inverse pairs)   | 0 (vacuous)|
| `ma_completeness_for_binary_length4_chord_unconditional` | `Ps = [P_0, P_1, P_2, P_3]` with explicit chord conditions | 2 chord pairs at level 0 |
| `ma_completeness_for_binary_length6_chord_unconditional` | length 6 chord-pairs                                | 3 level-0 + 1 level-1 = 4 |
| `ma_completeness_for_binary_length8_chord_unconditional` | length 8 chord-pairs                                | 4 level-0 + 2 level-1 = 6 |

Pattern for length 2N (N ≥ 2): need `2N - 2` chord conditions
(every combine except the final inverse-vacuous one at the top
level).

### Generic chord-chain theorem (commit `e57cc25`)

`ma_completeness_binary_chain` takes a single
recursive certificate `IteratedLevelStepCombineExtras E n accs` defined
as:

```
IteratedLevelStepCombineExtras 0 _ := True
IteratedLevelStepCombineExtras (n+1) accs :=
  LevelStepCombineExtras E accs ∧
  IteratedLevelStepCombineExtras n (level_step E accs)
```

This collapses all per-length scaffolding into a single accumulator-only
recursive predicate. `iteratedLevelStepCombineExtras_iff_forall_lt`
proves equivalence with the universally-quantified `h_extras`.

Per-length corollaries become thin chord-chain certificates instead of
~500 lines of repetitive `interval_cases` / iterator unfolding.

Architectural notes (per codex review):
- Predicate is **accumulator-only** (no `xss` parameter; the proof
  doesn't need it).
- The certifying predicate `LandmarkInvStrongCombineAffineExtras`
  remains the per-pair condition — but for `native_decide`-friendly
  use, we'd want a thinner certifying wrapper that case-splits on the
  combine dispatcher's actual shape (zero / inverse / distinct chord /
  tangent), so the heavy tangent-branch obligations only fire when
  needed.

### admSet specialization (commits 2ad01a5, 6568eb5)

Modular normalization framework with swap-friendly architecture:

**Foundation (`DefsPre.lean`)**:
- `CoordRingElt.instSMul` (`ZMod q`-action), `smul_a`/`smul_b`/`eval_smul`.

**Scaled binary structure (`IsHonestForBinary.lean`)**:
- `IsHonestForBinaryScaled`: alternative IsHonestForBinary where
  `msg.toD = c • eagenBuild_singletons E Ps` for non-zero scalar `c`.
- `IsHonestForBinaryScaled.ofBinary`: coercion from `c = 1` case.
- `splitsOnE_smul`, `divisor_identity_smul` invariance lemmas.
- `ma_completeness_for_binary_with_scalar` — admSet-agnostic helper
  that's the lever for all admSet specializations.

**Per-admSet specializations**:
- `admSetMax`: `ma_completeness_for_binary_admSetMax_unconditional` (no
  normalization — D non-zero from landmark theorem).
- `admSetParker` (coeff(a,1) = 1): `ma_completeness_for_binary_admSetParker_unconditional`,
  `ma_completeness_binary_chain_admSetParker`.
  Precondition: `(eagenBuild_singletons E Ps).a.coeff 1 ≠ 0`. Scalar:
  `(a.coeff 1)⁻¹`.

**Adding more admSets is now mechanical** — admSetEagen, admSetHash
each become ~30-line thin wrappers picking their own scalar from
preconditions. The heavy lifting is in the `with_scalar` helper.

All closures match `ma_completeness*` exactly.

### Full admSet coverage (commit `ea8a7d2`)

All four admissible sets in the paper now have unconditional binary
completeness wrappers:

| admSet         | Precondition                 | Scalar               |
|----------------|------------------------------|----------------------|
| `admSetMax`    | (auto: D non-zero)           | identity             |
| `admSetParker` | `(D.a).coeff 1 ≠ 0`          | `((D.a).coeff 1)⁻¹`  |
| `admSetEagen`  | `(D.a).coeff 0 ≠ 0`          | `((D.a).coeff 0)⁻¹`  |
| `admSetHash r` | `admSetHashInner r D ≠ 0`    | `(admSetHashInner)⁻¹`|

Each admSet has both an `h_extras`-conditional theorem
(`ma_completeness_for_binary_admSet*_unconditional`) and a chord-chain
certificate variant
(`ma_completeness_for_binary_chord_chain_admSet*_unconditional`).

### Auto-construct Ps from wit.scalars (commit `8d71b24`)

Gap 1 closed: `binarySupport stmt wit hk h_binary` derives the support
list automatically from `(-target) :: filter (wit.scalars i = 1) bases`.
Two bridge lemmas establish:
- `binarySupport_sumOnE_eq_zero`: from `relDlog` (witness validity), the
  support sums to zero on E.
- `binarySupport_formalDivisorOfList_eq_honestDivisorCoeffs`: the formal
  divisor of `binarySupport` extensionally matches `honestDivisorCoeffs`.

`MAProverMsg.IsHonestForBinary.fromWitness` (and its `Scaled` variant)
take `(stmt, wit, msg, h_binary, h_valid, h_toD_eq, h_nodup, ...)` and
produce the structure automatically — no manual `Ps`/`h_formal_eq_honest`
proof.

Closure for the new bridges: ONLY `propext, Classical.choice, Quot.sound`
(combinatorial reasoning).

Closures of all four corollaries exactly match `ma_completeness*`.

The length-4 chord-case (`9039704`) handles the typical binary
protocol configuration: `P_0 = -target`, `P_1, P_2, P_3` are selected
bases with `target = P_1 + P_2 + P_3`, the level-0 pairs `(P_0, P_1)`
and `(P_2, P_3)` are non-degenerate chord configurations (no
2-torsion, chord not tangent at endpoints).

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
