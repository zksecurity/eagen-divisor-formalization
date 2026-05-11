# Binary Completeness — Final Summary

This document summarizes the binary-completeness extension to the
Eagen MA protocol formalized in `Divisor/`.

## Top-level API

For any binary witness (`wit.scalars i ∈ {0, 1}`) with valid
`relDlog stmt wit`, the user can invoke a single theorem:

```lean
ma_completeness_binary E stmt wit hk msg hkm
  h_binary hValid h_toD_eq
  h_scalars_match h_target_on_curve h_bases_on_curve
  hNodup h_chain h_admSetMax
  hDeg hDegK
```

returning the standard `ma_completeness` bound.

Variants for each admSet (`admSetMax`, `admSetParker`, `admSetEagen`,
`admSetHash`) take a precondition + scalar match.

## Auto-construct Ps from wit.scalars

```lean
binarySupport stmt wit hk h_binary :=
  (-stmt.target) :: filter (fun i => wit.scalars i = 1) stmt.bases
```

Two combinatorial bridges (axiom-light) prove:
- `binarySupport_sumOnE_eq_zero`: from `relDlog` (witness validity).
- `binarySupport_formalDivisorOfList_eq_honestDivisorCoeffs`:
  the formal divisor matches `honestDivisorCoeffs`.

`MAProverMsg.IsHonestForBinary.fromWitness` (and `Scaled` variant)
build the structure automatically.

## admSet specialization framework

Modular per-admSet normalization (commits `2ad01a5`, `6568eb5`, `ea8a7d2`):

| admSet         | Precondition                 | Scalar               |
|----------------|------------------------------|----------------------|
| `admSetMax`    | (auto: D non-zero)           | identity             |
| `admSetParker` | `(D.a).coeff 1 ≠ 0`          | `((D.a).coeff 1)⁻¹`  |
| `admSetEagen`  | `(D.a).coeff 0 ≠ 0`          | `((D.a).coeff 0)⁻¹`  |
| `admSetHash r` | `admSetHashInner r D ≠ 0`    | `(admSetHashInner)⁻¹`|

Each admSet has both an `h_extras`-conditional theorem and a
chord-chain certificate variant.

## Generic chord-chain certificate

`IteratedLevelStepCombineExtras` (commit `e57cc25`) is a recursive
predicate over (n : ℕ, accs : List EagenAccum) that captures all
per-level non-degeneracy conditions in one structure:

```lean
IteratedLevelStepCombineExtras 0 _ := True
IteratedLevelStepCombineExtras (n+1) accs :=
  LevelStepCombineExtras E accs ∧
  IteratedLevelStepCombineExtras n (level_step E accs)
```

`iteratedLevelStepCombineExtras_iff_forall_lt` gives an equivalence
with the universally-quantified `h_extras`.

## Per-length unconditional corollaries

For specific lengths where `h_chain` is fully discharged via geometric
analysis (commits `aab80bb`, `fe8f446`, `9039704`, `11181c1`,
`e222a5c`):

| Length | Configuration                                 | Conditions  |
|--------|-----------------------------------------------|-------------|
| 2      | `[P, -P]`                                     | 0 (vacuous) |
| 4      | `[P_0, -P_0, P_2, -P_2]` (inverse pairs)      | 0 (vacuous) |
| 4      | `[P_0, P_1, P_2, P_3]` (chord pairs)          | 2           |
| 6      | length-6 chord pairs                          | 4           |
| 8      | length-8 chord pairs                          | 6           |

Pattern for length 2N: `2N - 2` chord-non-degeneracy conditions.

## Multiplicativity infrastructure (used by landmark theorem)

- m=2 cross-case multiplicativity (existing).
- m=3 cross-case multiplicativity (commit `7759417`) — second-derivative
  vanishing argument.
- m≤3 unified multiplicativity bridge (commit `8ffdad1`).
- m≤3 combine cases preservation (commit `941cd45`).
- Iterate preservation for Nodup affine sum-zero (commit `ae2f976`).

These are foundational for the `LandmarkInvStrong`-based unconditional
chain.

## Closure analysis

All binary-completeness theorems have axiom closure exactly matching
`ma_completeness*`:

```
{propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g}
```

(`_clean` variants add `Divisor.hasse_weil`, same as base.)

NO new axioms introduced. Verified by `Tests/AxiomClosurePin.lean`.

## Remaining gaps

1. **`h_chain` discharge** for arbitrary lengths.
   - ✅ Per-length corollaries for lengths 2, 4, 6, 8 (chord configurations).
   - ✅ **`native_decide` path** via the point-skeleton certificate (commit `600c442`):
     `ma_completeness_binary_*_point_certificate` takes `IteratedPointChordCase`
     (computable / Decidable predicate over `List (ECPoint E)`) instead of `h_chain`.
     Users can write `(h_point_chain := by native_decide)` for concrete numerical
     inputs at any length. The bridge to the full polynomial-side certificate is
     proved once: `iteratedLevelStepCombineExtras_of_iteratedPointChordCase`.
   - **Theoretically remaining**: unconditional structural genericity predicate on
     the input list that implies chord-safety without per-input numerical check.

2. **`Ps.Nodup` restriction**. Lifting requires multiplicativity at
   `rootMult > 3`, which would either:
   - Pull in soundness-side axiom `divisorClass_eq_zero_of_b_ne_zero`
     (closure expansion).
   - Require new axiom-free m=4, m=5, ... cross-case proofs.

3. **2-torsion / tangent-doubling cases** for intermediate iterate
   accumulators. Currently excluded by chord-only conditions in the
   per-length corollaries.

## File map

- `Divisor/IncrementalConstruction.lean` — m=2 and m=3 cross-case
  multiplicativity.
- `Divisor/EagenBuildLandmark.lean` — `LandmarkInvStrong`,
  `IteratedLevelStepCombineExtras`, smul-invariance lemmas.
- `Divisor/IsHonestForBinary.lean` — `IsHonestForBinary`,
  `IsHonestForBinaryScaled`, `binarySupport`, `fromWitness`,
  per-admSet specializations, top-level theorems.
- `Tests/AxiomClosurePin.lean` — closure regression tests.
- `docs/ma-completeness-binary-status.md` — running status notes.
- `docs/binary-completeness-summary.md` — this file.

## Practical use

For a typical binary protocol with Parker admSet:

```lean
ma_completeness_binary_admSetParker
  E stmt wit hk msg hkm
  h_binary hValid hParker_pre
  h_admSetParker
  h_toD_eq
  h_scalars_match h_target_on_curve h_bases_on_curve
  hNodup h_chain
  hDeg hDegK
```

For users with concrete numerical inputs and small length, `hNodup`
and `h_chain` can be discharged by `decide` / `native_decide` (after
a future certifying-wrapper PR for `LandmarkInvStrongCombineAffineExtras`).

For arbitrary length: per-input geometric analysis required, but the
infrastructure is in place.
