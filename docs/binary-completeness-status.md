# Binary completeness — session status

Branch: `work/binary-completeness` (off `work/no-principal-iff` after merge).

## Headline results

### Unconditional (no project axioms beyond mathlib + completeness's existing closure)

**`ma_completeness_for_binary_M_eq_3`** (Divisor/IsHonestForBinary.lean) — for any binary
witness with `k = 3`, `wit.scalars = (1, 1, 1)`, plus the existing
`IsHonestForLength4Simple` data, we recover the standard `ma_completeness`
rejection bound `≤ (3·numZeros + 4)·|E_aff|`.

Composes the existing length-4-simple bridge (which has its own
constructive proof of `isHonestFor`) directly with `ma_completeness`.
No `PairwiseCombineHyp` required.

### Conditional on per-pair combine hypothesis

**`ma_completeness_for_binary`** + `ma_completeness_clean_for_binary` —
for any `MAProverMsg.IsHonestForBinary` instance plus the per-pair
combine hypothesis `Landmark.PairwiseCombineHyp E`, recover the
standard rejection bound.

The chain composing this:

  1. `eagenBuild_singletons_landmark` — landmark properties (D ≠ 0,
     vanishing at every input, `normPoly natDegree = Ps.length`)
     under sum-zero non-empty input + per-pair combine hypothesis.
     **Axiom-free up to the combine hypothesis.**
  2. `splitsOnE_of_landmark` — `splitsOnE E D` from landmark + `Nodup`.
     Axiom-free.
  3. `divisorOfD_eq_formalDivisorOfList_of_landmark` — full per-`R`
     divisor identity from landmark + `splitsOnE` + `Nodup`. Uses
     existing `ordAt`/`splitsOnE` machinery (acceptable per spec).
  4. `eagenBuild_singletons_divisor_identity` — composition.
  5. `isHonestFor_of_isHonestForBinary` — bridge to
     `MAProverMsg.isHonestFor`.
  6. `ma_completeness_for_binary` — final composition with
     `ma_completeness`.

### Per-pair combine cases proved

  - `combine_oo` (both points = O) — unconditional.
  - `combine_ol` (a.point = O) — unconditional.
  - `combine_or` (b.point = O) — unconditional.
  - `combine_vertical_no_collision` — conditional on no-x-collision
    + non-2-torsion.
  - `combine_distinct_no_collision` (chord) — conditional on
    no-x-collision + non-2-torsion + distinct x.
  - `combine_tangent_torsion`, `combine_tangent_smooth` — NOT proved
    (need `(X - C xa)²` divisibility argument; requires multiplicity-
    tracking refactor).

## What remains for full unconditional M-arbitrary binary completeness

1. **Discharge the per-pair combine hypothesis unconditionally.** Per
   Codex consultation, this requires strengthening `LandmarkInv` with
   point/sheet-level multiplicity tracking. Estimated: ~600-1000 LOC.

2. **Or per-instance discharge** via Codex's `ReachedPair` framework
   (decidable side conditions for specific dlog instances). Estimated:
   ~300-500 LOC.

3. **Fix `degE`/`natDegree` mismatch for M=1 vertical case.**
   `honestDivisorCoeffs` at infinity uses `msg.toD.degE` (= 3 for
   vertical line) but divisor identity gives `-natDegree(normPoly)` (= 2).
   Either change the `honestDivisorCoeffs` definition or pad the
   polynomial. ~100-200 LOC.

4. **Closure pin verification** for `ma_completeness_for_binary*` —
   should match `ma_completeness*` if the per-pair combine hypothesis
   is discharged unconditionally.

## Files changed

  - `Divisor/EagenBuildLandmark.lean` — new, ~2100 LOC, all landmark
    infrastructure.
  - `Divisor/IsHonestForBinary.lean` — new, ~225 LOC, structure +
    bridges + final compositions.
  - `Divisor/Protocol.lean` — `isHonestFor` updated to use `splitsOnE`
    instead of `IsPrincipal` (from `work/no-principal-iff` merge).
  - `Tests/AxiomClosurePin.lean` — closure annotations updated.
  - `Divisor/EagenBuildRecursive.lean` — minor cleanup from merge.

## Closure status

  `ma_completeness` and `ma_completeness_clean` no longer depend on
  `principal_divisor_iff`. Closure: propext, Classical.choice, Quot.sound,
  `chord_fiber_product_eq_normZ_under_split`,
  `resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`,
  + `hasse_weil` (clean form only).
