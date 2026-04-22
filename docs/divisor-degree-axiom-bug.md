# Bug — `CoordRingElt.divisor_degree_eq` is false as stated

**Found**: 2026-04-22, by Aristotle (Harmonic) while investigating `chordLogDerivMatchesNormZ` for the `hPolyGZero` discharge (`docs/goal.md`). Run id `f8b8a4c9-34e2-4f68-a990-940ae33a661e`.

**Status**: documented; fix pending.

## Statement of the axiom (as of commit `7f90a96`)

`Divisor/BetaConstructive.lean:514-516`:

```lean
axiom CoordRingElt.divisor_degree_eq
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (∑ P ∈ E.points, betaConstructive E D P) = D.degE
```

Claims: for every nonzero `D = a(x) − y·b(x) ∈ F_q[E]`, the total `betaConstructive`-multiplicity over `E.points` (the set of *affine F_q-rational* points) equals `D.degE = max(2·natDegree a, 3 + 2·natDegree b)` (the pole order at ∞).

## Counterexample

- `E : y² = x³ + 1` over `F_7` (`curveA = 0`, `curveB = 1`). Discriminant `−16·(4·0³ + 27·1²) = −432 ≡ 2 · 6 ≡ 5 ≢ 0 (mod 7)` — non-singular.
- `D = x² + 1`, i.e. `D.a = X² + 1`, `D.b = 0`. So `¬ (D.a = 0 ∧ D.b = 0)` holds.
- `D.degE = max(2·2, 3 + 2·0) = 4`.
- For each `P = (x, y) ∈ E(F_7)`, `D.eval P.1 P.2 = x² + 1`. This vanishes iff `x² ≡ −1 ≡ 6 (mod 7)`. The QRs mod 7 are `{1, 2, 4}`; `6` is a non-residue. Hence `D` has **no affine F_7-rational zeros** on `E`.
- Therefore `zerosFinset E D = ∅` and `∑_{P ∈ E.points} betaConstructive E D P = 0`.
- **Axiom predicts** `0 = 4`. False.

## Root cause

`betaConstructive` is defined via `rootMultiplicity P.1 (normPoly E D)`, which counts only F_q-rational roots of the 2-sheet norm `normPoly E D = D.a² − D.b² · curveX`. When `normPoly E D` does not split over `F_q`, algebraic zeros of `D` that live over non-rational x-coordinates contribute to the "true" divisor degree (Silverman III Prop 3.4, stated over the algebraic closure) but are invisible to `betaConstructive` / `zerosFinset`.

In the counterexample, `normPoly = (x² + 1)²` which has no F_7 roots, so `rootMultiplicity` sees nothing, but the degree on `E(\overline{F_7})` really is 4 (the divisor has a pair of conjugate zeros over `F_49` each with multiplicity 2).

The axiom's own doc comment (`Divisor/BetaConstructive.lean:501-513`) already acknowledges this gap — "possible failure of `normPoly` to split over `F_q` ... The classical identity holds over the algebraic closure and descends via the Galois structure" — but the stated theorem has no splitting precondition.

## Proper statement

Silverman III Prop 3.4 gives `deg((f)_0) = deg((f)_∞)` as a sum over the algebraic closure. To restate as a sum over `E.points` (F_q-rational points), one of the following preconditions is required:

1. `normPoly_splits_over_Fq E D` (defined at `Divisor/BetaConstructive.lean:554`): all algebraic zeros descend to F_q-rational x-coordinates, each with a rational y by the curve equation or by the `y² = x³ + Ax + B` relation.
2. Equivalently, `Multiset.card (normPoly E D).roots = (normPoly E D).natDegree`.

The corrected axiom should read:

```lean
axiom CoordRingElt.divisor_degree_eq
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    (∑ P ∈ E.points, betaConstructive E D P) = D.degE
```

## Impact on `Divisor.ma_extractable`

`CoordRingElt.divisor_degree_eq` is on the `ma_extractable` axiom surface (one of the 9 Tier-1 names printed by `#print axioms`). Any downstream theorem that invokes it without a splitting hypothesis in scope is, formally, deriving its conclusion from a false premise — so the soundness proof is currently formally unsound for `D` whose norm does not split over `F_q`.

Either the call sites already have `normPoly_splits_over_Fq E D` in scope (in which case the fix is purely statement-level and propagates without changing proofs), or additional threading is needed. See `docs/divisor-degree-axiom-fix-audit.md` (pending) for the call-graph audit.

## Sibling axiom

`CoordRingElt.divisor_group_sum_zero` (`Divisor/BetaConstructive.lean:495-499`) has the same structural shape (sum of `betaConstructive` over `E.points`). On Aristotle's counterexample it is vacuously true (the weighted sum is `0` because `betaConstructive ≡ 0` on the support), so the counterexample does not falsify it — but the classical identity it names (Silverman III Prop 3.4 group-sum part) also lives over the algebraic closure, and the `F_q`-rational-only restatement needs the same splitting precondition for a faithful restatement. The audit will determine whether it also must be patched.

## Source artifact

`f8b8a4c9-34e2-4f68-a990-940ae33a661e-aristotle.tar.gz` (tracked at repo root) contains Aristotle's full output, including `Divisor/ChordLogDerivProof.lean` with the counterexample written up in the file header and a proof of `chordLogDerivMatchesNormZ_holds` that takes the scalar Lemma 6 identity as a hypothesis. The `ChordLogDerivProof.lean` file itself is not being merged — the proof is a trivial inversion of the already-proved `lemma6_chord_residue`; the function-field norm identity is still unmechanized. Only the counterexample documented here is valuable.
