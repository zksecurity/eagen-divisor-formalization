# Landmark Deprecation Plan

## Goal

Delete `Divisor/EagenBuildLandmark.lean` and the `Divisor.Landmark`
namespace. Migrate every consumer
(`Divisor/IsHonestForBinary.lean`, `Tests/EndToEndSmoke.lean`,
`Tests/AxiomClosurePin.lean`, `Tests/PointCertificateDecidable.lean`)
to the recursive infrastructure in
`Divisor/EagenBuildRecursive.lean`.

After the port, every `ma_completeness_binary_*` theorem proves the
same `(3·numZeros + 4) · |E.points|` rejection-set bound it does
today, but routed through the recursive driver — leaving exactly one
Eagen driver in the codebase, which the computable layer
(`eagenBuildC`) already bridges to.

## Design constraint

The recursive `EagenAccum.point` is `ZMod q × ZMod q`, not
`ECPoint E`. This is deliberate: it's the type-design decision that
makes `eagenBuildC` computable. The port preserves this and rephrases
Landmark's `ECPoint`-typed lemmas as `(point : ZMod q × ZMod q) +
(h : point ∈ E.points)` in the style `AccInv` already uses.

## Mapping table

**NEW** entries require new infrastructure; **EXISTS** entries are
already present in `Divisor/EagenBuildRecursive.lean`; **RELOCATE**
entries exist but need namespace/visibility cleanup.

### Data and combinators

| `Landmark` | Recursive | Status |
|---|---|---|
| `EagenAccum` (`point : ECPoint E`) | `EagenAccum` (`point : ZMod q × ZMod q` + `AccInv`'s `∃ h : point ∈ E.points`) | EXISTS, type-shape change pervasive in consumers. |
| `levelInitSingleton P` | **NEW** `eagenBuild_level0_singletons` (one vertical-line acc per input) | Build alongside the existing adjacent-pair `eagenBuild_level0`. |
| `level0_singletons` | **NEW** matching list-level driver | Build. |
| `EagenAccum.combine_distinct` | `EagenAccum.combine_higher_distinct` | EXISTS. |
| `EagenAccum.combine_vertical` | `EagenAccum.combine_higher_vertical` (produces `TerminalInv`, not `AccInv`) | EXISTS as a terminal step, not a generic combine. |
| `EagenAccum.combine_oo` / `_ol` / `_or` | None | Three-way dispatch on infinity-vs-affine doesn't apply to raw-coord type; absorbed into AccInv's `(point ∈ E.points)` case analysis. |
| `EagenAccum.combine_tangent_torsion` / `_smooth` | None | Tangent doubling deferred (`EagenBuildRecursive.lean:113`, placeholder returns `a :: b`). Build or restrict (see Step 1). |
| `iterate` | `eagenBuild_iterate` | EXISTS. |
| `eagenBuild_singletons` | **NEW** `eagenBuild_from_singletons` (top driver over the singletons-level0 entry) | Build. |

### Invariants

| `Landmark` | Recursive | Status |
|---|---|---|
| `LandmarkInv` | `AccInv` | EXISTS; needs new initialization theorem for the singleton path. |
| `LandmarkInvStrong` (+ degree, `target ≤ localMult`) | `AccInv` + supplementary lemmas | **NEW** supplementary lemmas (degree-bound exists in part as `accInv_natDegree_normPoly` per recursive TODOs at `EagenBuildRecursive.lean:6510`; target-mass NEW). |
| `LandmarkInvList` / `LandmarkInvStrongList` | `AccInvList` | EXISTS but distinct-chord branch only; extend. |
| `LevelStepCombineExtras` (per-pair dispatch) | `AccsListChordStep` (distinct chord only) | **EXTEND** per Step 1 decision: under tangent-free input, only the vertical-terminal case needs to be added; under tangent-permissive input, also add tangent-doubling branches. |
| `IteratedLevelStepCombineExtras` | None | **NEW** chained-form predicate + propagation theorem. |

### Top-level facts

| `Landmark` | Recursive | Status |
|---|---|---|
| `eagenBuild_singletons_landmark` (invariant survives iterate) | None for singletons path | **NEW**. |
| `eagenBuild_singletons_divisor_identity` | None; `eagenBuild_correctness` is open (`EagenBuildRecursive.lean:6400`) | **NEW** — assembled across substeps 7a–7e. |
| `splitsOnE_of_landmark` (construction-side splits) | `splitsOnE_of_isHonestForExplicit` is consumer-side (requires honest message already) | **NEW** construction-side splits theorem. |
| Construction-side `eagenBuild` nonzero | None | **NEW**. |

### Helpers

| `Landmark` | Recursive | Status |
|---|---|---|
| `formalDivisorOfList` | `formalDivisorOfList` (`EagenBuildRecursive.lean:210`) | **EXISTS in both**; Landmark's local copy is deliberate to avoid an import cycle. Step 2 handles unification. |
| `sumOnE` (`EagenBuildLandmark.lean:306`) | None standalone; `AccInv` embeds the same fold (`EagenBuildRecursive.lean:247`) | RELOCATE: move `sumOnE` into the `Divisor` namespace (or hoist out the AccInv fold as a public definition). |
| `pointCombine`, `pointLevelStep`, `PointChordCase`, `LevelStepPointChordCase`, `IteratedPointChordCase` | None | **NEW** if certificate path is retained (Step 16); otherwise drop. |
| `localMult` and its lemmas (~700 LOC) | Existing `ordAt` machinery | Drop; reroute consumers through `ordAt`. |
| `target`, `targetMass` | None | Drop unless cross-referenced (verify via `rg`). |
| `PairwiseCombineHyp` | `LevelStepTangentFree` / `AllDistinctECPoints` | Partial match; under Step 1 (1a) `LevelStepTangentFree` suffices. |

## Sequential execution

Steps run in order; each is a self-contained commit, and each
downstream step depends on the upstream ones it cites. Run
`lake build Tests.AxiomClosurePin` after every step; closure must
not drift from master.

### Step 1 — Tangent / doubling policy

Decide whether `binarySupport` inputs can produce tangent doubling
at level ≥ 1. With `Nodup` input there's no level-0 doubling, but
sublist subsums (e.g. `B_0 + B_1 = B_2 + B_3`) can yield equal
intermediate points at higher levels — `Nodup` on `binarySupport`
alone is insufficient.

Choose one:
- **1a (recommended)** Strengthen `binarySupport` with a
  no-subsum-collision predicate over the input *partition tree*
  used by the recursion (not just element-wise `Nodup`). Document
  the restriction in the binary completeness statement; later
  loosen if needed.
- **1b** Add tangent branches (`combine_higher_tangent_torsion`,
  `combine_higher_tangent_smooth`) to recursive
  `eagenBuild_level_step` and prove their invariants. The
  placeholder at `EagenBuildRecursive.lean:168` becomes a real
  combine.

Record the choice in a comment at the top of this file. Steps 4
and 7a downstream branch on this decision.

### Step 2 — Unify `formalDivisorOfList`; relocate `sumOnE`

Both `Divisor.formalDivisorOfList` and `Divisor.Landmark.formalDivisorOfList`
exist with the same definition; the Landmark copy was local to avoid
an import cycle. Verify the definitions agree, then have Landmark
re-export the `Divisor.` version (or set up a temporary alias) so
consumers can begin transitioning. Defer the actual deletion of the
Landmark copy until Step 21 along with the rest of `EagenBuildLandmark.lean`.

Move `Divisor.Landmark.sumOnE` to `Divisor.sumOnE` (the function is
neutral). Leave a `Divisor.Landmark.sumOnE` alias for now.

### Step 3 — Build `eagenBuild_level0_singletons`

In `Divisor/EagenBuildRecursive.lean`, add the singletons-style
level-0 driver: input list of points, output list of accumulators
each carrying one input as a vertical-line polynomial (matching
`Landmark.levelInitSingleton` / `level0_singletons`).

Provide the obvious unfolding lemmas. Note that the singleton path
produces an acc list of the same length as the input (no pairing at
level 0), so odd-length input is trivially handled by the existing
`eagenBuild_level_step` odd-tail carry — no separate "odd-length
init theorem" needed.

### Step 4 — Extend `AccsListChordStep` per Step 1's decision

Under Step 1 = 1a: extend `AccsListChordStep`
(`EagenBuildRecursive.lean:6057`) to additionally cover the
**vertical-terminal** case (the `TerminalInv`-producing branch at
`EagenBuildRecursive.lean:6336`), so that the predicate is total
over the dispatcher in `eagenBuild_level_step` when restricted to
tangent-free input.

Under Step 1 = 1b: also extend to tangent-torsion and
tangent-smooth branches; this is contingent on the new combine
operations from Step 1's body.

Re-prove `accInvList_preservation_under_level_step` against the
extended predicate.

### Step 5 — Build chained-iterate predicate

Define `IteratedAccsListChordStep` (chained per-level extras analog
of `Landmark.IteratedLevelStepCombineExtras`). Prove
`accs_list_chord_step_of_iterated` (extract per-level extras from
the chain).

### Step 6 — Initial state for the singletons driver

Prove `AccInvList` initial state for `eagenBuild_level0_singletons`
under appropriate genericity hypotheses. The proof is largely
per-element (each acc is one vertical line through one input
point), substantially simpler than the adjacent-pair init theorem
at `EagenBuildRecursive.lean:5591`.

### Step 7 — Build `eagenBuild_correctness` (six substeps)

Each substep below is a separate commit. Together they discharge
the obligation that `EagenBuildRecursive.lean:6400` flags as future
work.

#### Step 7a — Tangent-free / no-subsum-collision propagation

Define (or re-use, under Step 1 = 1a) the predicate that survives
level-step iteration. Under 1a this is the no-subsum predicate on
the partition tree. Under 1b this is the existing
`LevelStepTangentFree` extended to the new tangent branches.

Prove the propagation lemma:
"`P_k`-holds on `xs` and `xs` non-empty ⇒ `P_{k+1}`-holds on
`eagenBuild_level_step xs`". Analog of
`accsListChordStep_propagates_under_level_step` mentioned at
`EagenBuildRecursive.lean:6405`.

#### Step 7b — Per-level genericity propagation

From the predicate of 7a, derive that `AccsListChordStep` (with
Step 4's extensions) holds at every level of the iteration. This
is the chained-form theorem on top of 7a.

#### Step 7c — Iterate preservation

Combine 7a + 7b + the existing `accInvList_preservation_under_level_step`
(extended by Step 4) to prove:
"`AccInvList xs accs` + chained predicate ⇒ `AccInvList`-holds on
the result of `eagenBuild_iterate n accs`".

#### Step 7d — Terminal vertical handoff

The terminal step of the recursion produces `TerminalInv` (not
`AccInv`) via `combine_higher_vertical` at
`EagenBuildRecursive.lean:6336`. Prove the mixed-handoff theorem:
"`AccInvList`-holds on a 2-element list with `a.point = -b.point`
⇒ `TerminalInv` holds on the result of
`combine_higher_vertical a b`". Already exists as
`terminalInv_of_accInvList_pair_via_vertical` at
`EagenBuildRecursive.lean:6336`; this substep verifies/extends it
for the singleton path's terminal shape.

#### Step 7e — Final output extraction

Compose 7c + 7d to prove `TerminalInv` holds on the iterated
result; extract the divisor identity:

```lean
divisorOfD E (eagenBuild_from_singletons E Ps) R
  = formalDivisorOfList E Ps R + residueDivisor E (sumOnE E Ps) R
```

under input genericity (from Step 1's decision), on-curve, sum-zero,
and `IteratedAccsListChordStep`.

#### Step 7f — Wrapper: divisor identity from `IsHonestForBinary` shape

State and prove a wrapper that takes the binary-protocol-shaped
hypotheses and produces the divisor identity from 7e. This is the
direct analog of `Landmark.eagenBuild_singletons_divisor_identity`
and is what Step 10 will consume.

### Step 8 — Construction-side splits and nonzero

Prove `splitsOnE_of_eagenBuild_from_singletons` (construction-side
splits, analog of `Landmark.splitsOnE_of_landmark`) and the
nonzero-output theorem. Both follow from Step 7's divisor identity
plus the existing per-chord `splitsOnE` machinery.

### Step 9 — Bridge to `eagenBuildC`

Extend `Divisor/EagenBuildComputable/Bridge.lean` to cover the
singletons driver:

```lean
theorem eagenBuildC_from_singletons_toCoordRingElt_eq :
    (eagenBuildC_singletons E.curveA E.curveB Ps).toCoordRingElt
      = eagenBuild_from_singletons E Ps
```

Reuses the existing recursion-bridge proof structure for
`eagenBuild_iterate` and the per-step bridges.

### Step 10 — Port `IsHonestForBinary` structures + method helpers (atomic)

Single landing unit (Codex flagged 11 and 12 in v2 as inseparable
unless temporary compatibility shims are used).

10.1 Edit `MAProverMsg.IsHonestForBinary` and
     `IsHonestForBinaryScaled` field types in
     `Divisor/IsHonestForBinary.lean`:
     - `h_toD_eq` references `eagenBuild_from_singletons E Ps`.
     - `h_sum_zero`, `h_divisor_identity_at` use
       `Divisor.sumOnE` / `Divisor.formalDivisorOfList`.

10.2 Re-prove the method-style helpers
     `IsHonestForBinaryScaled.toD_landmark`, `.toD_splitsOnE`,
     `.toD_divisor_identity`, `.toD_hAccount`, `.toD_residue_sum`
     against Steps 7/8.

Acceptance: structures elaborate; all method helpers close.

### Step 11 — Port length-N dispatch helpers

Re-state and re-prove `levelInitSingleton_chord_combine_extras`,
`chordSumX/Y`, `Length6Level1ChordConditions`, and the length-4 /
length-6 / length-8 `h_extras` builders
(`Divisor/IsHonestForBinary.lean:~1046–~2200`). Each retargets
recursive `AccsListChordStep` / `IteratedAccsListChordStep`.

### Step 12 — Port `admSet*_of_isHonestForBinary*` helpers

Port the four private helpers
(`Divisor/IsHonestForBinary.lean:~590–~700`). Coefficient reads
now come from `(eagenBuild_from_singletons E Ps).a.coeff k`.

### Step 13 — Port `ma_completeness_binary_extras` and chain forms

Port `ma_completeness_binary_extras`,
`ma_completeness_binary_with_scalar_extras`, their `_clean`
variants, and the eight
`ma_completeness_binary_admSet*_extras` / `_chain_admSet*`
theorems (`Divisor/IsHonestForBinary.lean:~500–~970`).

Each ported theorem proves the same
`(3·numZeros + 4) · |E.points|` bound and matches the existing
per-theorem axiom closure.

### Step 14 — Port length-N corollaries

Port length-2 / length-4 / length-6 / length-8 corollaries and
their `_clean`/`_chord` variants
(`Divisor/IsHonestForBinary.lean:~981–~2300`).

### Step 15 — Port certifying wrappers

Port the
`landmarkInvStrongCombineAffineExtras_of_combineCanFire_full`
chain (`Divisor/IsHonestForBinary.lean:~3000–~3500`).

### Step 16 — Point-skeleton certificate: port or delete

Decide whether the `native_decide`-friendly chord-chain certificate
(`PointChordCase`, `LevelStepPointChordCase`,
`IteratedPointChordCase`) needs to remain.

If retain: define recursive analogs (raw-coord points, no
`ECPoint.pointCombine`), derive Decidable instances, update
`Tests/PointCertificateDecidable.lean`, and update
`ma_completeness_binary_*_point_certificate` theorems in
`Divisor/IsHonestForBinary.lean`.

If drop: remove `_point_certificate` theorems from
`Divisor/IsHonestForBinary.lean` and delete
`Tests/PointCertificateDecidable.lean`.

Must precede Step 17 because the `fromWitness` chain consumes the
certificate.

### Step 17 — Port `binarySupport.fromWitness` chain

Port the `fromWitness` constructors
(`Divisor/IsHonestForBinary.lean:~2870–~3740`) against the
recursive driver. If Step 16 retained the certificate, wire the
`_point_certificate` variants through the new recursive
certificate; if dropped, those variants don't exist.

### Step 18 — Port `Tests/EndToEndSmoke.lean`

Repoint the `msg` construction to `eagenBuild_from_singletons` (or
to `eagenBuildC_singletons` via Step 9's bridge if computable
discharge is desired).

### Step 19 — Port `Tests/AxiomClosurePin.lean`

Remove the Landmark certifying-wrapper closure prints (lines
~191–192 in the existing file) or replace with recursive analogs
from Step 15. Confirm every remaining `#print axioms` line still
matches master.

### Step 20 — Verify Landmark namespace dead

Run `rg "Landmark\." Divisor/ Tests/`. Output must be empty modulo
the deprecation aliases from Step 2.

Run `rg "EagenBuildLandmark" Divisor/ Tests/`. Must be empty except
the import line in `Divisor/IsHonestForBinary.lean` (and possibly
`Tests/PointCertificateDecidable.lean` if Step 16 retained it via
direct import — unlikely after porting).

### Step 21 — Delete `Divisor/EagenBuildLandmark.lean`

Remove the file. Remove the `import Divisor.EagenBuildLandmark`
line wherever it appears. Remove the deprecation aliases left in
Step 2.

### Step 22 — Wire `eagenBuildC` into binary completeness

Add `_computable` companions for the chain-form completeness
theorems that take `eagenBuildC_singletons` (computable) via the
bridge from Step 9. Add a concrete `native_decide` smoke test
against the rejection bound on a small `q`.

### Step 23 — Final closure pin

Run `lake build`. Run `lake build Tests.AxiomClosurePin`. Diff the
closure output against master: every listed theorem must show
exactly the same axiom set, byte-for-byte. Includes the new
`_computable` companions from Step 22.

## Acceptance

* `Divisor/EagenBuildLandmark.lean` deleted.
* `Divisor.Landmark` namespace gone.
* `rg "Landmark\." Divisor/ Tests/` empty.
* `lake build` clean.
* `Tests/AxiomClosurePin.lean` shows the same axiom closures as
  master for every listed theorem (including any new
  `_computable` companions from Step 22).
* All `ma_completeness_binary_*` theorems prove the same rejection
  bound, routed through the recursive driver.
* `eagenBuildC_singletons` plugs into completeness via Step 9's
  bridge; concrete `#eval` + `native_decide` example passes.
