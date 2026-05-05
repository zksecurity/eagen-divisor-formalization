# Plan: 0/1-scalar completeness via constructive Eagen interpolation

## Goal

For dlog statements where each `wit.scalars i ∈ {0, 1}` (as `ZMod E.q`),
construct `msg.toD` via Eagen's recursive interpolation on the list

```
Ps = (-target) :: [ stmt.bases i | i ∈ Fin k, wit.scalars i = 1 ]
```

prove `MAProverMsg.isHonestFor`, and compose with `ma_completeness` to
get an axiom-clean completeness theorem `ma_completeness_for_binary` (and
its Hasse-clean variant `_clean_for_binary`) whose hypotheses are
- the dlog relation (`relDlog E stmt wit`),
- `wit.scalars i ∈ {0, 1}` for each `i`,
- distinctness of the *selected* bases (those with `scalars i = 1`),
- `wit.scalars i = 1 → stmt.bases i ∈ E.points`,
- `(stmt.target.1, -stmt.target.2) ∈ E.points`,
- the verifier-side `hAdm`, `hDeg*` checks (caller's responsibility).

No genericity hypothesis on subsums — those would require deciding
sub-sum vanishing on `E`, which is intractable for general dlog inputs.
The recursion proof handles all three branches (chord / vertical /
tangent) per pairing internally.

## Constraints

- No new `axiom`, `sorry`, `admit`.
- Closure of `ma_completeness_for_binary*` must equal closure of
  `ma_completeness*` (no new dependencies).
- Soundness side (`ma_extractable`, `ip_knowledge_sound`) byte-for-byte
  unchanged.
- Branch: `work/binary-completeness`, off `work/completeness`. Created.
- Do not sign commits; do not push.

## Pre-existing infrastructure

In `Divisor/EagenBuildRecursive.lean`:

- `eagenBuild_level0`, `eagenBuild_level_step`, `eagenBuild_iterate`
  definitions (lines 99, 155, 179).
- Three-branch dispatch on each pairing: `*_distinct`, `*_vertical`,
  `*_tangent` versions of `eagenBuild_level_step_cons_cons_*` (lines
  4949, 4967, 4987).
- `AccInv`, `TerminalInv`, `AccInvList` predicates (lines 243, 782,
  5449).
- Per-pair combine-step divisor identity for chord and vertical
  branches (eleven AccInv-form theorems for chord; vertical has
  TerminalInv form for the terminal sum-zero step).
- `accInvList_preservation_under_level_step` exists (line 6074) but is
  gated on the chord-only path.
- `eagenBuild_iterate_length_le_one_of_tangent_free` (line 5155) — the
  tangent-free hypothesis must be removed for our purposes since
  tangent-free preservation requires no-subsum-vanishes.

## Scope of work

### Phase 1 — `eagenBuild_correctness` without genericity gate

Generalize the existing per-pair preservation lemmas to dispatch on
all three branches, without assuming chord-only.

**1a. Tangent-branch step lemma** (~150–250 LOC, novel).

`accInv_combine_higher_tangent_step`: given `AccInv xs a` and
`AccInv ys b` with `a.point = b.point` (so the pairing takes the
tangent line at `a.point`), prove
`AccInv (xs ++ ys) (combine_higher_tangent E a b)`. The `combine_higher_*`
function for the tangent case may not exist yet — check for
`combine_higher_tangent` definition; if missing, define it.

The geometry: the tangent line at `a.point` has equation
`y - a.point.2 = ((3·a.point.1² + curveA) / (2·a.point.2)) · (x - a.point.1)`.
The "third intersection" with `E` is `-2·a.point` (as an ECPoint), which
becomes the new residue. If `a.point` is 2-torsion (`a.point.2 = 0`),
the tangent is vertical and the third intersection is at infinity
— this case routes through the vertical branch instead, so the tangent
branch only fires for non-2-torsion `a.point`.

Sub-lemmas (analogs of existing chord-case ones):
- divisor of the tangent-line `chordCoordRingElt` at `a = b`.
- divisible by `(X - a.point.1)²` after the tangent line vanishes
  doubly at `a.point`.
- `combine_higher_tangent_running_sum` (the new residue equals
  `-2·a.point`).
- `accInv_natDegree_normPoly` for the tangent combine output.

**1b. Vertical-branch as non-terminal AccInv** (~100–150 LOC).

Existing `terminalInv_combine_higher_vertical_step` produces `TerminalInv`,
which is the *terminal* form (residue = `O`, list summing to zero). For
non-terminal levels, when an internal pair has `a.point = -b.point`,
the vertical merge consumes both residues and the new residue is `O`
— but the recursion continues with `O` as the carried point.

The Eagen algorithm's handling of `O` as a residue: per Codex C5 in the
original plan,

> If an inner block sums to `O`, the residual is the identity and there
> is no affine chord through `−O`. Special-case: finalise that block's
> polynomial and skip the `−Q` step. The recursion then continues with
> one fewer slot at this level.

Translating to Lean: the EagenAccum `point : ECPoint E` field admits
`0 : ECPoint E`. When two adjacent accumulators have `a.point = -b.point`,
their merged accumulator has `point = 0` (infinity). The carry forward
is then "no point to pair against", which `level_step` skips on the
next iteration.

Need to verify the existing `EagenAccum` structure and `level_step`
recursion handle the `point = 0` case. If not, add the dispatch.

Sub-lemmas:
- `accInv_combine_higher_vertical_internal_step`: AccInv preservation
  when `a.point = -b.point` produces a new accumulator with
  `point = 0`.
- `level_step` skips `point = 0` accumulators on subsequent levels (or
  treats them as identity contributions).

**1c. AccInvList preservation under `level_step` (universal)**
(~150–250 LOC).

Generalize `accInvList_preservation_under_level_step` (line 6074) to
dispatch per-pair on which of the three branches each adjacent pairing
took. For each pair, apply the corresponding step lemma from 1a/1b
(or the existing chord lemma).

This is a list-induction. Three cases per pair, six total when
considering the carry from odd-length lists:
- chord-step pair → `combine_higher_distinct`.
- vertical-step pair → `combine_higher_vertical_internal`.
- tangent-step pair → `combine_higher_tangent`.

Carry handling for odd-length: the dangling element is forwarded
unchanged. Its AccInv carries through trivially.

**1d. `accInvList_preservation_under_iterate`** (~100–150 LOC).

Fold 1c over `n` iterations of `eagenBuild_iterate`. Termination: the
list length halves at each level (rounded up for odd), so reaches 1
in `ceil(log₂ |Ps|)` steps. The tangent-free hypothesis is *not* needed
for termination — it's purely combinatorial.

May need a "fuel ≥ length" variant: given fuel `n ≥ |xss|`, the iterate
converges to a singleton.

**1e. `eagenBuild_correctness`** (~150–250 LOC).

Final assembly. Given a non-empty list `Ps` with `Ps.sum = 0` on `E`
and all elements in `E.points`:

```lean
theorem eagenBuild_correctness
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hSumZero :
      (Ps.map (fun P => ECPoint.affine E P.1 P.2)).sum = 0)
    (hNonEmpty : Ps ≠ [])
    (hDistinct : Ps.Nodup) :
    ∀ R : ECPoint E,
      divisorOfD E (eagenBuild E Ps hSumZero) R = formalDivisorOfList E Ps R
```

Proof: `eagenBuild_level0 Ps` produces an `AccInvList` (initial state
has each accumulator's residual point matching the list element).
Iterate via 1d → singleton → its `TerminalInv` gives the divisor
identity for the full input list.

`hDistinct` rules out repeated points in `Ps`. With repeated points,
`formalDivisorOfList` would have coefficient ≥ 2 at the repeated
support point, which `eagenBuild` can't realize without multiplicity
machinery. Distinctness is the cleanest single restriction.

**Total Phase 1: ~750–1100 LOC.**

### Phase 2 — 0/1-scalar bridge

**2a. Build the input list `Ps`** (~50 LOC).

```lean
def selectedBasesList (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) : List (ZMod E.q × ZMod E.q) :=
  ((Finset.univ : Finset (Fin stmt.k)).filter
    (fun i => wit.scalars (hk ▸ i) = 1)).toList.map stmt.bases

def honestPs (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) : List (ZMod E.q × ZMod E.q) :=
  (stmt.target.1, -stmt.target.2) :: selectedBasesList E stmt wit hk
```

**2b. Sum-zero proof** (~50 LOC).

`relDlog E stmt wit` gives `target = Σ_i scalars i · bases i` on `E`.
With 0/1 scalars, this becomes `target = Σ_{i : scalars i = 1} bases i`,
hence `(-target) + Σ bases = 0` on `E`. Convert to list-sum form.

**2c. `IsHonestForBinary` structure** (~50 LOC).

```lean
structure MAProverMsg.IsHonestForBinary (E : ECSetup)
    (msg : MAProverMsg E.q) (stmt : DlogStatement E.q) where
  hk : ℕ            -- = stmt.k, threaded for convenience
  hk_eq : hk = stmt.k
  /-- Witness with all 0/1 scalars. -/
  wit : DlogWitness E.q
  hwit_k : stmt.k = wit.k
  h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1
  /-- The dlog relation. -/
  hRel : relDlog E stmt wit
  /-- The selected bases are distinct (no two with scalar 1 collide). -/
  h_selected_distinct :
    (selectedBasesList E stmt wit hwit_k).Nodup
  /-- target ≠ -B_i for any selected B_i (no internal cancellation). -/
  h_target_distinct_from_selected :
    (stmt.target.1, -stmt.target.2) ∉ selectedBasesList E stmt wit hwit_k
  /-- target on curve. -/
  h_target_on : (stmt.target.1, -stmt.target.2) ∈ E.points
  /-- Selected bases on curve. -/
  h_bases_on : ∀ i : Fin wit.k,
    wit.scalars i = 1 → stmt.bases (hwit_k ▸ i) ∈ E.points
  /-- msg.toD is the eagenBuild output. -/
  hSumZero :
    ((honestPs E stmt wit hwit_k).map
      (fun P => ECPoint.affine E P.1 P.2)).sum = 0
  h_toD_eq : msg.toD = eagenBuild E (honestPs E stmt wit hwit_k) hSumZero
  /-- Scalars match in ZMod q. -/
  h_m_match : ∀ i : Fin msg.k, msg.m i = wit.scalars (hwit_k ▸ hk_eq ▸ i)
```

Distinctness fields (`h_selected_distinct`,
`h_target_distinct_from_selected`) replace the no-subsum-vanishes
genericity. They rule out *repeated points in the list*, not internal
zero-subsums — those are handled by the recursion's three-branch
dispatch.

**2d. `splitsOnE_msg_toD_for_binary`** (~50–100 LOC).

By `eagenBuild_correctness`, divisor of `msg.toD` is `formalDivisorOfList`
of `honestPs`, which has support exactly the list elements (all in
`E.points`). So every affine zero of `msg.toD` is `F_q`-rational.
splitsOnE follows by support analysis.

**2e. Divisor identity** (~50–100 LOC).

`formalDivisorOfList (honestPs ...)` equals `honestDivisorCoeffs`
pointwise. At infinity: `formalDivisorOfList = -|honestPs|` and
`honestDivisorCoeffs = -degE`, so we need `|honestPs| = degE(msg.toD)`.
By `eagenBuild`'s output, `degE = |Ps| = 1 + #{i : scalars i = 1}`, which
equals `|honestPs|`. At affine `R`: `formalDivisorOfList = #{P ∈ Ps : P = R.coords}`
which is `0` or `1` for distinct `Ps`. `honestDivisorCoeffs` at `R` is
`(if R = -target then 1 else 0) + Σ_{i : bases i = R} scalars i`. With
0/1 scalars and distinct selected bases, this also reduces to 0 or 1,
matching pointwise.

**2f. `isHonestFor_of_isHonestForBinary`** (~50 LOC).

Compose 2d, 2e, structure fields into the five conjuncts of `isHonestFor`.

**Total Phase 2: ~250–400 LOC.**

### Phase 3 — `ma_completeness_for_binary{,_clean}`

**3a. `ma_completeness_for_binary`** (~30 LOC).

Thin composition with `ma_completeness`. Caller supplies `hAdm`,
`hDeg`, `hDegK`. Bridge supplies `isHonestFor` via Phase 2.

**3b. `ma_completeness_clean_for_binary`** (~30 LOC).

Same with the Hasse-clean bound.

**3c. Optional helper `admSetMax_holds_for_binary`** (~10 LOC).

Trivial: `eagenBuild ... ≠ 0`, so `admSetMax (msg.polyA, msg.polyB)`.
Caller using `admSetMax` gets `hAdm` for free.

**Total Phase 3: ~70 LOC.**

## Verification

1. `lake build Divisor` — clean, no `sorry`.
2. `lake env lean Tests/AxiomClosurePin.lean`:
   - `ma_completeness_for_binary` + `_clean_for_binary` printed,
     same axiom set as `ma_completeness` and `_clean`.
   - Soundness side byte-for-byte unchanged.
3. Existing `ma_completeness_for_length4Simple` + `_clean_for_length4Simple`
   should still build (the binary bridge specializes to length-4 simple
   when `k = 3` and all three scalars are 1; the older length-4 bridge
   may become dead code, removable in a follow-up).
4. Smoke test: `Tests/IncrementalSmokeTest.lean` — invoke the binary
   bridge on a hand-checked instance over `F_5`, confirm `eagenBuild`
   output divides as expected.

## Risk register

- **Tangent branch (1a)** is the most novel. Existing combine-step has
  scattered helpers but no full `AccInv → AccInv` chain for the
  tangent case. May find that the `combine_higher_tangent` function
  itself needs to be defined first.
- **Vertical-as-non-terminal (1b)** requires `EagenAccum.point = 0`
  case to be handled by `level_step`. If not currently handled, that's
  extra plumbing.
- **Distinctness vs sub-sum**: even with `h_selected_distinct` and
  `h_target_distinct_from_selected`, internal cancellations during
  recursion can still produce `point = 0` accumulators (e.g.,
  `B_i + B_j + B_k = 0` for three selected bases makes their merged
  accumulator's residue = `O`). That's the vertical-internal case, which
  1b handles. So distinctness alone is sufficient input-side restriction.

## Estimate

Total: **~1100–1600 LOC** of new theorem/proof work, distributed roughly
70/25/5 across phases 1/2/3. Single milestone commits per phase.

## Open question for Codex (before starting)

The novel piece is the tangent branch (1a). Codex should confirm:
- Whether `combine_higher_tangent` already exists (file is large,
  ~8000 LOC; easy to miss).
- Whether the combine-step chord/vertical lemmas can be straightforwardly
  adapted to tangent, or whether tangent has structural differences
  (e.g., the `(X - a.point.1)²` factor instead of `(X - a.point.1)`)
  that require new infrastructure.
- Whether the vertical-internal case (`point = 0` carry) is already
  modeled in `EagenAccum` and `level_step`, or needs to be added.
