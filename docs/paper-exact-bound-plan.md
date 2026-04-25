# Plan: Reach paper-exact bound `18·(d+k)·|E|`

Self-contained plan to tighten `Divisor.ma_extractable`'s bound from
its current state to the paper's exact bound.

## Starting state (tag `session-end` in git)

`Divisor.ma_extractable` (in `Divisor/ExtractorBridge.lean`) currently
proves:

```
((validPairs E).filter (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
  ≤ 54 * (stmt.degBound + stmt.k + 6) * E.points.card
```

Properties:
- Purely linear in `(d + k)·|E|` (no quadratic term).
- 7 user-defined axioms (no `sorryAx`):
  `bivariate_poly_zeros_on_ExE_le`,
  `chord_fiber_product_eq_normZ_under_split`,
  `chord_sum_eq_chord_fiber_product_logDeriv`,
  `CoordRingElt.divisor_group_sum_zero`,
  `ECPoint.add_assoc`, `ECPoint.add_comm`, `ECPoint.neg_add_cancel`.
- One unused sorry: `clearedFullPoly_swap_signed` (chord-symmetry
  dead-end, not in any proof chain).

## Target

`sections/ip.tex:478` Event_NotEq bound:

```
((validPairs E).filter (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
  ≤ 18 * (stmt.degBound + stmt.k) * E.points.card
```

Three independent slacks separate current from target:

| Slack | Source | Plan phase |
|---|---|---|
| `54 → 36` (linear coefficient `+18` boundary term) | `log_deriv_sz_paper` splits into `36·(d+k+6)·|E|` (Lang-Weil core) + `18·(d+k+6)·|E|` (F1-F8 boundary) | Phase 1 |
| `36 → 18` (factor of 2) | Lang-Weil axiom states `2·(dX+dY)·|E|`; the `2` accounts for two Y-branches per X | Phase 2 |
| `(d+k+6) → (d+k)` (offset `+6`) | Uniform `lamDen^N` clearing scale in `clearedFiberPoly` adds `+1` (D), `+4` (`dxdz`), `+1` (`-P` line) | Phase 3 |

Phases are independent and parallelisable.

---

## Phase 1 — Boundary unification (`54 → 36`)

**Goal:** drop the `+18·(d+k+6)·|E|` boundary contribution from
`logDerivCheckFn_undefined_set_bound` by absorbing the denom-undefined
pairs into the Lang-Weil zero set.

**Current decomposition** (`Divisor/ClearedFullPoly.lean`,
`log_deriv_sz_paper`):
```
badNE.card ≤ defBad.card + undefAll.card
         ≤ 36·(d+k+6)·|E| + 18·(d+k+6)·|E|
         = 54·(d+k+6)·|E|
```
where `defBad = bad ∩ {denom ≠ 0}` (Lang-Weil on `clearedFullPoly`)
and `undefAll = {denom = 0}` (F1-F8 union bound).

### Approach A — augmented polynomial

Define a polynomial `augPoly` that vanishes on BOTH bad pairs AND
denom-zero pairs:

```lean
noncomputable def augPoly (D P k B m) : FourVarPoly E.q :=
  clearedFullPoly E D P k B m   -- vanishes on bad pairs (proven)
  -- TODO: + something that vanishes on denom-zero pairs
```

If we set `augPoly = clearedFullPoly · denomFull` where `denomFull`
is the 4-variate lift of `logDerivCheckFnDenom`, then `augPoly`
vanishes wherever EITHER `clearedFullPoly = 0` OR `denomFull = 0`.
But this MULTIPLIES degrees: bi-x-degree becomes
`(9·(d+k+6) + (something), 9·(d+k+6) + (something))`. Lang-Weil bound
worsens proportionally.

**Verdict**: probably not net improvement. Skip.

### Approach B — strengthen `clearedFiberPoly_identity` (PREFERRED)

Show that `clearedFiberPoly_identity` HOLDS WITHOUT `hDef` (i.e., the
identity is a polynomial identity in `(A₀, A₁)`, not just a pointwise
identity on the `hDef ∧ hNV` open set).

The current proof uses field arithmetic with `hDef` to clear
denominators. Both LHS (`bivEval (clearedFiberPoly ...) A₁`) and RHS
(`(A₁.1 - A₀.1)^N · logDerivCheckFnCleared`) are polynomial in
`(A₀, A₁)`. If the polynomial identity holds, then on denom-zero
pairs:
```
bivEval₂ clearedFullPoly = (A₁.1-A₀.1)^N · logDerivCheckFn · denom
                         = (A₁.1-A₀.1)^N · logDerivCheckFn · 0  = 0
```

Note: in `ZMod q`, polynomial identities can fail to extend from
sub-domains because `x^q - x ≡ 0` on `F_q` but not as polynomials.
The identity needs to hold AS POLYNOMIALS, not just pointwise.

**Sub-task 1.1**: Refactor `clearedFiberPoly_identity` (in
`Divisor/ClearedPolyForm.lean:2172`) to prove the identity in the
polynomial ring `(ZMod q)[X][X]` directly (without `hDef` hypothesis).
Reformulate the existing proof to use polynomial-equality reasoning
rather than field arithmetic.

**Sub-task 1.2**: Once identity holds without `hDef`, modify
`bivEval₂_clearedFullPoly_eq_zero_of_bad` (in
`Divisor/ClearedFullPoly.lean`) to drop the `hDef` hypothesis.
`clearedFullPoly` then vanishes on the FULL bad set (not just
denom-defined part).

**Sub-task 1.3**: Replace `log_deriv_sz_paper`'s split-then-add with
a single Lang-Weil application:
```
badNE ⊆ {bivEval₂ clearedFullPoly = 0} on E×E
badNE.card ≤ 36·(d+k+6)·|E|
```
Update `ma_extractable`'s bound from `54·(…)` to `36·(…)`.

**Risk**: proof restructuring may be heavy. If Approach B fails,
explore Approach A (with care to bound the degree blow-up).

**Bound after Phase 1**: `36·(d+k+6)·|E|`.

---

## Phase 2 — Y-linearity-aware Lang-Weil (`36 → 18`)

**Goal:** halve the Lang-Weil bound for `clearedFullPoly` by
exploiting that, after reduction modulo the curve relations
`Y_i^2 = X_i^3 + A·X_i + B`, the polynomial is LINEAR in each `Y_i`
(degree ≤ 1 in `X 1` and `X 3`).

The current axiom gives `2·(dX + dY)·|E|` — the factor of 2 absorbs
two `Y_i`-branches per `X_i`. For Y-linear polynomials, each X-fibre
gives at most one Y-value per branch, shaving the factor of 2.

### Sub-task 2.1: define `bi_y_linear`

```lean
def bi_y_linear (E : ECSetup) (f : FourVarPoly E.q) : Prop :=
  f.degreeOf 1 ≤ 1 ∧ f.degreeOf 3 ≤ 1
```

(degree ≤ 1 in `X 1 = Y_0` and `X 3 = Y_1`).

### Sub-task 2.2: derive a Y-linearity-aware Lang-Weil

```lean
theorem bivariate_poly_zeros_on_ExE_le_y_linear
    (E : ECSetup) (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hYlinear : bi_y_linear E f)
    (hNonzero : ∃ A₀ A₁ ∈ E.points, bivEval₂ f A₀ A₁ ≠ 0) :
    {pairs vanishing}.card ≤ (dX + dY) * E.points.card
```

Half of the existing axiom's bound. Whether this is derivable from
the existing `bivariate_poly_zeros_on_ExE_le` axiom is an open
question — it might require a modified Lang-Weil argument with
Y-linearity baked in. If not derivable, would need a NEW axiom,
which violates the no-new-axioms constraint.

**Sub-task 2.2a**: Investigate whether the existing axiom's
`2·(dX+dY)` factor is essentially optimal or can be tightened for
Y-linear polynomials. Look at the axiom's docstring + Lang-Weil
1954 paper Theorem 1.

### Sub-task 2.3: define `%ₘ₂` and prove `clearedFullPoly` is Y-linear MOD CURVE

```lean
noncomputable def MvPolynomial.modByMonic₂ (f g h : FourVarPoly q) : FourVarPoly q := ...
notation:65 f " %ₘ₂ " "(" g "," h ")" => MvPolynomial.modByMonic₂ f g h

theorem clearedFullPoly_y_linear_mod_curve (D P k B m) :
    bi_y_linear E (clearedFullPoly E D P k B m %ₘ₂ (curveEq₀ E, curveEq₁ E))
```

`clearedFullPoly` mod (curveEq₀, curveEq₁) is Y-linear: each `Y_i^2`
gets reduced to `X_i^3 + A·X_i + B`. The reduction is defined and
computable — the key is to formalise it cleanly.

### Sub-task 2.4: apply the Y-linearity-aware bound

If 2.2 gives `(dX+dY)·|E|` and 2.3 gives Y-linearity, combine to
update `log_deriv_sz_paper_core`'s bound to `18·(d+k+6)·|E|`.

**Risk**: 2.2 may genuinely require a new axiom. Investigate first
before proceeding.

**Bound after Phase 2** (if 2.2 succeeds): `18·(d+k+6)·|E|`.

---

## Phase 3 — Drop the `+6` offset (`(d+k+6) → (d+k)`)

**Goal:** remove the `+6` from the bi-x-degree bound on
`clearedFullPoly` by replacing the uniform `lamDen^N` clearing scale
with per-factor mod-curve reduction.

Current `clearedFullPoly` has bi-x-degree `9·(d+k+6)` per axis. The
`+6` decomposes as:
- `+1` for D's degE
- `+4` from `dxdzAllScaled` (three `dxdz` factors + corrections via `lamDen^4`)
- `+1` for `-P` line factor (`linesProductScaled` has `lamDen^(k+1)`)

These offsets exist because `clearedFiberPoly` was built with uniform
clearing `lamDen^N` to keep the algebra uniform. The paper reduces
mod the curve equation directly in the coordinate ring, achieving
`9·(d+k)` without these.

### Sub-task 3.1: redefine `clearedFullPoly` with per-factor clearing

Major refactor of `Divisor/ClearedFullPoly.lean`. Each Full-component
gets its own scaling factor, and the assembly carefully combines them
so the final `clearedFullPoly` has bi-x-degree `9·(d+k)` per axis.

### Sub-task 3.2: re-prove identity, degree bound, nonzero witness

The compatibility chain `bivEval₂ clearedFullPoly = bivEval clearedFiberPoly`
needs to be re-derived for the new structure. Most of the helpers
(`varA*y_bi`, `lamDen_bi`, `line_bi`, `x₂Scaled_bi`, etc.) carry over
but the assembly changes.

Either re-prove `clearedFullPoly_identity` directly with the new
scaling, or re-define `clearedFiberPoly` (in
`Divisor/ClearedPolyForm.lean`) to match.

### Sub-task 3.3: re-wire downstream

`log_deriv_sz_paper_core`, `sigma_matching_*`, `ma_extractable` all
use the bi-x-degree bound. Update to `9·(d+k)`.

**Risk**: ~500 LOC rewrite across `ClearedFullPoly.lean` and possibly
`ClearedPolyForm.lean`. Many helper lemmas need updating.

**Bound after Phase 3**: `18·(d+k)·|E|` — paper-exact (when combined
with Phases 1 + 2).

---

## Phase 4 — Cleanup

After Phases 1-3:

- Remove dead infrastructure now unreferenced:
  `log_deriv_sz` (in `ClearedPolyForm.lean`),
  `logDerivCheckFn_fiber_count_bound`,
  `logDerivCheckFn_badA₀_bound`,
  `resultantX_*` family,
  `extractorSucceeds_of_logDerivCheck_identically_zero_general`,
  `extracted_scalars_valid` (general case),
  `extractor_succeeds_and_groupSumZero`,
  `distinctSigma_exists`,
  `log_deriv_nonvanishing_criterion` (T5, in `PolyFibK.lean`).
- Resolve `clearedFullPoly_swap_signed`: either prove it (the
  signed version IS true and provable with care) or delete it.
- Re-run `#print axioms ma_extractable` and verify the axiom list
  matches expectations (still 7 user axioms, no `sorryAx`).
- Run a full `lake build` and confirm zero warnings about unused
  definitions.

---

## Schedule

| Phase | Sub-tasks | Estimated Aristotle dispatches |
|---|---|---|
| 1 (boundary unification) | 1.1–1.3 | 1 medium |
| 2 (Y-linearity) | 2.1–2.4 | 3 (2.2 risky) |
| 3 (offset drop) | 3.1–3.3 | 3 (3.1 major refactor) |
| 4 (cleanup) | — | 1 medium |

Total: ~8 Aristotle dispatches, ~1-2 sessions.

## Phase ordering and parallelism

Phases are independent and can be parallelised:

- Phase 1 needs no other phase.
- Phase 2 needs no other phase (only the `%ₘ₂` definition for 2.3,
  which is a self-contained sub-task).
- Phase 3 is independent of 1 and 2 but the most invasive.

Recommended order: run Phase 1 first (smallest, most likely to
succeed). Then dispatch Phases 2 and 3 in parallel (each in its own
Aristotle dispatch, modifying mostly disjoint code regions — Phase
2 touches the Lang-Weil layer, Phase 3 the polynomial construction).
Cleanup (Phase 4) after all three converge.

## Stop conditions

If any phase requires a NEW axiom not in the current 7-axiom set
(or the 10 axioms originally planned in
`docs/bivariate-sz-paper-faithful.md`), STOP and surface the gap.
The current axiom usage is established and stable; new axioms warrant
a re-planning step.

Specific risk: Phase 2.2 (Y-linearity-aware Lang-Weil) may not be
derivable from the existing axiom and may genuinely require a new
axiom. Investigate before committing to the full proof.

---

## Delegating to Aristotle

The orchestrator (Claude session) prepares scaffolding and dispatches
Aristotle. **Aristotle fills proof `sorry`s; it does NOT fill `def`
sorries or refactor architecture.** All `def`s, theorem statements,
new types, and structural changes must be in place BEFORE dispatch.

### Workflow per phase

1. **Scaffold first.** Add new `def`s, `theorem` statements with
   `sorry` body, helper lemmas (also `sorry`d), and any new
   notations/abbreviations. Run `lake build` — must compile with only
   "uses sorry" warnings.
2. **Commit the scaffold** (separate from the dispatch). This makes
   the diff readable and lets you re-dispatch on the same scaffold if
   the first attempt fails.
3. **Write the prompt** to `/tmp/aristotle-dispatch/prompt_<phase>.txt`.
   Include:
   - Exact theorem statements (copy-paste from file).
   - All lemma names Aristotle should use, with their signatures.
   - Paper context VERBATIM if the proof is paper-aligned.
     Aristotle has no access to `~/paper/` — paste the relevant
     sections directly.
   - Specific approach hints (Approach A / B / C as appropriate).
   - Fallback instructions: "if X is intractable, weaken to Y" or
     "leave sorry with documentation".
   - Build command: `lake build Divisor.<TargetFile>`.
   - Hard constraints: "no new axioms", "only modify `<file>.lean`",
     "build must pass", "partial closures OK".
4. **Dispatch** with `aristotle submit "$(cat <prompt>)" --project-dir <repo>`.
   Capture the project ID.
5. **Wait via background task**: `aristotle result <id> --wait
   --destination <tar>` with `run_in_background: true`. Optionally
   set up a progress monitor with the `Monitor` tool for periodic
   notifications.
6. **Merge** when the wait task completes:
   - Extract the tarball.
   - Diff against your current file.
   - Apply the proven sub-sorries; KEEP your scaffolding's docstrings
     where possible.
   - Verify build.
   - Commit with a message citing the Aristotle project ID.
7. **Inspect remaining sorries** — Aristotle often leaves partial
   progress with sub-sorries it couldn't close. These are good
   targets for follow-up dispatches.

### Per-phase prompt skeletons

#### Phase 1 — Boundary unification (Approach B)

```
Refactor `clearedFiberPoly_identity` (in
`Divisor/ClearedPolyForm.lean:2172`) to drop the `hDef` hypothesis,
making it a polynomial identity in `(ZMod q)[X][X]` rather than a
pointwise identity on the `hDef ∧ hNV` open set.

Both LHS (`bivEval (clearedFiberPoly ...) A₁`) and RHS
(`(A₁.1 - A₀.1)^N · logDerivCheckFnCleared E D P k B m A₀ A₁`) are
polynomial expressions in (A₀.1, A₀.2, A₁.1, A₁.2). The current proof
uses field arithmetic with `hDef` to clear denominators. Reformulate
to use polynomial-equality reasoning directly.

[paste full current proof of `clearedFiberPoly_identity` here]

[paste relevant `logDerivCheckFnCleared` and `logDerivCheckFn` defs]

Once `clearedFiberPoly_identity` holds without `hDef`:
1. Update `bivEval₂_clearedFullPoly_eq_zero_of_bad` (in
   ClearedFullPoly.lean) to drop `hDef`.
2. Update `log_deriv_sz_paper` to merge `defBad` and `undefAll` into
   a single Lang-Weil application, dropping the `+18·(d+k+6)`
   boundary contribution.
3. The bound becomes `36·(d+k+6)·|E|`.

If the polynomial-identity reformulation is intractable, leave
`clearedFiberPoly_identity` as-is and explore Approach A
(augmented polynomial) or Approach C (direct accept-set count).

[hard constraints]
```

#### Phase 2 — Y-linearity Lang-Weil

```
Prove or refute the Y-linearity-tightened Lang-Weil:
`bivariate_poly_zeros_on_ExE_le_y_linear`. Statement:

[paste full statement]

Prove from the existing `bivariate_poly_zeros_on_ExE_le` axiom.
Strategy: for each (A₀.1, A₁.1) pair (X-fibre), Y-linearity gives
at most 1 (Y_0, Y_1)-completion per X-fibre that satisfies the curve
equation, vs 2 in the general case. Hence factor of 2 saved.

If this is NOT derivable from the existing axiom (the existing
axiom's `2·(dX+dY)` may be tight for non-Y-linear polynomials AND
we cannot exploit Y-linearity classically), report this finding
and STOP — adding a new axiom requires re-planning.

[paste axiom statement + docstring]

If the proof works, then prove `clearedFullPoly_y_linear_mod_curve`
(define `%ₘ₂` first, an MvPolynomial.modByMonic for two equations) and
combine to get the `18·(d+k+6)·|E|` bound.

[hard constraints]
```

#### Phase 3 — Offset drop

```
Redefine `clearedFullPoly` (in `Divisor/ClearedFullPoly.lean`) using
per-factor mod-curve reduction instead of the uniform `lamDen^N`
clearing scale. Target bi-x-degree: `9·(d+k)` per axis (drop the
`+6`).

The current uniform-clearing structure (`Divisor/ClearedPolyForm.lean`)
inherits a scaling `N = D.degE + k + 6`:
- `+1` for D's degree (DAtA₂Scaled scaling)
- `+4` from dxdzAllScaled (three dxdz factors + corrections via lamDen^4)
- `+1` for the `-P` line factor

To drop these:
1. Introduce per-factor scaling per atom, NOT uniform.
2. Use `MvPolynomial.modByMonic` (or `%ₘ₂`) to reduce mod the curve
   equations directly in the coordinate ring during the assembly,
   so each Y_i^2 becomes X_i^3 + A·X_i + B without needing a separate
   clearing factor.

This is a major refactor of `clearedFullPoly`'s 8 summands and their
assembly. Each summand and its compat lemma need to be re-derived
with the new scaling.

[paste all current Full atom definitions]

[paste current clearedFullPoly assembly]

After the refactor:
- `clearedFullPoly_bi_x_degree_le` updates to `9·(d+k)` (without `+6`).
- Compat with old `clearedFiberPoly` may break — either re-prove
  `clearedFullPoly_identity` directly, or re-define
  `clearedFiberPoly` to match.
- Downstream `log_deriv_sz_paper_core` updates to `36·(d+k)·|E|`.
- Combined with Phase 1 (boundary unification): `36·(d+k)·|E|` total.
- Combined with Phase 2 (Y-linearity): `18·(d+k)·|E|` — paper-exact.

This is the most invasive phase. Expect ~500 LOC of refactor across
ClearedFullPoly.lean and possibly ClearedPolyForm.lean.

[hard constraints]
```

### Tips drawn from prior dispatches

- **Project size**: `divisors-faithful` is ~1MB of source. Aristotle
  takes 10-90 minutes per dispatch depending on complexity. Queue
  times can be 30+ minutes during peak load.
- **Multiple dispatches in parallel**: Aristotle handles concurrent
  jobs; submit independent sub-tasks separately and merge results.
  Conflicts arise only if jobs touch the same theorem in the same
  file.
- **Partial closures are common**: Aristotle often closes 2-3
  sorries out of 4 in a dispatch. Re-prompt for the remainder with
  more focused hints.
- **`COMPLETE_WITH_ERRORS`**: still download and inspect the result
  — it may have made structural progress (renamed lemmas, added
  helpers) that's worth merging even if a sorry remains.
- **Membership hypotheses**: If a lemma needs `Q k ∈ E.points` or
  `R j ∈ E.points` and there's no proof in context, ADD the
  hypothesis and propagate to callers. Don't expect Aristotle to
  invent missing hypotheses.
- **Use `aristotle list --status IN_PROGRESS` to monitor**, and
  `aristotle list --limit N` for recent history.
- **Prompt iteration**: if a dispatch fails to close anything, the
  prompt was likely too vague. Add concrete strategy hints
  ("Approach A", "use lemma X from file Y") and paper context.
- **`#print axioms <theorem>`**: run after each phase to verify no
  new axioms have crept in. Append `#print axioms ma_extractable` to
  `Divisor.lean` (top-level) — the build prints the list as an
  `info` diagnostic.
