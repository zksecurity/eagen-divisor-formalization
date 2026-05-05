# Plan: remove `principal_divisor_iff` from `ma_completeness*` closure

## Context

Repository: `/Users/rot256/src/divisors`. Lean 4 / Mathlib formalization
of the MA protocol (Eagen, arXiv:2206.13099). Branch `work/completeness`.

After the `weil_reciprocity_honest` axiom was discharged via Eagen's
incremental construction (length-4 simple bridge), the closure of
`ma_completeness` and `ma_completeness_clean` is:

- `propext`, `Classical.choice`, `Quot.sound` (Lean kernel)
- `Divisor.chord_fiber_product_eq_normZ_under_split` (project axiom)
- `Divisor.principal_divisor_iff` (project axiom — Silverman III.3.5)
- `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`

The first and third project axioms are legitimately used in the
log-derivative chain. **`principal_divisor_iff` is currently dead
weight** — present only because of a round-trip in the bridge.

### The round-trip

`MAProverMsg.isHonestFor` (`Divisor/Protocol.lean:206`) carries five
conjuncts. Two of them are relevant here:

```lean
∧ IsPrincipal E (honestDivisorCoeffs E stmt wit hk msg)
∧ (∀ R : ECPoint E,
    divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
```

The second (the divisor identity) commits to an explicit polynomial
`msg.toD` whose divisor IS the honest divisor coefficient function.
So `msg.toD` is itself the rational-function witness; `IsPrincipal`
adds nothing new.

Currently:

- **mpr step** (`isPrincipal_honestDivisorCoeffs_for_length4Simple`,
  `Divisor/EagenBuildRecursive.lean:8495`) — the bridge proves
  `Σ coeffs = 0` and `Σ [coeffs]·P = 0`, then invokes
  `principal_divisor_iff.mpr` (line 8507) to convert to `IsPrincipal`.
- **mp step** (`honestDivisorCoeffs_deg_zero_of_isHonestForExplicit`,
  `Divisor/EagenBuildRecursive.lean:7180`) — the consumer takes
  `IsPrincipal` from `isHonestFor` and immediately destructs via
  `principal_divisor_iff.mp` (line 7190) to recover `Σ coeffs = 0`.
- The destructed `Σ coeffs = 0` feeds
  `honestDivisorCoeffs_affine_sum_eq_degE`
  (`Divisor/EagenBuildRecursive.lean:7315`), which is then used at
  line 7323.

The bridge built sum-zero, packed it into `IsPrincipal`, immediately
unpacked it back to sum-zero. Drop the middleman and the axiom
disappears from completeness's closure.

### Why the Eagen algorithm IS sufficient

The divisor identity (third conjunct of `isHonestFor`) gives us
`divisorOfD E msg.toD = honestDivisorCoeffs`. This is a *concrete*
function divisor — it's `divisorOfD` of an explicit `CoordRingElt`,
not an opaque "exists f" claim. So the existence half of principality
is built in.

For the consumer's only use of `IsPrincipal` (extracting
`Σ honestDivisorCoeffs = 0`), we can prove this directly:

1. By divisor identity, `Σ honestDivisorCoeffs = Σ divisorOfD msg.toD`.
2. `divisorOfD E D` of any nonzero `D` is supported in
   `insert 0 affinePoints`. The infinity coefficient is
   `-(normPoly E D).natDegree`.
3. The affine sum `Σ_{R ∈ affinePoints} ordAt(D, R)` equals
   `(normPoly E D).natDegree` *under* `splitsOnE E D`
   (`sum_ordAt_eq_natDegree_under_split`,
   `Divisor/OrdP/LocalRing.lean:754`).
4. For the honest `msg.toD`, `splitsOnE` follows from the divisor
   identity: every zero of `msg.toD` on `E` lies in the support
   of `honestDivisorCoeffs`, which is a finite set of `F_q`-rational
   points (target `−P` and the bases `B_i`).

So `Σ divisorOfD msg.toD = (normPoly degree) + (-normPoly degree) = 0`
without any reference to `IsPrincipal`.

## Hard constraints (carried over from original plan)

- No new `axiom`, `sorry`, `admit`.
- Do **not** modify `ma_extractable`, `ip_knowledge_sound`, or any
  axiom they depend on. `ma_extractable` does NOT use
  `principal_divisor_iff` — confirm via `Tests/AxiomClosurePin.lean`
  unchanged on the soundness side.
- Do not sign commits (`git -c commit.gpgsign=false commit`).
- Do not push.
- Closure pin must show `principal_divisor_iff` REMOVED from
  `ma_completeness` and `ma_completeness_clean`.

## Codex review corrections (integrated)

The original plan was reviewed by Codex. Substantive findings:

- **Step 1 was not provable as stated.** `divisorOfD` is indexed over
  `ECPoint E` (rational points only); non-`F_q` roots of `normPoly`
  are invisible to it. `sum_ordAt_fst_eq_eq_rootMult` (`Divisor/OrdP/LocalRing.lean:640`)
  only gives the equality at rational fibers; for `α` with no rational
  lift we only have `≤` (`sum_ordAt_fst_eq_le`, line 715). So we
  cannot pinch and conclude `splitsOnE` from the divisor identity alone.
- **Dropping `IsPrincipal` with no replacement weakens `isHonestFor`
  too much.** The generic completeness path already derives
  `splitsOnE` from `h_honest` (`EagenBuildRecursive.lean:8645`),
  which currently runs through `principal_divisor_iff.mp` for the
  accounting equality. Replacement must carry equivalent strength.
- **Round-trip diagnosis stands.** Bridge packs sum-zero +
  group-sum-zero into `IsPrincipal`; consumer immediately destructs
  to recover sum-zero. But the right cure is to *replace* the
  conjunct with something tighter and more directly usable, not
  to delete it.
- **The constant-unit edge case is moot.** `(C c, 0)` has
  `degE = 3` but `normPoly` natDegree 0, so the divisor identity
  never holds for it. No need to special-case.

The revised plan replaces `IsPrincipal honestDivisorCoeffs` with
**`splitsOnE E msg.toD`**, which is exactly what the consumer needs
and which the bridge can prove directly from the explicit Eagen
construction (the four affine roots are the four `F_q`-rational
points `B_i`).

## Refactor steps

### Step 1 — replace `IsPrincipal` conjunct with `splitsOnE`

Edit `Divisor/Protocol.lean:206`:

```lean
def MAProverMsg.isHonestFor (E : ECSetup) (msg : MAProverMsg E.q)
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hkm : stmt.k = msg.k) : Prop :=
  (∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
  ∧ splitsOnE E msg.toD                                      -- replaces IsPrincipal
  ∧ (∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
  ∧ (stmt.target.1, -stmt.target.2) ∈ E.points
  ∧ (∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
```

Same arity, conjunct positions unchanged — every `h_honest.2.1`
projection now yields `splitsOnE` instead of `IsPrincipal`.
**Downstream destructuring shape is preserved**, only the *meaning*
of `h_honest.2.1` changes.

Update doc comment (`Divisor/Protocol.lean:189-205`) to describe
splitting as the contract instead of principality.

### Step 2 — reroute `honestDivisorCoeffs_deg_zero_*` through `splitsOnE`

Rewrite `honestDivisorCoeffs_deg_zero_of_isHonestForExplicit`
(`Divisor/EagenBuildRecursive.lean:7180`) to use `splitsOnE` instead
of `IsPrincipal`:

```lean
theorem honestDivisorCoeffs_deg_zero_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    ∃ hFinSupp : Set.Finite (Function.support
        (honestDivisorCoeffs E stmt wit hk msg)),
      ∑ P ∈ hFinSupp.toFinset, honestDivisorCoeffs E stmt wit hk msg P = 0
```

Proof:

1. `h_split : splitsOnE E msg.toD := h_honest.2.1`.
2. `h_div_id := h_honest.2.2.1` (divisor identity).
3. By divisor identity, `honestDivisorCoeffs = divisorOfD E msg.toD`,
   so finite-support is inherited from `divisorOfD_finiteSupport`.
4. Sum decomposes:
   `Σ divisorOfD msg.toD R = divisorOfD msg.toD 0 + Σ_{R∈affinePoints} divisorOfD msg.toD R`.
5. Infinity term: `divisorOfD msg.toD 0 = -(normPoly E msg.toD).natDegree` by
   definition.
6. Affine term: by `sum_ordAt_eq_natDegree_under_split` with `h_split`,
   `Σ_{R∈affinePoints} divisorOfD msg.toD R = (normPoly E msg.toD).natDegree`.
7. Sum cancels to 0.

**Caveat (Codex):** `hAccount_of_splitsOnE` (`EagenBuildRecursive.lean:7096`)
requires `hD : msg.toD ≠ 0`, traceable to
`sum_ordAt_eq_natDegree_under_split` (`OrdP/LocalRing.lean:754`).
The proposed signature above has no `hD`. Two options:

- **Option A (preferred):** thread `hD` through. Completeness already
  has `hD` available at `EagenBuildRecursive.lean:8627`. Add `hD`
  to the signature; pass it via the `splitsOnE` projection plus
  `hD` directly, bypassing the old `hAccount_of_isHonestForExplicit`
  wrapper.
- **Option B:** add a zero-`D` fallback using `ordAt_eq_zero_of_zero`
  (when `D = 0`, all `ordAt` are 0, sum = 0 trivially, and the
  divisor identity forces honest coeffs to be 0 too).

Option A is structurally cleaner and matches existing call-site
data flow.

### Step 3 — fix downstream destructuring (mostly nothing to do)

Because Step 1 *replaces* the `IsPrincipal` conjunct with `splitsOnE`
in the same position, projections like `h_honest.2.1`,
`h_honest.2.2.1`, etc. keep their indices. The only change is
*type/meaning* at index `.2.1`:

- `h_honest.1` → scalar reduction (unchanged).
- `h_honest.2.1` → was `IsPrincipal`; now `splitsOnE`. **Type changes.**
- `h_honest.2.2.1` → divisor identity (unchanged).
- `h_honest.2.2.2.1` → target on-curve (unchanged).
- `h_honest.2.2.2.2` → bases on-curve (unchanged).

Audit consumers of `h_honest.2.1`:

```sh
grep -rn "\.2\.1\|isHonestFor\|hHonestDivisor" Divisor/ --include="*.lean" \
  | grep -v "^.*--" | head -50
```

Files affected (from initial scan):

- `Divisor/EagenBuildRecursive.lean:8645` — currently derives splitsOnE
  *through* IsPrincipal. After refactor, `splitsOnE` is **directly
  available** as `h_honest.2.1`, eliminating that whole derivation
  path. Net negative LOC.
- `Divisor/EagenBuildRecursive.lean:7180-7190` — replaced (Step 2).
- `Divisor/EagenBuildRecursive.lean:8612` — bridge assembly site
  (replaced in Step 4).
- `Divisor/Soundness.lean:297, 327, 515`, `WeilReciprocityDescent.lean`
  — search for `.2.1` projections of `isHonestFor` and confirm none
  *use* the IsPrincipal type directly. Most consumers either go via
  the bridge `IsHonestForExplicit` (which has its own type
  destructuring) or use higher-level lemmas.

### Step 4 — replace bridge proof of `IsPrincipal` with proof of `splitsOnE`

Delete `isPrincipal_honestDivisorCoeffs_for_length4Simple`
(`Divisor/EagenBuildRecursive.lean:8495`).

Add new theorem in the same place:

```lean
theorem splitsOnE_msg_toD_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    splitsOnE E msg.toD
```

**Codex confirmed: this is one line.** The existing lemma
`splitsOnE_eagenBuild_length4` at
`Divisor/IncrementalConstruction.lean:6592` does the work. Proof:

```lean
  rw [h_simple.h_toD_eq]
  exact splitsOnE_eagenBuild_length4 E ...  -- pass h_simple's fields
```

`h_simple` carries all required hypotheses (cf.
`Divisor/LogDerivEagenLength4.lean:955`).

**Do NOT** try to prove via `∏ (X - P_i.1)` — x-coordinates can
collide across pairs and the existing lemma routes around that.

Bridge assembly site (`Divisor/EagenBuildRecursive.lean:8612`):
replace `isPrincipal_honestDivisorCoeffs_for_length4Simple ...` call
with `splitsOnE_msg_toD_for_length4Simple ...`.

### Step 5 — update generic completeness derivation

`ma_completeness_via_isHonestForExplicit` (around
`Divisor/EagenBuildRecursive.lean:8622, 8645`) currently derives
`splitsOnE` via the long route through `principal_divisor_iff`. Now
just take `h_honest.2.1`. **Net deletion of the derivation
machinery** — confirm via grep what `normPoly_splits_of_isHonestForExplicit`
(`EagenBuildRecursive.lean:7435`) and
`fiber_rationality_of_isHonestForExplicit` (line 7471) still need.
Both might become dead code or simplify substantially.

### Step 6 — delete dead helpers (if unused)

After Step 4, audit which of these become unused:

- `honestCoeffs_total_sum_eq_zero_for_length4Simple` (line 8282) —
  was fed into `principal_divisor_iff.mpr`. Codex flagged this
  shouldn't be deleted *until* the splitsOnE replacement is proved.
  Once the new `splitsOnE_msg_toD_for_length4Simple` is in place
  and verified, grep for any other consumer; delete if unused.
- `honestCoeffs_total_weightedSum_eq_zero_for_length4Simple` (line 8311)
  — same status.

Conservative: keep them and mark with a doc comment for now. Delete
in a follow-up if confirmed dead.

### Step 7 — annotate axiom file

Edit `axioms/principal_divisor_iff.md` (if it exists) or
`Divisor/Axioms/AxiomPrincipalDivisorIff.lean` doc-comment to
note: "no longer in the closure of `ma_completeness*` after
[date]; remains in the codebase but unused by headline theorems."

Codex confirmed (via closure pin doc) that `ma_extractable` /
`ip_knowledge_sound` do **not** currently depend on
`principal_divisor_iff` — the `ExtractorBridge.lean:573` and
`:2370` hits are *comments only*, not actual proof uses. So
after this refactor the axiom may be fully removable from the
build chain. Defer that decision to a follow-up; first land the
completeness-side cleanup.

### Step 8 — verification

1. `lake build Divisor` — clean build, no warnings, no `sorry`.
2. `lake env lean Tests/AxiomClosurePin.lean` — closure of
   `ma_completeness` and `ma_completeness_clean` no longer mentions
   `principal_divisor_iff`. Closure of `ma_extractable` /
   `ip_knowledge_sound` is **byte-for-byte unchanged** (they may
   still depend on `principal_divisor_iff`, and that's fine — the
   refactor only touches completeness).
3. `Tests/RegressionDoublingChallenge.lean` still passes
   (`native_decide`).
4. `cd /Users/rot256/src/divisors-axiom-tests && just` — full
   axiom-test suite passes.
5. `git status` shows only the listed files modified.
6. Closure pin diff: `Divisor.principal_divisor_iff` line removed
   from `ma_completeness*` blocks.

### Out of scope

- Eliminating `principal_divisor_iff` from the soundness side. The
  extractor uses `principal_divisor_iff.mpr` to lift sum-zero +
  group-sum-zero into `IsPrincipal`, and there's no equivalent
  shortcut there because the extractor synthesizes a divisor from
  protocol observations rather than from an explicit polynomial.
  Out of scope for this refactor.

## Open questions (post-Codex)

1. **`normPoly` factorisation for `eagenBuild_length4_explicit`.**
   Step 4 needs `normPoly E (eagenBuild_length4_explicit ...)` to
   factor as a product over `(X - P_i.1)`. Is there an existing
   lemma giving the explicit factorisation, or does it need to be
   proved? Cf. infrastructure in `Divisor/SplitsOnE.lean` and
   `Divisor/IncrementalConstruction.lean`. If proving from scratch:
   leverage `eagenBuild_length4_explicit_degE_eq_four` + the four
   pointwise vanishing facts already in `h_simple`.

2. **`normPoly_splits_of_isHonestForExplicit` simplification.**
   After the refactor, this theorem (line 7435) becomes nearly
   trivial (its conclusion is now a direct projection of
   `isHonestFor`). Decide whether to keep it as a thin wrapper or
   inline at call sites.

## Files modified

- `Divisor/Protocol.lean` — replace `IsPrincipal` conjunct with
  `splitsOnE`, update doc. (`Divisor/HonestExplicit.lean` does not
  exist; `IsHonestForExplicit` is an alias inside
  `EagenBuildRecursive.lean:6670`.)
- `Divisor/EagenBuildRecursive.lean` —
  - delete `isPrincipal_honestDivisorCoeffs_for_length4Simple`,
  - add `splitsOnE_msg_toD_for_length4Simple`,
  - rewrite `honestDivisorCoeffs_deg_zero_of_isHonestForExplicit`
    to use `splitsOnE` directly,
  - simplify `ma_completeness_via_isHonestForExplicit` (drop the
    splitsOnE-derivation block at line ~8645),
  - audit/keep/delete `honestCoeffs_total_*` lemmas.
- `Divisor/Soundness.lean` — Codex verified: existing projections
  are `.2.2.2.*` (e.g. line 307), not `.2.1`, so unaffected by the
  conjunct swap. Audit only.
- `Divisor/WeilReciprocityDescent.lean` — same audit.
- Stale doc-strings: `Divisor/Protocol.lean:164` and
  `Divisor/EagenBuildRecursive.lean:6661` still describe the
  `IsPrincipal` contract — update to reference `splitsOnE`.
- `Tests/AxiomClosurePin.lean` — update expected closure (drop
  `principal_divisor_iff` from `ma_completeness*` blocks).
- `Divisor/Axioms/AxiomPrincipalDivisorIff.lean` doc-comment —
  annotate as discharged for completeness side.

## Estimated impact

- LOC: net negative. Delete ~3 theorems (~80-150 LOC), add ~1
  theorem (~30-50 LOC), reindex projections (mechanical).
- Closure: completeness loses one project axiom. Headline
  axiom-surface for `ma_completeness*` shrinks from 3 project
  axioms to 2.
- Risk: low — the round-trip is structural, not load-bearing.
  Main risk is downstream `h_honest.2.X` projection reindexing
  errors, caught by the typechecker.
