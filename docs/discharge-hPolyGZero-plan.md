# Continuation Plan — Discharge `hPolyGZero` (fully close the residue identity)

**Last updated**: 2026-04-21 (after Phase 5 close-out commit `758287c`)
**Baseline**: `758287c` on `master`. Axiom surface is 9. `ma_extractable` carries `hPolyGZero` hypothesis threaded through from `polyG_zero_of_logDerivCheck_identically_zero` (ExtractorBridge.lean:1074-1105).

## Goal

Remove the `hPolyGZero` hypothesis from `polyG_zero_of_logDerivCheck_identically_zero` so the theorem takes the original (axiom-style) inputs only. Cascade the removal up through `ma_extractable` and `ip_knowledge_sound`. Final state: 9 axioms, no extra hypotheses, `ma_extractable` has the clean pre-Session-44 signature.

**Non-goals**: reducing the axiom count below 9. The Silverman-III + Lean-core axioms are fixed.

## Execution model

Same as the previous plan (`docs/continuation-plan.md`). Driver agent launches subagents per phase, verifies the gate after each, retries on failure. Each phase commits once clean. No AI attribution, no new axioms, no `sorry`/`admit`, `lake build` green, `--no-gpg-sign`.

## Strategy overview

The `hPolyGZero` hypothesis asserts `polyG(A₀, A₁) = 0` at every non-vertical (A₀, A₁) on `E × E`. Discharging it requires two pieces:

1. **Vanishing on defined pairs** — `polyG = 0` at every non-vertical (A₀, A₁) where `logDerivCheckFnDefined` holds.
2. **Density extension** — `polyG = 0` at every non-vertical pair on `E × E`, including undefined ones.

Two broad routes:

- **Route A (polynomial bridge)** — Fallback B of the original plan. Establish a ring identity
    `clearedFiberPoly A₀ = polyGPoly A₀ · F + curveEqPoly · H`
  (with `F` nonzero on `E`) and use it to transfer vanishing of `clearedFiberPoly` (derivable from `hAllZero`) to vanishing of `polyGPoly` mod `curveEqPoly`. Avoids Lemma 6 / function-field theory.
- **Route B (function-field norm + Lemma 6)** — discharge `chordLogDerivMatchesNormZ` (Phase 3's deferred hypothesis) by mechanizing the Sylvester/resultant norm identity, then feed it through `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (ResidueIdentity.lean:644) pair-by-pair, then apply the density extension.

Both routes share the density extension (Phase 9 below). They diverge on how they prove vanishing at defined pairs.

**Primary path: Route A.** Strictly fewer foundational Mathlib additions (no Sylvester matrix library required). Route B is documented as a backup in case Route A's ring identity turns out to be intractable.

## Constraints (never violate)

- NO new axioms.
- NO `sorry` / `admit`.
- NO AI attribution in commits.
- NO signed commits (`git commit --no-gpg-sign`).
- `lake build` must be green before every commit.
- Axiom surface of `Divisor.ma_extractable` must stay at exactly 9 (the permitted Silverman-III + Lean-core set).

## Allowed axioms (unchanged from the last plan)

- Lean core: `propext`, `Classical.choice`, `Quot.sound`.
- Group law: `ECPoint.add_assoc`, `add_comm`, `neg_add_cancel`.
- `principal_divisor_iff` (Silverman III Cor 3.5).
- `CoordRingElt.divisor_degree_eq`, `divisor_group_sum_zero` (Silverman III Prop 3.4).

## Execution plan — ready-to-use subagent prompts

### PHASE 6 — Ring identity `clearedFiberPoly ≡ polyGPoly · F (mod curveEqPoly)`

**Goal**: establish the polynomial bridge between `clearedFiberPoly A₀` (from `Divisor/ClearedPolyForm.lean:720`) and `polyGPoly A₀` (from `Divisor/PolyGBridge.lean:36`). Specifically, find polynomials `F, H ∈ (ZMod E.q)[X][X]` (with `F %ₘ curveEqPoly ≠ 0`, i.e., `F` doesn't vanish identically on `E`) such that

  `clearedFiberPoly A₀ = polyGPoly A₀ · F + curveEqPoly · H`

as an equality in `(ZMod E.q)[X][X]`. Ideally `F` is recognizable (a product of line-evaluations or a power of `(X₁ − A₀.1)`).

**Subagent prompt** (copy verbatim):

```
You are executing Phase 6 of /Users/rot256/src/divisors/docs/discharge-hPolyGZero-plan.md.

CONSTRAINTS (absolute):
- NO new axioms.
- NO sorry / admit.
- No AI attribution in commits.
- git commit --no-gpg-sign.
- lake build clean before commit.

CURRENT STATE: baseline commit 758287c on master. Axiom surface 9; target:
discharge hPolyGZero. ma_extractable still carries the hPolyGZero hypothesis.

TASK: establish a polynomial ring identity relating
`clearedFiberPoly A₀` (from Divisor/ClearedPolyForm.lean:720) and
`polyGPoly A₀` (from Divisor/PolyGBridge.lean:36). The identity takes
the form

  clearedFiberPoly A₀ = polyGPoly A₀ · F + curveEqPoly · H

for specific F, H ∈ (ZMod E.q)[X][X], with F %ₘ curveEqPoly ≠ 0.

SOURCES OF THE IDENTITY:
The paper's Corollary 1 proof (ec.tex:625-730) derives this by
unfolding both polynomials. `clearedFiberPoly` encodes
(Σ_i logDerivTerm(A_i, λ)) · denom − (Σ_j m'_j · L(R_j)⁻¹) · denom
(after clearing denominators), while `polyGPoly` encodes
Σ_k β_k · (prod of L) + Σ_j m'_j · (prod of L). Lemma 6 gives
(Σ logDerivTerm) · D(A_0)·D(A_1)·D(A_2) · ... = (Σ β/L_Q(Q_k)) · (prod of line evals).
After clearing all denominators and grouping terms, the ring identity
emerges with F a specific polynomial (likely a product of line
evaluations at the Q_k and B_j, times possibly D.eval at some points).

APPROACH:
1. Read the two polynomial forms (ClearedPolyForm.lean, PolyGBridge.lean).
2. Compute LHS − polyGPoly · F for a candidate F (start with the product
   of D-evaluations at all the zero/residue points).
3. Show the result is a multiple of curveEqPoly using `Polynomial.modByMonic`
   and ring manipulations.
4. This may need extensive symbolic manipulation. Expect ~400-600 LOC.

READ FIRST:
- Divisor/ClearedPolyForm.lean lines 720-2100 (clearedFiberPoly construction
  + clearedFiberPoly_identity at line 2079)
- Divisor/PolyGBridge.lean (polyGPoly, bivEval_polyGPoly, degree bounds)
- Divisor/ResidueIdentity.lean lines 200-400 (chord aggregate identity — may
  already contain partial polynomial-form content)
- Divisor/Lemma6.lean (Phase 3's scalar Lemma 6)
- ~/paper/divisor/sections/ec.tex lines 557-730 (Lemma 6 + Cor 1 paper proofs)

NEW FILE: Divisor/PolyBridge.lean (or similar). Target ~400-600 LOC.
Register in Divisor.lean umbrella.

HALT CONDITIONS:
- If the ring identity requires a new axiom to state (e.g., a
  non-mechanical scalar identity), do NOT introduce one. Instead:
  * first, try to refine the identity by absorbing the scalar content
    into a different polynomial form (e.g., replace LHS with a modified
    `clearedFiberPoly` variant).
  * if still stuck, return a FAIL report. Do NOT commit.

Before committing:
- `lake build` clean.
- Verify `#print axioms Divisor.ma_extractable` still produces exactly
  9 axioms (no regressions, no additions).

Commit: "Phase 6: polynomial ring identity clearedFiberPoly ≡ polyGPoly · F mod curveEqPoly".

Return commit SHA, a ≤150-word summary, and the specific F and H.
```

**Gate**: commit lands, `lake build` green, 9 axioms unchanged.
**Fallback if blocked**: pivot to Route B (Phase 6'). See § "Route B fallback" below.

---

### PHASE 7 — `clearedFiberPoly A₀ %ₘ curveEqPoly = 0` from `hAllZero` + density

**Goal**: use `hAllZero` to conclude `clearedFiberPoly A₀ %ₘ curveEqPoly = 0` for every fixed `A₀ ∈ E.points`. Requires counting the defined non-vertical pairs and exceeding the polynomial's `resultantX`-natDegree bound.

**Subagent prompt** (copy verbatim):

```
You are executing Phase 7 of /Users/rot256/src/divisors/docs/discharge-hPolyGZero-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution,
--no-gpg-sign, lake build clean.

CURRENT STATE: Phase 6 landed the polynomial ring identity. Baseline
commit is Phase 6's SHA (check `git log --oneline -3`).

TASK: prove, for every fixed `A₀ ∈ E.points` and every choice of
(D, P, k, B, m) satisfying the hypotheses of the narrowed theorem:

  clearedFiberPoly A₀ %ₘ curveEqPoly = 0.

STRATEGY:
1. From `hAllZero` (the narrowed theorem's hypothesis), every defined
   non-vertical (A₀, A₁) on E × E satisfies logDerivCheckFn = 0, hence
   logDerivCheckFnCleared = 0 (via logDerivCheckFn_eq_zero_iff_cleared
   in Divisor/LogDeriv.lean, both directions trivial).
2. By clearedFiberPoly_identity (ClearedPolyForm.lean:2079),
   `bivEval (clearedFiberPoly ...) A₁ · (A₁.1 − A₀.1)^(−N) =
    logDerivCheckFnCleared ... A₀ A₁`
   at defined non-vertical pairs. Since A₀.1 ≠ A₁.1 by hNV, conclude
   `bivEval (clearedFiberPoly A₀) A₁ = 0` at every defined non-vertical
   A₁ ∈ E.
3. Count: the set `Defined(A₀) := {A₁ ∈ E.points : A₀.1 ≠ A₁.1 ∧
     logDerivCheckFnDefined E D P B A₀ A₁}` has cardinality ≥
     #E.points − (number of bad A₁'s making denom zero) − 1 (the vertical
     pair). Under Hasse-Weil (already axiomatized), this is Ω(E.q).
4. Apply `card_zeros_on_E_le` (CubicIntersection.lean:270-286):
   if `clearedFiberPoly A₀ %ₘ curveEqPoly ≠ 0`, its zero count on E is
   ≤ 2 · natDegree(resultantX (clearedFiberPoly A₀)). For sufficiently
   large q, |Defined(A₀)| > this bound, contradiction.
5. Conclude `clearedFiberPoly A₀ %ₘ curveEqPoly = 0`.

CARDINALITY HYPOTHESIS: the count argument in step 4 needs a lower
bound on q relative to D.degE + k. If this bound matches the existing
`logDerivCheckFn_zero_set_bound` axiom (if it's still there) or a
reasonable q-dependence, use it. Otherwise introduce it as a scalar
hypothesis passed through Phase 8/9 (NOT as an axiom).

NEW FILE: Divisor/DefinedDensity.lean or extend an existing file.
Target ~200-400 LOC.

Before committing: `lake build` clean, 9 axioms unchanged.

Commit: "Phase 7: clearedFiberPoly vanishes mod curveEqPoly from hAllZero".

Return commit SHA + summary + any cardinality-hypothesis details.
```

**Gate**: as before.
**Fallback if blocked**: if the cardinality count is tight, extract the required q-bound as a separate hypothesis and thread it as an explicit non-axiomatic condition. Do not regress axiom count.

---

### PHASE 8 — `polyGPoly A₀ %ₘ curveEqPoly = 0`

**Goal**: combine Phase 6's ring identity with Phase 7's `clearedFiberPoly A₀ %ₘ curveEqPoly = 0` to conclude `polyGPoly A₀ %ₘ curveEqPoly = 0`. Requires `F` (from Phase 6) to be invertible modulo `curveEqPoly` OR nonzero on all of `E.points`.

**Subagent prompt** (copy verbatim):

```
You are executing Phase 8 of /Users/rot256/src/divisors/docs/discharge-hPolyGZero-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution,
--no-gpg-sign, lake build clean.

CURRENT STATE: Phases 6, 7 landed. See git log for commit SHAs.

TASK: prove, for every fixed `A₀ ∈ E.points` and every choice of
(D, P, k, B, m, Q, beta) satisfying the narrowed-theorem hypotheses:

  polyGPoly A₀ %ₘ curveEqPoly = 0.

STRATEGY:
1. From Phase 6's ring identity:
     clearedFiberPoly A₀ = polyGPoly A₀ · F + curveEqPoly · H.
2. Reduce both sides mod curveEqPoly:
     (clearedFiberPoly A₀ %ₘ curveEqPoly) =
       (polyGPoly A₀ · F) %ₘ curveEqPoly.
3. Phase 7 gives LHS = 0. So `(polyGPoly A₀ · F) %ₘ curveEqPoly = 0`,
   i.e. `polyGPoly A₀ · F ≡ 0 (mod curveEqPoly)`.
4. Use `F %ₘ curveEqPoly ≠ 0` (Phase 6 invariant): the residue ring
   `(ZMod E.q)[X][X] / curveEqPoly` is a domain (E is integral for
   generic E), so `polyGPoly A₀ %ₘ curveEqPoly = 0`.

Notes on step 4: `(ZMod E.q)[X][X] / curveEqPoly` is an integral
domain when curveEqPoly is prime (irreducible over ZMod E.q[X]); this
follows from E being an elliptic curve, i.e. curveEqPoly having no
rational roots of multiplicity > 1. Check if Divisor/CubicIntersection
has this lemma; if not, prove it from the discriminant nonvanishing
(already a definitional requirement of ECSetup).

FILE: extend Divisor/DefinedDensity.lean or a new Divisor/PolyGDensity.lean.
Target ~150-300 LOC.

Before committing: `lake build` clean, 9 axioms unchanged.

Commit: "Phase 8: polyGPoly vanishes mod curveEqPoly via Phase 6 + Phase 7".

Return commit SHA + summary + the irreducibility-of-curveEqPoly argument used.
```

**Gate**: as before.

---

### PHASE 9 — Discharge `hPolyGZero`

**Goal**: from Phase 8's `polyGPoly A₀ %ₘ curveEqPoly = 0`, derive `polyG E Q β R m' A₀ A₁ = 0` at every non-vertical (A₀, A₁). Replace the hypothesis in `polyG_zero_of_logDerivCheck_identically_zero` with a proof. Cascade the removal up through `ma_extractable` and `ip_knowledge_sound`.

**Subagent prompt** (copy verbatim):

```
You are executing Phase 9 of /Users/rot256/src/divisors/docs/discharge-hPolyGZero-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution,
--no-gpg-sign, lake build clean.

CURRENT STATE: Phases 6-8 landed. `polyGPoly A₀ %ₘ curveEqPoly = 0` is
proved (for fixed A₀). Baseline = Phase 8's commit SHA.

TASK: discharge `hPolyGZero` and cascade the signature simplification.

STEPS:
1. In Divisor/ExtractorBridge.lean line 1074, remove the hPolyGZero
   hypothesis from `polyG_zero_of_logDerivCheck_identically_zero`.
   The theorem body now proves `polyG(A₀, A₁) = 0` directly:
     a) Apply Phase 8's `polyGPoly A₀ %ₘ curveEqPoly = 0`.
     b) Deduce `bivEval (polyGPoly A₀) A₁ = 0` for `A₁ ∈ E.points`
        (use the standard `bivEval_of_modByMonic_zero` or similar).
     c) Use `bivEval_polyGPoly` (PolyGBridge.lean:49) to conclude
        `polyG E Q β R m' A₀ A₁ = 0`.
2. Remove hPolyGZero from all downstream theorems that thread it:
   `polyG_distinct_zero_cons`, `polyG_distinct_zero_of_logDerivCheck_identically_zero`,
   `distinctSigma_exists`, `extractor_succeeds_and_isPrincipal`,
   `extractorSucceeds_of_logDerivCheck_identically_zero_general`,
   `extracted_scalars_valid`, `ma_extractable`, `ip_knowledge_sound`.
   Each of these currently takes `hPolyGZero` as an argument (or a
   derived hypothesis). After Phase 9 they take the original
   axiom-style arguments only.
3. Verify `#print axioms Divisor.ma_extractable` is still 9 axioms.
4. Run `lake build` — clean.

CASCADING: Phase 4's subagent listed the threaded consumers. Walk the
call tree top-down (from ma_extractable) updating each call site.

Before committing: lake build clean, 9 axioms, no regressions.

Commit: "Phase 9: discharge hPolyGZero — ma_extractable no longer takes extra hypothesis".

Return commit SHA + final axiom surface + confirmation that
ma_extractable's signature matches its pre-Session-44 form.
```

**Gate**: commit lands, `lake build` green, 9 axioms, `ma_extractable`'s new signature matches the pre-Session-44 form.

---

### PHASE 10 — Close-out documentation

**Goal**: update `docs/axiom-elimination-plan.md`, `README.md`, `docs/continuation-plan.md`, `docs/discharge-hPolyGZero-plan.md` with the completion. Archive or reference historical docs.

**Subagent prompt** (copy verbatim):

```
You are executing Phase 10 (close-out) of /Users/rot256/src/divisors/docs/discharge-hPolyGZero-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution,
--no-gpg-sign, lake build clean.

CURRENT STATE: Phases 6-9 landed. hPolyGZero discharged; ma_extractable
has clean signature; axiom surface is 9.

TASKS:

1. Append "Session 45 — hPolyGZero discharged" entry to
   docs/axiom-elimination-plan.md documenting the commit chain and
   the closure of Route A.

2. Update README.md:
   - Remove any remaining "hPolyGZero hypothesis" references in the
     Outstanding-work section.
   - Add a note that the residue identity is now fully mechanized
     via the polynomial bridge approach (Phase 6-8).

3. Update docs/continuation-plan.md and docs/discharge-hPolyGZero-plan.md
   with a "COMPLETED" header.

4. Verify `lake build` clean and #print axioms shows 9 axioms.

Commit: "Phase 10: close-out hPolyGZero discharge — residue identity fully mechanized".

Return commit SHA + final axiom surface.
```

---

## Route B — Function-field norm fallback (use only if Route A blocks)

If Phase 6 cannot establish the ring identity within 3 retries (the polynomial bridge genuinely requires content that isn't mechanically derivable from the existing definitions), fall back to the Sylvester-resultant approach:

### PHASE 6' (Route B) — Mechanize `normPoly` as a resultant

Define the Sylvester matrix / resultant of `D(x, y) = a(x) − y·b(x)` with the curve equation `y² − (x³ + A·x + B)`. Prove the resultant equals `a² − b² · curveX = normPoly E D` (already defined). This is pure Mathlib-level infrastructure work (~400-600 LOC).

### PHASE 7' — Discharge `chordLogDerivMatchesNormZ`

Use Phase 6''s resultant identity to prove `N(D)(z) = lc(D)³ · ∏_k (z − z(Q_k))^β_k` as a polynomial equality in `F_q[z]`. Then apply Phase 3's Lemma 6 machinery to discharge `chordLogDerivMatchesNormZ` at defined chord pairs.

### PHASE 8' — Apply Lemma 6 + bridge theorem at defined pairs

For each non-vertical (A₀, A₁) with `logDerivCheckFnDefined`, combine:
- Phase 3's `lemma6_chord_residue` (now with `chordLogDerivMatchesNormZ` discharged).
- The bridge theorem `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (ResidueIdentity.lean:644).

Conclude `polyG(A₀, A₁) = 0` at every defined non-vertical pair.

### PHASE 9' — Density extension (shared with Route A Phase 9)

Same as the Route A density argument: from `polyG = 0` at defined pairs, apply `card_zeros_on_E_le` to conclude `polyGPoly %ₘ curveEqPoly = 0`, hence global vanishing.

### PHASE 10' — Close-out

Same as Phase 10.

## Halt conditions

Halt and report if:
- Phase 6 needs a new axiom AND Phase 6' also fails after 3 retries each.
- The density counting in Phase 7 / 9 requires a field-size bound that cannot be satisfied by the existing Hasse-Weil axioms.
- An unknown lemma about `curveEqPoly` irreducibility is required and not provable from existing `ECSetup` invariants.

In any halt case, document the specific blocker in this plan doc and return honestly.

## Critical references

- `docs/continuation-plan.md` — full history of Phases 1a-5 closure (Session 44 narrowing).
- `docs/axiom-elimination-plan.md` — sessions 1-44.
- `~/paper/divisor/sections/ec.tex:557-579` — Lemma 6.
- `~/paper/divisor/sections/ec.tex:595-676` — Corollary 1.

## First step on resumption

1. `cd /Users/rot256/src/divisors && lake build` — confirm `758287c` is clean.
2. Read this plan + the survey notes + `Divisor/ExtractorBridge.lean:1074` (narrowed theorem).
3. Read `Divisor/ClearedPolyForm.lean:2079` (`clearedFiberPoly_identity`) — understand the key polynomial identity Phase 6 will extend.
4. Read `Divisor/PolyGBridge.lean` (whole file) — `polyGPoly`, `bivEval_polyGPoly`, natDegree bounds.
5. Read `~/paper/divisor/sections/ec.tex:625-730` — Cor 1 proof sketch (motivates the Phase 6 ring identity).
6. Begin Phase 6 via subagent.
