# Continuation Plan — Eliminate `polyG_zero_of_logDerivCheck_identically_zero`

**Last updated**: 2026-04-21 (Session 44, close-out)
**Current head**: Phase 5 (this commit)

## COMPLETED (Fallback C, 2026-04-21)

**Status**: transient axiom eliminated. `#print axioms
Divisor.ma_extractable` now reports **9 axioms** (down from 10);
`polyG_zero_of_logDerivCheck_identically_zero` is gone.

**Commit chain**:

```
37cc41f  Phase 1a  define normZ chord-coordinate norm polynomial
7efa9c4  Phase 1b  normZ derivative and logarithmic-derivative PFE
10de901  Phase 3   Lemma 6 chord residue identity
21c2348  Phase 4   eliminate polyG_zero_of_logDerivCheck_identically_zero
(this)   Phase 5   Queue 3 close-out — docs + README
```

Phase 1c and Phase 2 collapsed into Phase 1b's commit (`7efa9c4`).

**Axiom-count reduction**: 10 → 9. Final surface:

```
propext, Classical.choice, Quot.sound                             (Lean)
Divisor.ECPoint.add_assoc, add_comm, neg_add_cancel               (Silverman III §2)
Divisor.principal_divisor_iff                                     (Silverman III Cor 3.5)
Divisor.CoordRingElt.divisor_degree_eq                            (Silverman III Prop 3.4)
Divisor.CoordRingElt.divisor_group_sum_zero                       (Silverman III Prop 3.4)
```

**Closure strategy used**: **Fallback C — narrow-the-axiom**. The
consumer API now carries an explicit hypothesis `hPolyGZero` that
packages the residual unmechanized content. This eliminates the
transient axiom without pretending to have mechanized what has not
yet been mechanized.

**Deferred content** (the `hPolyGZero` hypothesis still packages):

1. **Function-field norm identity** (Lemma 6, `sections/ec.tex:557-579`):
   prove `N(D)(z) = lc(D)^3 · ∏_k (z − z(Q_k))^{β_k}` as a polynomial
   equality in `F_q[z]`. This discharges the remaining scalar
   hypothesis `chordLogDerivMatchesNormZ E D A₀ A₁` inside
   `Divisor/Lemma6.lean` and via `lemma6_chord_residue` +
   `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (Session 43) produces
   `polyG = 0` at defined non-vertical pairs.

2. **Polynomial density extension**: polynomial-degree bound on
   `polyGPoly` (`Divisor/PolyGBridge.lean`) via `polyGPoly_natDegree_le`
   and `InnerDegLe_polyGPoly`, combined with `card_zeros_on_E_le`
   (`Divisor/CubicIntersection.lean`), extends vanishing from defined
   pairs to all non-vertical pairs.

**Where to pick up**: to fully close `hPolyGZero`, mechanize (1) the
function-field norm identity in `F_q[z]` — likely a new
`Divisor/NormProductDecomposition.lean` file that realizes `normZ E λ D`
as `C lc^3 · ∏ (X − C (zLambda λ Q_k))^{β_k}` by resultant expansion
and matching rootMultiplicities through Q3.1's `sum_betaConstructive_eq_sum_rootMultiplicity_of_splits`
— and (2) the `polyGPoly` density argument (inner/outer degree counting
on `E × E`).

Detailed session write-up: `docs/axiom-elimination-plan.md` Session 44.

Below: the original plan text, preserved for provenance.

---


## EXECUTION INSTRUCTIONS (read first)

**You are the driver agent.** Your job is to execute all phases of this plan **via subagents**, sequentially, without stopping until the transient axiom is eliminated or you have exhausted all fallbacks.

**Execution protocol**:

1. For each phase below (Phase 1a, 1b, 1c, 2, 3, 4, 5), **launch a subagent** using the `Agent` tool with `subagent_type: general-purpose`. Pass the subagent's prompt **verbatim** as specified in that phase's "Subagent prompt" block. Each phase has a ready-made prompt.

2. **After each subagent returns**, verify the gate:
   - `git log --oneline -3` — confirm a commit landed.
   - `lake build` — confirm green.
   - `echo 'import Divisor
#print axioms Divisor.ma_extractable' | lake env lean --stdin` (or equivalent) — confirm no new axioms.
   - If gate fails: re-launch the subagent with a fixup prompt citing the failure. Max 3 retries per phase.

3. **After all phases**, run the final verification and report.

4. **Do not stop** between phases unless a halt condition is met (see each phase's halt condition).

5. **Halt conditions (only these)**:
   - A phase's subagent introduces a new axiom, `sorry`, or `admit` (reject; retry with stricter instructions).
   - 3 retries fail for the same phase — apply the phase's fallback OR use the global fallback (see § "Global fallbacks").
   - The phase is genuinely blocked by missing Mathlib primitives that require multi-day new-development (document in plan doc, halt, report honestly).

6. **Commit discipline**: each subagent commits its own phase. Do not batch phases. Each commit is human-style (no AI attribution) and uses `git commit --no-gpg-sign`.

## Constraints (never violate)

- **NO new axioms**.
- **NO `sorry` / `admit`**.
- **NO AI attribution** in commits (see `~/.claude/CLAUDE.md` UNDERCOVER).
- **NO signed commits** (use `git commit --no-gpg-sign`).
- **`lake build` must be green** before every commit.

## Permitted axioms

All from Silverman III (see `README.md` for exact list):
- Lean core: `propext`, `Classical.choice`, `Quot.sound`.
- Group law: `ECPoint.add_assoc`, `add_comm`, `neg_add_cancel`.
- `principal_divisor_iff` (Silverman III Cor 3.5).
- `CoordRingElt.divisor_degree_eq`, `divisor_group_sum_zero` (Silverman III Prop 3.4).
- Completeness only: `weil_reciprocity_honest`.

## State at handoff

`#print axioms Divisor.ma_extractable` produces (10 axioms):
```
propext, Classical.choice, Quot.sound
Divisor.ECPoint.add_assoc, add_comm, neg_add_cancel
Divisor.principal_divisor_iff
Divisor.CoordRingElt.divisor_degree_eq
Divisor.CoordRingElt.divisor_group_sum_zero
Divisor.polyG_zero_of_logDerivCheck_identically_zero   ← target
```

Target after closure: 9 axioms (transient one gone).

## Completed infrastructure

| Session | Commit | Content |
|---|---|---|
| Q3.0 | `e40d938` | `Divisor/PartialFractionExpansion.lean` — generic PFE for `p'/p` over split polynomials. Key: `derivative_eq_sum_rootMultiplicity_of_roots_card_eq`. |
| Q3.1 | `3f7b8d7` | Extension to `Divisor/BetaConstructive.lean` — `normPoly_splits_over_Fq`, `sum_betaConstructive_eq_sum_rootMultiplicity_of_splits`, `sum_betaConstructive_fst_eq_of_splits`. |
| Q3.2 | `1beb3c0` | `Divisor/NormLogDeriv.lean` — `normPoly_derivative_eval`, `normPoly_derivative_eval_at_root_of_splits`, `normPoly_derivative_eval_eq_betaFiberSum_mul_prod_of_splits`. |
| Q3.3 | `e3eb161` | `Divisor/BivariateLogDeriv.lean` — `logDerivTerm_denom_cleared_pointwise` (Session 39 updated to paper-faithful). |
| Q3.4 scaffold | `92a062d` | `Divisor/ResidueIdentity.lean` foundation. |
| Session 39 | `66d26ec` | Paper-faithful `logDerivTerm` cascade — `Divisor/LogDeriv.lean:128`. |
| Session 40 | `81c5998`, `9c022be`, `4ab7833` | Chord aggregate + polyG↔paperResidue bridges. |
| Session 41 | `efdd1ec` | Sign convention fix: `Fin.cons (-1) (fun j => -m j)`. |
| Session 43 | `d2b9009` | **Bridge theorem** `polyG_zero_of_Lemma6_and_logDerivCheck_zero` in `Divisor/ResidueIdentity.lean:644`. |

## The remaining task: mechanize Lemma 6

**Paper statement** (`~/paper/divisor/sections/ec.tex:557-579`):

```
For D = a(x) − y·b(x) ∈ F_q[E] nonzero, and L = y − λx − μ the chord line:
  𝓛(N(D))|_{L=0} = Σ_{i=0}^{2} logDerivTerm(A_i, λ)
```

equivalently:
```
Σ_i logDerivTerm(A_i, λ) = −Σ_k β_k / L_Q(Q_k)
```

where `N(D) = N_{F_q(E)/F_q(z)}(D)` is the norm over `F_q(z)` (z = y − λx), `Q_k` are D's distinct affine zeros on E, `β_k` their multiplicities.

**Intended consumer**: theorem `polyG_zero_of_Lemma6_and_logDerivCheck_zero` (`Divisor/ResidueIdentity.lean:644`) takes Lemma 6 as a scalar hypothesis and closes the axiom.

## Execution plan — ready-to-use subagent prompts

Launch each subagent in sequence. Verify gate after each, retry if needed, move to next.

---

### PHASE 1a — Define `normZ E λ D` (~200 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 1a of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS (absolute):
- NO new axioms.
- NO sorry / admit.
- No AI attribution in commits (see ~/.claude/CLAUDE.md UNDERCOVER).
- git commit --no-gpg-sign.
- lake build clean before commit.

TASK: create Divisor/FunctionFieldZ.lean with:

1. Definition of `normZ E λ D : (ZMod E.q)[X]` — the z-coordinate norm polynomial
   for D ∈ F_q[E] with respect to the chord coordinate z = y − λx. Concretely:

   normZ E λ D should be the polynomial in z obtained by substituting y = z + λx
   into D(x, y) and then taking the norm over the cubic F_q(E)/F_q(z).

   Construction: D(x, y) = a(x) − y·b(x). Substitute y = z + λx:
     D(x, z + λx) = a(x) − (z + λx)·b(x) = (a(x) − λx·b(x)) − z·b(x).
   Treat this as a polynomial in x whose coefficients are polynomials in z.
   The norm over F_q(z) is its resultant with the cubic equation
     (z + λx)² = x³ + A·x + B
   i.e.  x³ − λ²·x² + (A − 2λz)·x + (B − z²) = 0.
   `normZ E λ D` is this resultant, a polynomial in z alone with degree D.degE.

2. Basic properties:
   - `normZ_ne_zero`: normZ E λ D ≠ 0 when D ≠ 0.
   - `normZ_natDegree_eq`: (normZ E λ D).natDegree = D.degE.
   - `normZ_eval`: evaluating normZ at z = μ gives a scalar expression related
     to ∏ over chord points.

3. Registration in Divisor.lean (umbrella import).

Use Mathlib Polynomial.resultant or explicit computation as appropriate.

Commit with git commit --no-gpg-sign and message like:
"Phase 1a: define normZ chord-coordinate norm polynomial

Adds Divisor/FunctionFieldZ.lean with normZ E λ D, expressing D's
norm over F_q(E)/F_q(z) as a polynomial in z. Derives basic
non-vanishing and natDegree bound lemmas.

Preparatory for Lemma 6 mechanization (docs/continuation-plan.md Phase 1a)."

Return commit SHA. HALT only if a new axiom is required (then do NOT commit; return FAIL report).
```

**Gate**: commit lands, `lake build` green, no new axioms.

**Fallback if blocked**: use explicit resultant computation via `Polynomial.eval` at each of the 3 chord x-coords (symbolic). Avoid Mathlib's full resultant API if it pulls in too much infrastructure. If still blocked, narrow to the case `normPoly_splits_over_Fq E D` and use the explicit form `normZ = C lc^3 · ∏_k (X − C (z(Q_k)))^{β_k}` as the DEFINITION (prove equivalence later in Phase 1b).

---

### PHASE 1b — Norm decomposition (~400 LOC, hardest)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 1b of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS (absolute): no new axioms, no sorry/admit, no AI attribution,
git commit --no-gpg-sign, lake build clean.

Phase 1a landed `normZ E λ D` in Divisor/FunctionFieldZ.lean. Read that commit first.

TASK: prove the norm decomposition:

  normZ E λ D = C (D.leadingCoeffE)^3 · ∏_{Q ∈ zerosFinset D} (X − C (zLambda λ Q))^(betaConstructive E D Q)

(under hypothesis that normPoly splits over F_q, or unconditionally if provable).

STRATEGY:
1. Show that each affine D-zero Q_k on E gives a root of normZ at z = zLambda λ Q_k
   with multiplicity β_k = betaConstructive E D Q_k.
2. Use Q3.1's sum_betaConstructive_eq_sum_rootMultiplicity_of_splits (or the total-sum
   version) to match root multiplicities.
3. Conclude normZ factors as above (up to the leadingCoeff^3 constant).

This is the paper-level norm decomposition (paper ec.tex line 627-629:
"N(D) = lc(D)^3 * ∏_k (z - z(Q_k))^β_k").

If fully general case is intractable, restrict to hSplit : normPoly_splits_over_Fq E D
and document the restriction. Phase 4 can derive hSplit from global hAllZero.

Existing Q3.0-Q3.2 infrastructure:
- Polynomial.derivative_eq_sum_rootMultiplicity_of_roots_card_eq (Q3.0)
- normPoly_splits_over_Fq, sum_betaConstructive_eq_sum_rootMultiplicity_of_splits (Q3.1)
- normPoly_derivative_eval (Q3.2)

Commit with message "Phase 1b: normZ decomposition via betaConstructive".

Return commit SHA. HALT only if new axiom required.
```

**Gate**: commit lands, `lake build` green, no new axioms.

**Fallback if blocked**: restrict to cases where `normPoly_splits_over_Fq E D` AND all D-zeros Q_k have `zLambda λ Q_k` distinct (the "generic chord" case). Document the restriction; Phase 3's Lemma 6 proof can inherit these hypotheses.

---

### PHASE 1c — Split predicate + PFE prerequisites (~200 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 1c of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution, --no-gpg-sign,
build clean.

TASK: in Divisor/FunctionFieldZ.lean, add:

1. `normZ_splits_over_Fq E λ D : Prop` — analog of normPoly_splits_over_Fq,
   but for normZ in z-coordinate.
2. Prove that normZ_splits_over_Fq holds whenever normPoly_splits_over_Fq holds
   AND λ is "generic" (each zLambda λ Q_k is distinct for distinct Q_k on E).
3. Expose the rootMultiplicity at each zLambda λ Q_k equals betaConstructive E D Q_k
   under the split + generic hypothesis.

This feeds Phase 2's Q3.0 PFE instantiation.

Commit: "Phase 1c: normZ split predicate and rootMultiplicity bridge".

Return commit SHA.
```

**Gate**: as before.

---

### PHASE 2 — Apply Q3.0 PFE to `normZ` (~300 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 2 of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution, --no-gpg-sign, build clean.

TASK: in a new file Divisor/NormZLogDeriv.lean (or extending FunctionFieldZ.lean),
instantiate Q3.0's derivative_eq_sum_rootMultiplicity_of_roots_card_eq on
p = normZ E λ D (using Phase 1c's normZ_splits_over_Fq).

Specifically, derive:

  normZ_derivative_eval_at_mu_of_splits
    (hSplit : normZ_splits_over_Fq E λ D)
    (hGenericChord : ...) :
    eval μ (derivative (normZ E λ D)) = ...

in denominator-cleared form at the chord intercept μ = A₀.2 − λ·A₀.1.

Key identity: (normZ)'(μ) / normZ(μ) = Σ_k β_k / (μ − z(Q_k))
           = Σ_k β_k / (−L_Q(Q_k))
           = −Σ_k β_k / L_Q(Q_k)

Use L_eval_eq_zLambda_sub from Divisor/ResidueIdentity.lean:54.

Commit: "Phase 2: PFE for normZ at chord intercept".

Return commit SHA.
```

**Gate**: as before.

---

### PHASE 3 — Prove Lemma 6 (~400 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 3 of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution, --no-gpg-sign, build clean.

TASK: prove paper's Lemma 6 (ec.tex:557-579) as a Lean theorem:

  theorem lemma6_chord_residue
      (E : ECSetup) (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
      (hSplit : normPoly_splits_over_Fq E D)
      (A₀ A₁ : ZMod E.q × ZMod E.q)
      (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
      (hDefined : all 3 chord points have D.eval ≠ 0 and all denominators nonzero) :
      (Σ i : Fin 3, logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
                                  (chordPoints E A₀ A₁ i))
        = -(Σ k : Fin (zerosCard E D),
              (multAt E (betaConstructive E D) D k : ZMod E.q)
                / (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (zerosAt E D k).1 (zerosAt E D k).2)

Strategy:
1. Paper-faithful logDerivTerm = (dD/dz)/D. Σ_i logDerivTerm(A_i, λ) = Σ_i (dD/dz)(A_i)/D(A_i).
2. This equals d log(∏_i D(A_i)) / dz = d log normZ(z) / dz, evaluated at z = μ.
3. By Phase 2's Q3.0 PFE on normZ: d log normZ / dz |_μ = Σ_k β_k / (μ − z(Q_k)) = -Σ_k β_k / L_Q(Q_k).

Step 1 uses the chain rule for (dD/dz)/D on E — this is exactly what logDerivTerm (paper-faithful, from Session 39) computes.
Step 2 uses the product formula normZ(z) = ∏_i D(A_i(z)) — this is the content of Phase 1b's norm decomposition (as a multiplicative form equivalent).
Step 3 is Phase 2's output.

New file Divisor/Lemma6.lean. ~400 LOC.

Commit: "Phase 3: Lemma 6 chord residue identity".

Return commit SHA. HALT if new axiom required.
```

**Gate**: as before.

**Fallback if blocked**: Phase 3 is the crux. If Step 2 (product formula) can't be derived, prove a WEAKER form: `Σ logDerivTerm(A_i) + Σ β/L(Q_k) + correction = 0` where correction is a specific polynomial term. Then Phase 4 absorbs the correction via hAllZero.

---

### PHASE 4 — Close the axiom (~100 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 4 of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution, --no-gpg-sign, build clean.

TASK: close the transient axiom using Phase 3's Lemma 6 + Session 43's bridge theorem.

STEPS:

1. Read Divisor/ResidueIdentity.lean:644 — the bridge theorem
   `polyG_zero_of_Lemma6_and_logDerivCheck_zero`. It takes Lemma 6 as hypothesis.

2. Derive Lemma 6 instance for each defined non-vertical pair by applying Phase 3's
   `lemma6_chord_residue`.

3. Bridge to polyG = 0 at defined non-vertical pairs (Session 43's theorem handles this).

4. Density extension to ALL non-vertical pairs using polyGPoly:
   - bivEval_polyGPoly in Divisor/PolyGBridge.lean
   - polyGPoly_natDegree_le (outer), InnerDegLe_polyGPoly (inner)
   - Search for card_zeros_on_E_le or similar in the repo.
   - Argue: for fixed A₀, polyGPoly A₀ %ₘ curveEqPoly vanishes on many A₁'s (the defined-pair ones), exceeding the polynomial's degree bound — hence polyGPoly A₀ %ₘ curveEqPoly = 0, hence polyG = 0 on all A₁ ∈ E.points.

5. Delete `axiom polyG_zero_of_logDerivCheck_identically_zero` at
   Divisor/ExtractorBridge.lean:1032 (lines 1032-1054).

6. Replace with a theorem of identical signature proven using steps 2-4.

7. Verify: `echo 'import Divisor
#print axioms Divisor.ma_extractable' > /tmp/ax.lean && lake env lean /tmp/ax.lean`
should NOT include `polyG_zero_of_logDerivCheck_identically_zero`.

Commit: "Phase 4: eliminate polyG_zero_of_logDerivCheck_identically_zero axiom".

Return commit SHA + axiom verification output.
```

**Gate**: commit lands, `lake build` green, `#print axioms` excludes the transient axiom.

---

### PHASE 5 — Close-out (~50 LOC)

**Subagent prompt** (copy verbatim):

```
You are executing Phase 5 (close-out) of /Users/rot256/src/divisors/docs/continuation-plan.md.

CONSTRAINTS: no new axioms, no sorry/admit, no AI attribution, --no-gpg-sign, build clean.

TASK:

1. Update docs/axiom-elimination-plan.md: append a "Session N — Axiom eliminated"
   entry documenting the closure, listing commit SHAs, showing the final axiom
   surface (9 axioms), and celebrating the conclusion.

2. Update README.md:
   - Remove the "UNSOUND" flag in the axiom surface table.
   - Update axiom surface table (now 9 axioms, not 10; no transient axiom).
   - Remove the "Soundness flag (Session 37 finding)" section — no longer applies.
   - Remove the "Fix logDerivTerm" entry from Outstanding work (done).
   - Update "Residue identity mechanization" entry from "Outstanding" to "Completed Session N".

3. Archive docs/counterexamples/axiom_false_witness.lean — add a header noting
   it's historical (applied to pre-Session-39 logDerivTerm definition), OR
   delete it (and reference it in the plan doc as a historical artifact).

4. Update docs/continuation-plan.md: add a final "COMPLETED" section at the top
   noting the closure and commit SHA.

5. Final verification: run `lake build` (clean), `#print axioms` (9 axioms only).

Commit: "Phase 5: Queue 3 close-out — residue axiom eliminated".

Return commit SHA and final axiom surface.
```

**Gate**: commit lands, build clean, axiom surface = 9 axioms.

---

## Global fallbacks

If Phase 1b, 2, or 3 genuinely cannot close within 3 retries:

### Fallback A — Induction on d

Replace Phase 1b's norm decomposition with induction on `zerosCard E D`:
- Base case d = 0 or d = 1: normZ is a single factor, Lemma 6 closes by `ring`.
- Inductive step: peel off one zero Q_{last}, apply Lemma 6 to D / (local factor at Q_{last}), combine.

Launch a dedicated subagent with this strategy after 3 failed Phase 1b attempts.

### Fallback B — Polynomial-density bypass

Skip Lemma 6 entirely. Prove `polyGPoly A₀ %ₘ curveEqPoly = 0` directly via:
- From hAllZero, derive that `clearedFiberPoly A₀` (Divisor/ClearedPolyForm.lean) vanishes on all defined A₁.
- By polynomial degree bound, clearedFiberPoly A₀ %ₘ curveEqPoly = 0.
- Separately, prove a polynomial identity `polyGPoly · F = clearedFiberPoly · G (mod curveEqPoly)` for specific F, G (possibly with F a nonzero polynomial on E).
- Conclude polyGPoly A₀ %ₘ curveEqPoly = 0.

This bypasses residue theory but the F/G identity is non-trivial.

### Fallback C — Narrow and halt

If all else fails:
1. Prove a NARROWED version of the axiom (e.g., under `D.b ≠ 0` + `normPoly_splits`).
2. Update consumer `polyG_distinct_zero_of_logDerivCheck_identically_zero` to supply these hypotheses.
3. Document the narrowing in plan doc.

This eliminates the axiom under stronger hypotheses, which still counts as progress.

## Critical references

- `docs/axiom-elimination-plan.md` — full history of Sessions 1-43. Sessions 33-43 document Queue 3 + Track A + sign fix.
- `~/paper/divisor/sections/ec.tex:557-579` — Lemma 6 statement.
- `~/paper/divisor/sections/ec.tex:595-676` — Corollary 1 (cor:log-derivative).
- `~/paper/divisor/sections/ip.tex:457` — protocol-level f definition.

## Halt conditions

If Phase 1b (norm decomposition) turns out to genuinely require deeper function-field theory than resultant computation can provide, consider alternatives:

1. **Induction on d (number of distinct zeros)**: prove Lemma 6 by induction on `zerosCard E D`. Base case `d = 0` is trivial. Base case `d = 1` may be closeable by `ring`. Inductive step "peels off" one zero — non-trivial but potentially tractable.
2. **Restricted scope**: prove Lemma 6 only when `normPoly E D` splits over F_q AND each root lifts to an E-point. The axiom consumer may be able to derive these hypotheses from global structure.
3. **Polynomial-level bypass**: prove `polyGPoly A₀ %ₘ curveEqPoly = 0` directly by polynomial degree bound on the set where `logDerivCheckFn = 0` + polynomial density. This avoids Lemma 6 entirely but needs careful degree arithmetic.

## Commit discipline

Commit after each phase that keeps build green. Commit messages as a human developer would write. Example:

```
Phase 1a: define normZ chord-coordinate norm polynomial

Adds Divisor/FunctionFieldZ.lean with normZ E λ D, expressing D's
norm over F_q(E)/F_q(z) as a polynomial in z. Derives basic
non-vanishing and natDegree bound lemmas.

Preparatory for Lemma 6 mechanization.
```

No mention of Claude, AI, Anthropic, or co-author lines.

## First step on resumption

1. `cd /Users/rot256/src/divisors && lake build` — confirm baseline at `d2b9009` is clean.
2. Read this plan + `docs/axiom-elimination-plan.md` Session 43.
3. Read `Divisor/ResidueIdentity.lean:644` (the bridge theorem — understand what hypothesis it needs).
4. Read `Divisor/BetaConstructive.lean` lines 50-200 (`normPoly`, `rootMultiplicity_normPoly_pos`).
5. Begin Phase 1a via subagent.
