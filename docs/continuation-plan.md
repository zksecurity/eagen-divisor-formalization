# Continuation Plan — Eliminate `polyG_zero_of_logDerivCheck_identically_zero`

**Last updated**: 2026-04-21 (Session 43)
**Current head**: `d2b9009`

## TL;DR for future agent

Your task: continue eliminating the transient axiom `polyG_zero_of_logDerivCheck_identically_zero` (at `Divisor/ExtractorBridge.lean:1032`). The foundation is in place. The remaining step is **mechanizing Lemma 6** (paper `lem:log-deriv-norm`), which requires building ~1500 LOC of function-field infrastructure.

**Do NOT**:
- Add new axioms.
- Add `sorry` / `admit`.
- Add AI attribution in commits (see `~/.claude/CLAUDE.md` UNDERCOVER).
- Sign commits (use `git commit --no-gpg-sign`).

**Do**:
- Commit incrementally after each phase that keeps `lake build` green.
- Use subagents for multi-file cascades (this is multi-hour work).
- Refer to this plan and to `docs/axiom-elimination-plan.md` Sessions 33–43 for history.

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

## Execution plan for future agent

### Phase 1: Build function-field infrastructure for `F_q(E)/F_q(z)` (~800 LOC)

Create new module `Divisor/FunctionFieldZ.lean`:

1. Define the chord-coordinate extension: for fixed slope `λ`, view `F_q(E)` as a degree-3 extension of `F_q(z)` where `z := y − λx`.
2. Define `normZ E λ D : (ZMod E.q)[X]` — the z-coordinate norm polynomial. Expected degree = `D.degE`.
3. Relate `normZ` to `normPoly E D` (the x-coord norm, already defined). The connection is through the resultant with the chord cubic `(λX + C·chordMu)² − (X³ + C·curveA·X + C·curveB)`.
4. Prove `normZ` decomposes: `normZ E λ D = C lc(D)³ · ∏_k (X − C (z(Q_k)))^{β_k}` where `β_k = betaConstructive E D (Q_k)`. This is the **norm decomposition** (paper line 627-629). The proof requires either:
   - Explicit resultant computation (favor this — mechanical but long).
   - OR function-field norm theory (harder in Lean/Mathlib).

### Phase 2: Apply Q3.0 PFE to `normZ` (~300 LOC)

1. Show `normZ_splits_over_Fq` (analog of `normPoly_splits_over_Fq` from Q3.1).
2. Apply Q3.0's `derivative_eq_sum_rootMultiplicity_of_roots_card_eq` to `normZ E λ D`.
3. Conclude: `(normZ)'(μ) · (∏_k (μ − z(Q_k))^{β_k}) = Σ_k β_k · (∏_{k'≠k} (μ − z(Q_{k'}))^{β_{k'}}) · lc(D)³ · (μ − z(Q_k))^{β_k − 1}`.
4. Denominator-cleared form matches the chord aggregate identity (Session 40 `chord_aggregate_identity`).

### Phase 3: Prove Lemma 6 (~400 LOC)

1. Apply Phase 2's PFE at `z = μ` (chord intercept).
2. Use `μ − z(Q_k) = −L_Q(Q_k)` (see `L_eval_eq_zLambda_sub` in `Divisor/ResidueIdentity.lean:54`).
3. Derive: `(normZ)'(μ) / normZ(μ) = Σ_k β_k / (μ − z(Q_k)) = −Σ_k β_k / L_Q(Q_k)`.
4. Bridge to `Σ_i logDerivTerm(A_i, λ)` using:
   - The three chord points A_i are the three sheets of `F_q(E)` over `z = μ`.
   - `logDerivTerm` (paper-faithful) equals `(dD/dz)/D` at each sheet.
   - `Σ_i dD/dz(A_i)/D(A_i) = d(log ∏_i D(A_i))/dz = d log N(D) / dz = (normZ)' / normZ` evaluated at `z = μ`.
5. This yields Lemma 6 as a Lean theorem.

### Phase 4: Close the axiom (~100 LOC)

1. Use Session 43's bridge: `polyG_zero_of_Lemma6_and_logDerivCheck_zero`.
2. Derive `normPoly_splits_over_Fq` under the axiom's hypotheses (`hAllZero` + `hQcov`). If this is not derivable generally, add it as hypothesis to the new theorem — the axiom consumer can supply it from global `hAllZero`.
3. Density extension from defined pairs to all non-vertical pairs. Use `polyGPoly` (`Divisor/PolyGBridge.lean`):
   - `bivEval_polyGPoly`, `polyGPoly_natDegree_le`, `InnerDegLe_polyGPoly`.
   - `card_zeros_on_E_le` (search the codebase).
4. Delete `axiom polyG_zero_of_logDerivCheck_identically_zero` in `Divisor/ExtractorBridge.lean:1032`.
5. Re-prove as a theorem of identical signature using Phases 1-3.
6. `lake build` and verify `#print axioms Divisor.ma_extractable` excludes the transient axiom.

### Phase 5: Close-out (~50 LOC)

1. Update `docs/axiom-elimination-plan.md` with closure session entry.
2. Update `README.md` axiom surface table (remove the "UNSOUND" flag, update axiom count from 10 to 9).
3. Delete or archive `docs/counterexamples/axiom_false_witness.lean` (no longer applicable; Session 39's cascade invalidated it).
4. Final verification: `lake build`, axiom check.

## Suggested subagent delegation

Phase 1 (function-field infrastructure) is the largest. Break it into subphases:

- **Phase 1a**: Define `normZ E λ D` and prove basic properties (~200 LOC).
- **Phase 1b**: Norm decomposition `normZ = C lc³ · ∏_k (X − C z(Q_k))^{β_k}` (~400 LOC, hardest).
- **Phase 1c**: Split predicate + PFE-prerequisites (~200 LOC).

Phase 2 is mostly mechanical Q3.0 instantiation (~300 LOC).

Phase 3 is the bridge proof — can be done in one subagent pass (~400 LOC).

Phase 4 + 5 should be one final subagent (~150 LOC).

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
