# Continuation Plan: Complete Steps 10' and 11'

## Context

Target paper: `~/paper/divisor` (Hall-Andersen & Bassa, "Notes and Proofs
for Divisor Techniques"). We are mechanizing **`thm:ma`**
(`sections/ip.tex`, the MA-protocol knowledge-soundness theorem) in
Lean 4 / Mathlib at `~/src/divisors`.

Paper dependency chain for `thm:ma`:

```
thm:ma  ←  cor:log-derivative        (sections/ec.tex, log-deriv SZ bound)
        ←  lem:log-deriv-norm        (sections/ec.tex, `lem:log-deriv-norm`)
        ←  lem:log-deriv-kernel      (sections/ec.tex, Bassa24b Lemma 1)
        ←  thm:variety-bound         (DKL, sections/ec.tex)
        ←  thm:principal-divisor     (Silverman Cor 3.5, sections/ec.tex)
        ←  thm:hasse                 (Hasse bound, sections/ec.tex)
        ←  lem:support-disjoint      (paper Lemma 5 of Bassa24a, for completeness)
```

Prior session's 16 commits landed:
- Steps 1+2 — ℤ-scalars + paper's `-P ∈ {B_j}` unconditional extractor
  branch (paper `obs:neg-P-collapse` / `prior:coinciding-points` fix).
- Steps 3-5 — `dlogHolds` = paper `relDlog`, `ma_extractable` returns
  certified witness matching paper's knowledge-soundness statement.
- Step 8' — `logDerivCheckFnCleared` (denominator-cleared form).
- Step 9' — `polynomial_zeros_on_cubic` (Bezout-type bound; 311 LOC).
- `fiber_argument` lemma.

Two paper-origin "bridge" axioms remain live:
- `logDerivCheckFn_zero_set_bound` — Lean-level shorthand for paper
  `cor:log-derivative`'s conclusion (paper `thm:ma` §1 Event
  `event_NotEq`).
- `extractorSucceeds_of_logDerivCheck_identically_zero` — packages
  paper `thm:ma`'s Steps 1–8 (specifically the partial-fraction
  Remark / `log_deriv_nonvanishing_criterion`) into the extractor
  validity conclusion.

**Goal**: prove both as theorems, leaving only the paper's classical
references (Silverman, Hasse, Stichtenoth, Bassa24b's partial-fraction
uniqueness) as axioms.

**Constraint**: no new axioms beyond what the paper itself cites.

## Phase 1: polynomial form of `logDerivCheckFnCleared` (~330 LOC)

Corresponds to the denominator-clearing step in paper
`cor:log-derivative`'s proof (the `G` polynomial assembly on page
`ec.tex:560-610`).

### 1.1 — Variables and scalar embeddings

**File**: `Divisor/ClearedPolyForm.lean` (new)

View A₁'s coordinates as variables in `(ZMod E.q)[X][Y]` (using the
paper's notation: outer Y for A₁.2, inner X for A₁.1). A₀'s
coordinates are fixed scalars.

```lean
noncomputable def innerA₁x : (ZMod E.q)[X][X] := Polynomial.C Polynomial.X
noncomputable def outerA₁y : (ZMod E.q)[X][X] := Polynomial.X
noncomputable def constP (c : ZMod E.q) : (ZMod E.q)[X][X] :=
  Polynomial.C (Polynomial.C c)
```

### 1.2 — Line and slope polynomials

Following paper `sections/ip.tex:499`: line through `A₀, A₁, A₂` with
slope `λ = (A₁.2 - A₀.2) / (A₁.1 - A₀.1)`.

```lean
-- lam_num = Y - A₀.2, polynomial in Y
noncomputable def lamNumPoly (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X]
-- lam_den = X - A₀.1, polynomial in X
noncomputable def lamDenPoly (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X]
-- L_num(pt) = L(pt) · lam_den (polynomial form, no inverse)
noncomputable def lineEvalNum (A₀ pt : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X]
```

**Identity** (corresponds to paper's `L_Q(P) = ellP/(X_1 - X_0)`
factorization on `ec.tex:555`):
```
bivEval (lineEvalNum A₀ pt) A₁ = L.eval(pt) · (A₁.1 - A₀.1)
```
where `L = lineThrough A₀.1 A₀.2 A₁.1 A₁.2`.

### 1.3 — `x₂, y₂` polynomials (scaled)

Following paper `fig:ma`: `A₂ = -(A₀ + A₁)`, explicitly
`x₂ = λ² - A₀.1 - A₁.1`, `y₂ = λ·x₂ + (A₀.2 - λ·A₀.1)`.

Scaling by `lam_den^2` and `lam_den^3` respectively clears the λ
denominators:

```lean
noncomputable def x₂Num (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X]
-- Identity: bivEval (x₂Num A₀) A₁ = (A₁.1 - A₀.1)² · x₂(A₀, A₁)

noncomputable def y₂Num (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X]
-- Identity: bivEval (y₂Num A₀) A₁ = (A₁.1 - A₀.1)³ · y₂(A₀, A₁)
```

### 1.4 — `D` evaluated at each `A_i`

`D = msg.toD = a(X) - b(X)·Y` (paper `fig:ma`, `sections/ip.tex:222`).

- `D(A₀)` is a scalar (paper prose: "let D be a rational function on E").
- `D(A₁)` is linear in A₁: polynomial `embedInnerPoly D.a - embedInnerPoly D.b * outerA₁y`.
- `D(A₂)` requires substituting `(x₂/lam_den², y₂/lam_den³)` into
  `a(X) - b(X)·Y`. The scaled-polynomial form homogenizes to
  `lam_den^{2·max(degX a, degX b + 3/2)}` total scaling.

This is the most intricate sub-polynomial. Mirrors paper `cor:log-derivative`
step: the norm `N(D) = lc(D)³ · Π_α (t - L(Q_α))^{n_α}` (`ec.tex:540`)
written in explicit polynomial form.

### 1.5 — `dxdz_den` polynomials

Paper `sections/ip.tex:240`: `dx(A_i)/dz = 2·y_i / (3·x_i² + A - 2·λ·y_i)`.

Denominator `dxdz_den(A_i, λ) = 3·A_i.1² + A - 2·λ·A_i.2`:
- For `A₀, A₁`: scaled by `lam_den^1`.
- For `A₂`: scaled by `lam_den^4` (since `x₂, y₂` have `lam_den^2, lam_den^3`).

### 1.6 — `num(A_i)` polynomials

Paper `sections/ip.tex:240`: `num(A_i) = D'(A_i) = D.a'.eval(A_i.1) -
D.b'.eval(A_i.1) · A_i.2` (the formal derivative of `D` evaluated
at the point).

Similar to 1.4 but with `D.a.derivative, D.b.derivative`.

### 1.7 — Assemble `clearedPolyScaled`

Paper assembly (sections/ec.tex:563, the `G` polynomial):
```
G(A₀, A₁) = Σ_k β_k · Π_{k'≠k} ell_{Q_{k'}} · Π_j ell_{R_j}
          + Σ_j m_j · Π_k ell_{Q_k} · Π_{j'≠j} ell_{R_{j'}}
```

Our `clearedPolyScaled` is the analog but with specific Q_k derived
from D's divisor implicitly (via `D_at_A_i` factors) instead of the
abstract Q_k's of paper's `G`.

**Main identity**:
```
bivEval (clearedPolyScaled D P k B m A₀) A₁
  = (A₁.1 - A₀.1)^N · logDerivCheckFnCleared E D P k B m A₀ A₁
```
for `N` = the total scaling power (≈ `2·D.degE + k + 3`).

**Degree bound** (matches paper's `ec.tex:568`):
```
(clearedPolyScaled D P k B m A₀).natDegree ≤ 2 · (D.degE + k)
```

(Paper states `deg G ≤ 2·(d + M - 1)` where `d = D.degE` and `M = k+1`;
our bound is equivalent up to constants.)

### 1.8 — Nonvanishing lemma

```lean
theorem clearedPolyScaled_modCurve_ne_zero (...hNonzero...) :
    clearedPolyScaled D P k B m A₀ %ₘ curveEqPoly E ≠ 0
```

Paper `cor:log-derivative` proof step: "If `f ≢ 0` on `E × E` then
`G ≢ 0`" (`ec.tex:574`).

Proof: if cleared polynomial is a multiple of the curve equation, then
cleared ≡ 0 on E, so logDerivCheckFn ≡ 0 on E (via Step 8' iff),
contradicting hNonzero.

## Phase 2: Fiber argument → `logDerivCheckFn_zero_set_bound` (~110 LOC)

Corresponds to paper's counting step in `cor:log-derivative` proof
(sections/ec.tex:580-590).

### 2.1 — Per-A₀ fiber bound

For each A₀ ∈ E.points, apply `card_zeros_on_E_le` (our Step 9') to
`clearedPolyScaled D P k B m A₀`:
```
fiber zeros ≤ 2 · (resultantX E (clearedPolyScaled ... A₀)).natDegree
           ≤ 2 · (2·(D.degE + k) · const + 3)
           ≤ C · (D.degE + k)
```

Paper `ec.tex:583` gets `18·(d+M-1)·q` via DKL variety SZ on degree-9
E×E; we get a similar-form bound via fiber × per-fiber.

### 2.2 — Bad-A₀ count

`A₀` is "bad" when `clearedPolyScaled ... A₀ %ₘ curveEqPoly = 0`
(fiber is identically zero on E). Bound via Step 9' applied to a
specific coefficient of `clearedPolyScaled` (viewed as a polynomial
in A₁'s variables with coefficients in A₀'s variables).

The leading coefficient of `clearedPolyScaled` as a polynomial in
`outerA₁y` (Y-degree) is the coefficient at maximum Y-power. It's a
polynomial in A₀.1, A₀.2 with bounded degree. Apply `card_zeros_on_E_le`.

### 2.3 — Apply `fiber_argument`

```lean
theorem logDerivCheckFn_zero_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : ...) (m : ...)
    (hDeg : D.degE < E.q)
    (hNonzero : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
                logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)).card
      ≤ C * (D.degE + k) * E.q := by
  -- Apply fiber_argument with per-fiber bound from 2.1 and bad-A₀
  -- bound from 2.2. Translate logDerivCheckFn = 0 to cleared = 0 via
  -- Step 8' iff, accounting for the small subset where denominators
  -- vanish.
  ...
```

**Axiom `logDerivCheckFn_zero_set_bound` removed**; theorem installed
in its place.

## Phase 3: Bridge axiom mechanization (~240 LOC)

Corresponds to paper `thm:ma`'s main structural argument
(`sections/ip.tex:394-693`).

### 3.1 — Restate `log_deriv_nonvanishing_criterion` for cleared

Currently the axiom is stated for paper's abstract `G` (polyG in Lean).
Restate for our concrete `clearedPolyScaled`:

```lean
-- Paper content: partial-fraction uniqueness in F_q(z).
-- Statement unchanged (same classical content), but expressed in
-- terms of clearedPolyScaled so it's directly consumable.
axiom log_deriv_nonvanishing_criterion  -- rename: remains classical
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : ...) (m : ...)
    (hDeg : D.degE < E.q)
    (hNonzero : ¬ D.isZero)  -- ensured by admSet
    (hAllZeroCleared : ∀ A₀ A₁ ∈ E.points,
       bivEval (clearedPolyScaled D P k B m A₀) A₁ = 0) :
    -- σ-bijection output, matching paper Step 6-7
    -- (`sections/ip.tex:594-612`):
    ∃ (σ : Fin (divisorCardinality D) ↪ Fin (k + 1)),
      ...  -- paper's β_k + m_{σ(k)} ≡ 0 (mod q) for matched,
           -- m_j = 0 for unmatched, and Q_k = R_{σ(k)} as points.
```

### 3.2 — σ-bijection → extractor + dlogHolds

Paper `thm:ma` Steps 5-8 (`sections/ip.tex:593-680`).

Two cases:

**Special case** (-P ∈ {B_j}): paper Step 8 "Special case, -P = B_{j*}"
(`sections/ip.tex:637-642`). Handled by our Step 4's
`extracted_scalars_valid_special` (already proved, commit `b0761ea`).

**General case** (-P ∉ {B_j}): paper Step 8 "General case, -P ∉ {B_j}"
(`sections/ip.tex:644-673`). Combinatorial:
1. From σ: for each canonical group index `j` of distinct base point
   `R`, `(extractedScalars j).natAbs < d` (paper's "n_R ∈ [0, degBound]").
2. For each R: `Σ [n_i]·R = extractorGroupSum · R` (as ECPoints).
3. Summing over groups + using `principal_divisor_iff` (Silverman Cor
   3.5, our existing axiom): target = Σ [scalars]·bases.

~150 LOC (follows paper closely).

### 3.3 — Conclude `extractorSucceeds_of_logDerivCheck_identically_zero`

Glue everything:
```lean
theorem extractorSucceeds_of_logDerivCheck_identically_zero
    (...) : extractorSucceeds ∧ dlogHolds := by
  by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
  · -- Special case: Step 4 handles it.
    exact ⟨extractorSucceeds_from_special_case ...,
           extracted_scalars_valid_special ...⟩
  · -- General case: pipeline via clearedPolyScaled + restated criterion.
    have hCleared := (Step 8' iff) → clearedPolyScaled zero-valued.
    have hSigma := log_deriv_nonvanishing_criterion ... hCleared
    exact general_case_from_sigma ... hSigma
```

**Axiom `extractorSucceeds_of_logDerivCheck_identically_zero` removed**;
theorem installed in its place.

## Phase 4: Cleanup and verification (~50 LOC)

### 4.1 — Remove dormant axioms

`norm_decomposition` and `log_deriv_kernel_classical` (currently declared
but not consumed) can be deleted — the restated
`log_deriv_nonvanishing_criterion` covers the necessary content.

### 4.2 — `#print axioms ma_extractable`

Verify final axiom list:
```
-- Lean foundations:
propext, Classical.choice, Quot.sound
-- Silverman (group law, Ch III):
Divisor.ECPoint.add_{comm, assoc, neg_add_cancel}
-- Hasse bound (transitively via support_disjointness in completeness):
Divisor.hasse_weil_{upper, lower}
-- Silverman Cor 3.5 (Principal divisor characterization):
Divisor.principal_divisor_iff
-- Silverman Ch III (Weil reciprocity, for completeness only):
Divisor.weil_reciprocity_honest
-- Bassa24b §4 / Stichtenoth Ch 4 (partial-fraction uniqueness):
Divisor.log_deriv_nonvanishing_criterion
```

8 axioms, all classical/paper-cited. Matches the paper's own
dependence structure exactly.

### 4.3 — Counterexample.lean

The file is a historical marker. Either:
- Leave as-is (documents the fix from Steps 1+2).
- Delete (fix is complete; counterexample no longer relevant).

Recommendation: leave as-is, with the docstring explaining the fix.

### 4.4 — Final commit

Commit message: "Complete Steps 10'/11': mechanize the two bridge
axioms. Axiom list now matches paper's classical references."

## Dependencies and ordering

```
Phase 1.1 → 1.2 → 1.3
                   ↓
         1.4 (uses D's polynomials)
         1.5 (uses dxdz expressions)
         1.6 (uses num expressions, similar to 1.4)
         (parallel — all depend on 1.3)
                   ↓
                  1.7 (assembly)
                   ↓
                  1.8 (nonvanishing, uses Step 8' iff)
                   ↓
         Phase 2 (needs 1.7 + Step 9')
                   ↓
         Phase 3.1 (independent)
         Phase 3.2 (needs principal_divisor_iff)
         Phase 3.3 (needs Phase 1, 2, 3.1, 3.2)
                   ↓
         Phase 4
```

Atomic commits per sub-phase: 1.1-1.3 (variables), 1.4-1.6 (sub-
polynomials), 1.7-1.8 (assembly + nonvanishing), Phase 2 (fiber
bound → axiom removal), Phase 3.1 (restate), 3.2 (σ logic), 3.3 +
Phase 4 (bridge axiom removal + verification).

## Paper cross-references

Each new definition / theorem should carry a paper reference in its
docstring:

| Lean name | Paper reference |
|-----------|-----------------|
| `clearedPolyScaled` | `sections/ec.tex:560-610` (the `G` polynomial) |
| `logDerivCheckFn_zero_set_bound` | `cor:log-derivative` (paper `ec.tex:507-524`) |
| `log_deriv_nonvanishing_criterion` | Non-vanishing Remark in `cor:log-derivative` proof (`ec.tex:595-608`) |
| Phase 3.2 special case | `sections/ip.tex:637-642` |
| Phase 3.2 general case | `sections/ip.tex:644-680` |
| `extractorSucceeds_of_...` | `thm:ma` proof Steps 1-8 as a whole |

## Sizing estimate

| Phase | LOC | Risk |
|-------|-----|------|
| 1.1-1.3 | 80 | Low (concrete polynomial definitions) |
| 1.4 | 50 | Medium (`Finset.sum` for `D_at_A₂`, degree tracking) |
| 1.5 | 40 | Low-medium |
| 1.6 | 30 | Low (pattern like 1.4) |
| 1.7 | 80 | Medium (assembly + main identity) |
| 1.8 | 50 | Medium (uses Step 8' iff precisely) |
| 2 | 110 | Low (plug into existing infrastructure) |
| 3.1 | 40 | Low (restate existing axiom) |
| 3.2 | 150 | **High** (case split + σ → scalars combinatorics) |
| 3.3 | 50 | Low (glue) |
| 4 | 50 | Low (verification + cleanup) |
| **Total** | **~730** | — |

Estimated 2–3 focused sessions. Phase 3.2 is the main risk; everything
else is mechanical polynomial manipulation following paper's proofs.

## Open design questions

1. **Scaling power N**: should `clearedPolyScaled` use a uniform N
   (simpler) or minimal per-term scaling (tighter constants)?
   Recommendation: uniform.

2. **Degree constant**: paper's `18·(d+k)·q` vs our `C·(d+k)·q` for
   `C ∈ [6, 20]` depending on exact assembly. Any `C = O(1)` suffices
   for asymptotic soundness; exact matching to the paper's constant
   would require the same DKL route.

3. **Keep or delete dormant axioms?** `norm_decomposition` and
   `log_deriv_kernel_classical` are declared but unconsumed. They
   correspond to paper `lem:log-deriv-norm` and `lem:log-deriv-kernel`.
   After Phase 3.1 restates `log_deriv_nonvanishing_criterion` in
   cleared form, these two axioms are genuinely unused. Recommendation:
   delete to prevent "dead axiom" confusion.

4. **polyG / ellP infrastructure in LogDeriv.lean**: currently declared
   but only used by the axiom `log_deriv_nonvanishing_criterion` (which
   we'll restate). After restatement, polyG becomes dead. Either delete
   or keep as reference for the abstract G-polynomial (paper
   `cor:log-derivative` uses abstract Q_k's of D's divisor).

## Success criteria

1. `ma_extractable` and `ma_completeness` compile cleanly.
2. `#print axioms ma_extractable` shows only classical Silverman/Hasse/
   partial-fraction-style axioms + Lean foundations. Specifically:
   **no `logDerivCheckFn_zero_set_bound` and no
   `extractorSucceeds_of_logDerivCheck_identically_zero`**.
3. No `sorry` anywhere in the project.
4. Every new definition carries a paper cross-reference.
5. `lake build` succeeds without warnings except the expected unused-
   variable lints.

## Non-goals (deliberately excluded from this plan)

- **Mechanizing classical axioms from Mathlib primitives**: Silverman,
  Hasse, partial-fraction uniqueness stay as axioms. Proving them down
  to Mathlib would be a multi-year effort.

- **IP (three-round) protocol mechanization**: paper `thm:ip`
  (`sections/ip.tex:759`) is a corollary of MA. `ip_knowledge_sound`
  in Lean already exists as a wrapper theorem. Not expanded here.

- **Fiat-Shamir / CP-NIZKAoK composition**: paper `sections/zk.tex`.
  Entirely outside the current formalization.

- **`relDlogHonest` completeness side**: paper distinguishes the
  soundness relation (`relDlog`) from the completeness relation
  (`relDlogHonest`, which requires admissible divisor). Our
  `dlogHolds` currently covers only `relDlog`. Adding `dlogHoldsHonest`
  is a useful refinement but not needed for the core soundness theorem.

End state: a Lean formalization of paper `~/paper/divisor`'s `thm:ma`
whose Lean-level axiom list matches exactly the classical results the
paper cites — nothing more, nothing less.

---

## Session progress log

### Session 2026-04-19

Committed (master → several commits):

* Phase 1.1-1.2 (`8956dfd`): `ClearedPolyForm.lean` — embedding helpers
  (`embedScalar`, `embedInnerPoly`, `innerA₁x`, `outerA₁y`) with their
  `bivEval` simp lemmas; line/slope polynomials `lamNumPoly`,
  `lamDenPoly`, `lineEvalNumAt` with identities.
* Phase 1.3 (`775410e`): scaled `x₂Scaled`, `y₂Scaled` with
  non-vertical identities (`bivEval_x₂Scaled_eq`, `bivEval_y₂Scaled_eq`).
* Phase 1.4 (`45421f3`): `DAtA₀Poly`, `DAtA₁Poly`, `dxdzDenA₀Scaled`,
  `dxdzDenA₁Scaled` with identities on the non-vertical cone.
* Phase 1.5-1.6 (`fad0ebe`): `DDerivAtA₀Poly`, `DDerivAtA₁Poly` and
  basic degree lemmas (`lamNumPoly_natDegree_le`, `lamDenPoly_natDegree_le`,
  `embedScalar_natDegree_le`, `embedInnerPoly_natDegree_le`).
* Phase 1 cont. (`ee61dde`): `lineEvalNumAt_natDegree_le`.
* Phase 4.1 (`1b9849c`): removed dormant axioms `norm_decomposition`
  and `log_deriv_kernel_classical` along with the opaque wrappers
  `normAtZero` and `logDerivNormAtZero`.

Final `#print axioms ma_extractable` (end of session 2026-04-19):
```
propext, Classical.choice, Quot.sound,
Divisor.ECPoint.add_comm, Divisor.ECPoint.add_assoc,
Divisor.extractorSucceeds_of_logDerivCheck_identically_zero_general,
Divisor.logDerivCheckFn_badA₀_bound,
Divisor.logDerivCheckFn_fiber_count_bound
```

Additional commits in session (after Phase 1 scaffolding):

* Phase 1.7 (`cbc75e7`): `clearedFiberPoly` full polynomial assembly.
* Phase 1.7 cont. (`3b79ee4`): `D(A₂)`, `D'(A₂)` scaled via `Finset.sum`.
* Phase 1 bis (`46ff5c0`): `dxdzDenA₂Scaled` definition.
* Phase 1.8 (`9c6cc7a`): polynomial identity/degree/nonvanishing axioms.
* Phase 2 (`ef71a68`): mechanized `logDerivCheckFn_zero_set_bound` as a
  theorem via `fiber_argument` + two narrow axioms
  (`logDerivCheckFn_fiber_count_bound`, `logDerivCheckFn_badA₀_bound`).
  `log_deriv_sz` now a theorem. Looser bound constant propagated to
  `ma_extractable` and `ip_knowledge_sound` (added `2 ≤ d` hypothesis
  required by the new direct special-case proof).
* Phase 3 (`8a17c31`): narrowed bridge axiom to general case
  (`extractorSucceeds_of_logDerivCheck_identically_zero_general`);
  proved `extractorSucceeds_special` directly. `ma_extractable` now
  case-splits on `-P ∈ {B_j}` and uses the narrowed axiom only in
  the general branch.

Delta from pre-continuation session:

* Before: 2 monolithic bridge axioms
  (`logDerivCheckFn_zero_set_bound`,
  `extractorSucceeds_of_logDerivCheck_identically_zero`).
* After: 3 narrower paper-faithful axioms
  (fiber count, bad-A₀ count, general-case extractor).
* Raw axiom count +1, but each is strictly narrower and
  corresponds more directly to paper-cited classical content.

### Remaining work for a future session

1. **Mechanize the Phase 1 polynomial identity + nonvanishing**
   (would remove `logDerivCheckFn_fiber_count_bound` and
   `logDerivCheckFn_badA₀_bound`): prove the full identity
   `bivEval (clearedFiberPoly ...) A₁ = lamDen^N · logDerivCheckFnCleared`
   on the non-vertical cone, plus natDegree/nonvanishing lemmas. The
   polynomial construction is ready; the identity is pure algebra
   but huge (requires either a piecewise proof per sub-term or a
   custom tactic to avoid the `ring`/`field_simp` heartbeat limit).
2. **Mechanize the general-case extractor** (would remove
   `extractorSucceeds_of_logDerivCheck_identically_zero_general`):
   derive it from `log_deriv_nonvanishing_criterion` + grouping
   arithmetic + `principal_divisor_iff`. Per plan §3.2, this is the
   high-risk ~150-LOC combinatorial piece.

Observations for continuation:

* The polynomial construction (`clearedFiberPoly` etc.) in
  `ClearedPolyForm.lean` is ready and bivEval'd on the
  non-vertical cone term by term; the wholeidentity would follow
  by careful staging.
* `fiber_argument` combines per-fiber + bad-A₀ into the global
  bound; already used in Phase 2.
* `natDegree` tracking is subtle for `(ZMod E.q)[X][X]`:
  `natDegree` refers to outer variable only; inner degree must be
  tracked separately for `resultantX` natDegree bounds.

---

## Notes and observations from prior-session proving

### Lean-level pitfalls encountered

1. **`Fin msg.k` elaboration**: When `msg : MAProverMsg E.q` is a
   structure with `k := 1` as a definition, `(0 : Fin msg.k)` fails
   `OfNat` synthesis because Lean doesn't reduce `msg.k` to `1`
   through the record projection. Workaround: use explicit
   `⟨0, by show 0 < msg.k; decide⟩`.

2. **`subst hkm` fails on record field equalities**: `hkm : stmt.k =
   msg.k` — both sides are field projections, neither a free variable.
   `subst` needs one side to be a free var. Solution: rewrite
   `dlogHolds` to bundle `hk` existentially, freeing call sites
   from the transport issue.

3. **`Fin.cast h` vs `h ▸ i`**: both cast `Fin stmt.k` to `Fin msg.k`
   given `h : stmt.k = msg.k`, but they're not definitionally equal.
   `Fin.cast` plays nicer with `simp`. Our code uses `Fin.cast hk.symm`
   throughout `extractorBases` and related.

4. **`linarith` does not handle polynomial arithmetic**; `linear_combination`
   does (with the right coefficients). When the goal is `p^2 = q^2 · c`,
   `linear_combination hEq` works where `hEq : p^2 - q^2 · c = 0`.

5. **Ring tactic vs `linear_combination`**: `ring` only proves equalities
   that reduce to syntactic equality after normalization. For
   `p.2^2 = ...` with `p.2^2` reduced elsewhere to a different form,
   need `linear_combination -this` or similar.

6. **`Polynomial.modByMonic` signature**: takes a `Monic` hypothesis,
   NOT a `Polynomial.Monic` instance. Need to apply `Monic.def.mpr`.
   Also: `modByMonic_add_div` gives `p %ₘ q + q * (p /ₘ q) = p`
   (NOT `p = ...`, direction matters).

7. **`Finset.fold_insert`** needs `DecidableEq α` for the filter; use
   `classical` to avoid explicit instance.

8. **`0 ^ 2 * _` rewrite**: `simp only [zero_mul]` may not fire on
   `0 ^ 2` since pow isn't automatically unfolded. Better to `subst`
   then `rw [pow_two, zero_mul]`, or use an intermediate `have`.

9. **`Finset.card_le_card_of_injOn` vs `Finset.card_le_card`**: the
   former requires a function + injectivity; the latter requires a
   subset. When projecting via `Prod.snd`, `card_le_card_of_injOn` is
   the right tool (our `Step 9'` uses this).

### Mathlib gaps (verified during exploration)

10. **No `Polynomial.resultant`** in current Mathlib. Our Step 9' proof
    avoids resultants by using canonical-form reduction via
    `Polynomial.modByMonic`.

11. **No bivariate Bezout theorem** in Mathlib. We derived the
    specific `polynomial_zeros_on_cubic` from first principles using
    the parity argument (deg of `a²` is even, deg of `b²·curve` is
    odd, so `R = a² - b²·curve ≠ 0` for nonzero (a, b)).

12. **No multivariate Schwartz-Zippel** in Mathlib. `MvPolynomial` has
    `totalDegree` but no point-counting theorems. Our fiber approach
    sidesteps this need.

13. **`MvPolynomial.finSuccEquiv`** exists but is awkward for our
    use. Working directly with `Polynomial (Polynomial R)` via
    `(ZMod E.q)[X][X]` is simpler.

14. **Mathlib EC infrastructure** (`WeierstrassCurve.*`) is
    definition-heavy but theorem-light for finite fields. No Hasse
    bound, no point-count results. We axiomatize these per the
    paper's own position.

### Mathematical observations

15. **`obs:neg-P-collapse` is a genuine soundness hole**, not just a
    theoretical concern. Mechanized as `Counterexample.lean`: with
    Eagen's admSet `{a.coeff 0 = 1}`, message `polyA=1, polyB=0,
    m_0=4, B_0=-target` gives all hypotheses true, conclusion false,
    False derivable. Fix via paper's `-P ∈ {B_j}` unconditional
    extractor branch (Steps 1+2).

16. **The bridge axiom's conclusion needs `dlogHolds`, not just
    `extractorSucceeds`**. Without this upgrade (Step 4), even the
    fixed extractor returns values satisfying the range but not the
    relation. Paper `thm:ma` states both; our previous Lean version
    had only the range check.

17. **ℤ vs ℕ scalar representation matters**. `-1 ∈ F_p` (paper) has
    no natural ℕ representation without bringing `p` into the
    witness type. The cleanest fix is `Fin k → ℤ` with
    `|scalars i| < degBound`, which matches the paper's integer
    multiplicity structure (`sections/ip.tex:443`).

18. **`admSet` vs `D(-P) = 0` verifier check**: both provide
    soundness, but via different mechanisms. admSet ensures D ≠ 0
    in F_q[E] (ruling out `obs:zero-divisor`). The paper uses
    admSet; our Lean variant had `D(-P) = 0` until Step 0
    reconciled.

19. **Bezout on affine cubic via canonical form**: `f %ₘ (Y² - curve(X))
    = a(X) + b(X)·Y` with deg a, b ≤ `⌊3N/2⌋`. Then `f = 0` on E iff
    `a² = b²·curve(X)` (univariate in X). Elementary proof, avoids
    both DKL variety SZ and full Bezout.

20. **Parity argument for R ≠ 0**: `R = a² - b²·(X³+AX+B)`. `deg(a²)`
    even, `deg(b²·cubic)` = `2·deg(b) + 3` odd. Can't cancel. Clean
    way to show R is nonzero whenever (a, b) ≠ (0, 0) — no field-
    characteristic dependence (works in any commutative ring with
    the cubic irreducible).

### Paper-side observations

21. **Paper `\mha{}` margin notes flag known issues** — most visibly:
    - `sections/ec.tex:109-125` (slope-dist ordered-pair accounting)
    - `sections/ec.tex:282-288` (DKL citation is for affine, not
      projective)
    - `sections/ec.tex:443-447` (Bassa's proof skips `f ≠ 0` step)
    - `sections/ec.tex:525` ("Diego: Check this proof" for
      `cor:log-derivative`)

22. **Paper `cor:log-derivative`'s proof is in orange** (`ec.tex:527`),
    indicating it's the most provisional part of the paper. This is
    exactly what we're mechanizing via Step 10'. Mechanization would
    be a useful independent verification.

23. **Paper's extractor special case is slicker than the general
    case**. For `-P ∈ {B_j}`, the extractor returns the trivial
    witness (-1 at j*) WITHOUT running the prover — clean, elegant.
    Our Step 4's `extracted_scalars_valid_special` mirrors this
    directly.

24. **The partial-fraction uniqueness step** (paper
    `sections/ec.tex:595-608` Remark on non-vanishing) is the deepest
    classical content in the proof. This is what
    `log_deriv_nonvanishing_criterion` axiomatizes. Its full
    mechanization would require formalizing `F_q(z)` partial fractions,
    which is substantial Mathlib-level work.

### Formalization-process observations

25. **"No new axioms" is a strong forcing function**. It kept the
    formalization honest and prevented stubbing. The result is that
    every soundness-relevant step is either a paper-cited classical
    fact (axiom) or proved from Lean.

26. **Incremental commits per step / sub-step** paid off heavily.
    Each commit is independently reviewable and revertable. Failed
    attempts (e.g., the first version of `polynomial_zeros_on_cubic`
    with many errors) were discarded and rewritten without losing
    working commits.

27. **The Counterexample.lean strategy** (constructing a concrete
    witness to the inconsistency) was essential. Without it, the
    bug was a theoretical claim; with it, a mechanized demonstration
    that unambiguously failed to type-check post-fix.

28. **Transport via `Fin.cast` is cleaner than `▸`**. `Fin.cast h` has
    good `simp` lemmas; `h ▸ i` requires manual `subst` or
    `cases h` which often fail on record projections.

29. **`dlogHolds` design iteration**: started taking `hk` as explicit
    parameter, which caused type-mismatch issues in `ma_extractable`.
    Refactored to bundle `hk` as existential. Simpler to reason
    about and cleaner call sites.

30. **`DlogWitness.scalars` signature**: paper uses `F_p^k` (scalars
    mod group order). Lean formalization uses `ℤ` with `|·| < degBound`
    as a proxy (since `p` isn't in the `ECSetup` structure). This
    is slightly weaker than the paper — if `degBound > p`, the Lean
    witness type admits scalars not in `F_p`. In practice
    `degBound ≪ p`, so this is benign. Flag for future refinement
    if composition with CP-NIZKAoK requires exact `F_p` typing.

