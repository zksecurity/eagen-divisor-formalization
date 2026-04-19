# Axiom Elimination Plan

Target end-state for `#print axioms Divisor.ma_extractable`:

```
propext, Classical.choice, Quot.sound                               -- Lean foundations
Divisor.ECPoint.add_comm, add_assoc, neg_add_cancel                 -- Silverman group law
Divisor.hasse_weil_upper, hasse_weil_lower                          -- Hasse
Divisor.principal_divisor_iff                                       -- Silverman Cor 3.5
Divisor.weil_reciprocity_honest                                     -- Silverman Ch III
```

Eight classical axioms (plus three Lean foundations). All protocol-specific axioms eliminated.

**Axioms to remove** (5):
| Tag | Axiom | Dependencies |
|---|---|---|
| T1 | `logDerivCheckFn_fiber_count_bound` | Phase B |
| T2 | `logDerivCheckFn_badA₀_bound` | T1 + symmetry |
| T3 | `logDerivCheckFn_undefined_set_bound` | existing Bezout |
| T4 | `extractorSucceeds_of_logDerivCheck_identically_zero_general` | B + T5 + sign fix |
| T5 | `log_deriv_nonvanishing_criterion` | independent |

Total estimated effort: **~2000 LOC over 3–5 focused sessions**.

---

## Prerequisite: Extractor sign correction (P0)

### Problem

In the general case (`¬ negPIndexSet.Nonempty`), current `extractedScalars` returns `(groupSum i).val : ℤ` where `groupSum i = Σ msg.m j` in `ZMod E.q`. Under partial-fraction uniqueness, honest prover's `msg.m j = −β_j (mod q)`, so `groupSum.val = q − β_j` for `β_j > 0`. Treating this as an integer gives `q − β_j`, which in group arithmetic gives `[q − β_j]·B = [−β_j]·B = −β_j·B`. Summing over all B's: `−Σ β_j·B_j = −P`, not `P`. Off by sign.

### Fix

Change `extractedScalars i` in general case to `((−(groupSum i)).val : ℤ)` (or equivalently `(q − (groupSum i).val) mod q` cast to ℤ, taking 0 instead of q when `groupSum = 0`). This yields `β_j` directly.

Edge case: `groupSum i = 0` means `msg.m j = 0` for all j in the group, meaning the B_i is unmatched by σ. Extractor should return 0. Both old and new definitions do this (`-0 = 0`).

### Cascade

- `extractedScalars` def in `Divisor/Soundness.lean`.
- `extracted_scalars_valid_special`: unchanged (uses −1 directly).
- `extractorSucceeds_special`: unchanged (same scalar magnitudes).
- `Counterexample.lean`: re-verify the "fixed" predicate still holds.
- Bridge axiom hypothesis semantics: unchanged structurally, but conclusion now uses corrected scalars — axiom remains stateable.

### Scope

~40 LOC. Low risk. Should be first commit.

---

## Phase B: Polynomial identity for `clearedFiberPoly`

### Goal

Prove, as theorems, the three axioms currently marked as "polynomial form stubs" (which were previously added and removed):

1. `clearedFiberPoly_identity`: on non-vertical cone, `bivEval (clearedFiberPoly ... A₀) A₁ = (A₁.1 − A₀.1)^(D.degE + k + 6) · logDerivCheckFnCleared E D P k B m A₀ A₁`.
2. `clearedFiberPoly_natDegree_le`: (inner + outer degree bounds).
3. `clearedFiberPoly_modCurve_ne_zero`: when defined fiber is nontrivial.

### Sub-phase B1: Finset-sum helpers (~120 LOC)

Two helpers:

```
lemma bivEval_DAPartAtA₂Scaled_eq (hNV : A₀.1 ≠ A₁.1) :
  bivEval (DAPartAtA₂Scaled D A₀) A₁
    = (A₁.1 − A₀.1)^D.degE · D.a.eval(x₂(A₀, A₁))

lemma bivEval_DBPartAtA₂Scaled_eq (hNV : A₀.1 ≠ A₁.1) :
  bivEval (DBPartAtA₂Scaled D A₀) A₁
    = (A₁.1 − A₀.1)^D.degE · D.b.eval(x₂(A₀, A₁)) · y₂(A₀, A₁)
```

Proof: `Polynomial.eval_finset_sum` + per-term identity via `bivEval_x₂Scaled_eq` etc. + `ring` per summand. Combine via `Finset.sum_congr` + factor extraction.

Yields directly:
```
lemma bivEval_DAtA₂Scaled_eq, bivEval_DDerivAtA₂Scaled_eq :
  bivEval (DAtA₂Scaled D A₀) A₁ = (A₁.1 − A₀.1)^D.degE · D.eval(x₂, y₂).
```

### Sub-phase B2: per-term bivEval identities (~420 LOC: 5 × ~85 each)

One lemma per sub-term:

```
lemma bivEval_lhsTerm0Scaled_eq (hNV) :
  bivEval (lhsTerm0Scaled ...) A₁
    = (A₁.1 - A₀.1)^N · (num(A₀)·2·A₀.2·D(A₁)·D(A₂)·dxdzDen(A₁)·dxdzDen(A₂)
                         ·L(-P)·∏ L(B_j))
```

Strategy per lemma:
1. `unfold lhsTerm0Scaled`.
2. `simp only [bivEval_mul]` to distribute over the 7-factor product.
3. Apply per-factor identities: `bivEval_DDerivAtA₀Poly`, `bivEval_embedScalar`, `bivEval_DAtA₁Poly`, `bivEval_DAtA₂Scaled_eq`, `bivEval_dxdzDenA₁Scaled_eq`, `bivEval_dxdzDenA₂Scaled_eq`, `bivEval_linesProductScaled_eq`.
4. Factor `(A₁.1 − A₀.1)` powers.
5. `ring`.

Five sub-lemmas. Estimated ~85 LOC each after the helpers.

The helper `bivEval_linesProductScaled_eq` (~60 LOC):
```
bivEval (linesProductScaled P k B A₀) A₁
  = (A₁.1 − A₀.1)^(k+1) · L(-P) · ∏ L(B_j)
```
via `Finset.prod_congr` + per-factor identity on `lineEvalNumAt`.

### Sub-phase B3: main identity assembly (~50 LOC)

```
theorem clearedFiberPoly_identity ... : by
  unfold clearedFiberPoly
  rw [bivEval_add_four_times, bivEval_lhsTerm0Scaled_eq, ...]
  -- 5 summands in LHS; all have common factor (A₁.1 - A₀.1)^N
  unfold logDerivCheckFnCleared logDerivCheckFn logDerivCheckFnDenom
  ring
```

Tight: the final `ring` has to match 5 specific cleared terms against the expanded `logDerivCheckFnCleared`. May need `field_simp` or `linear_combination` if `ring` times out. Fallback: case-by-case coefficient matching (another ~100 LOC).

### Sub-phase B4: natDegree bounds (~80 LOC)

Two bounds: outer and inner.

Outer degree: `k + 3` (dominated by `linesProductScaled` outer-degree `k+1` times `dxdzDenA₁Scaled` outer-degree `1` times ..., max 3).
Inner degree: `O(D.degE + k)`.

Track via `natDegree_mul_le`, `natDegree_add_le`, `natDegree_pow_le`, `natDegree_sum_le`. Each sub-term bounded independently; max over sub-terms.

Final bound: `(clearedFiberPoly ...).natDegree ≤ outer_bound`, and via the resultantX argument (using inner degree), downstream `card_zeros_on_E_le` gives the desired count.

### Sub-phase B5: nonvanishing (~50 LOC)

```
theorem clearedFiberPoly_modCurve_ne_zero
    (hFiberNonzero : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    clearedFiberPoly ... %ₘ curveEqPoly E ≠ 0 := by
  obtain ⟨A₁, hA₁, hNV, hDef, hne⟩ := hFiberNonzero
  by_contra h_vanish
  -- f %ₘ curve = 0 ⇒ bivEval f A₁ = bivEval 0 A₁ = 0
  have : bivEval (clearedFiberPoly ...) A₁ = 0 := by
    rw [bivEval_eq_modByMonic_on_E E hA₁, h_vanish]; simp
  rw [clearedFiberPoly_identity E D P k B m A₀ A₁ hNV.symm] at this
  unfold logDerivCheckFnCleared at this
  -- (lamDen)^N · logDerivCheckFn · denom = 0
  -- lamDen ≠ 0 (hNV), denom ≠ 0 (hDef) ⇒ logDerivCheckFn = 0, contradicting hne
  have hlamPow : (A₁.1 - A₀.1)^N ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hNV.symm.symm)
  have hDenom : logDerivCheckFnDenom ... ≠ 0 := hDef
  exact hne (by
    have := mul_eq_zero.mp this
    rcases this with h | h
    · exact absurd h hlamPow
    · exact (mul_eq_zero.mp h).resolve_right hDenom)
```

### Phase B summary

| Sub-phase | LOC | Risk |
|---|---|---|
| B1 Finset-sum helpers | 120 | low |
| B2 per-term identities | 420 | medium |
| B3 main identity | 50 | medium (ring timeout) |
| B4 natDegree | 80 | low |
| B5 nonvanishing | 50 | low |
| **Phase B total** | **720** | medium |

Three commits: one per B1, one batched for B2–B3, one for B4+B5.

---

## T1: fiber count bound (~150 LOC, low-medium risk)

### Proof

```
theorem logDerivCheckFn_fiber_count_bound (A₀) (hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ => defined ∧ logDerivCheckFn = 0)).card
      ≤ 18·(D.degE + k + 6) + 2
    ∨ (∀ A₁ ∈ E.points, defined → logDerivCheckFn = 0) := by
  classical
  by_cases hAll : ∀ A₁ ∈ E.points, defined → logDerivCheckFn = 0
  · exact Or.inr hAll
  · left
    push_neg at hAll
    obtain ⟨A₁w, hA₁w, hDefw, hnew⟩ := hAll
    -- Case on whether A₀.1 = A₁w.1. If yes, witness is vertical;
    -- may or may not have non-vertical witness.
    by_cases hNVWitness :
      ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧ defined ∧ logDerivCheckFn ≠ 0
    · -- Non-vertical witness: apply clearedFiberPoly_modCurve_ne_zero.
      have hFpNZ : clearedFiberPoly ... %ₘ curveEqPoly ≠ 0 :=
        clearedFiberPoly_modCurve_ne_zero _ _ _ _ _ _ A₀ hNVWitness
      -- Split fiber into vertical (x = A₀.1, ≤ 2) and nonvertical (≤ K-2).
      calc fiber.card
          ≤ vertical_fiber.card + nonvertical_fiber.card := by ...
        _ ≤ 2 + nonvertical_fiber.card := by apply card_points_with_fst_eq_le
        _ ≤ 2 + 2 · (resultantX (clearedFiberPoly ...)).natDegree := by
            apply Nat.add_le_add_left
            apply le_trans _ (card_zeros_on_E_le _ _ hFpNZ)
            -- Show nonvertical_fiber ⊆ zero set of clearedFiberPoly via
            -- clearedFiberPoly_identity.
            ...
        _ ≤ 2 + 2 · (2 · clearedFiberPoly.natDegree + 3) := by
            apply Nat.add_le_add_left
            apply Nat.mul_le_mul_left
            exact resultantX_natDegree_le ...
        _ ≤ 2 + 2 · (2 · (outer_bound) + 3) := by
            apply ...
            exact clearedFiberPoly_natDegree_le ...
        _ ≤ 18·(D.degE + k + 6) + 2 := by omega
    · -- Only vertical witnesses: fiber ⊆ vertical, ≤ 2.
      push_neg at hNVWitness
      have : fiber.card ≤ 2 := ...
      omega
```

Key sub-lemma: `resultantX_natDegree_le` (from earlier attempts, needs re-proving with correct inner-degree tracking).

**Gotcha**: `resultantX.natDegree` bound needs INNER degree of `clearedFiberPoly`, not outer. Phase B4 must provide both.

---

## T2: bad A₀ count bound (~100 LOC, low risk)

### Approach: symmetry

Step 1: prove `logDerivCheckFn_symm` (~60 LOC).

```
theorem logDerivCheckFn_symm (A₀ A₁) :
    logDerivCheckFn E D P k B m A₀ A₁ = logDerivCheckFn E D P k B m A₁ A₀
```

Unfold, use `slopeOf_comm` (trivial), `lineThrough_comm`, show `μ` and `A₂` are symmetric. Each sub-term is symmetric in A₀ ↔ A₁: `logDerivTerm(A_i)` terms swap for i=0,1; i=2 invariant; RHS line factors depend only on chord (symmetric). ~60 LOC.

Similarly `logDerivCheckFnDefined_symm`.

Step 2: apply (~40 LOC).

```
theorem logDerivCheckFn_badA₀_bound (hGlobalNonzero) : badA₀.card ≤ K := by
  -- badA₀ = {A₀ : ∀ A₁, defined → logDerivCheckFn = 0}
  --       = {A₀ : ∀ A₁, defined_swap → logDerivCheckFn_swap = 0}  (by symm)
  --       = {A₀ : fiber at A₀ via "A₀ varies, A₁ fixed" viewpoint, identically 0}
  --
  -- Apply T1's contrapositive: if A₀ is bad, the A₀-fiber at a good A₁ must
  -- include A₀ as a zero. For a good A₁ (from hGlobalNonzero, with role-swap),
  -- card of such A₀'s is bounded.
  ...
```

Concretely: pick A₁* from hGlobalNonzero (after symm). By T1 applied with A₁* as the "fixed" slot (after symm), fiber bound gives `badA₀.card ≤ K`.

---

## T3: undefined set bound (~180 LOC, low risk)

### Structure

Denom = product of `k + 7` factors. Each factor `f`: bound `|{(A₀, A₁) ∈ E×E : f = 0}|` separately, then union-bound.

```
theorem logDerivCheckFn_undefined_set_bound :
    (undef).card ≤ 18·(D.degE + k + 6) · |E| := by
  -- Union of k+7 sub-events, each bounded.
  calc undef ⊆ DA₀_zeros ∪ DA₁_zeros ∪ DA₂_zeros
              ∪ dxdzA₀ ∪ dxdzA₁ ∪ dxdzA₂ ∪ LnegP ∪ (⋃ j, LBj) := by ...
    undef.card ≤ Σ [each factor's zero count] := Finset.card_union_le_of_iUnion_subset
  -- Per-factor bounds:
  -- DA_i: D.degE · |E| each
  -- dxdz*: 3 · |E| each (linear form on E)
  -- L factors: 3 · |E| each (line through 2 points meets E in ≤ 3)
  -- LBj's: 3·|E|·k (union)
```

### Per-factor bounds (sub-lemmas)

**DAtA₀_zeros**: `|{(A₀, A₁) : D(A₀) = 0}| = |{A₀ : D(A₀) = 0}| · |E| ≤ numZeros D · |E| ≤ D.degE · |E|`.

Need: `numZeros_le_degE`. Probably provable from existing `numZeros` definition. ~30 LOC.

**DAtA₁_zeros**: symmetric. Free.

**DAtA₂_zeros**: for each (A₀, A₁), A₂ = −(A₀+A₁). `D(A₂) = 0 ⟺ A₂ ∈ zeros(D)`. For each A₀, each zero Q of D, there's at most one A₁ with A₂ = Q (namely A₁ = −A₀−Q). So total ≤ `|E| · numZeros D ≤ D.degE · |E|`. ~40 LOC.

**dxdzDen zeros**: the factor `(3·A₀.1² + curveA)(A₁.1−A₀.1) − 2·A₀.2(A₁.2−A₀.2)` is linear in A₁ with A₀-dependent coefficients. For each A₀ (generic), `linear_form_zeros_le_three` gives ≤ 3 zeros on E. Total ≤ `|E| · 3`. ~30 LOC each, 3 factors total ≤ `9·|E|`.

**L(-P) zeros**: chord through (A₀, A₁) passes through −P. Three collinear points on E. Parameterize: for each A₀, set of A₁ collinear with A₀ and −P on E is at most 3 (the line through A₀ and −P meets E in ≤ 3 points, one is A₀, one is -P, so ≤ 1 A₁... actually ≤ 2 since the third intersection is also a candidate). Total ≤ `3·|E|`. ~30 LOC.

**L(B_j) zeros**: similarly `3·|E|` per j, union ≤ `3·|E|·k`. ~20 LOC.

**Sum**: `3·D.degE·|E| + 9·|E| + 3·|E| + 3·|E|·k ≤ (3·D.degE + 3k + 12)·|E| ≤ 18·(D.degE + k + 6)·|E|`. ✓

---

## T5: log_deriv_nonvanishing_criterion (~560 LOC, high risk)

### Sub-phase A1: Simple-pole partial-fraction lemma (~70 LOC, low risk)

File: new `Divisor/PartialFraction.lean`.

```
lemma simple_pole_fraction_zero {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → K) (c : ι → K) (hα : Set.InjOn α s)
    (h : (∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, (X - C (α j))) = 0) :
    ∀ i ∈ s, c i = 0 := by
  intro k hk
  have hE : (∑ i ∈ s, (C (c i) * ∏ j ∈ s.erase i, (X - C (α j)))).eval (α k) = 0 := by
    rw [h]; simp
  rw [Polynomial.eval_finset_sum] at hE
  rw [Finset.sum_eq_single k] at hE
  · simp only [eval_mul, eval_C, Polynomial.eval_prod, eval_sub, eval_X] at hE
    have hProdNZ : ∏ j ∈ s.erase k, (α k - α j) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      have hjs : j ∈ s := (Finset.mem_erase.mp hj).2
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      exact sub_ne_zero.mpr (fun heq => hjk (hα hjs hk heq).symm).symm
    exact (mul_eq_zero.mp hE).resolve_right hProdNZ
  · intro i hi hne
    simp only [eval_mul, eval_C, Polynomial.eval_prod, eval_sub, eval_X]
    have : ∃ j ∈ s.erase i, α k - α j = 0 :=
      ⟨k, Finset.mem_erase.mpr ⟨Ne.symm hne, hk⟩, by ring⟩
    obtain ⟨j, hj, hjz⟩ := this
    rw [Finset.prod_eq_zero hj hjz]; ring
  · simp
```

Self-contained. No Mathlib beyond standard polynomial API.

### Sub-phase A2: slope-μ-projection polynomial (~120 LOC, medium risk)

Define `polyFibK_λ : (ZMod E.q)[X]` as the polynomial whose coefficients are determined by β, m, Q, R (via `z_λ` projection).

```
noncomputable def zLambda (λ : ZMod E.q) (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  pt.2 − λ · pt.1

noncomputable def polyFibK
    {d M : ℕ} (λ : ZMod E.q)
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) : (ZMod E.q)[X] :=
  ∑ k : Fin d, C (β k) · ∏ k' ∈ Finset.univ.erase k, (X - C (zLambda λ (Q k')))
    · ∏ j : Fin M, (X - C (zLambda λ (R j)))
  + ∑ j : Fin M, C (m j) · ∏ k : Fin d, (X - C (zLambda λ (Q k)))
    · ∏ j' ∈ Finset.univ.erase j, (X - C (zLambda λ (R j')))
```

Key connection lemma (~60 LOC):
```
lemma polyG_eq_polyFibK_eval
    (Q β R m A₀ A₁) (hNV : A₀.1 ≠ A₁.1)
    (hslope : slopeOf ... = λ) (hmu : zLambda λ A₀ = μ) :
    polyG E Q β R m A₀ A₁ = (A₁.1 − A₀.1)^(d+M-1) · polyFibK λ Q β R m eval μ
```
(up to possibly extra factors — needs detailed check; paper argument is symbolic but the Lean form requires explicit scaling).

### Sub-phase A3: per-slope μ-count (~150 LOC, **HIGH RISK**)

Goal: for each λ except O((d+M)²) exceptions, set `V_λ := {μ : ∃ (A₀, A₁) chord slope λ intercept μ}` has `|V_λ| ≥ d + M`.

Strategy:
1. Parameterize chords with slope λ by intercept μ ∈ F_q. For fixed (λ, μ), line `y = λx + μ` meets E in ≤ 3 points (by `line_meets_cubic_le_three`).
2. Σ_μ #(pairs on line λ, μ) = Σ_μ binom(line-points(λ, μ), 2). Total over all λ, μ equals `|distinctPairs(E)| = |E|² − |E|` (using chord uniqueness: each ordered pair determines a unique (λ, μ)).
3. By averaging: Σ_λ Σ_μ binom(lp(λ,μ), 2) = |E|² − |E|. For each λ, Σ_μ binom(lp, 2) ≤ q · 3 (each line has ≤ 3 points, binom(3,2)=3). So mean over λ is (|E|²-|E|)/q ≈ |E|(|E|-1)/q.
4. By Hasse, |E| ≈ q, so mean ≈ q−1. Most slopes λ satisfy Σ_μ binom(lp(λ,μ), 2) ≥ q/2.
5. For such λ, the number of μ with lp(λ, μ) ≥ 2 is ≥ q/6 (since each contributes ≤ 3 to the sum). Thus `|V_λ| ≥ q/6` for most λ.
6. Since `d + M ≤ D.degE + k + 1 < q`, we have `q/6 ≥ d + M` for sufficiently large q (or d + M small). Where this bound is tight, may need to exclude small-q cases.

**Gotcha**: the averaging argument is paper-standard but requires:
- Total pair count (via `card_validPairs_lb` and careful counting).
- Hasse bound for |E|.
- Several inequality chases.
- ~150 LOC realistic.

**Alternative**: prove the weaker bound `|V_λ| ≥ d + M` for *some* λ (rather than most). Easier; pigeonhole on the total. Sufficient for our needs (we only need existence of a good λ with distinctness).

### Sub-phase A4: generic λ distinctness (~80 LOC)

Exclusion set: pairs (P₁, P₂) from `{Q_k} ∪ {R_j}` with `P₁ ≠ P₂` have `zLambda λ P₁ = zLambda λ P₂` iff `P₁.2 − P₂.2 = λ · (P₁.1 − P₂.1)`, a linear equation in λ. If `P₁.1 ≠ P₂.1`, exactly one bad λ; if `P₁.1 = P₂.1` (vertical pair), need `P₁.2 = P₂.2` (contradiction to distinctness) — so no bad λ in this case. Total bad λ's: ≤ binom(d+M, 2).

Combined with A3: |F_q| − binom(d+M, 2) − exception-slopes ≥ 1 good λ exists. Uses `D.degE + k + 1 ≤ q` etc.

### Sub-phase A5: σ assembly (~80 LOC)

Fix good λ from A3+A4:
- `polyG ≡ 0 on E × E` + A2 identity + A3 ≥ d+M values of μ ⇒ `polyFibK λ ...` has > `d+M−1 = (polyFibK).natDegree` zeros ⇒ `polyFibK λ ... = 0` in F_q[X] (by `card_roots'` + natDegree).
- Expand `polyFibK λ` as `Σ β_k · Π_{k'≠k}(X − z_λ(Q_{k'})) · Π_j(X − z_λ(R_j))` + similar.
- By A4 (distinctness at good λ): set `{z_λ(Q_k)} ∪ {z_λ(R_j)}` has `d + M` distinct elements.
- Regroup `polyFibK λ` into the simple-pole partial fraction form (multiply/divide by appropriate Π factors).
- Apply A1 (`simple_pole_fraction_zero`) to get `β_k + Σ_{j : z_λ(R_j) = z_λ(Q_k)} m_j = 0` for each k, and `m_j = 0` for j with `z_λ(R_j) ∉ {z_λ(Q_k)}`.
- By A4 distinctness: at good λ, each `z_λ(Q_k)` matches at most one `z_λ(R_j)` (and since Q's are distinct from R's modulo this projection). The match `R_j = Q_k` is forced at the z_λ-level.
- Lift to the point level: if `z_λ(Q_k) = z_λ(R_j)` at our good λ with distinct projections, and we've ruled out cross-collisions, then `Q_k = R_j` (since different points would have given a bad λ).
- Define σ(k) := that j. Injectivity from uniqueness.
- `β_k ≠ 0` (hypothesis) ⇒ matched. Produces `β_k + m_{σ(k)} = 0`. Unmatched j: `m_j = 0`.

### T5 summary

| Sub-phase | LOC | Risk |
|---|---|---|
| A1 simple-pole lemma | 70 | low |
| A2 slope-projection polynomial | 120 | medium |
| A3 per-slope μ-count | 150 | **HIGH** |
| A4 generic λ distinctness | 80 | medium |
| A5 σ assembly | 80 | low-medium |
| helpers / glue | 60 | low |
| **Phase A total** | **560** | high |

Four commits: A1 (standalone), A2 + A4 (polynomial + distinctness), A3 (counting), A5 (assembly + final theorem).

---

## T4: general-case extractor bridge (~330 LOC after sign fix)

### Sub-phase D1: `logDerivCheckFn ≡ 0` ⇒ `polyG ≡ 0` bridge (~120 LOC)

Input: `hAllZero : ∀ A₀ A₁ ∈ E × E, defined → logDerivCheckFn = 0`.

Steps:
1. Define `Q : Fin d → F_q²` = D's distinct affine zeros, `β : Fin d → F_q` = their multiplicities. (Finite since D ≠ 0 by admSet + `zeros D E.points`.)
2. Define `R : Fin M → F_q²` = `{-P} ∪ distinct(B_j)` (under `¬ negPIndexSet`, these are distinct).
3. Define `m' : Fin M → F_q` where `m'(-P index) = -1` and `m'(canonical i) = groupSum i`.
4. Show `clearedFiberPoly D P k B m A₀` equals a scalar multiple of `polyG E Q β R m' · (products of cross-factors)`. Scalar multiple comes from relating D's inside-factors to the explicit Q, β list.
5. Use `hAllZero` + `clearedFiberPoly_identity` (Phase B) ⇒ `bivEval(clearedFiberPoly) = 0` on defined non-vertical pairs.
6. By density of defined non-vertical pairs in E × E (only O((D.degE+k)·|E|) excluded), and `card_zeros_on_E_le`: `clearedFiberPoly %ₘ curveEqPoly = 0`.
7. Step 4's relation ⇒ `polyG %ₘ curveEqPoly = 0`, i.e. `polyG ≡ 0 on E × E`.

Risky step: #4's algebraic bridge between `clearedFiberPoly` and `polyG`. Paper sketches this; Lean makes it explicit.

### Sub-phase D2: apply T5 (~30 LOC)

Hypotheses: `polyG ≡ 0`, `D.degE < q`, Q and R distinct, β nonzero. Get σ, coefficient matching.

### Sub-phase D3: combinatorial extractor analysis (~100 LOC)

Under general case (`-P ∉ {B_j}`), σ : Fin d ↪ Fin M where M = k + 1.
- For k ∈ Fin d: `β_k + m'_{σ(k)} = 0`.
  - If σ(k) = (-P index): `m'_{-P} = -1` ⇒ `β_k = 1`. D's simple zero at -P. Uniqueness: exactly one k.
  - If σ(k) = canonical i (for some i : Fin k): `m'_i = groupSum i` ⇒ `groupSum i = -β_k` ⇒ `(-groupSum i) = β_k` ⇒ `(corrected) extractedScalars i = β_k` (using P0 sign fix).
- For unmatched j : range(σ)ᶜ: `m'_j = 0`.
  - For canonical i not matched: `groupSum i = 0` ⇒ `extractedScalars i = 0`.
  - For -P unmatched: contradicts hypothesis that D has -P as zero (required by hAllZero). Rule out.

Conclude: `extractedScalars i` equals the integer `β_{σ⁻¹(i)}` if i is matched, else 0. And `β_{σ⁻¹(i)} ≤ D.degE − 1` (since -P eats one unit). So `(extractedScalars i).natAbs ≤ D.degE − 1 < d`. ✓ `extractorSucceeds`.

### Sub-phase D4: group-law equation via principal_divisor_iff (~80 LOC)

Construct coeffs function `c : ECPoint E.q → ℤ`:
- c(-P as ECPoint) = 1.
- c(B_i as ECPoint) = extractedScalars i for canonical i, accumulating by group.
- c(∞) = -D.degE.
- c = 0 elsewhere.

Claim: `c` is principal (i.e., satisfies degree-zero and group-sum-zero).

- Degree: Σ c = 1 + Σ extractedScalars + (-D.degE) = 1 + (D.degE − 1) + (-D.degE) = 0. ✓
- Group sum: from σ data and `principal_divisor_iff`'s converse, D's actual divisor (the "real" one from D being a rational function) IS principal. But we've defined c via the σ-data, which matches D's divisor exactly on the support (by σ definition).

Issue: we don't have "D's divisor is principal as a function of divisor data" without D being genuinely a function. Is D genuinely a function? YES — `CoordRingElt` is a rational function on E. Its divisor should be principal by definition.

Gap: we'd need to axiomatize "every `CoordRingElt` has a principal divisor" — or derive it. Paper uses this implicitly.

**Resolution**: add a new axiom (kept, since it's AG classical):
```
axiom CoordRingElt.divisor_isPrincipal (D : CoordRingElt E.q) (hNZ : ¬ D.isZero) :
    IsPrincipal E (coefficientsOfDivisor D)
```
where `coefficientsOfDivisor D` extracts the divisor coefficient function.

But this is circular — we'd need to define `coefficientsOfDivisor` first.

**Alternative resolution**: just use `principal_divisor_iff`'s forward direction directly. The σ-data tells us c's degree = 0 (computed above) and group sum = 0 (computed from σ + β). Iff direction gives IsPrincipal. We don't actually need the "D's divisor is principal" meta-claim — we construct a specific c from σ-data and show it satisfies the two conditions directly.

Computed group sum:
`Σ c_P · P` in the group
= `[1]·(-P) + Σ_i [extractedScalars i]·B_i + [-D.degE]·∞`
= `-P + Σ_i [β_{σ⁻¹(i)}]·B_i + 0`
= `-P + Σ_k [β_k]·B_{σ(k)\text{-canonical}}`

If we can show `-P + Σ_k [β_k]·Q_k = 0` (the group sum being zero), we're done. Here Q_k are D's zeros with multiplicities β_k.

**Where does this come from?** Paper: D being a rational function means div(D) is principal, so the group sum of its divisor is zero. div(D) = Σ β_k · Q_k + (-deg)·∞, so `Σ β_k · Q_k = 0` in the group. Since Q_0 = -P (the simple zero), `1·(-P) + Σ_{k≠0} β_k · Q_k = 0`, so `-P = -Σ_{k≠0} β_k · Q_k`, so `P = Σ_{k≠0} β_k · Q_k = Σ β_k · B_{σ⁻¹ ≠ -P}`. Exactly what we need.

**Need**: "D is a rational function on E" (structurally true of `CoordRingElt`) implies "div(D) is principal".

This is a ***new classical axiom we'd need*** OR a derived fact. Let's call it `coordRingElt_divisor_principal` and add to the "kept" axiom list. It's pure AG and aligned with Silverman Ch 2.

Updated axiom list: 8 classical + 1 new = **9 classical axioms**.

### Sub-phase D5: assemble target = Σ [extractedScalars]·B_i (~50 LOC)

Given the group sum `P = Σ [β_k]·Q_{σ⁻¹(k)}` from D4, translate to canonical indices and apply `ECPoint.weightedSum` manipulation to conclude the extractor's relation.

### T4 summary

| Sub-phase | LOC | Risk |
|---|---|---|
| D1 logDerivCheckFn → polyG bridge | 120 | medium |
| D2 apply T5 | 30 | low |
| D3 combinatorics | 100 | medium |
| D4 principal divisor use | 80 | low (uses new axiom) |
| D5 assembly | 50 | low |
| **Phase D total** | **380** | medium |

Three commits: D1, D2+D3, D4+D5.

---

## Ordering and commits

### Recommended order

1. **P0** — Extractor sign fix (~40 LOC). One commit. Removes the soundness-gap in `extractedScalars`.
2. **T3** — Undefined set bound (~180 LOC). Independent of Phase B. Uses only existing infrastructure. Removes 1 axiom.
3. **Phase B (B1-B5)** — Polynomial identity (~720 LOC). Four commits. Enables T1, T2, T4.
4. **T1** — Fiber count bound (~150 LOC). One commit. Removes 1 axiom.
5. **T2** — Bad A₀ count via symmetry (~100 LOC). One commit. Removes 1 axiom.
6. **T5 A1** — Simple-pole lemma (~70 LOC). One commit, independent standalone.
7. **T5 A2+A4** — Polynomial + distinctness (~200 LOC). One commit.
8. **T5 A3** — Per-slope counting (~150 LOC). One commit. **CHECKPOINT** — if this doesn't converge, reassess.
9. **T5 A5** — σ assembly + `log_deriv_nonvanishing_criterion` as theorem (~80 LOC). Removes 1 axiom.
10. **T4 D1** — polyG bridge (~120 LOC).
11. **T4 D2-D5** — Apply T5 + combinatorics + principal_divisor_iff (~260 LOC). Removes 1 axiom.
12. **Final audit** — `#print axioms` verification + plan update + docs cleanup.

### Checkpoints

After step 5: build clean, 3 axioms removed (T3, T1, T2). Mid-checkpoint commit.
After step 9: build clean, 4 axioms removed (add T5). Pre-final checkpoint.
After step 11: build clean, all 5 axioms removed. Final state.

### Commit hygiene

- One atomic commit per sub-phase (B1, B2, etc.).
- Commit messages: "Phase X.Y: <what's proven>. Axioms remaining: N."
- Never skip signing policy.
- Never introduce sorries (revert if necessary; document blockers).

---

## Risk management

### Highest-risk items

1. **T5/A3 (per-slope counting)** — 150 LOC, high risk. If this doesn't converge, consider:
   - Weakening the per-slope bound claim (existence of one good λ instead of most).
   - Accepting a stronger hypothesis in T5 (e.g., `d + M small compared to q`).
   - Falling back to `log_deriv_nonvanishing_criterion` as a kept axiom (paper-cited); accept +1 to final axiom count.

2. **Phase B3 (main identity assembly)** — final `ring` may time out. Mitigations:
   - Use `linear_combination` with explicit sub-identities.
   - Stage via intermediate expression rewrites.
   - Worst case: manual coefficient matching, +100 LOC.

3. **T4/D1 (clearedFiberPoly to polyG bridge)** — algebraic translation step. Risk: 120 LOC may be insufficient. Mitigations:
   - Prove step-by-step with intermediate lemmas showing the bridge is a multiplicative relation.
   - Cross-check with paper's exact algebraic identity.

### Mitigating risks

- **Prototype first**: for each high-risk piece, attempt a 50-LOC prototype before committing to full implementation.
- **Allow fallbacks**: if Phase B doesn't converge, T1/T2 can remain axiomatic but with narrower scope.
- **Preserve existing progress**: each commit should leave the build clean and downstream intact. Use `git stash` for experiments.

---

## Success criteria

1. `lake build` succeeds with no errors and no `sorry`.
2. `#print axioms Divisor.ma_extractable` shows the 8–9 classical axioms listed at top + Lean foundations. **No** T1-T5 axioms remain.
3. `ma_extractable`, `ip_knowledge_sound`, `ma_completeness` compile unchanged at the statement level (modulo bound-constant propagation).
4. `Counterexample.lean` continues to exhibit the correct "fixed-state" behavior.
5. Plan document updated at each phase with status + any divergences.

## Non-goals

- Mechanizing `principal_divisor_iff`, `hasse_weil_*`, `weil_reciprocity_honest`, `ECPoint.add_*` — accepted as classical axioms.
- Removing Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) — impossible.
- Tightening probability bound constants to match paper's `18·(d+k)·q` exactly — asymptotic equivalence suffices.
- Mechanizing the alternative norm-based soundness route (`thm:bassa-monic`) — not on the dependency chain.

---

## Estimated calendar

Based on ~500 LOC/session for mechanical work + slower on high-risk pieces:

| Session | Content | LOC |
|---|---|---|
| 1 | P0 + T3 | 220 |
| 2 | Phase B1, B2 (partial) | 500 |
| 3 | Phase B2 (rest), B3, B4, B5 | 500 |
| 4 | T1, T2 | 250 |
| 5 | T5 A1, A2, A4 | 350 |
| 6 | T5 A3 (counting) | 150 |
| 7 | T5 A5 + T4 D1 | 200 |
| 8 | T4 D2–D5 | 260 |

**Total: ~8 sessions × ~250 effective LOC = ~2000 LOC over 8 sessions.**

Compared to earlier rough estimate (3–5 sessions, 1150 LOC), this extensive plan reveals the true scope: ~2000 LOC and 8 sessions. The additional scope comes from:
- Explicit polyG bridge for T4 (D1: +120 LOC).
- Extractor sign fix and cascades (P0: +40 LOC).
- Detailed natDegree bookkeeping in B4 (+30 LOC).
- PolyFibK construction and counting in A2+A3 (+100 LOC over rough estimate).
- Buffer for unexpected Mathlib gaps.

---

## Next action

Implement P0 (extractor sign fix) as first commit. It's independent, ~40 LOC, and removes a real soundness gap before any axiom elimination begins.

---

## Execution log

### Session 1 — P0 complete

**P0 — Extractor sign correction**: Done (`fe227de`).
- Changed general case of `extractedScalars` from `(groupSum).val` to `(-groupSum).val`.
- Captures paper's integer multiplicity `β_k` rather than `q − β_k`.
- No Lean downstream proofs broke (special case and valid_special lemmas untouched).
- Build clean.

Axiom count unchanged (fix was correctness, not axiom-removal).

### T3 attempted — blocked on degree infrastructure

**Finding**: Proving `numZeros_le_two_degE` (the key helper for T3) requires ~100 LOC of degree-parity reasoning that duplicates the logic already present in `CubicIntersection.lean`'s `resultantX_aux_ne_zero` + `card_zeros_on_E_le`. The cleanest path is to:

1. Instantiate `card_zeros_on_E_le` on `DAtA₁Poly` (the bivariate form of D).
2. Prove `DAtA₁Poly %ₘ curveEqPoly = DAtA₁Poly ≠ 0` when `¬ D.isZero` (outer degree already < 2, so mod-curve is identity).
3. Extract `numZeros ≤ 2·(resultantX DAtA₁Poly).natDegree ≤ 2·D.degE`.

Estimated ~60 LOC for `numZeros_le` via this route, then ~120 LOC for T3 assembly. Deferred pending Phase B work which shares the same infrastructure pattern.

### Revised realistic scope

The 8-session estimate assumed focused, single-topic sessions. In a continuous-execution setting, context constraints apply:

- **P0** achievable in a single response (done).
- **T3, T1, T2** are mechanical but each is ~150-250 LOC of intricate Lean polynomial algebra with high setup cost per session.
- **Phase B (polynomial identity)** is ~720 LOC and shares natDegree/bivEval infrastructure with T1-T3. Best done as one focused multi-session effort.
- **T5 (log_deriv_nonvanishing_criterion)** is ~560 LOC with a high-risk core step (A3, per-slope counting).
- **T4 (extractor general-case bridge)** is ~380 LOC, depends on B + T5.

### Current axiom state after P0

```
propext, Classical.choice, Quot.sound
Divisor.ECPoint.add_comm, add_assoc, neg_add_cancel             [kept]
Divisor.hasse_weil_upper, hasse_weil_lower                      [kept]
Divisor.principal_divisor_iff                                   [kept]
Divisor.weil_reciprocity_honest                                 [kept]
Divisor.log_deriv_nonvanishing_criterion                        [T5 target]
Divisor.extractorSucceeds_of_logDerivCheck_identically_zero_general  [T4 target]
Divisor.logDerivCheckFn_fiber_count_bound                       [T1 target]
Divisor.logDerivCheckFn_badA₀_bound                             [T2 target]
Divisor.logDerivCheckFn_undefined_set_bound                     [T3 target]
```

5 axioms to eliminate. Each session carves off one or two via the ordering in the plan's "Recommended order" section. Checkpoint commits at milestones per that ordering.

### Continuation path

Per the plan's dependency ordering:
1. **Next**: T3 via `numZeros_le_two_degE` helper + `support_disjointness` + per-factor bounds (dedicated session, ~200 LOC).
2. **Then**: Phase B sub-phases (B1 → B5, ~720 LOC over 2 sessions).
3. **Then**: T1 + T2 (~250 LOC, one session).
4. **Then**: T5 Phase A sub-phases (~560 LOC, two sessions, A3 is the risk checkpoint).
5. **Then**: T4 sub-phases (~380 LOC, one session).
6. **Finally**: audit + plan close-out.

Each step is a separate focused session.

### Session 1 final state (2026-04-19)

Commits:
- `e626435` — plan doc (this file, initial).
- `fe227de` — P0 extractor sign fix.
- `7012158` — plan: P0 logged.
- `50747e7` — plan: T3 approach + revised scoping.

T3 attempted twice (via `numZeros_le_two_degE` helper). Each attempt
ran aground on intricate natDegree-parity reasoning that duplicates
(but does not cleanly factor through) `resultantX_aux_ne_zero` in
`CubicIntersection.lean`. Both attempts reverted cleanly; no partial
sorry-laden code was committed.

**Key finding during T3 attempts**: the `DAtA₁Poly`-based route to
`numZeros_le_two_degE` is the right shape but needs ~80 LOC of
supporting natDegree bookkeeping for `DAtA₁Poly.natDegree < 2`
(outer variable) and `resultantX (DAtA₁Poly).natDegree ≤ D.degE`.
Both are provable by direct coefficient analysis of
`C D.a - C D.b * X`.

Each remaining session should use this finding as its starting point:
inline the natDegree analysis rather than trying to reuse
infrastructure built for different polynomial shapes (the generic
`clearedFiberPoly` machinery is higher-degree and has different
structural bounds).

### Session 2 (2026-04-19) — T3 helper landed

Commits:
- `0901e71` — T3 helper: `numZeros_le_two_degE` via `DAtA₁Poly` +
  `card_zeros_on_E_le`. ~94 LOC. Build clean.

**What landed**: The foundational helper plus its supporting lemmas in
`Divisor/ClearedPolyForm.lean`:
- `DAtA₁Poly_natDegree_lt_two`
- `DAtA₁Poly_coeff_zero` / `DAtA₁Poly_coeff_one` (= `D.a`, `-D.b`)
- `DAtA₁Poly_modByMonic_self` (mod-curve = self since natDegree < 2)
- `DAtA₁Poly_ne_zero_of_ab` (from `(D.a, D.b) ≠ (0,0)`)
- `DAtA₁Poly_xPart` / `DAtA₁Poly_yPart` (= `D.a`, `-D.b`)
- `resultantX_DAtA₁Poly_natDegree_le` (= `D.a² - D.b²·curveX`,
  natDegree ≤ `D.degE`)
- `numZeros_le_two_degE` (the headline result)

Hypothesis required: `¬ (D.a = 0 ∧ D.b = 0)`. When `D ≡ 0`, every pair
in `E × E` has denom = 0, so the `T3` axiom would need this hypothesis
in any case (or fail when `|E|^2 > 18·9·|E|`).

**Continuation path for T3** (next session, ~250 LOC):

The undefined set is `denom = 0`, where denom factors as
`D(A₀)·D(A₁)·D(A₂)·dxdz(A₀)·dxdz(A₁)·dxdz(A₂)·L(-P)·∏ⱼ L(Bⱼ)`
(7 + k factors). Bound each via union, with hypothesis
`hD : ¬ (D.a = 0 ∧ D.b = 0)` propagated from `logDerivCheckFn_zero_set_bound`.

Per-factor bounds (each is `≤ Cⱼ · |E|`):

| Factor | Approach | Cⱼ | LOC |
|---|---|---|---|
| F1 `D@A₀` | `(zeros D) ×ˢ E.points`, card ≤ `numZeros · |E| ≤ 2D.degE · |E|` | `2D.degE` | 20 |
| F2 `D@A₁` | symmetric to F1 | `2D.degE` | 15 |
| F3 `D@A₂` | per-A₀ slicing; A₂ via `thirdPoint_inj_on_A₁` (already proved) plus vertical-case ≤ 2|E| | `2D.degE+2` | 50 |
| F4 `dxdz@A₀` | per-A₀ via `bivEval_dxdzDenA₀Scaled`; resultantX natDeg ≤ 3, plus 4|E| degenerate | `7` | 50 |
| F5 `dxdz@A₁` | symmetric to F4 | `7` | 30 |
| F6 `dxdz@A₂` | per-A₀ via `bivEval_dxdzDenA₂Scaled`; natDegree analysis on the 4-th-power scaled polynomial | `~15` | 80 |
| F7 `L(-P)` | per-A₀, ≤ 3 collinear A₁'s on E | `4` | 40 |
| F8 `L(Bⱼ)` | union over j, ≤ 4 per j | `4k` | 40 |

Sum of constants: `4D.degE + 4k + ~40` ≤ `18·(D.degE + k + 6)`. ✓

**Key insights** for the per-factor proofs:
1. For F1, F2: just use `Finset.card_product` on `zeros(D) ×ˢ E.points`.
2. For F4, F5: the `bivEval_dxdzDenA*Scaled` identities (already in
   `ClearedPolyForm.lean`) give the polynomial form. The polynomial form
   captures `factor = 0` modulo a small (≤ 4) edge-case set; bound the
   polynomial zero set per A₀ via `card_zeros_on_E_le`.
3. For F3, F6: use the existing `*Scaled` polynomials (`DAtA₂Scaled`,
   `dxdzDenA₂Scaled`) and natDegree analysis. The non-vertical /
   vertical case split is needed.
4. For F7, F8: the line factor `L.eval Q` becomes a linear form
   `(Qy-A₀.2)·(A₁.1-A₀.1) - (Qx-A₀.1)·(A₁.2-A₀.2)`. For each A₀ ≠ Q,
   per-A₀ ≤ 3 zeros (line meets cubic).

**Cascade after T3 lands**:
- `logDerivCheckFn_zero_set_bound` needs `hD` propagation: extract from
  `hNonzero` (since `¬defined ∨ logDerivCheckFn ≠ 0` at some pair
  implies some denom factor is ≠ 0, which implies in particular
  `D.eval ≠ 0` somewhere, hence `D.a ≠ 0 ∨ D.b ≠ 0`).
- Soundness statement unchanged at the type level.

### Session boundary guidance

Future sessions should:
1. Budget 250-500 LOC of committed work per session.
2. Prototype one sub-lemma before the full sub-phase; if it compiles
   cleanly, continue; if it balloons, commit what works and stop.
3. Commit plan updates at each session boundary, documenting what
   landed and what remains.
4. Avoid introducing `sorry` at any commit point.
5. Re-read this plan at session start to remember the overall
   strategy.

Axiom count at end of session 1: **unchanged** (P0 was correctness,
not elimination). Target still 5 eliminations remaining.

### Session 3 (2026-04-19) — T3 F1+F2 factor bounds

Commits (this session):
- T3 F1+F2: D-factor zero bounds as standalone lemmas
  (`DAtA₀_zero_pairs_card_le`, `DAtA₁_zero_pairs_card_le`). ~55 LOC.

**What landed**: two per-factor bounds covering the `D(A₀) = 0` and
`D(A₁) = 0` contributions to the undefined set. Both thin wrappers
around `numZeros_le_two_degE` + `Finset.card_product`. Both take the
`hD : ¬ (D.a = 0 ∧ D.b = 0)` hypothesis that T3 will propagate.

Bounds: `|F1 pairs| ≤ 2·D.degE · |E|` and same for F2. Summed these
contribute `4·D.degE · |E|` ≤ `18·(D.degE + k + 6)·|E|` target.

**Remaining factor bounds** (for next session, referencing the F3-F8
map in session 2 log):
- F3 (D@A₂): `thirdPoint`-based; blueprint in `support_disjointness`
  proof (`SupportDisjoint.lean` `hS2_card + hS3_card`). ~60 LOC.
- F4 (dxdz@A₀), F5 (dxdz@A₁): per-A₀ polynomial via
  `dxdzDenA₀Scaled` / `dxdzDenA₁Scaled` + `card_zeros_on_E_le`.
  Each ~40 LOC with natDegree bookkeeping.
- F6 (dxdz@A₂): dxdzDenA₂Scaled outer natDegree analysis. ~60 LOC
  (most intricate — product of x₂Scaled² + curveA·lamDen⁴ + ...).
- F7 (L(-P)): per-A₀ polynomial `lineEvalNumAt A₀ (P.1, -P.2)` mod
  curveEq; natDegree ≤ 1, resultantX ≤ 3. Need A₀ ≠ -P edge. ~50 LOC.
- F8 (L(B_j)): union over j via F7 pattern. ~30 LOC.

After F3-F8: assemble union bound + thread `hD` through
`logDerivCheckFn_zero_set_bound` caller (extract from `hNonzero`: if
`D.a = 0 ∧ D.b = 0` then `D.eval ≡ 0` and `logDerivCheckFnDenom ≡ 0`,
contradicting the defined non-zero witness). Then replace T3 axiom
with theorem. Bound constants sum to ≤ `4·D.degE + 2·D.degE + 2 + 3 +
3 + C₆ + 3 + 3k` ≤ 18·(D.degE + k + 6) with some slack.
