# Eagen-construction session progress

**Branch:** `work/completeness`
**Plan file:** `~/.claude/plans/we-want-to-fix-steady-cocke.md`

## Next firing focus: bridge `chordCoordRingElt` to `divisorOfD_mul_add_when_chord_line_D2`

The `divisorOfD_mul_add_when_chord_line_D2` theorem (proved at 100
commits) requires the hypothesis `∀ x, rootMult x (normPoly D₂) ≤ 1`.
This holds for `chordCoordRingElt P Q` in the distinct-chord case
(P.1 ≠ Q.1, no tangent collision with third intersection). The
required bridge lemma:

```lean
theorem chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord
    (P Q : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (hxx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) :
    ∀ x : ZMod E.q,
      Polynomial.rootMultiplicity x
        (normPoly E (chordCoordRingElt E P Q)) ≤ 1
```

Proof sketch:
1. `natDegree (normPoly chord) = 3` (existing
   `natDegree_normPoly_chordCoordRingElt_nonvertical`).
2. Three distinct x-roots: `P.1, Q.1, A₂x` (via existing eval lemmas
   + `normPoly_eval_eq_D_mul_D_neg`).
3. As a Finset of size 3 contained in `(normPoly).roots.toFinset`.
4. `Polynomial.card_le_degree_of_subset_roots`: card of roots ≤ 3.
5. Since card of `roots` = sum of `rootMultiplicity`, and we have 3
   distinct elements each contributing ≥ 1, sum = 3 exactly.
6. Each x ∈ {P.1, Q.1, A₂x} has rootMultiplicity = 1; all others = 0.

Once this bridge lands, eagenBuild's chord step (multiplication of
the accumulator F by `chordCoordRingElt P Q` for distinct-chord pairs)
can directly invoke `divisorOfD_mul_add_when_chord_line_D2` for
divisorOfD-additivity.

## eagenBuild_length4 per-ECPoint status (May 2026, 137+ commits)

**All eight per-ECPoint cases COMPLETE:**

* `eagenBuild_length4_div_at_P₀ = 1`
* `eagenBuild_length4_div_at_P₁ = 1`
* `eagenBuild_length4_div_at_P₂ = 1`
* `eagenBuild_length4_div_at_P₃ = 1`
* `eagenBuild_length4_div_at_Q₀ = 0` (cancellation: chord-1 + vertical = 1+1 net 0 with -1 sign)
* `eagenBuild_length4_div_at_negQ₀ = 0` (cancellation: chord-2 + vertical = 1+1 net 0 with -1 sign)
* `eagenBuild_length4_div_at_generic_R = 0` (off all support)
* `eagenBuild_length4_div_at_infinity = -4` (already complete earlier)

**Downstream corollaries (for chord-residue identity hypotheses):**

* `eagenBuild_length4_normPoly_natDegree_eq_four` — natDegree = 4
  (from `divisorOfD = -4` at infinity).
* `eagenBuild_length4_explicit_ne_zero` — `¬ (D.a = 0 ∧ D.b = 0)`.
* `eagenBuild_length4_explicit_eval_zero_at_P_i` for i=0,1,2,3 —
  `D.eval P_i.1 P_i.2 = 0`.
* `eagenBuild_length4_explicit_eval_ne_zero_at_generic_R` —
  off the entire support, `D.eval R.1 R.2 ≠ 0`.
* `eagenBuild_length4_explicit_eval_ne_zero_at_Q_0` —
  third intersection of L_1, `D.eval ≠ 0`.
* `eagenBuild_length4_explicit_eval_ne_zero_at_negQ_0` —
  third intersection of L_2 (by sum-zero), `D.eval ≠ 0`.

**Helper added:** `divisorOfD_vertical_at_x₀_nonTwoTorsion_affine`
gives `divisorOfD ((X - x_0), 0) = 1` at `(x_0, y_0)` with `y_0 ≠ 0`.

These corollaries discharge `hβsup` (forward: input points are zeros)
and prepare the way for `hβcov` (reverse: zero implies input point
or Q_0/-Q_0/generic R, all of which contradict the pos-divisor) and
`hAccount` (sum-of-ordAt = 4 by per-point characterization) needed by
`chord_sum_eq_residue_sum`.

Branch state: 140+ commits since master, 8098 jobs build cleanly. Closure
pin shows `ma_extractable`/`ip_knowledge_sound` byte-for-byte unchanged
from master; `ma_completeness*` still gated on `weil_reciprocity_honest`
(now sound under strengthened bad-set predicate per B4).

**Zero-set characterization (May 2026, 146 commits):**

* `ECPoints_same_x_y_eq_or_neg` — y-uniqueness on E (helper).
* `eagenBuild_length4_explicit_zero_iff_input` — for Q ∈ E.points with
  `D.eval Q = 0`, Q is one of the four input points P_0..P_3. Combines
  per-ECPoint divisor characterization with curve y-uniqueness.
* `zerosFinset_eagenBuild_length4_eq` — exact Finset equality:
  `zerosFinset E (eagenBuild_length4_explicit ...) = {P_0, P_1, P_2, P_3}`.

This pins down `zerosFinset(eagenBuild_length4) = {P_0..P_3}` as an exact
Finset equality. Combined with the per-ECPoint ordAt characterization
(`ordAt = 1` at each P_i), this directly satisfies `chord_sum_eq_residue_sum`'s
`hβsup` and `hβcov` hypotheses for β_fun = `ordAt`. The `hAccount` (sum
of ordAt = 4) follows from the Finset cardinality.

Closure pin (verified post-zerosFinset_eq): `ma_extractable` /
`ip_knowledge_sound` byte-for-byte unchanged from master.
`ma_completeness*` still gated on (now-sound) `weil_reciprocity_honest`.

## MILESTONE: length-4-specific logDerivCheckFn = 0 theorem (May 2026, 150+ commits)

`Divisor/LogDerivEagenLength4.lean` (new file): the theorem
`logDerivCheckFn_zero_for_eagenBuild_length4` proves
`logDerivCheckFn E (eagenBuild_length4_explicit P_0 P_1 P_2 P_3) ... = 0`
for any "good" challenge pair `(A_0, A_1)`, modulo three per-pair
hypotheses: `hQline`, `hDen`, `hResidueMatch`.

**Critical**: this theorem's axiom closure does **NOT** depend on
`weil_reciprocity_honest`! Verified via `#print axioms`:

```
'Divisor.logDerivCheckFn_zero_for_eagenBuild_length4' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   Divisor.chord_fiber_product_eq_normZ_under_split,
   Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g]
```

Both axioms it depends on are already in `ma_extractable`'s closure
(soundness side), so they're "allowed".

What remains to fully discharge `weil_reciprocity_honest` for length-4:
* `hResidueMatch` — **REMAINING**: protocol-level identification of
  `{P_0..P_3}` with the honest message's structure
  `{(-P), B_j with multiplicities}`.
* `hQline` — **DISCHARGED** via `hQline_of_hGood_eagenBuild_length4`
  (Bezout-style argument: chord ∩ E ⊆ {A_0, A_1, A_2}, all of which
  have D ≠ 0 by `¬badPairCompletenessPred`). Derived internally.
* `hDen` — **DISCHARGED** via `hDen_of_hGood` (chord-derivative-denominator
  factorization at A_0, A_1, A_2). Derived internally from
  strengthened bad set.

## ma_completeness path forward

Length-4 alone is insufficient to discharge `weil_reciprocity_honest`
in `ma_completeness`'s closure: the honest divisor for general k bases
+ scalars requires general-N `eagenBuild`, not just length-4.

The length-4 theorem demonstrates THE PATTERN works:
* Constructive D from `eagenBuild_length4_explicit` is sound.
* Chord-residue machinery applies for length-4 inputs.
* Output `logDerivCheckFn = 0` modulo (i) protocol-level residue match
  and (ii) hDen (derivable from B4).

Next: extend `eagenBuild` to recursive general-N driver. Estimate:
~500 LOC for the driver + per-step divisor characterization +
generalized closures of all length-4 corollaries.

## Session checkpoint (May 2026, 164 commits)

**Length-4 theorem now requires only `hResidueMatch` from the user.**
All static prerequisites + per-pair side conditions (hQline, hDen) are
derived internally from genericity hypotheses + `¬badPairCompletenessPred`.

Headline state:
* `logDerivCheckFn_zero_for_eagenBuild_length4` — main theorem.
* Static: `eagenBuild_length4_explicit_ne_zero`, `splitsOnE`,
  `zerosFinset_eq`, `normPoly_natDegree_eq_four`, `ordAt_sum_eq_four`.
* Per-pair: `hQline_of_hGood_eagenBuild_length4` (Bezout chord),
  `hDen_of_hGood` (chord-derivative-denominator factorization at all
  three points A_0, A_1, A_2 + strengthened bad set).

Axiom closure (verified post-hDen):
```
[propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g]
```
Both Divisor-specific axioms are already in `ma_extractable`'s closure.
NO `weil_reciprocity_honest` dependency.

Still gated on `weil_reciprocity_honest` for `ma_completeness*`:
the bridge from honest message structure to length-4 inputs requires
either:
1. A general-N `eagenBuild` driver (the path forward in the audit plan).
2. A specialized length-4 wrapper for k=3 bases with all scalars 1
   (simplest applicable subcase; still doesn't replace the axiom in
   `ma_completeness` but demonstrates full discharge of that subcase).

**Residue sum expansion (May 2026, 165 commits):** The new theorem
`eagenBuild_length4_residue_sum_eq` provides a closed-form
expansion of the residue sum:
```
∑ Q ∈ zerosFinset E (eagenBuild_length4_explicit P_0 P_1 P_2 P_3),
  (ordAt E D Q : ZMod E.q) * (L.eval Q.1 Q.2)⁻¹
  = (L.eval P_0.1 P_0.2)⁻¹ + (L.eval P_1.1 P_1.2)⁻¹
    + (L.eval P_2.1 P_2.2)⁻¹ + (L.eval P_3.1 P_3.2)⁻¹
```
This is the key tool for discharging `hResidueMatch` from a specific
honest divisor structure. For e.g. `k=3` bases with all scalars 1
and `P_0 = -P_target, P_i = B_{i-1}`, the LHS expansion matches the
protocol RHS verbatim.

Closure of `eagenBuild_length4_residue_sum_eq`: only standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`). No new
mathematical axioms.

## HEADLINE: full discharge for simplest honest case (May 2026, 169 commits)

**`weil_reciprocity_honest_length4_simple`** — for the length-4 honest
divisor with k=3 bases all at scalar 1 and input list
`[(-P_target), B 0, B 1, B 2]`, proves
`logDerivCheckFn = 0` with **no user hypotheses beyond on-curve +
genericity + ¬badPairCompletenessPred**.

Axiom closure (`#print axioms`):
```
[propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g]
```

**This proves the formerly-axiomatic `weil_reciprocity_honest` is
constructively dischargeable for at least one honest divisor structure**.
The remaining work is generalizing the construction (eagenBuild) to
other honest divisor shapes (k≠3 bases, scalars > 1, doublings).

## INTEGRATION: `rejectSet_bound_length4_simple` (May 2026, 172 commits)

The end-to-end integration theorem: for the length-4 simple honest D,
the rejection set (pairs where `logDerivCheckFn ≠ 0` and chord is
non-vertical) has cardinality bounded by `(3·4 + 4) · |E.points|`
— exactly mirroring `ma_completeness`'s conclusion but specialized
to k=3 simple honest case.

Axiom closure (verified):
```
[propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g]
```

**Codex confirmed this was the right next step (Option C from strategy
consultation): "demonstrating actual replacement of `weil_reciprocity_honest`
dependency".**

Per Codex's recommended sequence:
* C ✓ DONE — specialized end-to-end integration without axiom.
* D PARTIAL — `MAProverMsg.IsHonestForLength4Simple` structure added
  (174 commits). Bridge theorem (drop-in replacement matching
  `weil_reciprocity_honest`'s signature) deferred due to `subst`
  issues with `stmt.k`/`msg.k` projections; structure itself is
  usable via direct application of `weil_reciprocity_honest_length4_simple`.
* A/B LATER — expand coverage (length-N, doublings) only after the
  replacement path is demonstrated.

**`MAProverMsg.IsHonestForLength4Simple` structure (Codex D-option-1):**
Captures all the hypotheses needed to discharge `weil_reciprocity_honest`
for the simple length-4 honest case:
- `hk_eq_3 : stmt.k = 3`, `hkm_eq_3 : msg.k = 3`
- 4 input points `P_0..P_3` with structural identifications
  (`P_0 = -P_target`, `P_i = stmt.bases (i-1)` for i=1,2,3)
- `h_toD_eq : msg.toD = eagenBuild_length4_explicit E P_0 P_1 P_2 P_3`
- `h_m_eq_one : ∀ i, msg.m i = 1`
- All genericity + on-curve hypotheses for length-4 simple discharge.

**Raw-form bridge (May 2026, 178 commits):**
`logDerivCheckFn_zero_via_isHonestForLength4Simple_raw` provides the
drop-in replacement for `weil_reciprocity_honest` using raw types
(target, B, D, m as parameters) instead of stmt/msg projections.
Avoids `subst` pain on Lean's `stmt.k`/`msg.k` projections.

Axiom closure (verified): no `weil_reciprocity_honest` dependency.
Both Divisor-specific axioms it uses are already in `ma_extractable`'s
closure.

## TOP-LEVEL HEADLINE (May 2026, 187 commits)

**`ma_completeness_via_isHonestForLength4Simple`** — fully-discharged
version of `ma_completeness` for the length-4 simple honest case.

Theorem: given a `IsHonestForLength4Simple` structure attesting to the
honest construction, plus standard verifier hypotheses (degree, admSet),
proves the rejection set is bounded by `(3·numZeros + 4) · |E.points|`
— same conclusion as the formerly-axiomatic `ma_completeness`.

Axiom closure (`#print axioms`):
```
[propext, Classical.choice, Quot.sound,
 Divisor.chord_fiber_product_eq_normZ_under_split,
 Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g]
```
**NO `weil_reciprocity_honest` dependency.**

Architecture (Codex-recommended factoring):
* `ma_completeness_parameterized` (Soundness.lean) — takes per-pair
  logDerivCheckFn-zero claim as a hook. Closure: standard Lean axioms only.
* Existing `ma_completeness` factored through this parameterized version,
  instantiated with the (sound but axiomatic) `weil_reciprocity_honest`
  for backward compatibility.
* Length-4 simple instantiation: provides the hook via the constructive
  bridge from `IsHonestForLength4Simple`, fully discharging the axiom
  for this case.

Helpers added to support the integration:
* `logDerivCheckFn_eq_under_stmt_k_eq_three` — cast bridge for `stmt.k = 3`.
* `hNV_of_hGood` — extracts `A_0.1 ≠ A_1.1` from `¬badPairCompletenessPred`
  via the strengthened bad set's diagonal + vertical-chord exclusions.
* `logDerivCheckFn_zero_via_isHonestForLength4Simple` — structure-level
  bridge to the discharge.

This proves the formerly-axiomatic `ma_completeness` is **constructively
dischargeable for the restricted k=3 simple honest case** — the strongest
demonstration that the Eagen-construction approach works end-to-end.

## Toward any-k completeness (May 2026, 193 commits)

Per Eagen 596.pdf §3.1.1, the next phase generalizes from length-4 to ANY-N.

**`Divisor/EagenBuildRecursive.lean`** (skeleton complete) — recursive
`eagenBuild` driver per the paper's algorithm:
* `EagenAccum` structure (point + accumulated polynomial).
* `eagenBuild_level0` — pair adjacent inputs, build chord lines (with
  vertical-chord fallback for `P = -Q`).
* `combine_higher_distinct` / `combine_higher_vertical` — level-(k+1)
  combine: `chord · a.poly · b.poly / (X-x(a))(X-x(b))`, with vertical
  branch for sum-zero termination.
* `eagenBuild_level_step` — one level of pairing.
* `eagenBuild_iterate` — fuel-based iteration to convergence.
* `eagenBuild` — top-level driver.

**Pending for any-k:**
1. Tangent-doubling case (`P = Q` in input list, e.g., k=2 scalars (1, 2)).
2. Length-4 reduction proof: `eagenBuild [P_0..P_3] = eagenBuild_length4_explicit ...`.
3. Divisor equation by induction on levels.
4. `IsHonestForAny` predicate (any-k variant of length-4 simple).
5. `ma_completeness_via_isHonestForAny`.

Multi-firing project; foundational length-4 path remains the demonstration.

## Session checkpoint (May 2026, 156 commits)

Major milestones achieved this session:

1. **Per-ECPoint divisor characterization** — 8 cases for length-4 eagenBuild
   (4 input points = 1, Q_0 = 0, -Q_0 = 0, generic R = 0, infinity = -4).
2. **D.eval = 0 / ≠ 0 corollaries** — at all 7 affine cases.
3. **`zerosFinset_eagenBuild_length4_eq`** — exact Finset equality of zeros.
4. **`ordAt_sum_eagenBuild_length4_eq_four`** — hAccount discharged.
5. **`splitsOnE_eagenBuild_length4`** — D's normPoly splits over F_q.
6. **`logDerivCheckFn_zero_for_eagenBuild_length4`** (NEW FILE: `LogDerivEagenLength4.lean`)
   — main length-4 theorem proving log-derivative check vanishes.
   **Critical**: closure includes only `chord_fiber_product_eq_normZ_under_split` and
   `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`
   (both already in ma_extractable closure). NO `weil_reciprocity_honest`.
7. **`hQline_of_hGood_eagenBuild_length4`** — Bezout-style derivation that
   chord through challenge pair doesn't hit any zero of D.
8. **WeilReciprocityDescent.lean fix** — post-B4 stale `show` pattern updated.

Remaining gaps for full ma_completeness discharge:
* General-N `eagenBuild` driver (currently length-4 only).
* `hDen` derivation from strengthened bad set (math confirmed via Codex
  consultation, Lean derivation pending — ~100 LOC of algebraic work).
* `hResidueMatch` — protocol-level identification of honest input list.

The length-4 case demonstrates the entire approach works end-to-end
without requiring `weil_reciprocity_honest` as an axiom.

## Static prerequisites for `chord_sum_eq_residue_sum` — COMPLETE

All static (not per-pair) prerequisites for applying
`chord_sum_eq_residue_sum` to length-4 `eagenBuild_length4_explicit`
are now proven:

* **`eagenBuild_length4_explicit_ne_zero`** — `D ≠ 0`.
* **`zerosFinset_eagenBuild_length4_eq`** — `zerosFinset = {P_0..P_3}`.
* **`eagenBuild_length4_normPoly_natDegree_eq_four`** — natDegree = 4.
* **`ordAt_sum_eagenBuild_length4_eq_four`** — `∑ ordAt over E.points = 4` (hAccount).
* **`splitsOnE_eagenBuild_length4`** — both splits + fiber rationality.
* **β_fun = ordAt = betaTrue** — definitional, `betaTrue_support` and
  `ordAt_pos_iff_zero` discharge `hβsup`, `hβcov`.

Closure pin verified: `ma_extractable`/`ip_knowledge_sound` byte-for-byte
unchanged from master after splitsOnE landed.

## Next steps

The remaining inputs to `chord_sum_eq_residue_sum` are *per-pair*
side conditions on `(A_0, A_1)`:

1. **`hQline`** — chord through (A_0, A_1) doesn't pass through any
   zero of D. Derivable from `¬badPairCompletenessPred` (which excludes
   D vanishing at A_0, A_1, A_2) via Bezout: chord ∩ E ⊆ {A_0, A_1, A_2},
   so any zero of D on the chord ∈ {A_i} — contradicts `¬bad`.
2. **`hDen`** — `3·pt.1² + curveA - 2λ·pt.2 ≠ 0` for pt ∈ {A_0, A_1, A_2}.
   Application/configuration-specific; may need additional bad-set
   strengthening or per-pair hypothesis.
3. **`hA*def`** — `D.eval ≠ 0` at A_0, A_1, A_2. Already extractable
   from `¬badPairCompletenessPred` (existing in
   `logDerivCheckFn_zero_of_explicit_divisor_data`).
4. **Application** — assemble via
   `logDerivCheckFn_zero_of_chord_residue_match` to get
   `logDerivCheckFn = 0` modulo `hResidueMatch`.
5. **`hResidueMatch`** — protocol-level identification of the four
   eagenBuild inputs as `{(-P)} ∪ {B_j (with multiplicities)}`. This
   is the genuinely protocol-level bridge.

Beyond length 4: extend `eagenBuild` recursively (big lift but
mechanical given the chord-line algebra is already proved).

## eagenBuild_length4 status (May 2026, 123 commits)

**Driver and universal divisor identity COMPLETE:**

```lean
noncomputable def eagenBuild_length4_explicit
    (P₀ P₁ P₂ P₃ : ZMod E.q × ZMod E.q) : CoordRingElt E.q :=
  (mulCoordRingElt E (chordCoordRingElt E P₀ P₁) (chordCoordRingElt E P₂ P₃))
    .divLin (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)

theorem divisorOfD_eagenBuild_length4_eq_chord_pair_minus_vertical
    (genericity hyps) (R : ECPoint E) :
    divisorOfD E (eagenBuild_length4_explicit ...) R
      = divisorOfD E (mulCoordRingElt L₁ L₂) R - divisorOfD E L_v R

theorem eagenBuild_length4_div_at_infinity
    (genericity hyps) :
    divisorOfD E (eagenBuild_length4_explicit ...) (0 : ECPoint E) = -4
```

**For the affine ECPoint cases**, plug into the universal identity:
* `R = P_i`: divisorOfD chord at P_i (1 if on chord, 0 else) - 0 (vertical doesn't vanish at P_i.1 ≠ Q_0x).
* `R = Q_0`: 1 + 0 - 1 = 0 (chord vanishes once, vertical vanishes once, cancel).
* `R = -Q_0`: 0 + 1 - 1 = 0 (chord_2 vanishes once, vertical vanishes once).
* `R generic`: 0 + 0 - 0 = 0.

Each specific R value requires its own theorem combining the universal
identity with `divisorOfD_chordCoordRingElt_chord_distinct`,
`divisorOfD_chordCoordRingElt_chord_pointwise`, and a "vertical at affine
P off x_0" lemma. Mechanical but verbose; ~100-200 LOC each.

## Branch state at firing (May 2026)

**99 commits since master, all building cleanly (8098 jobs).**

Closure pin verified clean: `ma_extractable`, `ip_knowledge_sound`,
`ma_completeness*` byte-for-byte unchanged from master. The
`weil_reciprocity_honest` axiom is now sound (B4 strengthened
precondition).

Verified properties (cross-case multiplicativity wall broken):

* `ordAt_nonTwoTorsion_closed_form` — closed-form via `commonRootMultRat`.
* `cross_case_T_deriv_eq_normPoly_deriv` — Codex's derivative identity
  `B₁·T'(x₀) = -B₂·N(D₁)'(x₀)`.
* `cross_iterDivLin_invariant_when_min_eq_one` — full base case.
* `ordAt_mul_add_at_nonTwoTorsion_when_normPoly_D2_le_one` — unified
  ord-additivity at non-2-torsion under chord-line hypothesis.
* `divisorOfD_mul_add_when_chord_line_D2` — full divisorOfD-additivity
  at every ECPoint under chord-line hypothesis.

## Headline achievement

**The originally-defective `weil_reciprocity_honest` axiom is now
empirically sound** (B4 complete). The audit's first goal — "the
current axiom used is untrue" — has been addressed by strengthening
the bad-set predicate in `Divisor/SupportDisjoint.lean`. The Sage
STRONG-BAD-SET PASS shows 0 failures over 7542 challenges. The
F_5 doubling counterexample is now in the bad set, so the axiom
doesn't claim anything about it.

**ordAt-additivity at every ECPoint under chord-line multiplication
is FULLY PROVEN.** This includes the cross-case (D₁ lone at P, D₂
lone at -P) which previously appeared to require substantial
local-ring infrastructure. Achieved via:

* Closed-form `ordAt_nonTwoTorsion` via `commonRootMultRat` and
  `iterDivLin`.
* Codex's polynomial derivative identity
  `B₁·T'(x₀) = -B₂·N(D₁)'(x₀)`.
* `cross_iterDivLin_invariant_when_min_eq_one` (base case for chord
  lines, sufficient for eagenBuild).
* Composition with existing nonvan-fiber, lone-sheet, twin-descent
  lemmas via case dispatch + induction.

Final theorem: `divisorOfD_mul_add_when_chord_line_D2` covers all
chord lines through distinct affine points and vertical lines through
(P, -P) pairs.

Remaining for full B5 (axiom replacement):
* eagenBuild driver definition (recursion on lists of ECPoints).
* eagenBuild correctness theorem (`eagenBuild_div_eq`).
* Tangent line case extension (m₂ = 2; deferred — most eagenBuild
  uses don't hit this).
* B1 (constructive `isHonestFor`), B2 (resultant identity),
  B3 (logDerivCheckFn = 0), B5 (axiom delete + rewire).

## Final session summary

This branch (`work/completeness`) lands ~3450 lines of new Lean
across two main files plus 4 test files, in 60 commits. Verification:

* `lake build Divisor`: 8098 jobs, success.
* `Tests/AxiomClosurePin.lean`: `ma_extractable` and `ip_knowledge_sound`
  axiom closures byte-for-byte unchanged from `master`. `ma_completeness*`
  still depends on `weil_reciprocity_honest` (now sound under the
  strengthened precondition; B5 will replace it with a theorem once
  eagenBuild correctness is in place).
* `Tests/RegressionDoublingChallenge.lean`: F_5 doubling counterexample
  preserved (`claim_F5 = 2`).
* `Tests/IncrementalSmokeTest.lean` and `Tests/CrossCaseSmokeTest.lean`
  confirm chord-line algebra and cross-case ordAt-additivity at
  concrete F_5 configurations.
* `divisors-axiom-tests` (SageMath): STRONG-BAD-SET PASS shows
  7542 good challenges, 0 failures over 28 curves at q ∈ {5..23}.

## Key files modified / added

* `Divisor/IncrementalConstruction.lean` (NEW, 2522 lines) —
  chord-line foundations, multiplication, divLin, recursive
  identities, sub-cases of ordAt-additivity, eagenBuild base cases
  for lengths 2 and 3.
* `Divisor/SupportDisjoint.lean` (extended to 928 lines) — strengthened
  `badPairCompletenessPred` with diagonal + tangent-collision
  exclusions; new card-bounds via `thirdPoint_inj_on_A_1` + swap
  bijection; updated `support_disjointness` to `(3N+4)·|E_aff|`;
  `thirdPoint_symm`.
* `Divisor/Soundness.lean` — bumped `ma_completeness` and
  `ma_completeness_clean` constants to match.
* `Tests/RegressionDoublingChallenge.lean` (renamed from `AxiomCheck.lean`)
  — F_5 doubling counterexample regression.
* `Tests/IncrementalSmokeTest.lean`, `Tests/CrossCaseSmokeTest.lean`
  (NEW) — concrete F_5 verifications.
* `divisors-axiom-tests/test_weil_reciprocity_honest.py` — extended
  with strengthened-bad-set test (STRONG-BAD-SET PASS).
* `axioms/weil_reciprocity_honest.md` — annotated with audit-fix status.

## Summary

This session built out the foundation layer for Eagen's algorithmic
principal-divisor construction (eprint 2022/596 §3.1.1) in
`Divisor/IncrementalConstruction.lean` (~2520 lines).

All theorems are **closure-clean** — depend only on `propext`,
`Classical.choice`, `Quot.sound`. No project-specific axioms pulled
in. The `Tests/AxiomClosurePin.lean` confirms `ma_extractable`,
`ip_knowledge_sound`, `ma_completeness*` axiom closures byte-for-byte
unchanged from `master`.

## What landed

### Chord-line layer
- `chordCoordRingElt P Q` — three-branch dispatch (chord, tangent at
  non-2-torsion, vertical / 2-torsion).
- Non-zero-ness, evaluation lemmas at P, Q, third intersection.
- `normPoly` factorisation for both vertical (`(X − x₀)²`) and
  non-vertical (`(λX + μ)² − curveX`) branches via Vieta.
- `splitsOnE` unified across all three branches.
- Per-point `ordAt` exact multiplicities (chord: 1+1+1, tangent: 2+1,
  vertical-inverse: 1+1, 2-torsion: 2).
- `divisorOfD` identification at every relevant ECPoint per branch.
- Off-support divisor zero (chord case).
- Total degree zero verified.

### Multiplication layer
- `mulCoordRingElt` definition + commutativity + eval correctness.
- **`normPoly_mul_eq`**: `N(D₁·D₂) = N(D₁)·N(D₂)` (key algebraic
  identity, ring-level proof).
- `natDegree_normPoly_mul_eq` (additivity at infinity).

### `divLin` cancellation layer
- `divLin` reuse from `OrdP/Uniformizer.lean`.
- `divLin_eval_mul_X_sub_C` — eval correctness.
- `mulCoordRingElt_divLin_left` — the algebraic compatibility lemma
  used in the recursive ordAt induction.

### Wrapper-level recursive identities
- `ordAt_aux_fuel_irrelevant` at non-2-torsion (strong induction on
  natDegree-sum).
- `ordAt_nonTwoTorsion_twin_rec` (multiplier 1).
- `ordAt_twoTorsion_divLin_rec` (multiplier 2 via
  `normPoly_divLin_factor`).

### Multiplication ordAt-additivity (sub-cases)
- `ordAt_mul_add_twoTorsion` — 2-torsion P (always, via
  rootMultiplicity_mul + normPoly_mul_eq).
- `ordAt_mul_add_at_nonvanish` — neither factor vanishes at P
  (trivial: all three ords zero).
- `ordAt_mul_add_at_lone_sheet` — D₁ lone at P AND D₂ non-vanishing on
  fiber {P, −P}.
- `ordAt_mul_add_at_lone_sheet_swap` — symmetric.
- `ordAt_mul_add_at_nonTwoTorsion_when_D2_nonvanish` — full non-2-torsion
  when D₂ non-vanishing on fiber. Strong induction on D₁'s
  natDegree-sum, dispatching all three sub-cases (nonvanish, lone,
  twin) with twin descending via `mulCoordRingElt_divLin_left`.
- `ordAt_mul_add_when_D2_nonvanish_fiber` — unified theorem
  combining 2-torsion + non-2-torsion under one hypothesis.
- `divisorOfD_mul_add_affine_when_D2_nonvanish_fiber` — divisor lift.
- `divisorOfD_mul_add_at_infinity` — additivity at the pole.
- `divisorOfD_mul_add_when_one_factor_nonvanish_fiber` — disjunctive
  variant (either D₁ or D₂ non-vanishing on fiber).

### eagenBuild base cases
- `eagenBuild_length3_chord_correctness` — full divisor identification
  for length-3 lists in chord branch.
- `eagenBuild_length2_inverse_correctness` — vertical inverse pair.
- `eagenBuild_length2_2torsion_correctness` — 2-torsion doubling.

### Test files
- `Tests/RegressionDoublingChallenge.lean` — F_5 doubling counter-
  example to the unsound `weil_reciprocity_honest` axiom (preserved
  as regression).
- `Tests/IncrementalSmokeTest.lean` — concrete F_5 chord-line evaluation.
- `Tests/CrossCaseSmokeTest.lean` — concrete F_5 cross-case
  ordAt-additivity verification.

### Sage tests (`/Users/rot256/src/divisors-axiom-tests/`)
- Extended `test_weil_reciprocity_honest.py` with `lean_in_bad_set_strong`
  + STRONG-BAD-SET PASS: 7542 good challenges, 0 failures over 28
  curves, empirically confirming the planned strengthened bad-set
  predicate is sound.
- README annotated with the (∗) caveat about the current axiom.

## What remains

### Cross-case ordAt-additivity (the genuine obstacle)
The case where:
* `D₁` is **lone** at `P` (D₁(P) = 0, D₁(-P) ≠ 0)
* `D₂` is **lone** at `−P` (D₂(P) ≠ 0, D₂(-P) = 0)
The product `D₁·D₂` is **twin** at `P`, but neither factor's `divLin`
reduction directly applies (D₁ doesn't have (X-C P.1) | a, b; D₂
doesn't either).

This iteration verified additivity holds empirically in several F_5
configurations:
* `m = n = 1`: ord = 1
* `m = n = 3` (tangent doubling): ord = 3
* `m = 3, n = 1`: ord = 3

The pattern: ord(D₁·D₂)(P) = ord(D₁)(P) + 0 = m always (in cross
case where D₂(P) ≠ 0).

**Codex's recommended approach:** define a local valuation `v_P` in
the open where `Y + P.2` is inverted (where the maximal ideal is
generated by `X − C P.1`), prove `v_P` is multiplicative, then prove
`ordAt = v_P` at non-2-torsion by induction. This requires several
hundred lines of new local-ring formalisation (mathlib's
`DiscreteValuationRing` may help but the path through
`WeierstrassCurve.Affine.CoordinateRing.XYIdeal'` localisation is
non-trivial).

### eagenBuild driver + correctness
Length-4+ recursion documented inline in `IncrementalConstruction.lean`:
1. Build chord lines L_1, L_2 (through P_0,P_1 and P_2,P_3).
2. Build L_3 = chord through −Q_0, −Q_1 (vertical since their sum is 0).
3. Multiply L_1·L_2·L_3 then divide by (X − x_{Q_0})·(X − x_{Q_1}).

Eagen's recursion *inherently* generates cross-case configurations
(e.g., L_1 supports Q_0; L_3 supports −Q_0; their fibers share x-coord),
so cannot be proven correct without the cross-case piece above.

### Workstream B (axiom replacement)
- B1: rewrite `isHonestFor` constructively.
- B2: elliptic-resultant identity from eagenBuild.
- B3: log-derivative identity `logDerivCheckFn_zero_for_eagenBuild`.
- B4: strengthen `badPairCompletenessPred` in Lean (Codex confirmed
  bound: |S_5| ≤ |E.points|; |S_6| ≤ 4·|E.points|; combined with
  diagonal gives `(3N + ≤6)·|E.points|` total). Card-bound proof
  needs `thirdPoint_inj_on_A₁` + group-law translation.
- B5: delete `weil_reciprocity_honest` axiom + rewire `ma_completeness`.

All of B1–B5 are blocked on A6 (eagenBuild correctness), which is
blocked on the cross-case ordAt-additivity.

## Why even length-4 eagenBuild correctness needs the cross case

A natural hope is that eagenBuild correctness for short lists
(length 4, 5, etc.) might bypass the cross case under generic
assumptions on the input. **It does not**: Eagen's recursion
inherently produces cross-case configurations.

Concretely, for `[P_0, P_1, P_2, P_3]` with `P_0+P_1+P_2+P_3 = 0`:

* `L_1 = chord(P_0, P_1)` supports `{P_0, P_1, Q_0}` where
  `Q_0 = -(P_0+P_1)`.
* `L_2 = chord(P_2, P_3)` supports `{P_2, P_3, Q_1}` where
  `Q_1 = -(P_2+P_3)`.
* By assumption `Q_0 + Q_1 = 0`, so `Q_1 = -Q_0`.
* `L_3 = chord(-Q_0, -Q_1) = chord(-Q_0, Q_0)` is **vertical** at
  `x = x(Q_0)`, with support `{Q_0, -Q_0}`.

Now at `Q_0`:
* `L_1` is **lone at Q_0** (L_1(Q_0)=0, L_1(-Q_0) ≠ 0 generically).
* `L_3` **vanishes at both sheets** {Q_0, -Q_0} (since it's the
  vertical line through them).

So the product `L_1 · L_3` at Q_0 has D₁=L_1 lone at Q_0 and D₂=L_3
not non-vanishing on the fiber `{Q_0, -Q_0}` — exactly the cross
case. There's no generic configuration that avoids this.

Therefore **eagenBuild correctness for length ≥ 4 fundamentally
requires the cross-case ordAt-additivity**, which in turn requires
the local valuation v_P construction.

## Why strong-induction on natDegree-sum stalls (negative result)

A natural attempt is to prove submultiplicativity
`ord(D₁·D₂)(P) ≥ ord(D₁)(P) + ord(D₂)(P)` by strong induction on
`D₁.natDegree-sum + D₂.natDegree-sum`. Combined with the same at `-P`
and the pair-sum identity, additivity follows.

The induction handles three of four sub-cases cleanly:
* Non-vanish at P → both ords are 0.
* Lone × non-vanish-fiber → covered by the existing
  `ordAt_mul_add_at_lone_sheet`.
* Twin × anything → use `mulCoordRingElt_divLin_left` to reduce
  `(D₁·D₂).divLin` to `D₁.divLin · D₂`; IH on D₁'s reduced
  natDegree-sum closes.

But the cross case (`D₁` lone at `P`, `D₂` lone at `-P`, neither twin)
**stalls**: `(D₁·D₂).divLin` exists (both `(D₁·D₂).a` and
`(D₁·D₂).b` vanish at `x₀` — algebraic identity verified) but does
NOT factor as `D₁' · D₂'` for any smaller `D₁'`, `D₂'`. The IH would
need to be a statement about ARBITRARY CoordRingElt, but
submultiplicativity is itself a statement about products, not
arbitrary elements. Circularity.

The `v_P` valuation construction (Codex's recommendation) bypasses
this by working directly in the local ring, where multiplicativity
is built into the valuation axioms.

## Cross-case algebraic analysis (additional notes)

This session's analysis worked out the cross-case structure
algebraically:

For non-2-torsion `P = (x_0, P.2)`, when `D₁` is lone at `P` (so
`D₁.b(x_0) ≠ 0` and `D₁.a(x_0) = D₁.b(x_0)·P.2`) and `D₂` is lone at
`-P` (so `D₂.b(x_0) ≠ 0` and `D₂.a(x_0) = -D₂.b(x_0)·P.2`):

**Both `(D₁·D₂).a` and `(D₁·D₂).b` vanish at `x_0`** (verified by
direct substitution and using `P.2² = curveX(x_0)` from the curve
equation). So `(D₁·D₂).divLin x_0` makes sense.

`(D₁·D₂).divLin.eval(P) = D₂.b(x_0) · ∇_curve(D₁)(P)`

where `∇_curve(D₁)(P) = -2·P.2·∂x(D₁)|_P + D₁.b(x_0)·(3x_0² + A)`
is the directional derivative of `D₁` along the curve at `P`. This
vanishes iff `D₁` has order `≥ 2` at `P` (in the local ring).

Symmetrically, `(D₁·D₂).divLin.eval(-P) = D₁.b(x_0) · ∇_curve(D₂)(-P)`,
vanishing iff `D₂` has order `≥ 2` at `-P`.

So the recursion structure at `P` for `D₁·D₂`:
* Level 0: twin (both `(D₁·D₂)(±P) = 0`).
* Level 1 at `P`: vanishes iff `m = ord(D₁)(P) ≥ 2`.
* Level 1 at `-P`: vanishes iff `n = ord(D₂)(-P) ≥ 2`.
* ... and so on, with `m + n - 2k` rootMult after `k` levels.

The recursion expends `m` levels at `P` (one per "directional
derivative order of `D₁`"), then bottoms out. Total
`ord(D₁·D₂)(P) = m = ord(D₁)(P) + ord(D₂)(P) = m + 0`.

This is the underlying reason additivity holds — but proving it
formally requires either:
1. Establishing the local-ring valuation `v_P` and the equivalence
   `ordAt = v_P` via mathlib's `IsLocalization.AtPrime` infrastructure
   (clean but heavy);
2. A direct induction on (`m + n`) tracking "directional derivative
   structure" through each `divLin` step (concrete but messy);
3. A more clever mathematical observation tying the cross-case
   structure to a known identity.

The `Tests/CrossCaseSmokeTest.lean` regression check confirms the
formula at concrete F_5 configurations.

## Picking up

The `Tests/CrossCaseSmokeTest.lean` provides regression checks any
formalisation of the cross case must satisfy.

### Recommended approach (Codex consult, May 2026)

Codex's recommendation: bypass iterated `divLin` (route (b)) and DVR
infrastructure (route (a)) in favour of a closed-form route (d):

> Prove a closed-form lemma at the `branchRat / commonRootMultRat` layer,
> then bridge back. The clean recursive invariant is: after `r` twin
> divisions, `r = min m n`; the residual is lone at P if `n < m`, lone
> at -P if `m < n`, and nonvanishing on both if equal.

**Concretely, prove:** at non-2-torsion P (`y_0 ≠ 0`),

```
ordAt_nonTwoTorsion E D P =
  let m := rootMult P.1 (normPoly E D)
  let k := commonRootMultRat D.a D.b P.1     -- max j s.t. (X-x_0)^j | both
  let D̃ := D.divLin x_0 iterated k times    -- fully strip common factor
  if D̃.eval P.1 P.2 = 0 then m - k else k    -- branch on residual
```

This is provable by induction on `k` (each level strips one (X-x_0)
from each component, halves the normPoly's rootMult by 2). The base
case `k = 0` is the 3-way recursion leaf (nonvan, lone-at-P,
lone-at-(-P)).

Once we have this closed form, **multiplicativity** at non-2-torsion
follows from a 3-case analysis on which branch `D̃₁₂` falls into,
combined with the pair-sum identity (already proved at
`Divisor/OrdP/LocalRing.lean:626`) and `normPoly_mul_eq` (rootMult of
norm products adds). No iterated descent required.

**Cross-case verification:** in cross case at non-2-torsion P
(`D₁` lone at P with mult `m_1`, `D₂` lone at -P with mult `m_2`),
we have `D₁·D₂` with `m_norm = m_1 + m_2`, `k = min(m_1, m_2)` (after
stripping common factor), `D̃₁₂` lone at the sheet of the factor with
larger `m_i` (or nonvan if `m_1 = m_2`). Closed form returns:
* if `m_1 > m_2`: `D̃₁₂` lone at P, so output `m - k = (m_1+m_2) - m_2 = m_1`. ✓
* if `m_1 < m_2`: `D̃₁₂` lone at -P, so output `k = m_1`. ✓
* if `m_1 = m_2`: `D̃₁₂` nonvan, so output `k = m_1`. ✓

In all sub-cases, `ord(D₁·D₂)(P) = m_1 = ord(D₁)(P) + ord(D₂)(P)`. ✓

### Implementation plan

1. **Define `commonRootMultRat`** for two polynomials over `ZMod E.q`
   (rational analog of `commonRootMultiplicity`). Place in
   `Divisor/IncrementalConstruction.lean`. Foundation lemmas:
   `commonRootMultRat_le_left`, `_le_right`, `commonRootFactorRat_dvd_left`,
   `_dvd_right`. **DONE** (commit 6befe22, 12a1a5e).
2. **Prove `ordAt_nonTwoTorsion_closed_form`** by induction on
   `commonRootMultRat D.a D.b P.1`. **DONE** (commit 456e3fb).
3. **Prove `ordAt_mul_of_right_eval_ne_zero`** (Codex's
   recommendation): when `D₂.eval P.1 P.2 ≠ 0` (so `D₂` is a unit in
   the local ring at P), `ord(D₁·D₂)(P) = ord(D₁)(P)`. This subsumes
   both the existing `ordAt_mul_add_at_lone_sheet` (when D₂ also
   nonvan at -P) and the cross case (when D₂(-P) = 0).

   Proof strategy:
   - Induct on `D₁.a.natDegree + D₁.b.natDegree`.
   - Case D₁(P) ≠ 0 (`D₁` unit at P): `ord(D₁)(P) = 0`,
     `(D₁·D₂)(P) ≠ 0`, so `ord((D₁·D₂))(P) = 0`. ✓
   - Case D₁(P) = 0 ∧ D₁(-P) = 0 (`D₁` twin): use
     `mulCoordRingElt_divLin_left`, twin-recursion, IH on `D₁.divLin`.
   - Case D₁(P) = 0 ∧ D₁(-P) ≠ 0 (`D₁` lone at P) — the cross case
     when also D₂(-P) = 0:
     * Use closed form on `D₁·D₂`: need to compute
       `commonRootMultRat (D₁·D₂) P.1` and the branch of
       `iterDivLin (D₁·D₂) P.1 k`.
     * Auxiliary lemma: `iterDivLin (D₁·D₂) P.1 k₁ = D̃₁ · D₂` when
       `(X − x₀)^k₁` divides D₁.a, D₁.b (since divLin distributes
       over multiplication when one factor has the dividing factor).
     * In our case k₁ = 0 (since D₁ lone at P implies D₁.b(x₀) ≠ 0).
       So iterDivLin D₁ P.1 0 = D₁ already has D₁(P) = 0 (in lone
       branch).
     * For D₁·D₂: need to count common (X-x₀) factors after 0 strips.
       Use Codex's invariant: in cross case k_{12} = min(m_1, m_2).
       Concretely, prove `commonRootMultRat (D₁·D₂) P.1 ≥ 1` (both
       .a, .b vanish at x₀ in cross case), then induct on
       min(m_1, m_2) to peel off divLin steps until residual is
       non-twin.
4. **Combine with existing** `ordAt_mul_add_when_D2_nonvanish_fiber`
   to get unconditional ordAt-additivity at non-2-torsion. Then close
   `divisorOfD_mul_add` unconditionally.

### Inductive step for `min ≥ 2` (after Codex consultation #4)

Codex confirmed (May 2026) that the T_poly approach **does not work**
for the inductive step in general. Counter-example: `D = D₁*D₂` can have
`T_poly = 3*X^9` (rootMult 9) while `m₁ = 6`. The polynomial-rootMult
strategy only handles `min = 1` cleanly.

**Codex's recommendation:** prove the inductive step via the local-ring
valuation approach (geomLocalOrder_mul) rather than polynomial-level
analysis. Specifically:

```lean
cross_product_ordAt :
  ordAt_nonTwoTorsion E (mulCoordRingElt E D₁ D₂) P
    = rootMultiplicity P.1 (normPoly E D₁)
```

via `geomLocalOrder_mul` (multiplicativity of geometric local order
over Fqbar) plus an `ordAt_eq_geomLocalOrder_at_rationalLift` bridge.

Building this is substantial (~hundreds of lines of new local-ring
formalisation).

### Key insight: eagenBuild only needs `min = 1` cross case

In eagenBuild's recursion, every multiplication is by a **chord line**
`L` (or vertical line). Chord lines have multiplicity exactly 1 at
each of their 3 affine intersection points (or 2 for vertical).

Therefore in eagenBuild's cross case at any affine non-2-torsion P:
* The chord line `L` is the factor lone at one sheet with mult 1.
* The accumulator `F_{n-1}` is the factor lone at the other sheet
  with arbitrary mult.

Hence `min(m_L, m_F) = 1` always. **The full base case
`cross_iterDivLin_invariant_when_min_eq_one` is sufficient for
eagenBuild's correctness.**

This is a major simplification: the inductive step (min ≥ 2) is
NOT NEEDED for the eagenBuild axiom-replacement task. The full
cross-case formalization is reserved for future work / general
multiplicativity statement.

### Codex's clean lemma signature

```lean
theorem ordAt_mul_of_right_eval_ne_zero
    {D₁ D₂ : CoordRingElt E.q}
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (h₂P : D₂.eval P.1 P.2 ≠ 0) :
    ordAt E (mulCoordRingElt E D₁ D₂) P = ordAt E D₁ P
```

This subsumes the cross case and is the cleanest formulation: it says
"multiplying by a unit at P doesn't change the order". By symmetry (via
`mulCoordRingElt_comm`), the same holds when `D₁(P) ≠ 0`. Combined,
this gives ordAt-additivity in all cases except both factors vanishing
at P (which is then handled via mulCoordRingElt_divLin_left descent).

### eagenBuild infrastructure status (May 2026)

**Multiplication-additivity at every ECPoint under chord-line hypothesis: COMPLETE.**

```lean
divisorOfD_mul_add_when_chord_line_D2:
    rootMult x (normPoly D_2) ≤ 1 ∀ x ⟹
    divisorOfD (D_1·D_2) = divisorOfD D_1 + divisorOfD D_2 (pointwise)
```

This handles ALL chord lines through 3 distinct points (and vertical
lines through P, -P pairs). The tangent line case (multiplicity 2 at
the tangent point) requires extending to an `m₂ = 2` cross-case
handler — substantial but not blocking the recursive definition of
eagenBuild for non-tangent inputs.

For eagenBuild's GENERIC recursion (no tangent doubling), the chord-line
hypothesis suffices and the additivity is fully proven.

**Tangent doubling limitation (Codex consultation #5, May 2026):**
Codex confirmed `eagenBuild` does NOT intrinsically keep the accumulator
simple at -P when later multiplying by a tangent at P. Concrete
counterexample: input `[P, P, -P, -P]` with P non-2-torsion produces
two tangent lines (at P and at -P) whose product hits the m₂ = 2
cross case at x(P).

For full coverage we'd need:
* m₂ ≥ 2 cross-case proof (substantial), OR
* restrict eagenBuild driver to inputs without tangent doubling
  (e.g., distinct points, or first deduplicate via group law).

Practical workaround: the prover for `weil_reciprocity_honest`
typically uses distinct basis points B_i. If we restrict to that
setting (no doubling), the chord-line theorem is fully sufficient.

### Cross-case progress (May 2026, multiple firings)

The cross case for `min(m₁, m₂) = 1` is now FULLY proved:

* `ordAt_mul_add_in_cross_when_min_eq_one`: at non-2-torsion P with
  D₁ lone at P, D₂ lone at -P, and `min(m₁, m₂) = 1`:
  `ord(D₁·D₂)(P) = ord(D₁)(P) + ord(D₂)(P)`.

* `ordAt_mul_add_at_both_lone_same_sheet`: at non-2-torsion P with
  D₁, D₂ both lone at P (same sheet):
  `ord(D₁·D₂)(P) = ord(D₁)(P) + ord(D₂)(P)`.

These plus existing lemmas (nonvan-fiber, lone-sheet-with-nonvan-D₂,
twin-descent) cover all sub-cases at non-2-torsion under the hypothesis
`rootMult x_0 (normPoly D₂) ≤ 1`.

Remaining work for the unified `ordAt_mul_add_at_nonTwoTorsion_when_normPoly_D2_le_one`:
combine the sub-case lemmas via a single inductive proof on D₁'s
natDegSum (parallel to `ordAt_mul_add_at_nonTwoTorsion_when_D2_nonvanish`),
dispatching on D₁'s branch (nonvan / lone-P / lone-(-P) / twin) and
D₂'s branch (nonvan / lone-P / lone-(-P)).

### Cross-case sub-lemma needed

The cross case (D₁ lone at P, D₂ lone at -P) requires a structural
invariant about iterDivLin's progression. Codex's exact statement:

```lean
theorem cross_iterDivLin_invariant
    {D₁ D₂ : CoordRingElt E.q}
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (h₁P : D₁.eval P.1 P.2 = 0) (h₁n : D₁.eval P.1 (-P.2) ≠ 0)
    (h₂P : D₂.eval P.1 P.2 ≠ 0) (h₂n : D₂.eval P.1 (-P.2) = 0) :
    let m₁ := rootMultiplicity P.1 (normPoly E D₁)
    let m₂ := rootMultiplicity P.1 (normPoly E D₂)
    let D₁₂ := mulCoordRingElt E D₁ D₂
    commonRootMultRat E D₁₂ P.1 = min m₁ m₂ ∧
      ((iterDivLin E D₁₂ P.1 (min m₁ m₂)).eval P.1 P.2 = 0 ↔ m₂ < m₁)
```

Then the cross case in `ordAt_mul_of_right_eval_ne_zero` follows by
`lt_trichotomy` on `m₁` vs `m₂`. (Codex's tactic sketch in the
consultation log.)

#### Proof outline for cross_iterDivLin_invariant

The proof uses the **derivative formula** for iterated divLin: for a
polynomial `Q ∈ Polynomial (ZMod E.q)` with `Q(x₀) = 0`, we have
`(Q /ₘ (X - C x₀))(x₀) = Q'(x₀)`. Iterating: T_r(P) = (D₀⁺)^(r)(x₀),
where D₀⁺ := (D₁·D₂).a - (D₁·D₂).b·y₀.

Hence T_r(P) = 0 iff `r < rootMult x₀ D₀⁺`. The crux: in cross case,
**rootMult x₀ D₀⁺ = m₁** (the multiplicity of D₁ at P). Similarly
rootMult x₀ D₀⁻ = m₂.

This isn't obvious because D₀⁺ = D₁⁺·D₂⁺ + D₁.b·D₂.b·(X-x₀)·g, where
`g := (curveX - y₀²)/(X - x₀)`. In the special case where D₁⁺ = 0 as
a polynomial (degenerate; D₁.a = y₀·D₁.b), the correction term carries
all the rootMult — and luckily it equals m₁ via the formula
`m₁ = 1 + 2·rootMult D₁.b + rootMult g`.

In the non-degenerate case, the rootMult of D₀⁺ is governed by the
structure of D₁'s vanishing at P together with the base curve's
local geometry.

**Pragmatic alternative:** prove the claim via the closed-form on
both `D₁` and `D₁·D₂`, using `ordAt_nonTwoTorsion_pair_eq_rootMult`
(pair-sum) and the existing structure to constrain k₁₂ + branch.
6. Then proceed with eagenBuild driver + correctness:
   - Define `eagenBuild` recursively on lists of `ECPoint E`.
   - Base cases (length 2, 3) reuse existing `chordCoordRingElt`.
   - Recursive case follows Eagen §3.1.1 (chord pairs + divLin
     cancellation).
   - Correctness theorem via induction on list length, using the
     full ordAt-additivity (including cross case).
7. Finally B1–B5 axiom replacement:
   - Rewrite `isHonestFor` constructively as `msg.toD = eagenBuild [...]`.
   - Prove elliptic-resultant identity from eagenBuild output.
   - Prove `logDerivCheckFn_zero_for_eagenBuild` (replaces the false
     `weil_reciprocity_honest` axiom).
   - Strengthen `badPairCompletenessPred` (need card-bound for
     `S_5 = {(A_0, A_1) : thirdPoint = some A_0}` ≤ |E.points| via
     `thirdPoint_inj_on_A₁` + group-law `A_0 + A_1 = -A_0`, hence
     `A_1 = -2A_0`, unique).
   - Delete `weil_reciprocity_honest`; rewire `ma_completeness`.
