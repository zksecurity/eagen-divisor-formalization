/-
  Divisor/Soundness.lean

  `\ref{thm:ma}`: The MA protocol is extractable with knowledge error.
  `\ref{thm:ip}`: The IP protocol is knowledge-sound with the same error.

  The witness is trivially extractable from the first-round message.
  Soundness reduces to the log-derivative check (`\ref{lem:log-derivative}`),
  which in turn reduces to the norm check (`\ref{thm:bassa-monic}`/`\ref{thm:bassa-soundness}`) via
  classical function field theory.
-/
import Divisor.Defs
import Divisor.Axioms
import Divisor.SupportDisjoint
import Divisor.LogDeriv
import Divisor.ClearedPolyForm
import Divisor.Protocol
import Divisor.MACompletenessCore
import Divisor.EagenBuildRecursive

namespace Divisor

open Classical

variable (E : ECSetup)

/-! ## The Extractor (full-grouping version)

Paper's `\mha{GAP}` fix: the naive lift fails when `B_j = -P` (target's
negation appears among the bases) or when `B` contains duplicates. The
residue-matching analysis bundles each group of equal base points into a
single combined multiplicity, so the extractor must too: group positions
by equal `B_j`, compute the combined coefficient per distinct point, and
re-distribute each group's total onto the canonical (minimum-index)
position in the group. For the group at `-P` the residue side carries a
structural `+1` that must be subtracted off the combined total.
-/

/-- Transported bases: view `stmt.bases` as a function on `Fin msg.k`
    using the equality `hk : stmt.k = msg.k`. -/
def extractorBases (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hk : stmt.k = msg.k) : Fin msg.k → ZMod E.q × ZMod E.q :=
  fun j => stmt.bases (Fin.cast hk.symm j)

/-- Finset of positions sharing base point with `i`. -/
def extractorGroup (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hk : stmt.k = msg.k) (i : Fin msg.k) : Finset (Fin msg.k) :=
  Finset.univ.filter (fun j => extractorBases E stmt msg hk j =
    extractorBases E stmt msg hk i)

lemma mem_extractorGroup_self (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) (i : Fin msg.k) :
    i ∈ extractorGroup E stmt msg hk i :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

lemma extractorGroup_nonempty (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) (i : Fin msg.k) :
    (extractorGroup E stmt msg hk i).Nonempty :=
  ⟨i, mem_extractorGroup_self E stmt msg hk i⟩

/-- Combined coefficient at the group containing `i`, in `ZMod E.q`. -/
noncomputable def extractorGroupSum (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) (i : Fin msg.k) :
    ZMod E.q :=
  (extractorGroup E stmt msg hk i).sum (fun j => msg.m j)

/-- Canonical predicate: `i` is the minimum-index representative of its
    equal-base group. -/
noncomputable def extractorIsCanonical (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) (i : Fin msg.k) : Prop :=
  (extractorGroup E stmt msg hk i).min'
    (extractorGroup_nonempty E stmt msg hk i) = i

/-- Set of indices whose base point equals `-P`. -/
noncomputable def negPIndexSet (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) : Finset (Fin msg.k) :=
  (Finset.univ : Finset (Fin msg.k)).filter
    (fun j => extractorBases E stmt msg hk j = (stmt.target.1, -stmt.target.2))

/-- Scalars extracted from the first-round message.

    Paper `\protMA` extractor (two branches):

    * **Special case `-P ∈ {B_j}`**: set `n_{j*} = -1` at the
      minimum-index `j*` with `B_{j*} = -P`, and `n_i = 0` elsewhere.
      Ignores `msg.m` entirely. The resulting witness `[-1]·B_{j*} =
      [-1]·(-P) = P` is valid unconditionally.

    * **General case `-P ∉ {B_j}`**: residue matching. Non-canonical
      positions get `0`; canonical positions get the paper's integer
      multiplicity `n_i = β_{σ⁻¹(i)}` of D's zero at `B_i`.

      Paper's partial-fraction argument (paper eq:residue-identity,
      ip.tex:596-601) yields `Σ_{j : B_j = B_i} m_j ≡ β_{σ⁻¹(i)}
      (mod q)` at matched B_i's — POSITIVE match between the residue
      sum and the multiplicity. So the integer multiplicity is
      recovered as `groupSum.val`, giving a value in `[0, q) ∩
      [0, degE(D)]`.

      (Historical note: polyG-bridge sign resolution
      aligned `polyG`'s additive convention with `logDerivCheckFn`'s
      RHS sign by negating `distinctMCons`'s tail — propagating
      cleanly here so `groupSum.val` (no extra negation) is correct.) -/
noncomputable def extractedScalars (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) : Fin msg.k → ℤ :=
  fun i =>
    if hNegP : (negPIndexSet E stmt msg hk).Nonempty then
      -- Special case: -P ∈ {B_j}. Trivial witness at j* = min.
      if i = (negPIndexSet E stmt msg hk).min' hNegP then (-1 : ℤ) else 0
    else
      -- General case: -P ∉ {B_j}. Residue matching (paper's positive form).
      if extractorIsCanonical E stmt msg hk i then
        ((extractorGroupSum E stmt msg hk i).val : ℤ)
      else 0

/-- Predicate: the extractor succeeds at bound `d`.

    Simplified after the `-P ∈ {B_j}` special case: the only
    requirement is that every extracted scalar has absolute value
    `< d`. The old no-underflow guard is no longer needed because
    the residue `+1` at `-P` is absorbed into the special-case branch
    (which returns `-1` directly, with `|-1|.natAbs = 1 < d` for any
    reasonable `d ≥ 2`). -/
noncomputable def extractorSucceeds (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (hk : stmt.k = msg.k) : Prop :=
  ∀ i, ((extractedScalars E stmt msg hk i).natAbs) < d

/-- The full-grouping extractor.

    Returns `some` iff `extractorSucceeds` (range condition on every
    extracted scalar). -/
noncomputable def maExtractor (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (_hd : d < E.q)
    (hk : stmt.k = msg.k) :
    Option (DlogWitness E.q) :=
  if h : extractorSucceeds E stmt msg d hk then
    some {
      k := msg.k
      scalars := extractedScalars E stmt msg hk
      degBound := d
      hRange := h
    }
  else
    none

/-! ## Bad events -/

/-- BadRange: some extracted scalar is not in [0, d). -/
noncomputable def eventBadRange (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (hk : stmt.k = msg.k) : Prop :=
  ¬ extractorSucceeds E stmt msg d hk

/-! ## Bridge from log-derivative vanishing to extractor success

    The general-case bridge `logDerivCheckFn ≡ 0 on defined non-vertical
    E × E pairs ⇒ extractor succeeds ∧ target = Σ [extractedScalars] · B_i`
    is derived in `ExtractorBridge.lean` from the narrow
    `polyG_zero_of_logDerivCheck_identically_zero` axiom (scalar residue
    content) together with `CoordRingElt.has_principal_divisor` (Silverman
    III.3.5) and the D3 + D4 + D5 infrastructure. The special case
    `-P ∈ {B_j}` is handled here unconditionally below. -/

/-- **Paper Step 5 (special case)** (`thm:ma`, ip.tex `\ref{step:extract}`):
    extractor-success guarantee in the special branch (`-P ∈ {B_j}`,
    `d ≥ 2`).

    Direct proof: the special branch of `extractedScalars` returns
    `-1` at `j*` and `0` at all other indices. So `|scalars i|.natAbs`
    is either `1` (at `j*`) or `0` (elsewhere), both `< d` when `d ≥ 2`. -/
theorem extractorSucceeds_special
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hkm : stmt.k = msg.k)
    (hNegP : (negPIndexSet E stmt msg hkm).Nonempty)
    (hd2 : 2 ≤ d) :
    extractorSucceeds E stmt msg d hkm := by
  intro i
  show ((if hne : (negPIndexSet E stmt msg hkm).Nonempty
         then (if i = (negPIndexSet E stmt msg hkm).min' hne
               then (-1 : ℤ) else 0)
         else _)).natAbs < d
  rw [dif_pos hNegP]
  by_cases hi : i = (negPIndexSet E stmt msg hkm).min' hNegP
  · rw [if_pos hi]; exact hd2
  · rw [if_neg hi]; omega

/-! ## Special-case extractor validity (unconditional).

    When `-P ∈ {B_j}`, the `extractedScalars` definition returns
    `(-1)` at `j* := min{j : B_j = -P}` and `0` at all other indices,
    regardless of `msg.m`. We prove unconditionally that this satisfies
    the dlog relation `target = Σ [n_i] · bases i` = `-bases j*` =
    `-(-P)` = `P`. -/

/-- **Paper Step 5 (special case)** (`thm:ma`, ip.tex `\ref{step:extract}`):
    witness validity in the special branch (`-P ∈ {B_j}`).

    The witness `(n_{j*}, 0, …, 0) = (-1, 0, …, 0)` satisfies
    `Σ [n_i] · B_i = [-1] · B_{j*} = [-1](-P) = P` unconditionally,
    without inspecting `msg.m`. -/
theorem extracted_scalars_valid_special
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hNegP : (negPIndexSet E stmt msg hkm).Nonempty) :
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin msg.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg hkm i)
                   (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                                     (extractorBases E stmt msg hkm i).2)) := by
  classical
  set j_star : Fin msg.k :=
    (negPIndexSet E stmt msg hkm).min' hNegP with hJStar_def
  -- Base point at j_star is -P (by def of negPIndexSet).
  have hBase : extractorBases E stmt msg hkm j_star =
               (stmt.target.1, -stmt.target.2) := by
    have hInSet : j_star ∈ negPIndexSet E stmt msg hkm :=
      Finset.min'_mem _ _
    simpa [negPIndexSet] using hInSet
  -- Only the j_star term contributes.
  rw [ECPoint.weightedSum_eq_single (E := E)
       (s := (Finset.univ : Finset (Fin msg.k)))
       (f := fun i => ECPoint.zsmul E
                        (extractedScalars E stmt msg hkm i)
                        (ECPoint.affine E (extractorBases E stmt msg hkm i).1
                                          (extractorBases E stmt msg hkm i).2))
       (a := j_star) (Finset.mem_univ j_star)]
  · have hExtracted : extractedScalars E stmt msg hkm j_star = -1 := by
      show (if hne : (negPIndexSet E stmt msg hkm).Nonempty
            then (if j_star = (negPIndexSet E stmt msg hkm).min' hne then (-1 : ℤ) else 0)
            else _) = -1
      rw [dif_pos hNegP]
      simp [hJStar_def]
    simp only [hExtracted, ECPoint.zsmul_neg_one, hBase]
    -- `affine E x (-y) = -(affine E x y)` since on our curve `negY x y = -y`.
    have h := ECPoint.affine_neg E stmt.target.1 stmt.target.2
    -- h : -(affine E x y) = affine E x (-y)
    -- goal : affine E x y = -(affine E x (-y))
    rw [← h, neg_neg]
  · intro i _ hi_ne
    have hExtracted : extractedScalars E stmt msg hkm i = 0 := by
      show (if hne : (negPIndexSet E stmt msg hkm).Nonempty
            then (if i = (negPIndexSet E stmt msg hkm).min' hne
                  then (-1 : ℤ) else 0)
            else _) = 0
      rw [dif_pos hNegP, if_neg]
      exact fun h => hi_ne (h.trans hJStar_def.symm)
    simp only [hExtracted, ECPoint.zsmul_zero]

/-! ## Extractor validity and MA extractability

    The general-case bridge `extracted_scalars_valid` (combining the
    special case with the narrowed general case), the full
    knowledge-soundness theorem `ma_extractable`, and its IP-side
    consequence `ip_knowledge_sound` have been moved to
    `ExtractorBridge.lean`, which is the bottom-layer file in the
    import graph that can access both the extractor definitions
    (Soundness.lean) and the D4/D5 infrastructure + narrow T4 bridge
    axioms (`CoordRingElt.has_principal_divisor`,
    `polyG_zero_of_logDerivCheck_identically_zero`) in
    `ExtractorBridge.lean`. -/

/-! ## Completeness -/

-- `weil_reciprocity_honest` declared in
-- `Divisor/Axioms/AxiomWeilReciprocityHonest.lean`; imported via
-- `Divisor.Axioms` at the top of this file.

/-- **Completeness.** For the honest prover's first-round message `msg`
    (witnessed by `isHonestFor`), the set of challenges on which the MA
    verifier rejects is contained in `badChallengesCompleteness`, hence
    bounded by `(3 N + 1) · |E_aff|` via `\ref{lem:support-disjoint}` (`support_disjointness`),
    where `N = numZeros E msg.toD`.

    The three verifier checks:
    * degree check `degE(D) ≤ stmt.k` — required by `hDegK`;
    * admissible-set check `(polyA, polyB) ∈ admSet` — required by `hAdm`;
    * log-derivative identity — vanishes off the bad set by the
      Weil-reciprocity axiom, given the honest-divisor predicate.

    Hence rejection forces the challenge into the bad set.

    Refactored: factored through `ma_completeness_parameterized`
    (in `Divisor/MACompletenessCore.lean`), which takes the per-pair
    `logDerivCheckFn = 0` claim as a hook. This lets specialized
    integrations (e.g., `length-4 simple` from
    `Divisor.LogDerivEagenLength4`, the explicit honest-divisor
    identity in `Divisor.EagenBuildRecursive`) provide the hook
    without using the `weil_reciprocity_honest` axiom. -/

theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  let _ := hValid
  let _ := hDeg
  -- Derive D ≠ 0 from the admSet check + admSet_excludes_zero.
  have hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  -- Extract on-curve invariants from the strengthened isHonestFor.
  have h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points :=
    hHonestDivisor.2.2.2.1
  have h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points :=
    hHonestDivisor.2.2.2.2
  -- Route through the explicit honest-divisor bridge (no axiom).
  exact ma_completeness_via_isHonestForExplicit E stmt wit hk msg hkm
    hHonestDivisor hD h_negT h_bases hDegK hAdm

/-- **MA completeness, Hasse-clean form.** Applying Hasse (`|E| ≤ 2q`
    for `q ≥ 5`) and the paper-tight `numZeros ≤ degE ≤ degBound`,
    the rejection-set cardinality is bounded by `6 · (d + 1) · q`.
    Matches paper's `\compErr ≤ 6(\degBound + 1)/q` after dividing by
    `|E|² ≥ q²/2`. -/
theorem ma_completeness_clean
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hMA := ma_completeness E stmt wit hk hValid msg hkm hDeg hDegK hAdm hHonestDivisor
  have hNZ : numZeros E msg.toD ≤ stmt.degBound := by
    have h1 := numZeros_le_degE E msg.toD hD
    omega
  have hHasse : E.numAffine ≤ 2 * E.q := points_card_le_two_q E hQ
  calc _ ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := hMA
    _ ≤ (3 * stmt.degBound + 4) * (2 * E.q) := by
        apply Nat.mul_le_mul (by omega) hHasse
    _ ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by ring_nf; omega

/-! ## Paper-Lean naming correspondence

    Paper ↔ Lean (post-rename, primary names):

    * `event_deg`               ↔ `eventDeg` (= `¬ logDerivCheckFnDefined`)
    * `event_NotEq`             ↔ `eventNotEq` (Finset of bad challenges)
    * `\relation^{dlog}`        ↔ `relDlog`
    * `\relation^{dlog-honest}` ↔ `relDlogHonest`
    * `\protMA`                 ↔ structure (`MAProverMsg`, `MAChallenge`,
                                              `maVerifierAccepts`,
                                              `MAProverMsg.isHonestFor`)
    * `\protIP`                 ↔ structure (`IPProverMsg3`,
                                              `ipVerifierAccepts`,
                                              `computeA₂`,
                                              `ip_unique_third_round`)
    * `f` (discrepancy)         ↔ `logDerivCheckFn`
    * `\extractor`              ↔ `maExtractor` -/

/-- The `event_deg` bad event from paper (`ip.tex \ref{thm:ma}`): some
    denominator in the verifier's field expression vanishes
    (`D(A_i) = 0` for `i = 0, 1, 2`, `L(-P) = 0`, `L(B_j) = 0`, or one
    of the `dx/dz` denominators at `A_i`). Equivalently in Lean,
    `¬ logDerivCheckFnDefined`: the product `logDerivCheckFnDenom`
    vanishes, i.e. at least one of its 8 factors is zero. -/
def eventDeg
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  ¬ logDerivCheckFnDefined E D P B A₀ A₁

/-- Cardinality contribution of the paper's `event_NotEq` branch in
    the MA knowledge-error numerator. This is the nonzero-discrepancy
    Schwartz-Zippel/DKL term. -/
def eventNotEqBound (d k : ℕ) : ℕ :=
  18 * (d + k) * E.q

/-- Cardinality contribution of the paper's `event_deg` branch in the
    MA knowledge-error numerator. This is the accumulated denominator /
    undefined-expression term. -/
def eventDegBound (d k : ℕ) : ℕ :=
  (3 * d + 9 * k + 71) * E.points.card

/-! ### Paper-clean bad-challenge sets

Two disjoint refinements of `eventNotEq`, restricted to `validPairs`:

* `eventDegSet`: pairs where the verifier's denominator is **undefined**
  (`logDerivCheckFnDefined` fails). Paper's `event_deg`, restricted to
  the verifier's challenge space.
* `eventNotEqDefinedSet`: pairs where the denominator **is** defined yet
  the discrepancy still evaluates to zero. Paper's `event_NotEq` on the
  defined cone — the genuine Schwartz–Zippel/log-derivative event.

Their union is `badChallenges`, used by the headline accept-set bound. -/

/-- Pairs `(A₀, A₁) ∈ validPairs E` where the verifier check is
*undefined* (some denominator factor of `logDerivCheckFnDenom`
vanishes). Paper's `event_deg`, restricted to the validPairs space. -/
noncomputable def eventDegSet
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (validPairs E).filter (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2)

/-- Pairs `(A₀, A₁) ∈ validPairs E` where the verifier check **is
defined** *and* the discrepancy `logDerivCheckFn` evaluates to zero.
Paper's `event_NotEq` on the defined cone (the genuine SZ event). -/
noncomputable def eventNotEqDefinedSet
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (validPairs E).filter (fun p =>
    logDerivCheckFnDefined E D P B p.1 p.2 ∧
    logDerivCheckFn E D P k B m p.1 p.2 = 0)

/-- Paper-clean bad-challenge set: union of the undefined-denominator
event and the defined-zero-discrepancy event.

Headline accept-set bound: `acceptSet ⊆ badChallenges`. Cardinality
bound: `|badChallenges| ≤ eventNotEqBound + eventDegBound`
(see `badChallenges_card_le`). -/
noncomputable def badChallenges
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  eventDegSet E D P B ∪ eventNotEqDefinedSet E D P B m

/-- `eventNotEq ⊆ badChallenges`: any validPairs entry with totalised
discrepancy zero is either undefined (in `eventDegSet`) or defined
with zero discrepancy (in `eventNotEqDefinedSet`). -/
theorem eventNotEq_subset_badChallenges
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    eventNotEq E D P B m ⊆ badChallenges E D P B m := by
  classical
  intro p hp
  simp only [eventNotEq, Finset.mem_filter] at hp
  obtain ⟨hVP, hCheck⟩ := hp
  by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
  · refine Finset.mem_union.mpr (Or.inr ?_)
    simp only [eventNotEqDefinedSet, Finset.mem_filter]
    exact ⟨hVP, hDef, hCheck⟩
  · refine Finset.mem_union.mpr (Or.inl ?_)
    simp only [eventDegSet, Finset.mem_filter]
    exact ⟨hVP, hDef⟩

/-- The `\relation^{dlog-honest}` completeness relation from paper
    (`ip.tex \ref{thm:ma}`): `(stmt, wit) ∈ relDlog` together with an
    honest first-round message `msg` (whose divisor is principal and
    encodes the claimed scalars). -/
def relDlogHonest (stmt : DlogStatement E.q) (wit : DlogWitness E.q) : Prop :=
  ∃ (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k),
    relDlog E stmt wit ∧ msg.isHonestFor E stmt wit hk hkm

/-- **IP Completeness (off `eventDeg`).** On every challenge where
    `eventDeg` does **not** hold (paper: `¬event_deg`), the honest IP
    prover constructs a third-round message that the IP verifier
    accepts:

    * `h_i := D'(A_i) / D(A_i)` satisfies `h_i · D(A_i) = D'(A_i)`,
    * `g := -1 / L(-P)` satisfies `g · L(-P) = -1`,

    where `A_2 := computeA₂ chal = (chordX₂, chordY₂)` is the third
    chord-intersection.

    Mirrors paper Theorem `\ref{thm:ip}`'s claim `\compErr_{IP}` is
    bounded analogously to `\compErr_{MA}` once `event_deg` is
    accounted for — see `ip_completeness` below for the
    cardinality form. -/
theorem ip_accept_off_eventDeg
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (chal : MAChallenge E.q)
    (hNotDeg : ¬ eventDeg E msg.toD stmt.target stmt.bases chal.A₀ chal.A₁)
    (hDegK : msg.toD.degE ≤ stmt.degBound) :
    ∃ msg3 : IPProverMsg3 E.q,
      ipVerifierAccepts E stmt msg chal (computeA₂ chal) msg3 := by
  let _ := hkm
  -- Unfold ¬eventDeg = logDerivCheckFnDefined; extract the four nondegen
  -- facts via logDerivCheckFnDenom_factors_ne_zero.
  have hDef : logDerivCheckFnDefined E msg.toD stmt.target stmt.bases
                chal.A₀ chal.A₁ := not_not.mp hNotDeg
  have hFactors := logDerivCheckFnDenom_factors_ne_zero E msg.toD stmt.target
                     stmt.bases chal.A₀ chal.A₁ hDef
  obtain ⟨hD₀_nz, hD₁_nz, hD₂_chord_nz, _, _, _, hLP_nz, _⟩ := hFactors
  -- D(A_2)-nondegeneracy: A_2 = computeA₂ chal = (chordX₂, chordY₂)
  -- definitionally; use this to align with the chord form from hFactors.
  have hA₂_eq : computeA₂ chal =
      (chordX₂ chal.A₀ chal.A₁, chordY₂ chal.A₀ chal.A₁) := rfl
  have hD₂_nz : msg.toD.eval (computeA₂ chal).1 (computeA₂ chal).2 ≠ 0 := by
    rw [hA₂_eq]; exact hD₂_chord_nz
  -- Construct honest msg3.
  let D := msg.toD
  let A₂ := computeA₂ chal
  let h0 := (D.a.derivative.eval chal.A₀.1 -
              D.b.derivative.eval chal.A₀.1 * chal.A₀.2) /
                D.eval chal.A₀.1 chal.A₀.2
  let h1 := (D.a.derivative.eval chal.A₁.1 -
              D.b.derivative.eval chal.A₁.1 * chal.A₁.2) /
                D.eval chal.A₁.1 chal.A₁.2
  let h2 := (D.a.derivative.eval A₂.1 -
              D.b.derivative.eval A₂.1 * A₂.2) /
                D.eval A₂.1 A₂.2
  let g := -1 / (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
                  stmt.target.1 (-stmt.target.2)
  refine ⟨⟨fun i => match i with | 0 => h0 | 1 => h1 | 2 => h2, g⟩,
          hDegK, ?_, ?_, ?_, ?_⟩
  · show h0 * D.eval chal.A₀.1 chal.A₀.2 = _
    simp only [h0]; exact div_mul_cancel₀ _ hD₀_nz
  · show h1 * D.eval chal.A₁.1 chal.A₁.2 = _
    simp only [h1]; exact div_mul_cancel₀ _ hD₁_nz
  · show h2 * D.eval A₂.1 A₂.2 = _
    simp only [h2]; exact div_mul_cancel₀ _ hD₂_nz
  · show g * _ = -1
    simp only [g]; exact div_mul_cancel₀ _ hLP_nz

/-- **IP Completeness — cardinality form.** The set of challenges on
    which no third-round message makes the IP verifier accept is
    bounded by

      `(3·N + 1)·|E_aff| + (3·d + 9·k + 71)·|E.points|`,

    where `N = numZeros E msg.toD`, `d = msg.toD.degE`, and
    `k = stmt.k`. Single-set bound:
    `IP rejection ⊆ eventDeg`, so `|IP rejection| ≤ |eventDeg|`.
    Both sub-events captured by `ma_completeness` (the
    `D(A_i) = 0` / `A_2 = ∞` cases) and the IP-specific cases
    (`L(-P) = 0`, `L(B_j) = 0`, `dx/dz = 0`) live inside `eventDeg`,
    so a single bound on `|eventDeg|` covers both. -/
theorem ip_completeness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
  classical
  let _ := hkm
  -- IP rejection ⊆ eventDeg via `ip_accept_off_eventDeg` contrapositive.
  set rejectIP : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                  (computeA₂ ⟨p.1, p.2⟩) msg3) with hRIPdef
  set eventDegSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => eventDeg E msg.toD stmt.target stmt.bases p.1 p.2) with hUdef
  have hSub : rejectIP ⊆ eventDegSet := by
    intro p hp
    simp only [hRIPdef, Finset.mem_filter] at hp
    obtain ⟨hp_pts, hp_no_msg3⟩ := hp
    simp only [hUdef, Finset.mem_filter]
    refine ⟨hp_pts, ?_⟩
    by_contra hNotDeg
    apply hp_no_msg3
    exact ip_accept_off_eventDeg E stmt msg hkm ⟨p.1, p.2⟩ hNotDeg hDegK
  -- |eventDegSet| ≤ (3d + 9k + 71)·|E| by Bezout-on-(E×E).
  have hEventDegEq : eventDegSet =
      (E.points ×ˢ E.points).filter
        (fun p => ¬ logDerivCheckFnDefined E msg.toD stmt.target stmt.bases
                    p.1 p.2) := by
    apply Finset.ext
    intro p
    simp only [hUdef, Finset.mem_filter, eventDeg]
  calc rejectIP.card
      ≤ eventDegSet.card := Finset.card_le_card hSub
    _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
        rw [hEventDegEq]
        exact logDerivCheckFn_undefined_set_bound_tight E msg.toD stmt.target
                stmt.k stmt.bases hD

/-- **IP completeness, Hasse-clean form.** Applying Hasse
    (`|E| ≤ 2q` for `q ≥ 5`), the rejection-set cardinality is
    bounded by `18 · (d + k + 12) · q`. Single-`q` form. -/
theorem ip_completeness_clean
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by
  have hIP := ip_completeness E stmt msg hkm hDegK hD
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E hQ
  calc _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := hIP
    _ ≤ (3 * stmt.degBound + 9 * stmt.k + 71) * (2 * E.q) :=
        Nat.mul_le_mul (by omega) hHasse
    _ ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by ring_nf; omega

end Divisor
