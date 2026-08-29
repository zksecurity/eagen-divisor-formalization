/-
  Divisor/Soundness.lean

  The extraction algorithm and the bad-event accounting for the MA
  protocol's knowledge-soundness analysis:

  * `maExtractor` and its ingredients (`extractorBases`,
    `extractorGroup`, `extractedScalars`, `extractorSucceeds`) — the
    straight-line extractor that reads the witness scalars off the
    prover's first-round message, with the `-P ∈ {B_j}` special case
    handled unconditionally here.
  * The paper's bad events (`eventDeg`, `eventDegSet`,
    `eventNotEqDefinedSet`, `badChallenges`) and their cardinality
    budgets (`eventNotEqBound`, `eventDegBound`).

  The headline statements built on these live in
  `Divisor/Headlines.lean`; the proof machinery in
  `Divisor/ExtractorBridgeTheorems.lean` and
  `Divisor/Completeness.lean`.
-/
import Divisor.Bridges
import Divisor.LineBuildRecursive
import VCVio.OracleComp.ProbComp

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

/-- The statement bases, indexed by the arity shared with the message. -/
def extractorBases (stmt : DlogStatement E.q) (_msg : MAProverMsg E.q stmt.k) :
    Fin stmt.k → ZMod E.q × ZMod E.q :=
  stmt.bases

/-- Finset of positions sharing base point with `i`. -/
def extractorGroup (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k)
    (i : Fin stmt.k) : Finset (Fin stmt.k) :=
  Finset.univ.filter (fun j => extractorBases E stmt msg j =
    extractorBases E stmt msg i)

lemma mem_extractorGroup_self (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (i : Fin stmt.k) :
    i ∈ extractorGroup E stmt msg i :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

lemma extractorGroup_nonempty (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (i : Fin stmt.k) :
    (extractorGroup E stmt msg i).Nonempty :=
  ⟨i, mem_extractorGroup_self E stmt msg i⟩

/-- Combined coefficient at the group containing `i`, in `ZMod E.q`. -/
def extractorGroupSum (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (i : Fin stmt.k) :
    ZMod E.q :=
  (extractorGroup E stmt msg i).sum (fun j => msg.m j)

/-- Canonical predicate: `i` is the minimum-index representative of its
    equal-base group. -/
def extractorIsCanonical (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (i : Fin stmt.k) : Prop :=
  (extractorGroup E stmt msg i).min'
    (extractorGroup_nonempty E stmt msg i) = i

/-- Set of indices whose base point equals `-P`. -/
def negPIndexSet (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) : Finset (Fin stmt.k) :=
  (Finset.univ : Finset (Fin stmt.k)).filter
    (fun j => extractorBases E stmt msg j = (stmt.target.1, -stmt.target.2))

/-- Constructive decision procedure for canonical extractor indices. -/
def extractorIsCanonicalDecidable (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (i : Fin stmt.k) :
    Decidable (extractorIsCanonical E stmt msg i) := by
  unfold extractorIsCanonical
  infer_instance

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

      `polyG`'s additive convention is aligned with
      `logDerivCheckFn`'s RHS sign (via the negated `distinctMCons`
      tail), so `groupSum.val` needs no extra negation. -/
def extractedScalars (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) : Fin stmt.k → ℤ :=
  fun i =>
    letI : Decidable ((negPIndexSet E stmt msg).Nonempty) :=
      Finset.decidableNonempty
    letI : Decidable (extractorIsCanonical E stmt msg i) :=
      extractorIsCanonicalDecidable E stmt msg i
    if hNegP : (negPIndexSet E stmt msg).Nonempty then
      -- Special case: -P ∈ {B_j}. Trivial witness at j* = min.
      if i = (negPIndexSet E stmt msg).min' hNegP then (-1 : ℤ) else 0
    else
      -- General case: -P ∉ {B_j}. Residue matching (paper's positive form).
      if extractorIsCanonical E stmt msg i then
        ((extractorGroupSum E stmt msg i).val : ℤ)
      else 0

/-- Predicate: the extractor succeeds at bound `d` — every extracted
    scalar has absolute value `< d`. No separate underflow guard is
    needed: the residue `+1` at `-P` is absorbed by the special-case
    branch, which returns `-1` directly (`(-1).natAbs = 1 < d` for
    `d ≥ 2`). -/
def extractorSucceeds (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (d : ℕ) : Prop :=
  ∀ i, ((extractedScalars E stmt msg i).natAbs) < d

/-- Constructive decision procedure for the extractor's finite range check. -/
def extractorSucceedsDecidable (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (d : ℕ) :
    Decidable (extractorSucceeds E stmt msg d) := by
  unfold extractorSucceeds
  infer_instance

/-- The full-grouping extractor.

    This is a total function on the public statement and Merlin message.
    The returned witness uses the statement's public degree bound. Its finite
    grouping and range check take polynomial time (quadratic in `stmt.k` with
    the current direct implementation); the message polynomials are not
    inspected. -/
def maExtractor (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) : Option (DlogWitness E.q) :=
  letI : Decidable (extractorSucceeds E stmt msg stmt.degBound) :=
    extractorSucceedsDecidable E stmt msg stmt.degBound
  if h : extractorSucceeds E stmt msg stmt.degBound then
    some {
      k := stmt.k
      scalars := extractedScalars E stmt msg
      degBound := stmt.degBound
      hRange := h
    }
  else
    none

/-- The executable extractor succeeds and its exact output satisfies the
    discrete-log relation. The `none` branch is false, so this pins validity
    to the witness returned by `maExtractor`. -/
def maExtractorValid (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) : Prop :=
  match maExtractor E stmt msg with
  | some wit => relDlog E stmt wit
  | none => False

/-! ## Bad events -/

/-- BadRange: some extracted scalar is not in [0, d). -/
noncomputable def eventBadRange (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) (d : ℕ) : Prop :=
  ¬ extractorSucceeds E stmt msg d

/-! ## Bridge from log-derivative vanishing to extractor success

    The general-case bridge `logDerivCheckFn ≡ 0 on defined
    non-vertical E × E pairs ⇒ extractor succeeds ∧
    target = Σ [extractedScalars] · B_i` is derived in
    `ExtractorBridge.lean` from `polyG_zero_trace_formula`,
    `CoordRingElt.has_principal_divisor` (Silverman III.3.5), and the
    D3–D5 infrastructure. The special case `-P ∈ {B_j}` is handled
    unconditionally below. -/

/-- **Paper Step 5 (special case)** (`thm:ma`, ip.tex `\ref{step:extract}`):
    extractor-success guarantee in the special branch (`-P ∈ {B_j}`,
    `d ≥ 2`).

    Direct proof: the special branch of `extractedScalars` returns
    `-1` at `j*` and `0` at all other indices. So `|scalars i|.natAbs`
    is either `1` (at `j*`) or `0` (elsewhere), both `< d` when `d ≥ 2`. -/
theorem extractorSucceeds_special
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k) (d : ℕ)
    (hNegP : (negPIndexSet E stmt msg).Nonempty)
    (hd2 : 2 ≤ d) :
    extractorSucceeds E stmt msg d := by
  intro i
  show ((if hne : (negPIndexSet E stmt msg).Nonempty
         then (if i = (negPIndexSet E stmt msg).min' hne
               then (-1 : ℤ) else 0)
         else _)).natAbs < d
  rw [dif_pos hNegP]
  by_cases hi : i = (negPIndexSet E stmt msg).min' hNegP
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
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k)
    (hNegP : (negPIndexSet E stmt msg).Nonempty) :
    ECPoint.affine E stmt.target.1 stmt.target.2 =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin stmt.k))
        (fun i => ECPoint.zsmul E
                   (extractedScalars E stmt msg i)
                   (ECPoint.affine E (extractorBases E stmt msg i).1
                                     (extractorBases E stmt msg i).2)) := by
  classical
  set j_star : Fin stmt.k :=
    (negPIndexSet E stmt msg).min' hNegP with hJStar_def
  -- Base point at j_star is -P (by def of negPIndexSet).
  have hBase : extractorBases E stmt msg j_star =
               (stmt.target.1, -stmt.target.2) := by
    have hInSet : j_star ∈ negPIndexSet E stmt msg :=
      Finset.min'_mem _ _
    simpa [negPIndexSet] using hInSet
  -- Only the j_star term contributes.
  rw [ECPoint.weightedSum_eq_single (E := E)
       (s := (Finset.univ : Finset (Fin stmt.k)))
       (f := fun i => ECPoint.zsmul E
                        (extractedScalars E stmt msg i)
                        (ECPoint.affine E (extractorBases E stmt msg i).1
                                          (extractorBases E stmt msg i).2))
       (a := j_star) (Finset.mem_univ j_star)]
  · have hExtracted : extractedScalars E stmt msg j_star = -1 := by
      show (if hne : (negPIndexSet E stmt msg).Nonempty
            then (if j_star = (negPIndexSet E stmt msg).min' hne then (-1 : ℤ) else 0)
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
    have hExtracted : extractedScalars E stmt msg i = 0 := by
      show (if hne : (negPIndexSet E stmt msg).Nonempty
            then (if i = (negPIndexSet E stmt msg).min' hne
                  then (-1 : ℤ) else 0)
            else _) = 0
      rw [dif_pos hNegP, if_neg]
      exact fun h => hi_ne (h.trans hJStar_def.symm)
    simp only [hExtracted, ECPoint.zsmul_zero]

/-! ## Extractor validity and MA soundness

    The general-case bridge `extracted_scalars_valid` and the
    knowledge-soundness headlines `ma_soundness_count_bound` / `ip_extractable`
    live in `ExtractorBridge.lean` and
    `ExtractorBridgeTheorems.lean`, the layers of the import graph
    with access to both the extractor definitions here and the
    D3–D5 / polyG infrastructure. -/

/-! ## Paper-Lean naming correspondence

    Paper ↔ Lean (post-rename, primary names):

    * `event_deg` ↔ `eventDeg` (= `¬ logDerivCheckFnDefined`)
    * `event_NotEq` ↔ `eventNotEq` (Finset of bad challenges)
    * `\relation^{dlog}` ↔ `relDlog`
    * `\relation^{dlog-honest}` ↔ `relDlogHonest`
    * `\protMA` ↔ structure (`MAProverMsg`, `MAChallenge`,
                                              `maVerifierAccepts`,
                                              `MAProverMsg.isHonestFor`)
    * `\protIP` ↔ structure (`IPProverMsg3`,
                                              `ipVerifierAccepts`,
                                              `computeA₂`,
                                              `ip_unique_third_round`)
    * `f` (discrepancy) ↔ `logDerivCheckFn`
    * `\extractor` ↔ `maExtractor` -/

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
  12 * (d + k) * E.points.card

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

/-! ### Accept and reject sets

The two challenge-pair sets the headline theorems count. Soundness
statements bound the accept set over the distinct-x sample space
`validPairs`; completeness statements bound the reject set over the
full challenge space `E.points ×ˢ E.points`. -/

/-- Challenge pairs in `validPairs E` on which the MA verifier accepts
    `msg`. The soundness headlines (`ma_soundness_count_bound`, `ip_extractable`
    and variants) bound `(maAcceptSet …).card`. -/
noncomputable def maAcceptSet (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (validPairs E).filter (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩)

theorem maAcceptSet_eq (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) :
    maAcceptSet E stmt msg =
      (validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩) :=
  rfl

@[simp] theorem mem_maAcceptSet {stmt : DlogStatement E.q}
    {msg : MAProverMsg E.q stmt.k}
    {p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)} :
    p ∈ maAcceptSet E stmt msg ↔
      p ∈ validPairs E ∧ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ := by
  classical
  simp [maAcceptSet]

/-- Arthur's acceptance probability for a fixed public statement and a fixed
    Merlin message. Arthur samples uniformly from `validPairs E`; the theorem
    therefore models the protocol's valid-chord challenge distribution rather
    than conditioning an ambient sample after the fact. -/
noncomputable def maAcceptanceProbability (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) : ENNReal :=
  Pr[fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ |
    $ (validPairs E)]

/-- The VCVio experiment is exactly the accept-set count divided by the
    number of valid challenge pairs. -/
theorem maAcceptanceProbability_eq_card_div (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) :
    maAcceptanceProbability E stmt msg =
      ((maAcceptSet E stmt msg).card : ENNReal) /
        ((validPairs E).card : ENNReal) := by
  classical
  simp [maAcceptanceProbability, maAcceptSet]

/-- Point-count knowledge error for the MA protocol. -/
noncomputable def maSoundnessError (stmt : DlogStatement E.q) : ENNReal :=
  ((24 * (stmt.degBound + stmt.k + 3) * E.points.card : ℕ) : ENNReal) /
    ((validPairs E).card : ENNReal)

/-- Exact non-vacuity criterion for the advertised error bound. -/
theorem maSoundnessError_lt_one_iff (stmt : DlogStatement E.q)
    (hValidPairs : (validPairs E).Nonempty) :
    maSoundnessError E stmt < 1 ↔
      24 * (stmt.degBound + stmt.k + 3) * E.points.card <
        (validPairs E).card := by
  unfold maSoundnessError
  have hDenom : ((validPairs E).card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hValidPairs
  rw [ENNReal.div_lt_iff (Or.inl hDenom) (Or.inl (by simp))]
  norm_cast
  simp

/-- The point-count hypothesis used by `ma_soundness` makes its knowledge
    error genuinely smaller than one. -/
theorem maSoundnessError_lt_one_of_large (stmt : DlogStatement E.q)
    (hLargeQ : E.points.card >
      2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
      21 * (stmt.degBound + stmt.k + 2) + 72) :
    maSoundnessError E stmt < 1 := by
  have hn : 24 * (stmt.degBound + stmt.k + 3) + 3 < E.points.card := by
    omega
  have hnPos : 0 < E.points.card := by omega
  have hMul := Nat.mul_lt_mul_of_pos_right hn hnPos
  have hNumerator :
      24 * (stmt.degBound + stmt.k + 3) * E.points.card <
        E.points.card * E.points.card - 3 * E.points.card := by
    rw [Nat.lt_sub_iff_add_lt]
    nlinarith
  have hCount : 24 * (stmt.degBound + stmt.k + 3) * E.points.card <
      (validPairs E).card :=
    hNumerator.trans_le (by
      simpa only [ECSetup.numAffine] using card_validPairs_lb E)
  apply (maSoundnessError_lt_one_iff E stmt ?_).2 hCount
  exact Finset.card_pos.mp (Nat.zero_lt_of_lt hCount)

/-- Any instance of the headline's strict acceptance hypothesis already
    certifies that the advertised knowledge error is below one. This is kept
    separate from soundness so the headline does not carry a redundant
    non-vacuity premise. -/
theorem maSoundnessError_lt_one_of_accept (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k)
    (hAccept : maSoundnessError E stmt <
      maAcceptanceProbability E stmt msg) :
    maSoundnessError E stmt < 1 := by
  exact hAccept.trans_le (by
    unfold maAcceptanceProbability
    exact probEvent_le_one)

/-- Challenge pairs in `E.points ×ˢ E.points` on which the MA verifier
    rejects `msg`. The completeness headlines (`ma_completeness` and
    variants) bound `(maRejectSet …).card`. -/
noncomputable def maRejectSet (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (E.points ×ˢ E.points).filter
    (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩)

theorem maRejectSet_eq (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q stmt.k) :
    maRejectSet E stmt msg =
      (E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩) :=
  rfl

@[simp] theorem mem_maRejectSet {stmt : DlogStatement E.q}
    {msg : MAProverMsg E.q stmt.k}
    {p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)} :
    p ∈ maRejectSet E stmt msg ↔
      p ∈ E.points ×ˢ E.points ∧
        ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ := by
  classical
  simp [maRejectSet]

/-- The `\relation^{dlog-honest}` completeness relation from paper
    (`ip.tex \ref{thm:ma}`): `(stmt, wit) ∈ relDlog` together with an
    honest first-round message `msg` (whose divisor is principal and
    encodes the claimed scalars). -/
def relDlogHonest (stmt : DlogStatement E.q) (wit : DlogWitness E.q) : Prop :=
  ∃ (hk : stmt.k = wit.k) (msg : MAProverMsg E.q stmt.k),
    relDlog E stmt wit ∧ msg.isHonestFor E stmt wit hk

end Divisor
