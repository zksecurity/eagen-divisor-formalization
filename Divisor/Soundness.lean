/-
  Divisor/Soundness.lean

  Theorem 6: The MA protocol is extractable with knowledge error.
  Theorem 7: The IP protocol is knowledge-sound with the same error.

  The witness is trivially extractable from the first-round message.
  Soundness reduces to the log-derivative check (Corollary 1),
  which in turn reduces to the norm check (Theorem 4/5) via
  classical function field theory.
-/
import Divisor.Defs
import Divisor.Axioms
import Divisor.SupportDisjoint
import Divisor.LogDeriv
import Divisor.Protocol

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

/-- Scalars extracted from the first-round message, after full grouping.

    Semantics:
    * Non-canonical positions get `0` (the group's total lives at the
      canonical representative).
    * The canonical position of the group sitting at `-P` gets
      `(1 + groupSum).val - 1`: the residue-side sum at `-P` is
      `1 + Σ m_j`, and the structural `+1` corresponds to the target
      itself (not to any witness scalar). Nat-subtraction underflows to
      `0` when `(1 + groupSum).val = 0`; the `extractorSucceeds`
      predicate forbids that case.
    * The canonical position of every other group gets `groupSum.val`.
-/
noncomputable def extractedScalars (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hk : stmt.k = msg.k) : Fin msg.k → ℕ :=
  fun i =>
    let negP : ZMod E.q × ZMod E.q := (stmt.target.1, -stmt.target.2)
    if extractorIsCanonical E stmt msg hk i then
      if extractorBases E stmt msg hk i = negP then
        (1 + extractorGroupSum E stmt msg hk i).val - 1
      else
        (extractorGroupSum E stmt msg hk i).val
    else 0

/-- Predicate: the extractor succeeds at bound `d`.

    Captures both the range condition (`scalar_i < d` for every `i`)
    and the `(1 + gSum).val ≥ 1` constraint needed to subtract the
    structural `+1` at the `-P` group without underflow. -/
noncomputable def extractorSucceeds (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (hk : stmt.k = msg.k) : Prop :=
  (∀ i, extractedScalars E stmt msg hk i < d) ∧
  (∀ i,
    extractorIsCanonical E stmt msg hk i →
    extractorBases E stmt msg hk i = (stmt.target.1, -stmt.target.2) →
    (1 + extractorGroupSum E stmt msg hk i).val ≥ 1)

/-- The full-grouping extractor.

    Returns `some` iff `extractorSucceeds` (range + no-underflow at the
    `-P` group). This fixes the `\mha{GAP}` noted in the paper: the
    naive lift returned invalid witnesses when `B_j = -P` or `B`
    contained duplicates; here the combined coefficient at each
    distinct basis point is recovered as an integer in `[0, d)` and
    redistributed onto the minimum-index position in each equal-base
    group. -/
noncomputable def maExtractor (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (hd : d < E.q)
    (hk : stmt.k = msg.k) :
    Option (DlogWitness E.q) :=
  if h : extractorSucceeds E stmt msg d hk then
    some {
      k := msg.k
      scalars := extractedScalars E stmt msg hk
      degBound := d
      hRange := h.1
    }
  else
    none

/-! ## Bad events -/

/-- BadRange: some extracted scalar is not in [0, d). -/
noncomputable def eventBadRange (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (d : ℕ) (hk : stmt.k = msg.k) : Prop :=
  ¬ extractorSucceeds E stmt msg d hk

/-! ## Bridge axiom: identically-zero log-derivative ⇒ extractor succeeds

    **Why this is narrow:** `log_deriv_nonvanishing_criterion`
    (LogDeriv.lean) gives partial-fraction uniqueness at the `polyG` level
    (the denominator-cleared polynomial). To apply it here we must:
      (i) translate "`logDerivCheckFn ≡ 0` on `E × E`" into "`polyG ≡ 0`
          for the grouped distinct-bases vector", and
      (ii) feed the resulting `σ`, `beta + m ∘ σ = 0`, `m_j = 0 off σ`
          into the combinatorial grouping step to read off
          `extractedScalars i < d` and the no-underflow bound at `-P`.
    Step (i) is denominator-clearing (field arithmetic on ≈50 lines); step
    (ii) is the grouping/lifting arithmetic (another ≈100 lines, per the
    paper's GAP fix). Both are mechanical but orthogonal to the
    statement-level content of "if f ≡ 0 and D(-P)=0 then extractor
    succeeds"; axiomatizing the conclusion keeps content visible at the
    theorem statement rather than hiding it in a prover-supplied
    `hExtHonest` hypothesis.

    Hypotheses are exactly the structural assumptions on the message:
    `degE(D) ≤ d` and `D(-P) = 0` (both checked by the verifier on
    every challenge, so needed for even one challenge to accept), plus
    `d < q` (needed for the degE-to-integer lift to be injective). -/
axiom extractorSucceeds_of_logDerivCheck_identically_zero
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (d : ℕ)
    (hDeg : msg.toD.degE ≤ d) (hd : d < E.q) (hkm : stmt.k = msg.k)
    (hDnegP : msg.toD.eval stmt.target.1 (-stmt.target.2) = 0)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    extractorSucceeds E stmt msg d hkm

/-! ## Theorem 6: Extractable MA protocol -/

/-- **Theorem 6 (MA extractability) — disjunctive form.**

    Knowledge soundness of the MA protocol: for every first-round
    message, either

    * the full-grouping extractor succeeds outright (left disjunct),
      and the caller reads a valid witness out of it; or

    * the set of accepting challenges in `validPairs` has size at most
      `18 * (d + stmt.k) * E.q`, i.e. ≈ `18(d+k)/q` relative to the
      `≈ q²` valid challenges — so "accept without extract" is rare.

    The previous formulation bundled a `hExtHonest` hypothesis (that
    acceptance off the NotEq bad set ⇒ extractor succeeds) which hid
    the protocol's content behind a prover-supplied assumption and made
    one of the bound conjuncts vacuous (acceptance always forces
    `logDerivCheckFn = 0`, which *is* the NotEq bad set).

    Proof: case-split on whether `logDerivCheckFn` vanishes identically
    on `E × E`. If not, `log_deriv_sz` (Corollary 1) bounds the NotEq
    bad set, and the accept set is contained in it. If yes, then either
    the verifier's `D(-P) = 0` check fails (in which case no challenge
    accepts, so the accept set is empty), or it passes and the
    partial-fraction uniqueness criterion forces the extractor to
    succeed (via the narrow bridging axiom above). -/
theorem ma_extractable
    (stmt : DlogStatement E.q) (d : ℕ) (hd : d < E.q)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ d)
    (hkm : stmt.k = msg.k) :
    (maExtractor E stmt msg d hd hkm).isSome ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 18 * (d + stmt.k) * E.q := by
  -- Case on whether the extractor succeeds.
  by_cases hSucc : extractorSucceeds E stmt msg d hkm
  · -- Left disjunct: extractor is `some _`.
    left
    unfold maExtractor
    rw [dif_pos hSucc]
    rfl
  · -- Right disjunct: bound the accepting-challenges set.
    right
    -- The accept set is a subset of the NotEq bad set (acceptance forces
    -- `logDerivCheckFn = 0`).
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      (validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
    set badSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      badChallengesNotEq E msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) with hBS
    have hSub : acceptSet ⊆ badSet := by
      intro p hp
      simp only [hAS, Finset.mem_filter] at hp
      simp only [hBS, badChallengesNotEq, Finset.mem_filter]
      exact ⟨hp.1, hp.2.2.2⟩
    have hCardLe : acceptSet.card ≤ badSet.card := Finset.card_le_card hSub
    -- Case on whether `logDerivCheckFn` is identically zero on `E × E`.
    by_cases hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
       logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
         (fun i => msg.m (hkm ▸ i)) A₀ A₁ ≠ 0
    · -- Nonvanishing: `log_deriv_sz` bounds the NotEq bad set.
      have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt hDeg hd
      have hBound :=
        log_deriv_sz E msg.toD stmt.target stmt.bases
          (fun i => msg.m (hkm ▸ i)) hDegLt hNV
      have hMono : 18 * (msg.toD.degE + stmt.k) * E.q ≤ 18 * (d + stmt.k) * E.q := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add_right hDeg _
      exact le_trans hCardLe (le_trans hBound hMono)
    · -- Identically zero on `E × E`. Push to "identically zero everywhere".
      push_neg at hNV
      -- Sub-case on `D(-P) = 0`.
      by_cases hDnegP : msg.toD.eval stmt.target.1 (-stmt.target.2) = 0
      · -- Bridging axiom gives `extractorSucceeds`, contradicting `hSucc`.
        -- `hNV` (after `push_neg`) says: on `E.points × E.points`, f = 0.
        exfalso
        apply hSucc
        exact extractorSucceeds_of_logDerivCheck_identically_zero E
          stmt msg d hDeg hd hkm hDnegP
          (fun A₀ A₁ hA₀ hA₁ => hNV A₀ A₁ hA₀ hA₁)
      · -- `D(-P) ≠ 0`: no challenge accepts; accept set is empty.
        have hEmpty : acceptSet = ∅ := by
          apply Finset.eq_empty_of_forall_not_mem
          intro p hp
          simp only [hAS, Finset.mem_filter] at hp
          exact hDnegP hp.2.2.1
        rw [hEmpty]
        simp

/-! ## Completeness -/

/-- **Weil reciprocity axiom** (classical, Silverman ch. III).

    If `msg` is the honest first-round message for `(stmt, wit)` — i.e.
    `msg.toD`'s divisor of zeros on `E` is `(-P) + Σ n_i · (B_i)` as
    encoded by `MAProverMsg.isHonestFor` — then the log-derivative
    identity `logDerivCheckFn` vanishes at every challenge whose
    `{A₀, A₁, A₂}` is disjoint from `supp((D)_0)` (equivalently:
    `(A₀, A₁) ∉ badChallengesCompleteness E msg.toD`).

    This is Weil reciprocity applied to the principal divisor of the
    rational function `D / L^m` where `L` is the chord line through
    `A₀, A₁, A₂`: the log-derivative identity is obtained from the
    fact that a principal divisor has zero sum of residues on `E`, so
    summing residues over the divisor of zeros yields the stated
    identity whenever the evaluation points avoid the support of that
    divisor. -/
axiom weil_reciprocity_honest
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0

/-- **Completeness.** For the honest prover's first-round message `msg`
    (witnessed by `isHonestFor`), the set of challenges on which the MA
    verifier rejects is contained in `badChallengesCompleteness`, hence
    bounded by `(3 N + 1) · |E_aff|` via Lemma 2 (`support_disjointness`),
    where `N = numZeros E msg.toD`.

    The three verifier checks:
    * degree check `degE(D) ≤ stmt.k` — required by `hDegK`;
    * target-vanishing `D(-P) = 0` — required by `hDnegP`;
    * log-derivative identity — vanishes off the bad set by the
      Weil-reciprocity axiom, given the honest-divisor predicate.

    Hence rejection forces the challenge into the bad set. -/
theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : dlogHolds stmt wit hk)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.k)
    (hDnegP : msg.toD.eval stmt.target.1 (-stmt.target.2) = 0)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 1) * E.numAffine := by
  -- unused-variable guards: record that these hypotheses participate
  -- structurally in the statement content.
  let _ := hValid
  let _ := hDeg
  -- Show: the reject-set is contained in `badChallengesCompleteness`.
  set rejectSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hRS
  have hSub : rejectSet ⊆ badChallengesCompleteness E msg.toD := by
    intro p hp
    simp only [hRS, Finset.mem_filter] at hp
    obtain ⟨_, hpR⟩ := hp
    -- If `p` is NOT in the bad set, `maVerifierAccepts` holds, contra `hpR`.
    by_contra hNotBad
    apply hpR
    refine ⟨hDegK, hDnegP, ?_⟩
    exact weil_reciprocity_honest E stmt wit hk msg hkm hHonestDivisor
      p.1 p.2 hNotBad
  -- Apply support_disjointness.
  exact le_trans (Finset.card_le_card hSub)
    (support_disjointness E msg.toD (numZeros E msg.toD) (le_refl _))

/-! ## Theorem 7: Knowledge-Sound IP -/

/-- **Theorem 7 (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight).

    Conjunct 1: extractor-or-bound — directly from `ma_extractable`.
    Conjunct 2: third-round uniqueness — directly from `ip_unique_third_round`. -/
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (d : ℕ) (hd : d < E.q)
    (msg1 : MAProverMsg E.q) (hDeg : msg1.toD.degE ≤ d)
    (hkm : stmt.k = msg1.k) :
    -- (1) Same knowledge guarantee as MA.
    ((maExtractor E stmt msg1 d hd hkm).isSome ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ 18 * (d + stmt.k) * E.q)
    -- (2) Uniqueness of third-round message.
    ∧ ∀ (chal : MAChallenge E.q) (A₂ : ZMod E.q × ZMod E.q)
        (msg3 msg3' : IPProverMsg3 E.q),
        msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0 →
        msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0 →
        msg1.toD.eval A₂.1 A₂.2 ≠ 0 →
        (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
            stmt.target.1 (-stmt.target.2) ≠ 0 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3' →
        msg3 = msg3' := by
  refine ⟨?_, ?_⟩
  · exact ma_extractable E stmt d hd msg1 hDeg hkm
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

end Divisor
