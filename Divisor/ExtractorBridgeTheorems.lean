/-
  Divisor/ExtractorBridgeTheorems.lean

  Headline theorems realising paper `\ref{thm:ma}` and `\ref{thm:ip}`:

    * `ma_extractable` — knowledge soundness of the MA protocol
      (Theorem `\ref{thm:ma}`).
    * `ip_knowledge_sound` — knowledge soundness of the 3-round IP
      protocol (Theorem `\ref{thm:ip}`).

  Both theorems consume the infrastructure built up in
  `Divisor/ExtractorBridge.lean` (D3-D5, S1-S6, polyG bridges,
  trace formula, sigma matching) and combine with `Soundness.lean`'s
  `ma_completeness` / extractor definitions.

  Split from `ExtractorBridge.lean`  to keep
  the user-facing theorem file under the project's size guideline.
-/
import Divisor.ExtractorBridge
import Divisor.GeometricSoundness

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Cardinality bounds on the paper-clean bad-challenge sets

These bounds package the headline accept-set count via two
disjoint events: the undefined-denominator set `eventDegSet`
(bounded by `eventDegBound`) and the defined-zero-discrepancy set
`eventNotEqDefinedSet` (bounded by `eventNotEqBound` under a
defined nonzero witness `hNV`). Their union, `badChallenges`,
gets the sum `eventNotEqBound + eventDegBound`. -/

/-- `|eventDegSet| ≤ eventDegBound`: the validPairs-restricted
undefined set is bounded by the standard
`(3·d + 9·k + 71)·|E|` count. Unconditional. -/
theorem eventDegSet_card_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (eventDegSet E D P B).card ≤ eventDegBound E D.degE k := by
  classical
  have hSub : eventDegSet E D P B ⊆
      (E.points ×ˢ E.points).filter
        (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) := by
    intro p hp
    simp only [eventDegSet, validPairs, distinctPairs, Finset.mem_filter] at hp
    simp only [Finset.mem_filter]
    exact ⟨hp.1.1.1, hp.2⟩
  exact (Finset.card_le_card hSub).trans
    (logDerivCheckFn_undefined_set_bound_tight E D P k B hD)

/-- `|eventNotEqDefinedSet| ≤ eventNotEqBound`: the
validPairs-restricted defined-zero-discrepancy set is bounded by
the SZ/log-derivative term `18·(d+k)·q`, under the standing
defined nonzero witness `hNV`. -/
theorem eventNotEqDefinedSet_card_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (eventNotEqDefinedSet E D P B m).card ≤ eventNotEqBound E D.degE k := by
  classical
  -- eventNotEqDefinedSet ⊆ A₀ne_A₁x_cleared_pair set on E×E.
  have hSub : eventNotEqDefinedSet E D P B m ⊆
      (E.points ×ˢ E.points).filter
        (fun p => A₀ne_A₁x_cleared_pair E D P B m p) := by
    intro p hp
    simp only [eventNotEqDefinedSet, validPairs, distinctPairs,
               Finset.mem_filter] at hp
    obtain ⟨⟨⟨hPair, _hNeq⟩, hVNeq, _⟩, hDef, hCheck⟩ := hp
    simp only [Finset.mem_filter, A₀ne_A₁x_cleared_pair]
    -- A₀ne_A₁x_cleared_pair: p.1.1 ≠ p.2.1 ∧ denom ≠ 0 ∧ check = 0.
    exact ⟨hPair, hVNeq, hDef, hCheck⟩
  exact (Finset.card_le_card hSub).trans
    (log_deriv_sz_paper_core_tight_geometric E D P B m hDeg hNV)

/-- `|badChallenges| ≤ eventNotEqBound + eventDegBound`. Headline
sum bound on the paper-clean bad-challenge set. Combines
`eventDegSet_card_le` and `eventNotEqDefinedSet_card_le` via
`Finset.card_union_le`. -/
theorem badChallenges_card_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (badChallenges E D P B m).card
      ≤ eventNotEqBound E D.degE k + eventDegBound E D.degE k := by
  classical
  calc (badChallenges E D P B m).card
      = (eventDegSet E D P B ∪ eventNotEqDefinedSet E D P B m).card := rfl
    _ ≤ (eventDegSet E D P B).card + (eventNotEqDefinedSet E D P B m).card :=
        Finset.card_union_le _ _
    _ ≤ eventDegBound E D.degE k + eventNotEqBound E D.degE k :=
        Nat.add_le_add (eventDegSet_card_le E D P B hD)
          (eventNotEqDefinedSet_card_le E D P B m hDeg hNV)
    _ = eventNotEqBound E D.degE k + eventDegBound E D.degE k := by ring

/-- Hasse-clean form of `badChallenges_card_le`: under `q ≥ 5` and
the standard hypotheses, `|badChallenges| ≤ 36 · (d + k + 4) · q`. -/
theorem badChallenges_card_le_clean
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hQ : 5 ≤ E.q) :
    (badChallenges E D P B m).card ≤ 36 * (D.degE + k + 4) * E.q := by
  classical
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E hQ
  have hSum := badChallenges_card_le E D P B m hDeg hNV hD
  unfold eventNotEqBound eventDegBound at hSum
  calc (badChallenges E D P B m).card
      ≤ 18 * (D.degE + k) * E.q +
        (3 * D.degE + 9 * k + 71) * E.points.card := hSum
    _ ≤ 18 * (D.degE + k) * E.q +
        (3 * D.degE + 9 * k + 71) * (2 * E.q) :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_left _ hHasse)
          (18 * (D.degE + k) * E.q)
    _ = (18 * (D.degE + k) + 2 * (3 * D.degE + 9 * k + 71)) * E.q := by ring
    _ ≤ 36 * (D.degE + k + 4) * E.q := by
        apply Nat.mul_le_mul_right; omega

/-! ## `\ref{thm:ma}`: Extractable MA protocol -/

/-- Internal conditional form of MA extractability.

    This is the geometric all-zero proof with its current technical
    preconditions exposed. The public theorem `ma_extractable` below
    removes the redundant smoothness hypothesis and handles messages
    failing the verifier's degree check by the small-accept-set branch. -/
theorem ma_extractable_conditional
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k := by
  classical
  set d := stmt.degBound with hd_def
  by_cases hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
     logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ ∧
     logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
       (fun i => msg.m (hkm ▸ i)) A₀ A₁ ≠ 0
  · -- Nonzero discrepancy: geometric tight SZ branch.
    right
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      (validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
    set badSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      eventNotEq E msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) with hBS
    have hSub : acceptSet ⊆ badSet := by
      intro p hp
      simp only [hAS, Finset.mem_filter] at hp
      simp only [hBS, eventNotEq, Finset.mem_filter]
      exact ⟨hp.1, hp.2.2.2⟩
    have hCardLe : acceptSet.card ≤ badSet.card := Finset.card_le_card hSub
    have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt hDeg hd
    have hBound :=
      log_deriv_sz_paper_tight_geometric E msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) hDegLt hNV
    have hMono :
        18 * (msg.toD.degE + stmt.k) * E.q +
            (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card
          ≤ 18 * (d + stmt.k) * E.q +
            (3 * d + 9 * stmt.k + 71) * E.points.card := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        omega
      · apply Nat.mul_le_mul_right
        omega
    exact le_trans hCardLe (le_trans hBound hMono)
  · push_neg at hNV
    by_cases hAdm : stmt.admSet (msg.polyA, msg.polyB)
    · left
      exact extractor_of_logDerivCheck_all_zero_geometric E stmt hd hd2 msg hDeg hkm
        hSmooth hTargetOnE hBasesOnE hLargeQ hAdm
        (fun A₀ A₁ hA₀ hA₁ hNVxy hDef => hNV A₀ A₁ hA₀ hA₁ hNVxy hDef)
    · -- If `(a,b) ∉ admSet`, the verifier rejects unconditionally.
      right
      set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
        (validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
      have hEmpty : acceptSet = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [hAS, Finset.mem_filter] at hp
        exact hAdm hp.2.2.1
      rw [hEmpty]
      simp

/-- **Theorem `\ref{thm:ma}`** (paper, ip.tex): knowledge soundness of
    the MA protocol via a straight-line extractor.

    For every first-round message, one of two branches holds:

    * **Witness branch**: there exists `wit` satisfying the dlog
      relation `relDlog E stmt wit hkm`, with the extractor
      `maExtractor` returning `some wit`; or

    * **Bound branch**: the set of accepting challenges in `validPairs`
      has cardinality at most
      `eventNotEqBound E d k + eventDegBound E d k`.

    The active proof path is the geometric-zero route: zeros of `D` are
    handled over `F_qbar`, the cleared numerator descends to `F_q`, and
    the tight SZ bound applies without assuming `splitsOnE E D`.

    Hypotheses:
    * `hDenomNZ` — technical condition of the current mechanized
      all-zero extraction path. It is not intended as a final
      paper-level hypothesis; the desired unconditional statement must
      absorb its failure into `eventDegBound`.
    * `hTargetOnE`, `hBasesOnE` — statement well-formedness: target
      and base points lie on the curve.
    * `hLargeQ` — combined SZ-on-(E×E) threshold (≡ paper's `q ≥ 16`
      regime via Hasse). -/
theorem ma_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k := by
  classical
  by_cases hDeg : msg.toD.degE ≤ stmt.degBound
  · exact ma_extractable_conditional E stmt hd hd2 msg hDeg hkm E.hDisc
      hTargetOnE hBasesOnE hLargeQ
  · -- If the degree check fails, the verifier rejects every challenge.
    right
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      (validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hAS
    have hEmpty : acceptSet = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      simp only [hAS, Finset.mem_filter] at hp
      exact hDeg hp.2.1
    rw [hEmpty]
    simp

/-- **Paper-tight accept-set inclusion** (unconditional).

For any first-round message and degree-check-passing entry, the
verifier's accepting challenges are contained in `badChallenges`:
either the verifier check is undefined at the pair, or it is
defined and the discrepancy `logDerivCheckFn` evaluates to zero.

Combined with `badChallenges_card_le`, this gives the
numerical headline of `ma_extractable` as a corollary. -/
theorem maAcceptSet_subset_badChallenges
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k) :
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm))
      ⊆ badChallenges E msg.toD stmt.target stmt.bases
          (fun i => msg.m (hkm ▸ i)) := by
  classical
  intro p hp
  simp only [Finset.mem_filter] at hp
  obtain ⟨hVP, hAcc⟩ := hp
  -- maVerifierAccepts ⇒ logDerivCheckFn = 0.
  obtain ⟨_hDeg, _hAdm, hCheck⟩ := hAcc
  exact eventNotEq_subset_badChallenges E msg.toD stmt.target stmt.bases
    (fun i => msg.m (hkm ▸ i))
    (Finset.mem_filter.mpr ⟨hVP, hCheck⟩)

/-- **Paper-tight headline disjunction** (`\ref{thm:ma}` clean form).

For every prover first-round message:

* Either the extractor outputs a valid `dlog` witness, or
* The accepting challenges are contained in `badChallenges`.

The right disjunct is in fact unconditional (see
`maAcceptSet_subset_badChallenges`); this theorem packages it in the
witness-or-bound shape mirroring the paper. The numeric bound on
`|badChallenges|` follows from `badChallenges_card_le`. -/
theorem ma_extractable_paper
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (_hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (_hTargetOnE : stmt.target ∈ E.points)
    (_hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (_hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm))
      ⊆ badChallenges E msg.toD stmt.target stmt.bases
          (fun i => msg.m (hkm ▸ i)) :=
  Or.inr (maAcceptSet_subset_badChallenges E stmt msg hkm)

/-! ## `\ref{thm:ip}`: Knowledge-Sound IP -/

/-- **`\ref{thm:ip}` (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k)
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
  · exact ma_extractable E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **`\ref{thm:ip}` paper-tight form.** Same as `ip_knowledge_sound`
    but with the bound branch as the unconditional paper-tight
    inclusion `acceptSet ⊆ badChallenges`. The numeric form follows by
    `badChallenges_card_le`. -/
theorem ip_knowledge_sound_paper
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm))
      ⊆ badChallenges E msg1.toD stmt.target stmt.bases
          (fun i => msg1.m (hkm ▸ i)))
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
  · exact ma_extractable_paper E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **MA extractability, Hasse-clean form.** Same disjunction as
    `ma_extractable`, but with the cardinality bound consolidated to
    a single `q`-term via Hasse (`|E| ≤ 2q` for `q ≥ 5`):

      `≤ 36 · (d + k + 4) · q`. -/
theorem ma_extractable_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
  rcases ma_extractable E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ with hWit | hBound
  · left; exact hWit
  · right
    have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E hQ
    calc
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
          ≤ 18 * (stmt.degBound + stmt.k) * E.q +
            (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card := hBound
      _ ≤ 18 * (stmt.degBound + stmt.k) * E.q +
            (3 * stmt.degBound + 9 * stmt.k + 71) * (2 * E.q) := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left _ hHasse)
            (18 * (stmt.degBound + stmt.k) * E.q)
      _ = (18 * (stmt.degBound + stmt.k)
            + 2 * (3 * stmt.degBound + 9 * stmt.k + 71)) * E.q := by ring
      _ ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
          apply Nat.mul_le_mul_right
          omega

/-- **`\ref{thm:ip}` Hasse-clean form.** Same as `ip_knowledge_sound`
    but with the cardinality bound consolidated to a single `q`-term
    via Hasse: `≤ 36 · (d + k + 4) · q`. -/
theorem ip_knowledge_sound_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
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
  · exact ma_extractable_clean E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ hQ
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- Hasse-based lower bound on `|validPairs|` in terms of `q` only.
For `q ≥ 9`: `(q − 3)·(q − 9) ≤ 4·|validPairs|`, equivalently
`|validPairs| ≥ (q − 3)·(q − 9)/4 ≈ q²/4` for moderate `q`. -/
theorem validPairs_card_ge_q (hQ : 9 ≤ E.q) :
    (E.q - 3) * (E.q - 9) ≤ 4 * (validPairs E).card := by
  classical
  have hLB := card_validPairs_lb E
  have hHasse := Divisor.BivariateZerosOnExE.hasse_points_bound_lb E
  unfold ECSetup.numAffine at hLB
  set n := E.points.card with hn
  -- From hasse_points_bound_lb: q ≤ 2n + 3, so q - 3 ≤ 2n and q - 9 ≤ 2n - 6.
  -- card_validPairs_lb: n² - 3n ≤ |validPairs|, so 4(n² - 3n) = (2n)(2n-6) ≤ 4|validPairs|.
  -- Need: (q-3)(q-9) ≤ (2n)(2n-6).
  have hn_ge : 3 ≤ n := by omega
  have h1 : E.q - 3 ≤ 2 * n := by omega
  have h2 : E.q - 9 ≤ 2 * n - 6 := by omega
  have h3 : (E.q - 3) * (E.q - 9) ≤ (2 * n) * (2 * n - 6) :=
    Nat.mul_le_mul h1 h2
  -- (2n)(2n-6) = 4(n*n - 3n) (in ℕ for n ≥ 3).
  have hn2 : 6 ≤ 2 * n := by omega
  have h3n : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn_ge
  have h4 : (2 * n) * (2 * n - 6) = 4 * (n * n - 3 * n) := by
    zify [hn2, h3n]
    ring
  rw [h4] at h3
  omega

/-- **Soundness probability bound** in natural-number form.

Multiplied form of `|accept|/|validPairs| ≤ 36·(d + k + 4)·q /
(n·(n − 3))`, avoiding division. Gives the headline soundness-error
ratio: any prover who beats this on a uniformly random valid
challenge pair has a witness extracted.

Combines `ma_extractable_clean` (numerator) with
`card_validPairs_lb` (denominator). -/
theorem ma_soundness_probability
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      * (E.points.card * E.points.card - 3 * E.points.card)
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by
  rcases ma_extractable_clean E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hQ with hWit | hBound
  · left; exact hWit
  · right
    have hVPlb := card_validPairs_lb E
    -- |accept| ≤ 36(d+k+4)q. Multiply both sides by n²-3n; chain via |validPairs|.
    have hStep1 :
        ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
          * (E.points.card * E.points.card - 3 * E.points.card)
        ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q
          * (E.points.card * E.points.card - 3 * E.points.card) :=
      Nat.mul_le_mul_right _ hBound
    have hStep2 :
        36 * (stmt.degBound + stmt.k + 4) * E.q
          * (E.points.card * E.points.card - 3 * E.points.card)
        ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by
      apply Nat.mul_le_mul_left
      -- card_validPairs_lb uses numAffine; numAffine = E.points.card by defn.
      have h := hVPlb
      unfold ECSetup.numAffine at h
      exact h
    exact hStep1.trans hStep2

/-- **Single-`q` soundness probability bound.** Hasse-clean form of
`ma_soundness_probability` with `|validPairs|` lower-bounded by
`(q − 3)·(q − 9)/4`:

```
|accept| · (q − 3)·(q − 9) ≤ 144·(d + k + 4)·q · |validPairs|
```

Equivalently `|accept|/|validPairs| ≤ 144·(d + k + 4)·q / ((q-3)(q-9))`,
which is `O((d+k)/q)` for `q` of moderate size. -/
theorem ma_soundness_probability_q_form
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hQ : 9 ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      * ((E.q - 3) * (E.q - 9))
      ≤ 144 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by
  have hQ5 : 5 ≤ E.q := by omega
  rcases ma_extractable_clean E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hQ5 with hWit | hBound
  · left; exact hWit
  · right
    have hVP := validPairs_card_ge_q E hQ
    -- |accept| * (q-3)(q-9) ≤ 36(d+k+4)q * (q-3)(q-9) ≤ 36(d+k+4)q * 4|validPairs|.
    calc ((validPairs E).filter
            (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
              * ((E.q - 3) * (E.q - 9))
        ≤ (36 * (stmt.degBound + stmt.k + 4) * E.q) * ((E.q - 3) * (E.q - 9)) :=
          Nat.mul_le_mul_right _ hBound
      _ ≤ (36 * (stmt.degBound + stmt.k + 4) * E.q) * (4 * (validPairs E).card) :=
          Nat.mul_le_mul_left _ hVP
      _ = 144 * (stmt.degBound + stmt.k + 4) * E.q * (validPairs E).card := by ring
