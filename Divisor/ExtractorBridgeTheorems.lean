/-
  Divisor/ExtractorBridgeTheorems.lean

  Knowledge-soundness machinery for the MA and IP protocols — paper
  `\ref{thm:ma}` and `\ref{thm:ip}`. Every theorem is axiom-free and
  stated in the point-count currency `n = E.points.card`. The headline
  statements built from these (`ma_soundness_count_bound`, `ip_extractable`, the
  probability and `witness_of_excess` forms) live in
  `Divisor/Headlines.lean`; field-size (`q`-only) corollaries in
  `Divisor/Hasse.lean`, the only file consuming the Hasse–Weil axiom.

  Layout, in dependency order:

  * **Bad-challenge cardinality bounds** — `eventDegSet_card_le`,
    `eventNotEqDefinedSet_card_le`, `badChallenges_card_le`, and the
    consolidated `badChallenges_card_le_clean` (≤ `24·(d+k+3)·n`).
  * **MA knowledge soundness** — `ma_soundness_base` (two-event
    accounting), the accept-set inclusion
    `maAcceptSet_subset_badChallenges`, and the implication form
    `ma_soundness_paper`.
  * **IP extractability** — `ip_extractable_base` and
    `ip_extractable_paper`.

  Proof infrastructure comes from `Divisor/ExtractorBridge.lean`
  (D3–D5, polyG bridges, trace formula, sigma matching) and
  `Divisor/GeometricSoundness.lean` (the geometric all-zero route).
-/
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
the SZ/log-derivative term `12·(d+k)·|E|`, under the standing
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
    -- A₀ne_A₁x_cleared_pair: p.1.1 ≠ p.2.1 ∧ denom ≠ 0 ∧ check = 0.
    exact Finset.mem_filter.mpr ⟨hPair, hVNeq, hDef, hCheck⟩
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

/-- Consolidated single-term form of `badChallenges_card_le` in
    point-count currency (axiom-free):
    `|badChallenges| ≤ 24 · (d + k + 3) · |E.points|`. -/
theorem badChallenges_card_le_clean
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (badChallenges E D P B m).card
      ≤ 24 * (D.degE + k + 3) * E.points.card := by
  classical
  have hSum := badChallenges_card_le E D P B m hDeg hNV hD
  unfold eventNotEqBound eventDegBound at hSum
  calc (badChallenges E D P B m).card
      ≤ 12 * (D.degE + k) * E.points.card +
        (3 * D.degE + 9 * k + 71) * E.points.card := hSum
    _ = (12 * (D.degE + k) + (3 * D.degE + 9 * k + 71)) *
          E.points.card := by ring
    _ ≤ 24 * (D.degE + k + 3) * E.points.card := by
        apply Nat.mul_le_mul_right; omega

/-! ## `\ref{thm:ma}`: Sound MA protocol -/

/-- Internal conditional form of MA soundness: the geometric
    all-zero proof with its technical preconditions exposed. The base
    theorem `ma_soundness_base` below discharges the smoothness
    hypothesis from `E.hDisc` and handles messages failing the
    verifier's degree check by the small-accept-set branch. -/
theorem ma_soundness_conditional
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q stmt.k) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k := by
  classical
  set d := stmt.degBound with hd_def
  by_cases hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
     logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ ∧
     logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
       (fun i => msg.m i) A₀ A₁ ≠ 0
  · -- Nonzero discrepancy: geometric tight SZ branch.
    right
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      maAcceptSet E stmt msg with hAS
    set badSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      eventNotEq E msg.toD stmt.target stmt.bases
        (fun i => msg.m i) with hBS
    have hSub : acceptSet ⊆ badSet := by
      intro p hp
      simp only [hAS, mem_maAcceptSet] at hp
      simp only [hBS, eventNotEq, Finset.mem_filter]
      exact ⟨hp.1, hp.2.2.2⟩
    have hCardLe : acceptSet.card ≤ badSet.card := Finset.card_le_card hSub
    have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt hDeg hd
    have hBound :=
      log_deriv_sz_paper_tight_geometric E msg.toD stmt.target stmt.bases
        (fun i => msg.m i) hDegLt hNV
    have hMono :
        12 * (msg.toD.degE + stmt.k) * E.points.card +
            (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card
          ≤ 12 * (d + stmt.k) * E.points.card +
            (3 * d + 9 * stmt.k + 71) * E.points.card := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        omega
      · apply Nat.mul_le_mul_right
        omega
    exact le_trans hCardLe (le_trans hBound hMono)
  · push Not at hNV
    by_cases hAdm : stmt.admSet (msg.polyA, msg.polyB)
    · left
      exact extractor_of_logDerivCheck_all_zero_geometric E stmt hd hd2 msg hDeg
        hSmooth hTargetOnE hBasesOnE hLargeQ hSample hAdm
        (fun A₀ A₁ hA₀ hA₁ hNVxy hDef => hNV A₀ A₁ hA₀ hA₁ hNVxy hDef)
    · -- If `(a,b) ∉ admSet`, the verifier rejects unconditionally.
      right
      set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
        maAcceptSet E stmt msg with hAS
      have hEmpty : acceptSet = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        simp only [hAS, mem_maAcceptSet] at hp
        exact hAdm hp.2.2.1
      rw [hEmpty]
      simp

/-- **Theorem `\ref{thm:ma}`** (paper, ip.tex): knowledge soundness of
    the MA protocol via a straight-line extractor.

    For every first-round message, one of two branches holds:

    * **Witness branch**: there exists `wit` satisfying the dlog
      relation `relDlog E stmt wit`, with the extractor
      `maExtractor` returning `some wit`; or

    * **Bound branch**: the set of accepting challenges in `validPairs`
      has cardinality at most
      `eventNotEqBound E d k + eventDegBound E d k`.

    The active proof path is the geometric-zero route: zeros of `D` are
    handled over `F_qbar`, the cleared numerator descends to `F_q`, and
    the tight SZ bound applies without assuming `splitsOnE E D`.

    Hypotheses:
    * `hd : stmt.degBound < E.q` — degree fits in the field.
    * `hd2 : 2 ≤ stmt.degBound` — needed by the `-P ∈ {B_j}` special-
      case witness `(-1).natAbs < d`.
    * `hTargetOnE`, `hBasesOnE` — statement well-formedness: target
      and base points lie on the curve.
    * `hLargeQ` — combined SZ-on-(E×E) threshold on the point count.
    * `hSample` — the challenge sample space is large enough for the
      Frobenius slope-sampling pigeonhole (`q`-sized slope/intercept
      spaces vs. `|validPairs|`); discharged from the Hasse–Weil
      axiom in `Divisor/Hasse.lean`.

    Denominator failures need no separate precondition: they are
    absorbed into `eventDegBound` via the `badDenomA0` count argument
    inside `sigma_data_of_gd_support_rational`, so the statement is
    exactly the paper's two-event accounting. -/
theorem ma_soundness_base
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k := by
  classical
  by_cases hDeg : msg.toD.degE ≤ stmt.degBound
  · have hLargeQ' : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72 := by
      omega
    have hCore : msg.toD.degE + stmt.k + 1 ≤
        stmt.degBound + stmt.k + 1 := by
      omega
    have hScaled : 18 * (msg.toD.degE + stmt.k + 1) * E.q ≤
        18 * (stmt.degBound + stmt.k + 1) * E.q := by
      exact Nat.mul_le_mul_right E.q (Nat.mul_le_mul_left 18 hCore)
    have hSample' : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card :=
      le_trans (Nat.add_le_add_right hScaled 1) hSample
    exact ma_soundness_conditional E stmt hd hd2 msg hDeg E.hDisc
      hTargetOnE hBasesOnE hLargeQ' hSample'
  · -- If the degree check fails, the verifier rejects every challenge.
    right
    set acceptSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
      maAcceptSet E stmt msg with hAS
    have hEmpty : acceptSet = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      simp only [hAS, mem_maAcceptSet] at hp
      exact hDeg hp.2.1
    rw [hEmpty]
    simp

/-- **Paper-tight accept-set inclusion** (unconditional).

For any first-round message and degree-check-passing entry, the
verifier's accepting challenges are contained in `badChallenges`:
either the verifier check is undefined at the pair, or it is
defined and the discrepancy `logDerivCheckFn` evaluates to zero.

Combined with `badChallenges_card_le`, this gives the
point-count-dependent headline of `ma_soundness_base` as a corollary. -/
theorem maAcceptSet_subset_badChallenges
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k)
     :
    (maAcceptSet E stmt msg)
      ⊆ badChallenges E msg.toD stmt.target stmt.bases
          (fun i => msg.m i) := by
  classical
  intro p hp
  simp only [mem_maAcceptSet] at hp
  obtain ⟨hVP, hAcc⟩ := hp
  -- maVerifierAccepts ⇒ logDerivCheckFn = 0.
  obtain ⟨_hDeg, _hAdm, hCheck⟩ := hAcc
  exact eventNotEq_subset_badChallenges E msg.toD stmt.target stmt.bases
    (fun i => msg.m i)
    (Finset.mem_filter.mpr ⟨hVP, hCheck⟩)

/-- **Paper extraction implication** (`\ref{thm:ma}` clean form).

If a first-round message accepts on more challenges than the proven bad-event
bound, then the straight-line extractor returns a valid `dlog` witness.

This is the implication form of `ma_soundness_base`: the small-acceptance
branch is ruled out by `hAcceptLarge`. -/
theorem ma_soundness_paper
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (_hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAcceptLarge :
      eventNotEqBound E stmt.degBound stmt.k +
          eventDegBound E stmt.degBound stmt.k <
        (maAcceptSet E stmt msg).card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_soundness_base E stmt hd _hd2 msg
      hTargetOnE hBasesOnE hLargeQ hSample with hWit | hSmall
  · exact hWit
  · exact False.elim ((Nat.not_lt_of_ge hSmall) hAcceptLarge)

/-! ## `\ref{thm:ip}`: Knowledge-Sound IP -/

/-- **`\ref{thm:ip}` (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_extractable_base
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_base E stmt hd hd2 msg1
           hTargetOnE hBasesOnE hLargeQ hSample
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **`\ref{thm:ip}` paper extraction implication.**

    If the first-round message accepts on more challenges than the MA bad-event
    bound, the MA extractor returns a valid witness. The IP-specific part is
    the usual uniqueness of any accepted third-round response. -/
theorem ip_extractable_paper
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAcceptLarge :
      eventNotEqBound E stmt.degBound stmt.k +
          eventDegBound E stmt.degBound stmt.k <
        (maAcceptSet E stmt msg1).card) :
    (∃ wit : DlogWitness E.q,
       maExtractor E stmt msg1 = some wit
       ∧ relDlog E stmt wit)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_paper E stmt hd hd2 msg1
           hTargetOnE hBasesOnE hLargeQ hSample hAcceptLarge
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'
