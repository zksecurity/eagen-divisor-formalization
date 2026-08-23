/-
  Divisor/ExtractorBridgeTheorems.lean

  Knowledge soundness of the MA and IP protocols — paper
  `\ref{thm:ma}` and `\ref{thm:ip}`. Every theorem is axiom-free and
  stated in the point-count currency `n = E.points.card`; field-size
  (`q`-only) corollaries live in `Divisor/Hasse.lean`, the only file
  consuming the Hasse–Weil axiom.

  Layout, in dependency order:

  * **Bad-challenge cardinality bounds** — `eventDegSet_card_le`,
    `eventNotEqDefinedSet_card_le`, `badChallenges_card_le`, and the
    consolidated `badChallenges_card_le_clean` (≤ `24·(d+k+3)·n`).
  * **MA extractability** — `ma_extractable_base` (two-event
    accounting), the accept-set inclusion
    `maAcceptSet_subset_badChallenges`, the implication form
    `ma_extractable_paper`, and the headline `ma_extractable`
    (witness, or accept set ≤ `24·(d+k+3)·n`).
  * **IP extractability** — `ip_extractable_base`,
    `ip_extractable_paper`, and the headline `ip_extractable`
    (the MA dichotomy plus third-round uniqueness).
  * **Soundness probability** — `ma_soundness_probability`, the
    division-free `|accept|/|validPairs|` bound.
  * **Contrapositives** — the `witness_of_excess` family: observed
    acceptance above the bound forces extraction.

  Proof infrastructure comes from `Divisor/ExtractorBridge.lean`
  (D3–D5, polyG bridges, trace formula, sigma matching) and
  `Divisor/GeometricSoundness.lean` (the geometric all-zero route).
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

/-! ## `\ref{thm:ma}`: Extractable MA protocol -/

/-- Internal conditional form of MA extractability: the geometric
    all-zero proof with its technical preconditions exposed. The base
    theorem `ma_extractable_base` below discharges the smoothness
    hypothesis from `E.hDisc` and handles messages failing the
    verifier's degree check by the small-accept-set branch. -/
theorem ma_extractable_conditional
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
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
  · push_neg at hNV
    by_cases hAdm : stmt.admSet (msg.polyA, msg.polyB)
    · left
      exact extractor_of_logDerivCheck_all_zero_geometric E stmt hd hd2 msg hDeg hkm
        hSmooth hTargetOnE hBasesOnE hLargeQ hSample hAdm
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
    * `hd : stmt.degBound < E.q` — degree fits in the field.
    * `hd2 : 2 ≤ stmt.degBound` — needed by the `-P ∈ {B_j}` special-
      case witness `(-1).natAbs < d`.
    * `hkm` — index alignment between statement and prover message.
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
theorem ma_extractable_base
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
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
      hTargetOnE hBasesOnE hLargeQ hSample
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
point-count-dependent headline of `ma_extractable_base` as a corollary. -/
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

/-- **Paper extraction implication** (`\ref{thm:ma}` clean form).

If a first-round message accepts on more challenges than the proven bad-event
bound, then the straight-line extractor returns a valid `dlog` witness.

This is the implication form of `ma_extractable_base`: the small-acceptance
branch is ruled out by `hAcceptLarge`. -/
theorem ma_extractable_paper
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (_hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAcceptLarge :
      eventNotEqBound E stmt.degBound stmt.k +
          eventDegBound E stmt.degBound stmt.k <
        ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg stmt.degBound hd hkm = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_extractable_base E stmt hd _hd2 msg hkm
      hTargetOnE hBasesOnE hLargeQ hSample with hWit | hSmall
  · exact hWit
  · exact False.elim ((Nat.not_lt_of_ge hSmall) hAcceptLarge)

/-- **MA extractability** (headline, axiom-free). Same disjunction as
    `ma_extractable_base`, with the two-event bound consolidated into
    a single point-count term:

      `≤ 24 · (d + k + 3) · |E.points|`.

    The field-size corollary (`≤ 36·(d+k+4)·q` under the Hasse–Weil
    axiom) is `ma_extractable_hasse` in `Divisor/Hasse.lean`. -/
theorem ma_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
  rcases ma_extractable_base E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · left; exact hWit
  · right
    unfold eventNotEqBound eventDegBound at hBound
    calc
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
          ≤ 12 * (stmt.degBound + stmt.k) * E.points.card +
            (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card := hBound
      _ = (12 * (stmt.degBound + stmt.k)
            + (3 * stmt.degBound + 9 * stmt.k + 71)) * E.points.card := by ring
      _ ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
          apply Nat.mul_le_mul_right
          omega

/-! ## `\ref{thm:ip}`: Knowledge-Sound IP -/

/-- **`\ref{thm:ip}` (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_extractable_base
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
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
  · exact ma_extractable_base E stmt hd hd2 msg1 hkm
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
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAcceptLarge :
      eventNotEqBound E stmt.degBound stmt.k +
          eventDegBound E stmt.degBound stmt.k <
        ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card) :
    (∃ wit : DlogWitness E.q,
       maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
       ∧ relDlog E stmt wit)
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
           hTargetOnE hBasesOnE hLargeQ hSample hAcceptLarge
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **IP extractability** (headline, axiom-free). Same as
    `ip_extractable_base` but with the cardinality bound consolidated
    into the single point-count term `≤ 24 · (d + k + 3) · |E.points|`.

    The field-size corollary is `ip_extractable_hasse` in
    `Divisor/Hasse.lean`. -/
theorem ip_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card)
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
           hTargetOnE hBasesOnE hLargeQ hSample
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-! ## Soundness probability -/

/-- **Soundness probability bound** in natural-number form (axiom-free).

Multiplied form of `|accept|/|validPairs| ≤ 24·(d + k + 3)·n /
(n·(n − 3))` with `n = |E.points|`, avoiding division. Gives the
headline soundness-error ratio: any prover who beats this on a
uniformly random valid challenge pair has a witness extracted.

Combines `ma_extractable` (numerator) with
`card_validPairs_lb` (denominator). The single-`q` form is
`ma_soundness_probability_hasse` in `Divisor/Hasse.lean`. -/
theorem ma_soundness_probability
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      * (E.points.card * E.points.card - 3 * E.points.card)
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card
          * (validPairs E).card := by
  rcases ma_extractable E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · left; exact hWit
  · right
    have hVPlb := card_validPairs_lb E
    -- |accept| ≤ 24(d+k+3)n. Multiply both sides by n²-3n; chain via |validPairs|.
    have hStep1 :
        ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
          * (E.points.card * E.points.card - 3 * E.points.card)
        ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card
          * (E.points.card * E.points.card - 3 * E.points.card) :=
      Nat.mul_le_mul_right _ hBound
    have hStep2 :
        24 * (stmt.degBound + stmt.k + 3) * E.points.card
          * (E.points.card * E.points.card - 3 * E.points.card)
        ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card
          * (validPairs E).card := by
      apply Nat.mul_le_mul_left
      -- card_validPairs_lb uses numAffine; numAffine = E.points.card by defn.
      have h := hVPlb
      unfold ECSetup.numAffine at h
      exact h
    exact hStep1.trans hStep2

/-! ## Auditing-friendly contrapositive forms

If a prover's accept-set strictly exceeds the soundness bound, the
extractor is guaranteed to produce a witness. These are
the contrapositive shapes a verifier or auditor would actually use:
"observed acceptance > bound ⟹ extraction succeeds". -/

/-- **Auditing-friendly ratio form** (contrapositive of
`ma_soundness_probability`). If a prover's accept-set exceeds
`24·(d+k+3)·n · |validPairs| / (n·(n−3))`, the extractor returns a
witness.

Stated multiplicatively to avoid division: `|accept|·(n² − 3n) >
24·(d+k+3)·n · |validPairs|` ⟹ extractor succeeds. -/
theorem ma_extractable_witness_of_excess_ratio
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
        * (E.points.card * E.points.card - 3 * E.points.card)
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card
            * (validPairs E).card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg stmt.degBound hd hkm = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_soundness_probability E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · exact hWit
  · exact absurd hBound (Nat.not_le.mpr hExcess)

/-- **Auditing-friendly point-count form** (contrapositive of
`ma_extractable`). If accept-count exceeds `24·(d+k+3)·|E.points|`,
the extractor returns a witness. Cheap corollary of the ratio form
for local counting arguments where `|validPairs|` cancellation isn't
needed. -/
theorem ma_extractable_witness_of_excess_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg stmt.degBound hd hkm = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_extractable E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · exact hWit
  · exact absurd hBound (Nat.not_le.mpr hExcess)

/-- **IP auditing-friendly ratio form** (contrapositive of
`ip_extractable` ratio shape). If the prover's accept-set
exceeds the soundness ratio bound, the extractor returns a witness
*and* the IP third-round message is uniquely determined. -/
theorem ip_extractable_witness_of_excess_ratio
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
        * (E.points.card * E.points.card - 3 * E.points.card)
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card
            * (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit)
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
  · exact ma_extractable_witness_of_excess_ratio E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ hSample hExcess
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-- **IP auditing-friendly point-count form** (contrapositive of
`ip_extractable`). -/
theorem ip_extractable_witness_of_excess_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      ((validPairs E).filter
          (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit)
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
  · exact ma_extractable_witness_of_excess_clean E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ hSample hExcess
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'


