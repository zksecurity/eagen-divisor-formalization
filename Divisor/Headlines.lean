/-
  Divisor/Headlines.lean

  The headline theorems of the project, in one place — every
  axiom-free result the README and `Challenge.lean` advertise, and
  nothing else. Proof machinery lives in the files this module
  imports; the field-size (`q`-only) variants priced by the
  Hasse–Weil axiom live in `Divisor/Hasse.lean`, which builds on this
  file and is the only importer of the axiom.

  * **Knowledge soundness** — `ma_soundness_count_bound`, `ip_extractable`
    (witness, or accept set ≤ `24·(d+k+3)·|E|`; the IP form adds
    third-round uniqueness).
  * **Completeness** — `ma_completeness` (reject set ≤ `(3d+4)·|E|`),
    `ma_completeness_q`, `ip_completeness`, `ip_completeness_q`.
  * **Binary any-length completeness** —
    `ma_completeness_binary_any_length` and its decidable-certificate
    form, under the `SafePairs` general-position hypothesis.
  * **Soundness probability and contrapositives** —
    `ma_soundness_ratio_bound` and the `witness_of_excess` family:
    observed acceptance above the bound forces extraction.
-/
import Divisor.ExtractorBridgeTheorems
import Divisor.Completeness
import Divisor.SafeSupport

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Knowledge soundness -/

/-- **MA soundness count bound**. Same disjunction as
    `ma_soundness_base`, with the two-event bound consolidated into
    a single point-count term:

      `≤ 24 · (d + k + 3) · |E.points|`.

    The field-size corollary (`≤ 36·(d+k+4)·q` under the Hasse–Weil
    axiom) is `ma_soundness_count_bound_hasse` in `Divisor/Hasse.lean`. -/
theorem ma_soundness_count_bound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
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
    (maAcceptSet E stmt msg hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
  rcases ma_soundness_base E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · left; exact hWit
  · right
    unfold eventNotEqBound eventDegBound at hBound
    calc
      (maAcceptSet E stmt msg hkm).card
          ≤ 12 * (stmt.degBound + stmt.k) * E.points.card +
            (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card := hBound
      _ = (12 * (stmt.degBound + stmt.k)
            + (3 * stmt.degBound + 9 * stmt.k + 71)) * E.points.card := by ring
      _ ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
          apply Nat.mul_le_mul_right
          omega

/-- Here `maExtractorValid E stmt msg` says that `maExtractor` returns a
    witness and that this exact output satisfies `relDlog E stmt`.

    **MA knowledge soundness.** For every matching-arity Merlin message,
    honest or malicious, acceptance above the explicit knowledge error forces
    the executable extractor's exact output to satisfy `relDlog`. -/
theorem ma_soundness
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAccept : maSoundnessError E stmt <
        maAcceptanceProbability E stmt msg hkm) :
    maExtractorValid E stmt msg := by
  rcases ma_soundness_count_bound E stmt hd hd2 msg hkm
      hTargetOnE hBasesOnE hLargeQ hSample with hWit | hSmall
  · obtain ⟨wit, hExtract, hValid⟩ := hWit
    simp [maExtractorValid, hExtract, hValid]
  · have hCast :
        ((maAcceptSet E stmt msg hkm).card : ENNReal) ≤
          ((24 * (stmt.degBound + stmt.k + 3) * E.points.card : ℕ) : ENNReal) := by
      exact_mod_cast hSmall
    have hProbabilityLe : maAcceptanceProbability E stmt msg hkm ≤
        maSoundnessError E stmt := by
      rw [maAcceptanceProbability_eq_card_div]
      unfold maSoundnessError
      exact ENNReal.div_le_div_right hCast _
    exact False.elim ((not_lt_of_ge hProbabilityLe) hAccept)

/-- **IP extractability**. Same as
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
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_count_bound E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ hSample
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

/-! ## Completeness -/

/-- **MA completeness** (headline, point-count form). The honest
    prover is rejected on at most `(3·d + 4) · |E.points|` challenge
    pairs. Restates `ma_completeness_degBound`
    (`Divisor/Completeness.lean`); the field-size form is
    `ma_completeness_q` below. -/
theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * stmt.degBound + 4) * E.points.card :=
  ma_completeness_degBound E stmt wit hk hValid msg hkm hDeg hDegK hAdm
    hHonestDivisor hD

/-- **MA completeness, field-size form.** Trivial conversion of
    `ma_completeness` via the fiber bound `|E.points| ≤ 2q`
    (`points_card_le_two_q`; no axiom): the rejection-set
    cardinality is bounded by `(6·(d + 1) + 6) · q`. Matches paper's
    `\compErr ≤ 6(\degBound + 1)/q` after dividing by `|E|² ≥ q²/2`. -/
theorem ma_completeness_q
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    (maRejectSet E stmt msg hkm).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  have hMA := ma_completeness E stmt wit hk hValid msg hkm hDeg hDegK hAdm hHonestDivisor hD
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E
  calc _ ≤ (3 * stmt.degBound + 4) * E.points.card := hMA
    _ ≤ (3 * stmt.degBound + 4) * (2 * E.q) := Nat.mul_le_mul_left _ hHasse
    _ ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by ring_nf; omega

/-- **IP completeness, cardinality form.** The set of challenges on
    which no third-round message makes the IP verifier accept is
    bounded by `(3·d + 9·k + 71) · |E.points|`, where
    `d = msg.toD.degE` and `k = stmt.k`.

    Single-set bound: IP rejection ⊆ `eventDeg`. The MA denominator
    cases (`D(A_i) = 0`, `A₂ = ∞`) and the IP-specific ones
    (`L(-P) = 0`, `L(B_j) = 0`, `dx/dz = 0`) all live inside
    `eventDeg`, so one bound on `|eventDeg|` covers both. -/
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
    rw [hUdef]
    exact Finset.filter_congr fun p _ => by simp only [eventDeg]
  calc rejectIP.card
      ≤ eventDegSet.card := Finset.card_le_card hSub
    _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
        rw [hEventDegEq]
        exact logDerivCheckFn_undefined_set_bound_tight E msg.toD stmt.target
                stmt.k stmt.bases hD

/-- **IP completeness, field-size form.** Trivial conversion of
    `ip_completeness` via the fiber bound `|E.points| ≤ 2q`
    (`points_card_le_two_q`; no axiom): the rejection-set
    cardinality is bounded by `18 · (d + k + 12) · q`. -/
theorem ip_completeness_q
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by
  have hIP := ip_completeness E stmt msg hkm hDegK hD
  have hHasse : E.points.card ≤ 2 * E.q := points_card_le_two_q E
  calc _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := hIP
    _ ≤ (3 * stmt.degBound + 9 * stmt.k + 71) * (2 * E.q) :=
        Nat.mul_le_mul (by omega) hHasse
    _ ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by ring_nf; omega

/-! ## Binary any-length completeness -/

/-- **Any-length binary completeness.** For a binary
witness whose support satisfies the semantic general-position
hypothesis `SafePairs` — every nonempty split of every sublist has a
chord-safe pair of subset sums — the honest line-build-singletons
message achieves the completeness bound, at ANY support length. The
hypothesis is decidable per instance via `SafePairsCert` +
`SafePairs.of_cert`. -/
theorem ma_completeness_binary_any_length
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (h_valid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       LineAccum.lineBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (h_nodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_safe : LineAccum.SafePairs E (binarySupport stmt wit hk h_binary))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_deg : msg.toD.degE ≤ wit.degBound)
    (h_deg_k : msg.toD.degE ≤ stmt.degBound) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  have h_ps_on := binarySupport_on_curve stmt wit hk h_binary
    h_target_on_curve h_bases_on_curve
  exact ma_completeness_binary_point_certificate E stmt wit hk msg hkm
    h_binary h_valid h_toD_eq h_degE_eq h_scalars_match
    h_target_on_curve h_bases_on_curve h_nodup
    (LineAccum.iteratedPointChordCase_of_safePairs E
      (binarySupport stmt wit hk h_binary) h_ps_on h_safe)
    h_admSetMax h_deg h_deg_k

/-- Any-length binary completeness with the general-position
hypothesis supplied by the computable certificate
(`decide`/`native_decide`-friendly). -/
theorem ma_completeness_binary_any_length_cert
    (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1)
    (h_valid : relDlog E stmt wit)
    (h_toD_eq : msg.toD =
       LineAccum.lineBuild_singletons E
         (binarySupport stmt wit hk h_binary))
    (h_degE_eq :
       msg.toD.degE = (binarySupport stmt wit hk h_binary).length)
    (h_scalars_match : ∀ i : Fin stmt.k,
       msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (h_nodup : (binarySupport stmt wit hk h_binary).Nodup)
    (h_cert : LineAccum.SafePairsCert E (binarySupport stmt wit hk h_binary))
    (h_admSetMax : stmt.admSet = admSetMax (q := E.q))
    (h_deg : msg.toD.degE ≤ wit.degBound)
    (h_deg_k : msg.toD.degE ≤ stmt.degBound) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine :=
  ma_completeness_binary_any_length E stmt wit hk msg hkm h_binary h_valid
    h_toD_eq h_degE_eq h_scalars_match h_target_on_curve h_bases_on_curve
    h_nodup
    (LineAccum.SafePairs.of_cert E
      (binarySupport_on_curve stmt wit hk h_binary
        h_target_on_curve h_bases_on_curve)
      h_cert)
    h_admSetMax h_deg h_deg_k

/-! ## Soundness probability and contrapositives -/

/-! ## Soundness probability -/

/-- **Soundness probability bound** in natural-number form (axiom-free).

Multiplied form of `|accept|/|validPairs| ≤ 24·(d + k + 3)·n /
(n·(n − 3))` with `n = |E.points|`, avoiding division. Gives the
headline soundness-error ratio: any prover who beats this on a
uniformly random valid challenge pair has a witness extracted.

Combines `ma_soundness_count_bound` (numerator) with
`card_validPairs_lb` (denominator). The single-`q` form is
`ma_soundness_ratio_bound_hasse` in `Divisor/Hasse.lean`. -/
theorem ma_soundness_ratio_bound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
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
    (maAcceptSet E stmt msg hkm).card
      * (E.points.card * E.points.card - 3 * E.points.card)
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card
          * (validPairs E).card := by
  rcases ma_soundness_count_bound E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · left; exact hWit
  · right
    have hVPlb := card_validPairs_lb E
    -- |accept| ≤ 24(d+k+3)n. Multiply both sides by n²-3n; chain via |validPairs|.
    have hStep1 :
        (maAcceptSet E stmt msg hkm).card
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
`ma_soundness_ratio_bound`). If a prover's accept-set exceeds
`24·(d+k+3)·n · |validPairs| / (n·(n−3))`, the extractor returns a
witness.

Stated multiplicatively to avoid division: `|accept|·(n² − 3n) >
24·(d+k+3)·n · |validPairs|` ⟹ extractor succeeds. -/
theorem ma_soundness_of_excess_ratio
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      (maAcceptSet E stmt msg hkm).card
        * (E.points.card * E.points.card - 3 * E.points.card)
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card
            * (validPairs E).card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_soundness_ratio_bound E stmt hd hd2 msg hkm
          hTargetOnE hBasesOnE hLargeQ hSample with hWit | hBound
  · exact hWit
  · exact absurd hBound (Nat.not_le.mpr hExcess)

/-- **Auditing-friendly point-count form** (contrapositive of
`ma_soundness_count_bound`). If accept-count exceeds `24·(d+k+3)·|E.points|`,
the extractor returns a witness. Cheap corollary of the ratio form
for local counting arguments where `|validPairs|` cancellation isn't
needed. -/
theorem ma_soundness_of_excess_count
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      (maAcceptSet E stmt msg hkm).card
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg = some wit
      ∧ relDlog E stmt wit := by
  rcases ma_soundness_count_bound E stmt hd hd2 msg hkm
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
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      (maAcceptSet E stmt msg1 hkm).card
        * (E.points.card * E.points.card - 3 * E.points.card)
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card
            * (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg1 = some wit
        ∧ relDlog E stmt wit)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_of_excess_ratio E stmt hd hd2 msg1 hkm
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
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hExcess :
      (maAcceptSet E stmt msg1 hkm).card
        > 24 * (stmt.degBound + stmt.k + 3) * E.points.card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg1 = some wit
        ∧ relDlog E stmt wit)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  refine ⟨?_, ?_⟩
  · exact ma_soundness_of_excess_count E stmt hd hd2 msg1 hkm
           hTargetOnE hBasesOnE hLargeQ hSample hExcess
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

end Divisor
