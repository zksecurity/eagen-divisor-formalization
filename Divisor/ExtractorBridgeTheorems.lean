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
import Divisor.SigmaMatching
import Divisor.TightBound

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Theorem 6: Extractable MA protocol -/

/-- **Theorem `\ref{thm:ma}`** (paper, ip.tex): knowledge soundness of
    the MA protocol via a straight-line extractor.

    For every first-round message, one of two branches holds:

    * **Witness branch**: there exists `wit` satisfying the dlog
      relation `relDlog E stmt wit hkm`, with the extractor
      `maExtractor` returning `some wit`; or

    * **Bound branch**: the set of accepting challenges in `validPairs`
      has cardinality at most
      `18·(d + k)·|F_q| + (6·d + 9·k + 71)·|E|`,
      linear in both `|F_q|` and `|E|`.

    The cardinality bound matches the paper's `\knowErr` (after Hasse)
    plus the boundary contribution from `event_deg`. The witness
    branch is delivered via paper Steps 1–5 (`\ref{step:logderiv}`–
    `\ref{step:extract}`); the bound branch is delivered via
    `log_deriv_sz_paper_tight` (SZ-on-(E×E) on the cleared log-deriv
    polynomial).

    Hypotheses:
    * `hSmooth`, `hSplit`, `hAccount`, `hDenomNZ` — technical
      conditions matching the paper's standing assumptions on `D` and
      the line/divisor framework (axiom-supported in `Divisor/Axioms`).
    * `hTargetOnE`, `hBasesOnE` — statement well-formedness: target
      and base points lie on the curve.
    * `hLargeQ` — combined SZ-on-(E×E) threshold (≡ paper's `q ≥ 16`
      regime via Hasse). -/
theorem ma_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hSplit : normPoly_splits_over_Fq E msg.toD)
    (hAccount : (∑ P ∈ E.points, betaConstructive E msg.toD P) =
                  (normPoly E msg.toD).natDegree)
    (hDenomNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm),
            distinctR E stmt msg hkm j ≠ A₀) →
        denomScaledPoly (E := E) msg.toD stmt.target
          (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm) A₀ %ₘ curveEqPoly E ≠ 0)
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
      ≤ 18 * (stmt.degBound + stmt.k) * E.q +
        (6 * stmt.degBound + 9 * stmt.k + 71) * E.points.card := by
  classical
  set d := stmt.degBound with hd_def
  -- Top-level case split (paper proof, ip.tex `\ref{thm:ma}`):
  -- mirrors the two-event decomposition `event_NotEq` vs `¬event_NotEq`.
  by_cases hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
     logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ ∧
     logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
       (fun i => msg.m (hkm ▸ i)) A₀ A₁ ≠ 0
  · -- =====================================================================
    -- Paper: `event_NotEq` (ip.tex `\ref{thm:ma}`):
    -- f ≢ 0 yet f(A₀,A₁) = 0. Bound via SZ-on-(E×E) (`lem:log-derivative` +
    -- Hasse), packaged as `log_deriv_sz_paper_tight`.
    -- =====================================================================
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
      log_deriv_sz_paper_tight msg.toD stmt.target stmt.bases
        (fun i => msg.m (hkm ▸ i)) hDegLt hSplit hAccount hNV
    have hMono : 18 * (msg.toD.degE + stmt.k) * E.q +
                   (6 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card
                 ≤ 18 * (d + stmt.k) * E.q +
                   (6 * d + 9 * stmt.k + 71) * E.points.card := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
      · apply Nat.mul_le_mul_right; omega
    exact le_trans hCardLe (le_trans hBound hMono)
  · push_neg at hNV
    -- =====================================================================
    -- Paper: `¬event_NotEq` branch (ip.tex `\ref{thm:ma}`):
    -- f ≡ 0 on E×E. Show extractor succeeds via Steps 1–5.
    -- =====================================================================
    -- **Paper Step 1** (ip.tex `\ref{step:logderiv}`):
    -- f as discrepancy of log-derivatives ⇒ trace formula gives `polyG = 0`
    -- on every defined non-vertical pair (Lean: `polyG_zero_trace_formula`).
    have hPolyGZero :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E (zerosAt E msg.toD)
            (fun k => ((multAt E (betaConstructive E msg.toD) msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0 :=
      polyG_zero_trace_formula stmt msg hkm hSmooth hSplit hAccount
        (fun A₀ A₁ hA₀ hA₁ hNVxy hDef => hNV A₀ A₁ hA₀ hA₁ hNVxy hDef)
        hDenomNZ hLargeQ
    -- Paper proof preamble: when (a, b) ∉ admSet the verifier rejects
    -- unconditionally, so the accept-extract event is empty in that branch.
    -- Lean dispatches it as the third sub-branch below.
    by_cases hAdm : stmt.admSet (msg.polyA, msg.polyB)
    · classical
      by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
      · -- =================================================================
        -- **Paper Step 5 (special case)** (ip.tex `\ref{step:extract}`):
        -- -P ∈ {B_j}; extractor returns the trivial witness without
        -- inspecting m. Lean: `extractorSucceeds_special` +
        -- `extracted_scalars_valid_special`.
        -- =================================================================
        left
        have hSucc : extractorSucceeds E stmt msg d hkm :=
          extractorSucceeds_special E stmt msg d hkm hNegP hd2
        have hRelation := extracted_scalars_valid_special E stmt msg hkm hNegP
        let wit : DlogWitness E.q :=
          ⟨msg.k, extractedScalars E stmt msg hkm, d, hSucc⟩
        refine ⟨wit, ?_, ?_⟩
        · show (if h : extractorSucceeds E stmt msg d hkm
                then some (⟨msg.k, extractedScalars E stmt msg hkm, d, h⟩ : DlogWitness E.q)
                else none) = _
          rw [dif_pos hSucc]
        · refine ⟨hkm, ?_⟩
          show (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q) =
            ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
              (fun i => ECPoint.zsmul E (wit.scalars i)
                (ECPoint.affine
                  (stmt.bases (Fin.cast hkm.symm i)).1
                  (stmt.bases (Fin.cast hkm.symm i)).2))
          convert hRelation using 1
      · -- =================================================================
        -- **Paper Step 5 (general case)** (ip.tex `\ref{step:extract}`):
        -- -P ∉ {B_j}. Path: Step 2 (SZ-on-(E×E) ⇒ polyGFull ≡ 0)
        -- → Step 3 (σ-matching) → Step 4 (lift to integer mults)
        -- → Step 5 general (extractor returns valid witness via
        --   `target_eq_weightedSum_of_weightedSum`).
        -- =================================================================
        left
        -- Setup: β_fun coefficients and their structural properties.
        set β_fun := betaConstructive E msg.toD with hβ_def
        have hD : ¬ msg.toD.isZero := admSet_implies_toD_nonzero stmt msg hAdm
        have hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ msg.toD.eval P.1 P.2 = 0 :=
          fun P hP => betaConstructive_support E msg.toD P hP
        have hβcov : ∀ P ∈ E.points, msg.toD.eval P.1 P.2 = 0 → β_fun P ≠ 0 :=
          fun P hP hZ => betaConstructive_covers E msg.toD hD P hP hZ
        have hβsum : (∑ P ∈ E.points, β_fun P) ≤ msg.toD.degE :=
          betaConstructive_sum_le_degE E msg.toD
        have hβgroup : ECPoint.weightedSum E E.points
            (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine P.1 P.2)) = 0 :=
          betaConstructive_group_sum_zero E msg.toD hD hSplit
        -- Prepare injective/nonzero hypotheses for sigma_matching.
        have hQinj : Function.Injective (zerosAt E msg.toD) :=
          zerosAt_injective E msg.toD
        have hDistinctR_inj : Function.Injective (distinctR E stmt msg hkm) :=
          distinctR_injective E stmt msg hkm hNegP
        have hβPos : ∀ k : Fin (zerosCard E msg.toD),
                       multAt E β_fun msg.toD k > 0 :=
          multAt_pos E β_fun msg.toD hβcov
        have hBetaLt : ∀ k, multAt E β_fun msg.toD k < E.q := by
          intro k
          have hSingle : multAt E β_fun msg.toD k ≤
              ∑ k' : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k' := by
            refine Finset.single_le_sum
              (f := fun k' => multAt E β_fun msg.toD k') ?_ (Finset.mem_univ k)
            intro k' _; exact Nat.zero_le _
          have hβSum : (∑ k : Fin (zerosCard E msg.toD),
                         multAt E β_fun msg.toD k) ≤ msg.toD.degE :=
            sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
          exact lt_of_le_of_lt (hSingle.trans (hβSum.trans hDeg)) hd
        have hBetaNz : ∀ k,
            ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q) ≠ 0 := by
          intro k
          rw [Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
          intro hdvd
          have hPos : 0 < multAt E β_fun msg.toD k := hβPos k
          have hLt : multAt E β_fun msg.toD k < E.q := hBetaLt k
          exact Nat.not_lt.mpr (Nat.le_of_dvd hPos hdvd) hLt
        -- Membership hypotheses.
        have hQonE : ∀ k, zerosAt E msg.toD k ∈ E.points :=
          fun k => zerosAt_mem_E E msg.toD k
        have hRonE : ∀ j, distinctR E stmt msg hkm j ∈ E.points :=
          fun j => distinctR_mem_points E stmt msg hkm hTargetOnE hBasesOnE j
        -- Size bounds: zerosCard + M ≤ d + k + 1.
        have hd_zero_le_d : zerosCard E msg.toD ≤ d := by
          have hCardLe : zerosCard E msg.toD ≤
              ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k := by
            calc zerosCard E msg.toD
                = ∑ _k : Fin (zerosCard E msg.toD), 1 := by
                    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k :=
                    Finset.sum_le_sum (fun k _ => hβPos k)
          have hβSum : (∑ k : Fin (zerosCard E msg.toD),
                         multAt E β_fun msg.toD k) ≤ msg.toD.degE :=
            sum_multAt_le_degE E β_fun msg.toD hβsup hβsum
          exact hCardLe.trans (hβSum.trans hDeg)
        have hBICount_le : baseImageCount E stmt msg hkm ≤ stmt.k := by
          have hleK : baseImageCount E stmt msg hkm ≤ msg.k := by
            unfold baseImageCount baseImage
            refine (Finset.card_image_le (f := extractorBases E stmt msg hkm)
                       (s := Finset.univ)).trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
          rw [hkm]; exact hleK
        have hSum_le :
            zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
              ≤ d + stmt.k + 1 := by
          have : zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
                  ≤ d + (1 + stmt.k) :=
            Nat.add_le_add hd_zero_le_d (Nat.add_le_add_left hBICount_le _)
          omega
        -- zerosCard ≤ msg.toD.degE (each mult ≥ 1, sum ≤ degE).
        have hZC_degE : zerosCard E msg.toD ≤ msg.toD.degE := by
          have hCardLe : zerosCard E msg.toD ≤
              ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k := by
            calc zerosCard E msg.toD
                = ∑ _k : Fin (zerosCard E msg.toD), 1 := by
                    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E β_fun msg.toD k :=
                    Finset.sum_le_sum (fun k _ => hβPos k)
          exact hCardLe.trans (sum_multAt_le_degE E β_fun msg.toD hβsup hβsum)
        -- Linear |E|-threshold consumed by `sigma_matching_core`.
        have hELarge : E.points.card >
            4 * (zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)) + 2 := by
          have h1 : 4 * (zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)) + 2
              ≤ 4 * (msg.toD.degE + stmt.k + 1) + 2 := by omega
          omega
        -- DKL+Bezout threshold for `polyGFull_vanishes_on_ExE_of_polyG_zero`,
        -- derived from `hLargeQ` via Hasse.
        have hELarge_dkl :
            E.points.card * E.points.card - 2 * E.points.card
              > 18 * (zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)) * E.q := by
          -- Derive from hLargeQ via Hasse-Weil.
          -- Let N = E.points.card, q = E.q, DM = zerosCard + (1 + baseImageCount).
          -- From hLargeQ: N > 31*(msg.toD.degE + stmt.k + 2) + 78.
          -- From hSum_le: DM ≤ d + stmt.k + 1.  And d = stmt.degBound ≥ msg.toD.degE.
          -- From Hasse: ((N+1 : ℤ) - q - 1)^2 ≤ 4*q, i.e., ((N : ℤ) - q)^2 ≤ 4*q.
          set N := E.points.card
          set DM := zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
          -- Hasse bound in usable form
          have hHasse : ((N : ℤ) - E.q)^2 ≤ 4 * E.q := by
            have h := hasse_weil E
            rw [E.hNumPoints] at h
            push_cast at h ⊢
            linarith
          -- DM + 1 ≤ msg.toD.degE + stmt.k + 2
          have hDM1 : DM + 1 ≤ msg.toD.degE + stmt.k + 2 := by omega
          -- Step 1: From Hasse + N ≥ 140, derive 5*q ≤ 7*N + 10
          have hQ : 5 * (E.q : ℤ) ≤ 7 * N + 10 := by
            by_contra hc; push_neg at hc
            nlinarith [sq_nonneg ((N : ℤ) - E.q),
                       sq_nonneg (5 * (E.q : ℤ) - 7 * N - 11)]
          -- Step 2: N*N > 2*N + 18*DM*q by nlinarith
          suffices h : N * N > 2 * N + 18 * DM * E.q by omega
          suffices h : (N : ℤ)^2 > 2 * N + 18 * DM * E.q by
            have : (N : ℤ)^2 = ↑(N * N) := by push_cast; ring
            rw [this] at h; exact_mod_cast h
          have h31 : 31 * (DM : ℤ) < (N : ℤ) - 109 := by omega
          nlinarith [sq_nonneg (N : ℤ),
                     mul_le_mul_of_nonneg_left hQ (show (0 : ℤ) ≤ 18 * ↑DM by omega)]
        -- ---------------------------------------------------------------
        -- **Paper Step 2** (ip.tex `\ref{step:szbiv}`):
        -- Cleared polynomial `polyGFull` vanishes identically on E × E.
        -- Lean: `polyGFull_vanishes_on_ExE_of_polyG_zero` (DKL+Bezout
        -- contrapositive, threshold `hELarge_dkl`).
        -- ---------------------------------------------------------------
        have hPolyGFullVanishing :
            ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
              A₀ ∈ E.points → A₁ ∈ E.points →
              bivEval₂ (polyGFull E (zerosAt E msg.toD)
                (fun k => ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q))
                (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)) A₀ A₁ = 0 :=
          polyGFull_vanishes_on_ExE_of_polyG_zero E
            (zerosAt E msg.toD)
            (fun k => ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            hPolyGZero hELarge_dkl
        -- ---------------------------------------------------------------
        -- **Paper Step 3** (ip.tex `\ref{step:sigma}`):
        -- Permutation σ matches multisets {Q_α} ↔ {-P, B_j} with
        -- multiplicities (≡ paper's residue identity `eq:residue-identity`).
        -- Lean: `sigma_matching_from_polyGFull_vanishing`.
        -- ---------------------------------------------------------------
        obtain ⟨σ, hσ_eq, hσ_betam, hσ_off⟩ :=
          sigma_matching_from_polyGFull_vanishing E
            (zerosAt E msg.toD)
            (fun k => ((multAt E β_fun msg.toD k : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            hQinj hDistinctR_inj hBetaNz hQonE hRonE
            hPolyGFullVanishing hELarge hELarge_dkl
        -- ---------------------------------------------------------------
        -- **Paper Step 4** (ip.tex `\ref{step:lift}`):
        -- Lift σ-matching residues to integer multiplicities n_R ∈ [0, d]
        -- (≡ paper's `eq:integer-mult`). Yields D3-coeff bound + canonical
        -- and non-canonical witness extraction. Lean:
        -- `extractorCoeffFromSigma_satisfies_D3` →
        -- `extractorSucceeds_of_natural_witness`.
        -- ---------------------------------------------------------------
        obtain ⟨hBound, hCanon, hNonCanon⟩ :=
          extractorCoeffFromSigma_satisfies_D3 E stmt msg d hDeg hkm hNegP
            β_fun hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off
        obtain ⟨hSucceeds, _hScalars_eq⟩ :=
          extractorSucceeds_of_natural_witness E stmt msg d hd hkm hNegP
            (extractorCoeffFromSigma E stmt msg hkm β_fun σ)
            hBound hCanon hNonCanon
        -- Pointwise matching ⇒ functional equality for divisor coefficients.
        have hEq : extractorDivisorCoeffs E stmt msg hkm =
                   dCoeffs E msg.toD β_fun := by
          funext P
          exact extractorDivisorCoeffs_eq_dCoeffs E stmt msg d hDeg hd hkm
            hNegP β_fun hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off P
        -- Group-sum-zero transfer (principal divisor of D ⇒ Σ[n_R]·R = O).
        have hβsup_P : ∀ P, β_fun P ≠ 0 → P ∈ E.points :=
          fun P hP => (hβsup P hP).1
        have hFinSupp : Set.Finite (Function.support (dCoeffs E msg.toD β_fun)) :=
          dCoeffs_finiteSupport E msg.toD β_fun hβsup_P
        have hGSup :
            ECPoint.weightedSum E hFinSupp.toFinset
              (fun P => ECPoint.zsmul E (dCoeffs E msg.toD β_fun P) P) = 0 :=
          dCoeffs_groupSum_zero E msg.toD β_fun hβsup_P hβgroup hFinSupp
        have hSupSub : Function.support (dCoeffs E msg.toD β_fun) ⊆
            ↑(extractorDivisorCandidate E stmt msg hkm) := by
          intro P hP
          have hP' : extractorDivisorCoeffs E stmt msg hkm P ≠ 0 := by
            rw [hEq]; exact hP
          exact extractorDivisorCoeffs_support_subset_candidate E stmt msg hkm hP'
        have hFinSupp_sub : hFinSupp.toFinset ⊆
            extractorDivisorCandidate E stmt msg hkm := by
          intro P hP
          rw [Set.Finite.mem_toFinset] at hP
          exact hSupSub hP
        have hWSum : ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
            (fun P => ECPoint.zsmul E (dCoeffs E msg.toD β_fun P) P) = 0 := by
          rw [ECPoint.weightedSum_subset_of_zero_outside E hFinSupp_sub
            (fun P _ hPnotSup => by
              rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
              rw [hPnotSup]; exact ECPoint.zsmul_zero E P)]
          exact hGSup
        have hWSum' : ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
            (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) = 0 := by
          convert hWSum using 2; funext P; rw [hEq]
        -- ---------------------------------------------------------------
        -- **Paper Step 5 (general case)** (ip.tex `\ref{step:extract}`):
        -- Convert principal-divisor group-sum-zero into the dlog relation
        -- `P = Σ[n_j]·B_j`. Lean: `target_eq_weightedSum_of_weightedSum`.
        -- ---------------------------------------------------------------
        have hRelation := target_eq_weightedSum_of_weightedSum E stmt msg hkm hNegP hWSum'
        let wit : DlogWitness E.q :=
          ⟨msg.k, extractedScalars E stmt msg hkm, d, hSucceeds⟩
        refine ⟨wit, ?_, ?_⟩
        · show (if h : extractorSucceeds E stmt msg d hkm
                then some (⟨msg.k, extractedScalars E stmt msg hkm, d, h⟩ : DlogWitness E.q)
                else none) = _
          rw [dif_pos hSucceeds]
        · refine ⟨hkm, ?_⟩
          show (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q) =
            ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
              (fun i => ECPoint.zsmul E (wit.scalars i)
                (ECPoint.affine
                  (stmt.bases (Fin.cast hkm.symm i)).1
                  (stmt.bases (Fin.cast hkm.symm i)).2))
          convert hRelation using 1
    · -- =================================================================
      -- ¬hAdm: (a, b) ∉ admSet, verifier rejects unconditionally
      -- (paper proof preamble; no explicit Step in `\ref{thm:ma}`).
      -- =================================================================
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

/-! ## Theorem 7: Knowledge-Sound IP -/

/-- **Theorem 7 (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q) (hDeg : msg1.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg1.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hSplit : normPoly_splits_over_Fq E msg1.toD)
    (hAccount : (∑ P ∈ E.points, betaConstructive E msg1.toD P) =
                  (normPoly E msg1.toD).natDegree)
    (hDenomNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg1.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg1 hkm),
            distinctR E stmt msg1 hkm j ≠ A₀) →
        denomScaledPoly (E := E) msg1.toD stmt.target
          (baseImageCount E stmt msg1 hkm)
          (baseAt E stmt msg1 hkm) A₀ %ₘ curveEqPoly E ≠ 0)
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
      ≤ 18 * (stmt.degBound + stmt.k) * E.q +
        (6 * stmt.degBound + 9 * stmt.k + 71) * E.points.card)
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
  · exact ma_extractable E stmt hd hd2 msg1 hDeg hkm hSmooth hSplit hAccount hDenomNZ
           hTargetOnE hBasesOnE hLargeQ
  · intro chal A₂ msg3 msg3' hD₀ hD₁ hD₂ hLP hAcc hAcc'
    exact ip_unique_third_round E stmt msg1 chal A₂ msg3 msg3'
            hD₀ hD₁ hD₂ hLP hAcc hAcc'

