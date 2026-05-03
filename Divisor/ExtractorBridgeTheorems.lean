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

/-! ## `\ref{thm:ma}`: Extractable MA protocol -/

/-- **Theorem `\ref{thm:ma}`** (paper, ip.tex): knowledge soundness of
    the MA protocol via a straight-line extractor.

    For every first-round message, one of two branches holds:

    * **Witness branch**: there exists `wit` satisfying the dlog
      relation `relDlog E stmt wit hkm`, with the extractor
      `maExtractor` returning `some wit`; or

    * **Bound branch**: the set of accepting challenges in `validPairs`
      has cardinality at most
      `18·(d + k)·q + (3d + 9k + 71)·|E|`.

    The active proof path is the geometric-zero route: zeros of `D` are
    handled over `F_qbar`, the cleared numerator descends to `F_q`, and
    the tight SZ bound applies without assuming `splitsOnE E D`.

    Hypotheses:
    * `hSmooth`, `hDenomNZ` — technical
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
        (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card := by
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
        hSmooth hDenomNZ hTargetOnE hBasesOnE hLargeQ hAdm
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

/-! ## Unconditional MA extractability

The headline `ma_extractable` carries `hDenomNZ` as a precondition
(see `docs/hDenomNZ-discharge-plan.md`). The form below removes that
precondition by replacing it with a third disjunctive option:
"there exists a verifier-bad `A₀`" (denomScaledPoly mod curveEq = 0).

This makes the theorem genuinely unconditional on the prover message,
at the cost of a weaker conclusion (`A` ∨ `B` ∨ `C` rather than
`A` ∨ `B`). The "C" branch (`badA₀_exists`) corresponds exactly to
the paper's `event_deg` (`paper/divisor/sections/ip.tex:396`), which
the paper charges to the error bound; closing the conditional/
unconditional gap requires the full `badA₂Mod` count argument from
`Divisor/HDenomNZBound.lean`. -/

/-- **MA extractability — unconditional disjunction**.

    Either:
    1. The extractor outputs a valid witness (`relDlog` holds), OR
    2. The accept-set has size bounded by the standard SZ-on-(E×E)
       count (the "good prover" case), OR
    3. There exists a verifier-bad `A₀ ∈ E.points` (paper's
       `event_deg`): an `A₀` that's not a `D`-zero and not a
       distinct-base-image root, yet `denomScaledPoly` mod
       `curveEqPoly` vanishes — the verifier's totalised
       expression evaluates ill-definedly there.

    The case-split is by classical decidability of `hDenomNZ`. The
    paper's analysis charges the third branch to the error bound via
    a count of bad `A₀`'s; the Lean discharge plan in
    `Divisor/HDenomNZBound.lean` provides the count
    (`badA₂Mod_card_mul_card_sub_two_le`) needed to absorb it. -/
theorem ma_extractable_unconditional
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
      ≤ 18 * (stmt.degBound + stmt.k) * E.q +
        (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card ∨
    (∃ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD ∧
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm),
            distinctR E stmt msg hkm j ≠ A₀) ∧
        denomScaledPoly (E := E) msg.toD stmt.target
          (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm) A₀ %ₘ curveEqPoly E = 0) := by
  classical
  by_cases hDNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD →
      (∀ j : Fin (1 + baseImageCount E stmt msg hkm),
          distinctR E stmt msg hkm j ≠ A₀) →
      denomScaledPoly (E := E) msg.toD stmt.target
        (baseImageCount E stmt msg hkm)
        (baseAt E stmt msg hkm) A₀ %ₘ curveEqPoly E ≠ 0
  · rcases ma_extractable E stmt hd hd2 msg hDeg hkm hSmooth hDNZ
            hTargetOnE hBasesOnE hLargeQ with hwit | hsmall
    · exact Or.inl hwit
    · exact Or.inr (Or.inl hsmall)
  · -- hDNZ fails: extract the bad A₀.
    push_neg at hDNZ
    obtain ⟨A₀, hA₀_pts, hA₀_nz, hA₀_nr, hbadDenom⟩ := hDNZ
    exact Or.inr (Or.inr ⟨A₀, hA₀_pts, hA₀_nz, hA₀_nr, hbadDenom⟩)

/-! ## `\ref{thm:ip}`: Knowledge-Sound IP -/

/-- **`\ref{thm:ip}` (IP knowledge soundness).**

    The IP has the same knowledge guarantee as the MA (extractor-or-
    small-accept-set disjunction), plus uniqueness of the third-round
    response (which makes the IP-to-MA reduction tight). -/
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q) (hDeg : msg1.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg1.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
        (3 * stmt.degBound + 9 * stmt.k + 71) * E.points.card)
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
  · exact ma_extractable E stmt hd hd2 msg1 hDeg hkm hSmooth hDenomNZ
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
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
  rcases ma_extractable E stmt hd hd2 msg hDeg hkm hSmooth hDenomNZ
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
