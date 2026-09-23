/-
  Challenge.lean — frozen headline statements for the Comparator judge.

  This module states the headline theorems with `sorry`, importing only
  the definition layer (`Divisor.Soundness` for the protocol, extractor
  and accept/reject-set definitions; `Divisor.ProverDefs` for the
  honest prover's definitions;
  `Divisor.Axioms.AxiomHasseWeil` so the judge can also pin the
  statement of the one permitted axiom). No import proves any of the
  theorems below.

  `leanprover/comparator` compares these statements against the library
  (`Judge/README.md` has the procedure): the solution must prove
  byte-for-byte these statements, within the permitted axiom list, and
  survive an independent kernel replay. Keep this file free of any
  import that already proves a judged theorem, or the judge loses its
  independence.
-/
import Divisor.Soundness
import Divisor.ProverDefs
import Divisor.Axioms.AxiomHasseWeil

namespace Divisor

open Classical

variable (E : ECSetup)

theorem ma_soundness_count_bound
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
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
  sorry

theorem ma_soundness
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAccept : maSoundnessError E stmt <
        maAcceptanceProbability E stmt msg) :
    maExtractorValid E stmt msg := by
  sorry

theorem ip_extractable
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
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  sorry

theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q stmt.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    (maRejectSet E stmt msg).card
      ≤ (3 * stmt.degBound + 4) * E.points.card := by
  sorry

theorem ma_completeness_q
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q stmt.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    (maRejectSet E stmt msg).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q := by
  sorry

theorem ip_completeness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
  sorry

theorem ip_completeness_q
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q stmt.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by
  sorry

theorem ma_soundness_count_bound_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
  sorry

theorem ip_extractable_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q stmt.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hQbig : 72 * (stmt.degBound + stmt.k + 4) ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  sorry

theorem prover_complete
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (N : AdmNormalizer E.q) (hN : stmt.admSet = N.admSet)
    (hValid : relDlog E stmt wit) (hNonneg : ∀ i, 0 ≤ wit.scalars i)
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points) :
    (∀ msg, prove E stmt wit hk N = some msg →
      msg.isHonestFor E stmt wit hk ∧ stmt.admSet (msg.polyA, msg.polyB) ∧
        ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) ∧
        msg.toD.degE = 1 + ∑ i, (wit.scalars i).toNat) ∧
    (prove E stmt wit hk N = none →
      ∀ msg : MAProverMsg E.q stmt.k, msg.isHonestFor E stmt wit hk →
        ¬ stmt.admSet (msg.polyA, msg.polyB)) := by
  sorry

theorem ma_completeness_prover
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (N : AdmNormalizer E.q) (hN : stmt.admSet = N.admSet)
    (hValid : relDlog E stmt wit) (hNonneg : ∀ i, 0 ≤ wit.scalars i)
    (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
    (hBudgetW : 1 + ∑ i, (wit.scalars i).toNat ≤ wit.degBound)
    (hBudgetS : 1 + ∑ i, (wit.scalars i).toNat ≤ stmt.degBound) :
    (∀ msg, prove E stmt wit hk N = some msg →
      (maRejectSet E stmt msg).card ≤ (3 * stmt.degBound + 4) * E.points.card) ∧
    (prove E stmt wit hk N = none →
      ∀ msg : MAProverMsg E.q stmt.k, msg.isHonestFor E stmt wit hk →
        ¬ stmt.admSet (msg.polyA, msg.polyB)) := by
  sorry

end Divisor
