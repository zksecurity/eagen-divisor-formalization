/-
  Challenge.lean — frozen headline statements for the Comparator judge.

  This module states the headline theorems with `sorry`, importing only
  the definition layer (`Divisor.Soundness` for the protocol, extractor
  and accept/reject-set definitions; `Divisor.Axioms.AxiomHasseWeil` so
  the judge can also pin the statement of the one permitted axiom).
  Neither import proves any of the theorems below.

  `leanprover/comparator` compares these statements against the library
  (`Judge/README.md` has the procedure): the solution must prove
  byte-for-byte these statements, within the permitted axiom list, and
  survive an independent kernel replay. Keep this file free of any
  import that already proves a judged theorem, or the judge loses its
  independence.
-/
import Divisor.Soundness
import Divisor.Axioms.AxiomHasseWeil

namespace Divisor

open Classical

variable (E : ECSetup)

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
    (maAcceptSet E stmt msg hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card := by
  sorry

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
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  sorry

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
      ≤ (3 * stmt.degBound + 4) * E.points.card := by
  sorry

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
  sorry

theorem ip_completeness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
  sorry

theorem ip_completeness_q
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ 18 * (stmt.degBound + stmt.k + 12) * E.q := by
  sorry

theorem ma_extractable_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (msg.toD.degE + stmt.k + 4) ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q := by
  sorry

theorem ip_extractable_hasse
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hdk : stmt.degBound + stmt.k + 3 ≤ E.q)
    (hQbig : 72 * (msg1.toD.degE + stmt.k + 4) ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
    ∧ IPUniqueThirdRound E stmt msg1 := by
  sorry

end Divisor
