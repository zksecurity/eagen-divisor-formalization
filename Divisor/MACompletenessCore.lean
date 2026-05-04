/-
  Divisor/MACompletenessCore.lean

  Parameterized core of the MA completeness theorem. This file is the
  "lower half" of `Divisor/Soundness.lean`, extracted upstream so that
  the explicit honest-divisor bridge in
  `Divisor/EagenBuildRecursive.lean` can sit between this file and the
  public `ma_completeness` wrapper in `Soundness.lean` without creating
  an import cycle.

  Contents:
  * `ma_completeness_parameterized` — the parameterized rejection-set
    bound, taking the per-pair `logDerivCheckFn = 0` claim as a hook.
-/
import Divisor.Defs
import Divisor.SupportDisjoint
import Divisor.LogDeriv
import Divisor.Protocol

namespace Divisor

open Classical

variable (E : ECSetup)

/-- **Parameterized MA completeness.** Given the per-pair
    `logDerivCheckFn = 0` claim for "good" challenges as a hook, the
    rejection set on `E × E` has cardinality bounded by
    `(3 N + 4) · |E_aff|`, where `N = numZeros E msg.toD`.

    Specialized integrations (length-4 simple, the explicit
    honest-divisor identity, etc.) provide the hook without depending
    on the `weil_reciprocity_honest` axiom. -/
theorem ma_completeness_parameterized
    (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (h_logDerivCheckFn_zero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points →
        (A₀, A₁) ∉ badChallengesCompleteness E msg.toD →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  set rejectSet : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
    (E.points ×ˢ E.points).filter
      (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) with hRS
  have hSub : rejectSet ⊆ badChallengesCompleteness E msg.toD := by
    intro p hp
    simp only [hRS, Finset.mem_filter] at hp
    obtain ⟨hpIn, hpR⟩ := hp
    by_contra hNotBad
    apply hpR
    refine ⟨hDegK, hAdm, ?_⟩
    have hpPts := Finset.mem_product.mp hpIn
    exact h_logDerivCheckFn_zero p.1 p.2 hpPts.1 hpPts.2 hNotBad
  exact le_trans (Finset.card_le_card hSub)
    (support_disjointness E msg.toD (numZeros E msg.toD) (le_refl _))

end Divisor
