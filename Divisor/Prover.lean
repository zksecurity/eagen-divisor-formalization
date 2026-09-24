/-
  Divisor/Prover.lean — completeness of the honest MA prover.

  `interpolate` (the noncomputable line build over `honestSupport`) is
  honest (`isHonestFor`), nonzero, and of pole order `1 + Σ nᵢ` for every
  valid witness with nonnegative scalars, with no general-position
  hypothesis. The executable `proveC` (`Divisor/ProverDefs.lean`) computes
  it (`lineBuildC_singletons_toCoordRingElt`), up to the normalizer's scale.

  `proveC_spec`: the prover's output is honest and admissible, or no
  honest message for the given witness is admissible.
  `proveC_rejectSet_bound` composes
  this with the unchanged `ma_completeness` bound.
-/
import Divisor.ProverDefs
import Divisor.OrdP.Units
import Divisor.LineBuildExact
import Divisor.Completeness
import Divisor.CoordRingElt.Smul

open Polynomial

namespace Divisor

variable (E : ECSetup)

variable (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)

/-- The message carrying `D`, with the witness residues. -/
noncomputable def msgOfD (D : CoordRingElt E.q) : MAProverMsg E.q stmt.k where
  m i := (wit.scalars (hk ▸ i) : ZMod E.q)
  polyA := D.a
  polyB := D.b

@[simp] theorem msgOfD_toD (D : CoordRingElt E.q) : (msgOfD E stmt wit hk D).toD = D := rfl

/-- The prover's polynomial, as a `CoordRingElt`: the line build over
    `honestSupport`. -/
noncomputable def interpolate : CoordRingElt E.q :=
  LineAccum.lineBuild_singletons E (honestSupport stmt wit hk)

/-- The executed build computes `interpolate`. -/
theorem interpolateC_toCoordRingElt :
    (LineAccum.lineBuildC_singletons E (honestSupport stmt wit hk)).toCoordRingElt =
      interpolate E stmt wit hk :=
  LineAccum.lineBuildC_singletons_toCoordRingElt E _

/-- `proveC` is the normalized interpolation, read coefficient-wise. -/
theorem proveC_eq_map (N : AdmNormalizer E.q) :
    (proveC E stmt wit hk N).map MsgC.toMsg =
      (N.normalize (LineAccum.lineBuildC_singletons E (honestSupport stmt wit hk))).map
        fun c => msgOfD E stmt wit hk (c • interpolate E stmt wit hk) := by
  rw [proveC, Option.map_map]
  congr 1
  funext c
  simp only [Function.comp, MsgC.toMsg, msgOfD, CoeffPoly.toPolynomial_smul,
    CoordRingElt.smul_a, CoordRingElt.smul_b, ← interpolateC_toCoordRingElt,
    CoordRingEltC.toCoordRingElt_a, CoordRingEltC.toCoordRingElt_b]

section Honest

variable {E stmt wit hk}
variable (hValid : relDlog E stmt wit) (hNonneg : ∀ i, 0 ≤ wit.scalars i)
  (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
  (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
include hValid hNonneg h_target_on_curve h_bases_on_curve

theorem interpolate_spec :
    let D := interpolate E stmt wit hk
    ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ Q ∈ E.points, ordAt E D Q = (honestSupport stmt wit hk).count Q) ∧
      splitsOnE E D ∧ D.degE = 1 + ∑ i, (wit.scalars i).toNat := by
  have h := LineAccum.Exact.lineBuild_singletons_exact E (honestSupport stmt wit hk)
    (honestSupport_on_curve stmt wit hk h_target_on_curve h_bases_on_curve)
    (honestSupport_sumOnE_eq_zero stmt wit hk hValid hNonneg h_target_on_curve h_bases_on_curve)
    (List.cons_ne_nil _ _)
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (honestSupport_length stmt wit hk)⟩

/-- Any nonzero rescaling of the interpolated polynomial is an honest message. -/
theorem msgOfD_smul_interpolate_isHonestFor (c : ZMod E.q) (hc : c ≠ 0) :
    (msgOfD E stmt wit hk (c • interpolate E stmt wit hk)).isHonestFor E stmt wit hk := by
  obtain ⟨hD, hord, hsplit, _⟩ :=
    interpolate_spec hValid hNonneg h_target_on_curve h_bases_on_curve
  refine ⟨fun _ => rfl, ?_, ?_, h_target_on_curve, h_bases_on_curve⟩
  · exact (splitsOnE_smul E c hc _).mpr hsplit
  · intro R
    rw [msgOfD_toD, divisorOfD_smul E c hc]
    rcases R with _ | ⟨x, y, hns⟩
    · simp only [divisorOfD, honestDivisorCoeffs, msgOfD_toD,
        CoordRingElt.degE_smul E c hc, normPoly_natDegree_eq]
    · have hmem : (x, y) ∈ E.points :=
        E.hComplete x y ((E.equation_iff x y).mp (E.equation_iff_nonsingular.mpr hns))
      simp only [divisorOfD, honestDivisorCoeffs]
      rw [hord _ hmem, honestSupport_count_eq stmt wit hk hNonneg]

omit hValid h_target_on_curve h_bases_on_curve in
/-- An honest message's order at a rational point is the honest
    coefficient there, which does not depend on the message. -/
theorem ordAt_of_isHonestFor {msg : MAProverMsg E.q stmt.k}
    (h : msg.isHonestFor E stmt wit hk) {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    (ordAt E msg.toD Q : ℤ) = (honestSupport stmt wit hk).count Q := by
  rw [honestSupport_count_eq stmt wit hk hNonneg]
  have hdiv := h.2.2.1 (ECPoint.affineOfMem E hQ)
  rcases Q with ⟨x, y⟩
  simpa [ECPoint.affineOfMem, ECPoint.affineOfEqn, divisorOfD, honestDivisorCoeffs] using hdiv

end Honest

section Complete

variable {E stmt wit hk}
variable (N : AdmNormalizer E.q) (hN : stmt.admSet = N.admSet)
  (hValid : relDlog E stmt wit) (hNonneg : ∀ i, 0 ≤ wit.scalars i)
  (h_target_on_curve : (stmt.target.1, -stmt.target.2) ∈ E.points)
  (h_bases_on_curve : ∀ i, stmt.bases i ∈ E.points)
include hN hValid hNonneg h_target_on_curve h_bases_on_curve

/-- **Prover completeness.** The prover's output is honest, admissible,
    nonzero and of pole order `1 + Σ nᵢ`; if it returns nothing, no honest
    message for this witness is admissible. -/
theorem proveC_spec :
    (∀ out, proveC E stmt wit hk N = some out →
      out.toMsg.isHonestFor E stmt wit hk ∧ stmt.admSet (out.toMsg.polyA, out.toMsg.polyB) ∧
        ¬ (out.toMsg.toD.a = 0 ∧ out.toMsg.toD.b = 0) ∧
        out.toMsg.toD.degE = 1 + ∑ i, (wit.scalars i).toNat) ∧
    (proveC E stmt wit hk N = none →
      ∀ msg : MAProverMsg E.q stmt.k, msg.isHonestFor E stmt wit hk →
        ¬ stmt.admSet (msg.polyA, msg.polyB)) := by
  obtain ⟨hD, hord, hsplit, hdeg⟩ :=
    interpolate_spec hValid hNonneg h_target_on_curve h_bases_on_curve
  have hmap := proveC_eq_map E stmt wit hk N
  set Dc := LineAccum.lineBuildC_singletons E (honestSupport stmt wit hk)
  have hDc : Dc.toCoordRingElt = interpolate E stmt wit hk :=
    interpolateC_toCoordRingElt E stmt wit hk
  set D := interpolate E stmt wit hk
  refine ⟨fun out hout => ?_, fun hnone msg hmsg hadm => ?_⟩
  · have hmsg : (N.normalize Dc).map (fun c => msgOfD E stmt wit hk (c • D)) =
        some out.toMsg := by rw [← hmap, hout, Option.map_some]
    obtain ⟨c, hc, hceq⟩ := Option.map_eq_some_iff.mp hmsg
    rw [← hceq]
    obtain ⟨hc0, hcadm⟩ := N.sound Dc c hc
    rw [hDc] at hcadm
    refine ⟨msgOfD_smul_interpolate_isHonestFor hValid hNonneg h_target_on_curve
      h_bases_on_curve c hc0, hN ▸ hcadm, ?_, ?_⟩
    · rw [msgOfD_toD]
      exact fun h => hD ((CoordRingElt.smul_isZero_iff E c hc0 D).mp h)
    · rw [msgOfD_toD, CoordRingElt.degE_smul E c hc0, hdeg]
  · have hnorm : N.normalize Dc = none := by
      have h' := congrArg (Option.map MsgC.toMsg) hnone
      rw [hmap, Option.map_none] at h'
      exact Option.map_eq_none_iff.mp h'
    by_cases hz : msg.toD.a = 0 ∧ msg.toD.b = 0
    · apply stmt.admSet_excludes_zero
      have : (msg.polyA, msg.polyB) = ((0 : Polynomial (ZMod E.q)), 0) :=
        Prod.ext hz.1 hz.2
      exact this ▸ hadm
    · obtain ⟨c, hc, hcD⟩ := eq_smul_of_ordAt_eq E msg.toD D hz hD hmsg.2.1 hsplit
        fun Q hQ => by
          have h1 := ordAt_of_isHonestFor hNonneg hmsg hQ
          rw [hord Q hQ]
          exact_mod_cast h1
      apply N.complete Dc hnorm c hc
      rw [hDc, ← hcD, ← hN]
      exact hadm

/-- **MA completeness of the prover.** Composed with the unchanged
    `ma_completeness`: within the degree budget, the prover's output is
    rejected on at most `(3·d + 4)·|E|` challenge pairs, and when the
    prover returns nothing no honest message is admissible. -/
theorem proveC_rejectSet_bound
    (hBudgetW : 1 + ∑ i, (wit.scalars i).toNat ≤ wit.degBound)
    (hBudgetS : 1 + ∑ i, (wit.scalars i).toNat ≤ stmt.degBound) :
    (∀ out, proveC E stmt wit hk N = some out →
      (maRejectSet E stmt out.toMsg).card ≤ (3 * stmt.degBound + 4) * E.points.card) ∧
    (proveC E stmt wit hk N = none →
      ∀ msg : MAProverMsg E.q stmt.k, msg.isHonestFor E stmt wit hk →
        ¬ stmt.admSet (msg.polyA, msg.polyB)) := by
  obtain ⟨hsome, hnone⟩ :=
    proveC_spec N hN hValid hNonneg h_target_on_curve h_bases_on_curve
  refine ⟨fun out hout => ?_, hnone⟩
  obtain ⟨hhon, hadm, hD, hdeg⟩ := hsome out hout
  exact ma_completeness_degBound E stmt wit hk hValid out.toMsg (hdeg ▸ hBudgetW)
    (hdeg ▸ hBudgetS) hadm hhon hD

end Complete

end Divisor
