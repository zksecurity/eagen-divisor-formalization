/-
  Tests/Length2Regression.lean

  Tight length-two completeness regression.

  Under the old `degE`, every coordinate-ring element had pole order at
  least three, so the length-two completeness premises were
  contradictory and the theorems stating them could never be
  instantiated. This file keeps that boundary inhabited: on
  `y² = x³ + 1` over `F₁₇`, one base equal to the target with scalar
  `1` gives the support `[−P, P]`, `P = (1, 6)`. The prover's output is
  the vertical line `D = x − 1` of pole order exactly two, and
  `ma_completeness_prover` applies with both degree budgets equal to
  two, the smallest `ma_soundness` admits.
-/
import Divisor.Headlines
import Tests.CurveFixtures

namespace Tests.Length2Regression

open Divisor

private abbrev E17 : ECSetup := Tests.CurveFixtures.E17

/-- One base, equal to the target, with scalar `1`: `P = [1]·P`. -/
private def stmt : DlogStatement E17.q where
  k := 1
  degBound := 2
  bases := fun _ => (1, 6)
  target := (1, 6)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 1
  degBound := 2
  hRange := by intro i; norm_num

private theorem valid : relDlog E17 stmt wit := by
  refine ⟨rfl, ?_⟩
  simp only [ECPoint.weightedSum]
  rw [show (Finset.univ : Finset (Fin wit.k)) = {(⟨0, by decide⟩ : Fin wit.k)} from by decide,
    Finset.sum_singleton]
  simp [stmt, wit, ECPoint.zsmul, Fin.cast]

private theorem target_on : (stmt.target.1, -stmt.target.2) ∈ E17.points :=
  E17.hComplete _ _ (by decide)

private theorem bases_on : ∀ i, stmt.bases i ∈ E17.points :=
  fun _ => E17.hComplete _ _ (by decide)

-- The prover's output is the vertical line `x − 1` through `(1, 6)` and
-- `(1, 11)`: `a = x − 1` (up to trailing zero coefficients), `b = 0`.
#guard (proveC E17 stmt wit rfl admNormMax).map
    (fun out => out.a.coeffs.take 2 == [16, 1] && (out.a.coeffs.drop 2).all (· == 0) &&
      out.b.coeffs.all (· == 0)) == some true

/-- The prover returns a message (so the statements below are not vacuous). -/
theorem prove_isSome : (proveC E17 stmt wit rfl admNormMax).isSome := by
  have hD := (interpolate_spec (hk := rfl) valid (by decide) target_on bases_on).1
  rw [← interpolateC_toCoordRingElt E17 stmt wit rfl] at hD
  simp only [proveC, Option.isSome_map, admNormMax]
  rw [if_neg]
  · rfl
  · rintro ⟨ha, hb⟩
    exact hD ⟨(CoeffPoly.toPolynomial_eq_zero_iff _).mpr ha,
      (CoeffPoly.toPolynomial_eq_zero_iff _).mpr hb⟩

/-- The prover's message is honest, admissible, and of pole order exactly two. -/
theorem prover_spec :
    ∀ out, proveC E17 stmt wit rfl admNormMax = some out →
      out.toMsg.isHonestFor E17 stmt wit rfl ∧ stmt.admSet (out.toMsg.polyA, out.toMsg.polyB) ∧
        out.toMsg.toD.degE = 2 := by
  intro out h
  obtain ⟨hon, adm, -, deg⟩ :=
    (prover_complete E17 stmt wit rfl admNormMax rfl valid (by decide) target_on bases_on).1
      out h
  exact ⟨hon, adm, deg.trans (by decide)⟩

/-- `ma_completeness_prover` at degree budget two. -/
theorem length2_completeness :
    ∀ out, proveC E17 stmt wit rfl admNormMax = some out →
      (maRejectSet E17 stmt out.toMsg).card ≤ (3 * stmt.degBound + 4) * E17.points.card :=
  (ma_completeness_prover E17 stmt wit rfl admNormMax rfl valid (by decide) target_on
    bases_on (by decide) (by decide)).1

/--
info: 'Tests.Length2Regression.prove_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prove_isSome
/--
info: 'Tests.Length2Regression.prover_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_spec
/--
info: 'Tests.Length2Regression.length2_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length2_completeness

end Tests.Length2Regression
