/-
  Tests/ProverSmoke.lean

  Inhabited prover completeness on `y² = x³ + 1` over `F₁₇`.

  Each instance constructs every premise of `ma_completeness_prover`
  (validity by explicit group-law arithmetic, on-curve facts, budgets),
  in configurations the old line build excluded:

  1. repeated base: `(0, 1) = 3·(1, 6)`; support `[(0,16), (1,6)³]`, so the
     second level-one pair is a tangent doubling;
  2. 2-torsion base: `(16, 0) = 3·(16, 0)`; support `[(16, 0)⁴]`;
  3. base equal to `−P` at a flex: `(0, 1) = 2·(0, 16)`; support `[(0,16)³]`;
  4. chord meeting the curve again at an endpoint: bases `[−2A, A]` with
     `A = (1, 6)`, target `−A`; the first chord is tangent at `A`;
  5. normalizers: `admNormMax` returns a message on instance 1; the
     `admSetLine` normalizer returns `none` on `(0,1) = 1·(0,1)`
     (`D ∝ x`), and `admSetParker` returns `none` on
     `(1,6) = (1,6) + 2·(16,0)` (`D ∝ x² − 1`); in both cases the
     completeness theorem then shows no honest message for that witness
     is admissible.

  The `none` cases identify the interpolated `D` up to a scalar through
  its ideal: the line build generates `∏ ⟨P⟩` over the support, and so
  does the explicit product of vertical lines.
-/
import Divisor.Headlines
import Tests.CurveFixtures

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Tests.ProverSmoke

open Divisor

private abbrev E17 : ECSetup := Tests.CurveFixtures.E17

private abbrev F := ZMod E17.q

/-! ## Helpers -/

private theorem mem (x y : F) (h : y ^ 2 = x ^ 3 + 0 * x + 1) : (x, y) ∈ E17.points :=
  E17.hComplete x y h

/-- Group law on concrete points, from a chord slope. -/
private theorem add_chord {x₁ y₁ x₂ y₂ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E17.points) (h₂ : (x₂, y₂) ∈ E17.points) (hx : x₁ ≠ x₂)
    (hl : l * (x₁ - x₂) = y₁ - y₂) (h3x : l ^ 2 - x₁ - x₂ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E17 x₁ y₁ + ECPoint.affine E17 x₂ y₂ = ECPoint.affine E17 x₃ y₃ := by
  have n₁ := nonsing_of_mem E17 h₁
  have n₂ := nonsing_of_mem E17 h₂
  have hxy : ¬ (x₁ = x₂ ∧ y₁ = E17.toW.toAffine.negY x₂ y₂) := fun h => hx h.1
  have hs : E17.toW.toAffine.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx), hl]
  rw [ECPoint.affine_of_nonsingular E17 n₁, ECPoint.affine_of_nonsingular E17 n₂,
    WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E17.toW.toAffine.addX x₁ x₂ (E17.toW.toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]
  have hY : E17.toW.toAffine.addY x₁ x₂ y₁ (E17.toW.toAffine.slope x₁ x₂ y₁ y₂) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E17 (nonsingular_add n₁ n₂ hxy)]

/-- Group law on concrete points, doubling with a tangent slope. -/
private theorem add_tangent {x₁ y₁ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E17.points) (hy : y₁ ≠ 0)
    (hl : l * (2 * y₁) = 3 * x₁ ^ 2) (h3x : l ^ 2 - 2 * x₁ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E17 x₁ y₁ + ECPoint.affine E17 x₁ y₁ = ECPoint.affine E17 x₃ y₃ := by
  have n₁ := nonsing_of_mem E17 h₁
  have hne : y₁ ≠ E17.toW.toAffine.negY x₁ y₁ := by
    rw [toW_negY]; intro h; exact hy ((neg_snd_eq_self_iff E17 y₁).mp h.symm)
  have hxy : ¬ (x₁ = x₁ ∧ y₁ = E17.toW.toAffine.negY x₁ y₁) := fun h => hne h.2
  have h2 : y₁ - -y₁ ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero (two_ne_zero_zmod E17) hy
  have hs : E17.toW.toAffine.slope x₁ x₁ y₁ y₁ = l := by
    rw [slope_of_Y_ne rfl hne, toW_negY, div_eq_iff h2]
    simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
    rw [show E17.curveA = 0 from rfl]
    linear_combination -hl
  rw [ECPoint.affine_of_nonsingular E17 n₁, WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E17.toW.toAffine.addX x₁ x₁ (E17.toW.toAffine.slope x₁ x₁ y₁ y₁) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]; ring
  have hY : E17.toW.toAffine.addY x₁ x₁ y₁ (E17.toW.toAffine.slope x₁ x₁ y₁ y₁) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E17 (nonsingular_add n₁ n₁ hxy)]

private theorem two_torsion_add : ECPoint.affine E17 16 0 + ECPoint.affine E17 16 0 = 0 := by
  nth_rw 2 [show (0 : F) = -0 by simp]
  rw [← ECPoint.affine_neg, add_neg_cancel]

/-- Two elements generating the same ideal differ by a nonzero scalar. -/
private theorem eq_smul_of_span_eq {D₁ D₂ : CoordRingElt E17.q}
    (h : Ideal.span {D₁.toCoordinateRing E17} = Ideal.span {D₂.toCoordinateRing E17}) :
    ∃ c : F, D₁ = c • D₂ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h.symm
  obtain ⟨c, -, hcu⟩ := isUnit_coordinateRing E17 u u.isUnit
  refine ⟨c, toCoordinateRing_injective E17 ?_⟩
  rw [toCoordinateRing_smul, ← hu, hcu, mul_comm]

private theorem listIdeal_perm {l₁ l₂ : List (ZMod E17.q × ZMod E17.q)} (h : l₁.Perm l₂) :
    listIdeal E17 l₁ = listIdeal E17 l₂ :=
  (h.map _).prod_eq

/-- The interpolated polynomial generates the support ideal. -/
private theorem span_interpolate (stmt : DlogStatement E17.q) (wit : DlogWitness E17.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E17 stmt wit) (hNonneg : ∀ i, 0 ≤ wit.scalars i)
    (hT : (stmt.target.1, -stmt.target.2) ∈ E17.points) (hB : ∀ i, stmt.bases i ∈ E17.points) :
    Ideal.span {(interpolate E17 stmt wit hk).toCoordinateRing E17} =
      listIdeal E17 (honestSupport stmt wit hk) :=
  (LineAccum.Exact.lineBuild_singletons_exact E17 _
    (honestSupport_on_curve stmt wit hk hT hB)
    (honestSupport_sumOnE_eq_zero stmt wit hk hValid hNonneg hT hB)
    (List.cons_ne_nil _ _)).2.1

/-! ## 1. Repeated base: `(0, 1) = 3·(1, 6)` (tangent doubling) -/

private def stmt₁ : DlogStatement E17.q where
  k := 1
  degBound := 4
  bases := fun _ => (1, 6)
  target := (0, 1)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit₁ : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 3
  degBound := 4
  hRange := by intro; decide

private theorem valid₁ : relDlog E17 stmt₁ wit₁ := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 0 1 = ∑ _i : Fin 1, (3 : ℤ) • ECPoint.affine E17 1 6
  rw [Fin.sum_univ_one]
  have hd := add_tangent (x₁ := 1) (y₁ := 6) (x₃ := 14) (y₃ := 12) (l := 13)
    (mem 1 6 (by decide)) (by decide) (by decide) (by decide) (by decide)
  have ha := add_chord (x₁ := 14) (y₁ := 12) (x₂ := 1) (y₂ := 6) (x₃ := 0) (y₃ := 1) (l := 7)
    (mem 14 12 (by decide)) (mem 1 6 (by decide)) (by decide) (by decide) (by decide)
    (by decide)
  rw [show (3 : ℤ) • ECPoint.affine E17 1 6 =
    ECPoint.affine E17 1 6 + ECPoint.affine E17 1 6 + ECPoint.affine E17 1 6 by abel, hd, ha]

/-- Instance 1: the prover's message on a repeated base. -/
theorem prover_repeated_base :
    ∀ out, proveC E17 stmt₁ wit₁ rfl admNormMax = some out →
      (maRejectSet E17 stmt₁ out.toMsg).card ≤ (3 * stmt₁.degBound + 4) * E17.points.card :=
  (ma_completeness_prover E17 stmt₁ wit₁ rfl admNormMax rfl valid₁ (by decide)
    (mem 0 16 (by decide)) (fun _ => mem 1 6 (by decide)) (by decide) (by decide)).1

/-! ## 2. 2-torsion base: `(16, 0) = 3·(16, 0)` -/

private def stmt₂ : DlogStatement E17.q where
  k := 1
  degBound := 4
  bases := fun _ => (16, 0)
  target := (16, 0)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit₂ : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 3
  degBound := 4
  hRange := by intro; decide

private theorem valid₂ : relDlog E17 stmt₂ wit₂ := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 16 0 = ∑ _i : Fin 1, (3 : ℤ) • ECPoint.affine E17 16 0
  rw [Fin.sum_univ_one]
  rw [show (3 : ℤ) • ECPoint.affine E17 16 0 =
    ECPoint.affine E17 16 0 + (ECPoint.affine E17 16 0 + ECPoint.affine E17 16 0) by abel,
    two_torsion_add, add_zero]

/-- Instance 2: the prover's message on a repeated 2-torsion base. -/
theorem prover_two_torsion :
    ∀ out, proveC E17 stmt₂ wit₂ rfl admNormMax = some out →
      (maRejectSet E17 stmt₂ out.toMsg).card ≤ (3 * stmt₂.degBound + 4) * E17.points.card :=
  (ma_completeness_prover E17 stmt₂ wit₂ rfl admNormMax rfl valid₂ (by decide)
    (mem 16 0 (by decide)) (fun _ => mem 16 0 (by decide)) (by decide) (by decide)).1

/-! ## 3. Base equal to `−P`, at a flex: `(0, 1) = 2·(0, 16)` -/

private def stmt₃ : DlogStatement E17.q where
  k := 1
  degBound := 3
  bases := fun _ => (0, 16)
  target := (0, 1)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit₃ : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 2
  degBound := 3
  hRange := by intro; decide

private theorem valid₃ : relDlog E17 stmt₃ wit₃ := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 0 1 = ∑ _i : Fin 1, (2 : ℤ) • ECPoint.affine E17 0 16
  rw [Fin.sum_univ_one]
  rw [show (2 : ℤ) • ECPoint.affine E17 0 16 =
    ECPoint.affine E17 0 16 + ECPoint.affine E17 0 16 by abel]
  exact (add_tangent (x₁ := 0) (y₁ := 16) (x₃ := 0) (y₃ := 1) (l := 0)
    (mem 0 16 (by decide)) (by decide) (by decide) (by decide) (by decide)).symm

/-- Instance 3: the prover's message when the base is `−P`. -/
theorem prover_base_neg_target :
    ∀ out, proveC E17 stmt₃ wit₃ rfl admNormMax = some out →
      (maRejectSet E17 stmt₃ out.toMsg).card ≤ (3 * stmt₃.degBound + 4) * E17.points.card :=
  (ma_completeness_prover E17 stmt₃ wit₃ rfl admNormMax rfl valid₃ (by decide)
    (mem 0 16 (by decide)) (fun _ => mem 0 16 (by decide)) (by decide) (by decide)).1

/-! ## 4. Chord meeting the curve again at an endpoint -/

/-- `A = (1, 6)`, `B = −2A = (14, 5)`, target `−A = (1, 11)`, bases `[B, A]`:
    the support `[A, B, A]` starts with the chord through `A` and `B`,
    whose third intersection is `A` again. -/
private def stmt₄ : DlogStatement E17.q where
  k := 2
  degBound := 3
  bases := ![(14, 5), (1, 6)]
  target := (1, 11)
  admSet := admSetMax (q := E17.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E17.q)

private def wit₄ : DlogWitness E17.q where
  k := 2
  scalars := fun _ => 1
  degBound := 3
  hRange := by intro; decide

private theorem valid₄ : relDlog E17 stmt₄ wit₄ := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 1 11 = ∑ i : Fin 2, (1 : ℤ) •
    ECPoint.affine E17 (![((14 : F), (5 : F)), (1, 6)] i).1 (![((14 : F), (5 : F)), (1, 6)] i).2
  simp only [Fin.sum_univ_two, one_zsmul, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (add_chord (x₁ := 14) (y₁ := 5) (x₂ := 1) (y₂ := 6) (x₃ := 1) (y₃ := 11) (l := 13)
    (mem 14 5 (by decide)) (mem 1 6 (by decide)) (by decide) (by decide) (by decide)
    (by decide)).symm

/-- Instance 4: the prover's message when a chord meets `E` again at an endpoint. -/
theorem prover_chord_endpoint :
    ∀ out, proveC E17 stmt₄ wit₄ rfl admNormMax = some out →
      (maRejectSet E17 stmt₄ out.toMsg).card ≤ (3 * stmt₄.degBound + 4) * E17.points.card :=
  (ma_completeness_prover E17 stmt₄ wit₄ rfl admNormMax rfl valid₄ (by decide)
    (mem 1 6 (by decide)) (fun i => by fin_cases i <;> exact mem _ _ (by decide))
    (by decide) (by decide)).1

/-! ## 5. Normalizers -/

/-- `admNormMax` always answers on a valid witness (instance 1). -/
theorem prove_max_isSome : (proveC E17 stmt₁ wit₁ rfl admNormMax).isSome := by
  have hD := (interpolate_spec (hk := rfl) valid₁ (by decide) (mem 0 16 (by decide))
    (fun _ => mem 1 6 (by decide))).1
  rw [← interpolateC_toCoordRingElt E17 stmt₁ wit₁ rfl] at hD
  simp only [proveC, Option.isSome_map, admNormMax]
  rw [if_neg]
  · rfl
  · rintro ⟨ha, hb⟩
    exact hD ⟨(CoeffPoly.toPolynomial_eq_zero_iff _).mpr ha,
      (CoeffPoly.toPolynomial_eq_zero_iff _).mpr hb⟩

/-! ## The judged headlines on the prover's message -/

/-- The prover's output on instance 1, and its message. -/
private def out₁ : MsgC E17.q stmt₁.k :=
  (proveC E17 stmt₁ wit₁ rfl admNormMax).get prove_max_isSome

private noncomputable def msg₁ : MAProverMsg E17.q stmt₁.k := out₁.toMsg

private theorem msg₁_spec :
    msg₁.isHonestFor E17 stmt₁ wit₁ rfl ∧ stmt₁.admSet (msg₁.polyA, msg₁.polyB) ∧
      ¬ (msg₁.toD.a = 0 ∧ msg₁.toD.b = 0) ∧
      msg₁.toD.degE = 1 + ∑ i, (wit₁.scalars i).toNat :=
  (prover_complete E17 stmt₁ wit₁ rfl admNormMax rfl valid₁ (by decide)
    (mem 0 16 (by decide)) (fun _ => mem 1 6 (by decide))).1 out₁ (Option.some_get _).symm

private theorem msg₁_degE : msg₁.toD.degE = 4 := by
  rw [msg₁_spec.2.2.2]; decide

/-- The unchanged judged `ma_completeness`, on the prover's message. -/
theorem prover_msg_ma_completeness :
    (maRejectSet E17 stmt₁ msg₁).card ≤ (3 * stmt₁.degBound + 4) * E17.points.card :=
  ma_completeness E17 stmt₁ wit₁ rfl valid₁ msg₁ (by rw [msg₁_degE]; decide)
    (by rw [msg₁_degE]; decide) msg₁_spec.2.1 msg₁_spec.1 msg₁_spec.2.2.1

/-- The judged field-size form `ma_completeness_q`, on the prover's message. -/
theorem prover_msg_ma_completeness_q :
    (maRejectSet E17 stmt₁ msg₁).card ≤ (6 * (stmt₁.degBound + 1) + 6) * E17.q :=
  ma_completeness_q E17 stmt₁ wit₁ rfl valid₁ msg₁ (by rw [msg₁_degE]; decide)
    (by rw [msg₁_degE]; decide) msg₁_spec.2.1 msg₁_spec.1 msg₁_spec.2.2.1

/-- Line instance: `(0, 1) = 1·(0, 1)`, support `[(0, 16), (0, 1)]`, so
    `D ∝ x` has no constant term. -/
private def stmtL : DlogStatement E17.q where
  k := 1
  degBound := 2
  bases := fun _ => (0, 1)
  target := (0, 1)
  admSet := admSetLine (q := E17.q)
  admSet_excludes_zero := admSetLine_excludes_zero (q := E17.q)

private def witL : DlogWitness E17.q where
  k := 1
  scalars := fun _ => 1
  degBound := 2
  hRange := by intro; decide

private theorem validL : relDlog E17 stmtL witL := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 0 1 = ∑ _i : Fin 1, (1 : ℤ) • ECPoint.affine E17 0 1
  rw [Fin.sum_univ_one, one_zsmul]

private theorem proveL_none : proveC E17 stmtL witL rfl admNormLine = none := by
  have hspan := span_interpolate stmtL witL rfl validL (by decide)
    (mem 0 16 (by decide)) (fun _ => mem 0 1 (by decide))
  rw [show honestSupport stmtL witL rfl = [((0 : F), (16 : F)), ((0 : F), -16)] by decide,
    ← span_verticalElt E17 (P := ((0 : F), (16 : F))) (mem 0 16 (by decide))] at hspan
  obtain ⟨c, hc⟩ := eq_smul_of_span_eq hspan
  have hcoeff : (interpolate E17 stmtL witL rfl).a.coeff 0 = 0 := by
    rw [hc]; simp [verticalElt]
  rw [← interpolateC_toCoordRingElt E17 stmtL witL rfl, CoordRingEltC.toCoordRingElt_a,
    CoeffPoly.toPolynomial_coeff] at hcoeff
  simp [proveC, admNormLine, hcoeff]

/-- No honest message lies in `admSetLine` for this statement. -/
theorem line_none_no_admissible :
    ∀ msg : MAProverMsg E17.q stmtL.k, msg.isHonestFor E17 stmtL witL rfl →
      ¬ stmtL.admSet (msg.polyA, msg.polyB) :=
  (prover_complete E17 stmtL witL rfl admNormLine rfl validL (by decide)
    (mem 0 16 (by decide)) (fun _ => mem 0 1 (by decide))).2 proveL_none

/-- Parker instance: `(1, 6) = (1, 6) + 2·(16, 0)`, support
    `[(1,11), (1,6), (16,0), (16,0)]`, so `D ∝ (x − 1)(x − 16) = x² − 1`
    has no linear term. -/
private def stmtP : DlogStatement E17.q where
  k := 2
  degBound := 4
  bases := ![(1, 6), (16, 0)]
  target := (1, 6)
  admSet := admSetParker (q := E17.q)
  admSet_excludes_zero := admSetParker_excludes_zero (q := E17.q)

private def witP : DlogWitness E17.q where
  k := 2
  scalars := ![1, 2]
  degBound := 4
  hRange := by intro i; fin_cases i <;> decide

private theorem validP : relDlog E17 stmtP witP := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E17 1 6 = ∑ i : Fin 2, (![1, 2] i : ℤ) •
    ECPoint.affine E17 (![((1 : F), (6 : F)), (16, 0)] i).1 (![((1 : F), (6 : F)), (16, 0)] i).2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℤ) • ECPoint.affine E17 16 0 =
    ECPoint.affine E17 16 0 + ECPoint.affine E17 16 0 by abel, two_torsion_add, one_zsmul,
    add_zero]

private theorem proveP_none : proveC E17 stmtP witP rfl admNormParker = none := by
  have hspan := span_interpolate stmtP witP rfl validP
    (by decide) (mem 1 11 (by decide))
    (fun i => by fin_cases i <;> exact mem _ _ (by decide))
  have hperm : (honestSupport stmtP witP rfl).Perm
      ([((1 : F), (6 : F)), ((1 : F), -6)] ++ [((16 : F), (0 : F)), ((16 : F), -0)]) := by
    decide
  rw [listIdeal_perm hperm, listIdeal_append,
    ← span_verticalElt E17 (P := ((1 : F), (6 : F))) (mem 1 6 (by decide)),
    ← span_verticalElt E17 (P := ((16 : F), (0 : F))) (mem 16 0 (by decide)),
    ← span_mulCoordRingElt] at hspan
  obtain ⟨c, hc⟩ := eq_smul_of_span_eq hspan
  have hcoeff : (interpolate E17 stmtP witP rfl).a.coeff 1 = 0 := by
    rw [hc]
    simp only [CoordRingElt.smul_a, Polynomial.coeff_smul, smul_eq_mul, mulCoordRingElt,
      verticalElt, mul_zero, zero_mul, add_zero]
    rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_mul_X_sub_C]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      Polynomial.coeff_C_succ, zero_add, Polynomial.coeff_X_one]
    exact mul_eq_zero_of_right _ (by decide)
  rw [← interpolateC_toCoordRingElt E17 stmtP witP rfl, CoordRingEltC.toCoordRingElt_a,
    CoeffPoly.toPolynomial_coeff] at hcoeff
  simp [proveC, admNormParker, hcoeff]

/-- No honest message lies in `admSetParker` for this statement. -/
theorem parker_none_no_admissible :
    ∀ msg : MAProverMsg E17.q stmtP.k, msg.isHonestFor E17 stmtP witP rfl →
      ¬ stmtP.admSet (msg.polyA, msg.polyB) :=
  (prover_complete E17 stmtP witP rfl admNormParker rfl validP
    (by decide) (mem 1 11 (by decide))
    (fun i => by fin_cases i <;> exact mem _ _ (by decide))).2 proveP_none

/-! ## Executed runs -/

/-- Every support point is a zero of the returned `D = a − b·y`. -/
private def vanishesOnSupport {k : ℕ} (out : Option (MsgC E17.q k))
    (Ps : List (ZMod E17.q × ZMod E17.q)) : Bool :=
  match out with
  | some o => Ps.all fun P => (⟨o.a, o.b⟩ : CoordRingEltC E17.q).eval P.1 P.2 == 0
  | none => false

#guard (proveC E17 stmt₁ wit₁ rfl admNormMax).isSome
#guard (proveC E17 stmt₂ wit₂ rfl admNormMax).isSome
#guard (proveC E17 stmt₃ wit₃ rfl admNormMax).isSome
#guard (proveC E17 stmt₄ wit₄ rfl admNormMax).isSome
#guard (proveC E17 stmtL witL rfl admNormLine).isNone
#guard (proveC E17 stmtP witP rfl admNormParker).isNone
#guard (proveC E17 stmt₁ wit₁ rfl admNormParker).isSome

#guard vanishesOnSupport (proveC E17 stmt₁ wit₁ rfl admNormMax) (honestSupport stmt₁ wit₁ rfl)
#guard vanishesOnSupport (proveC E17 stmt₂ wit₂ rfl admNormMax) (honestSupport stmt₂ wit₂ rfl)
#guard vanishesOnSupport (proveC E17 stmt₃ wit₃ rfl admNormMax) (honestSupport stmt₃ wit₃ rfl)
#guard vanishesOnSupport (proveC E17 stmt₄ wit₄ rfl admNormMax) (honestSupport stmt₄ wit₄ rfl)
#guard vanishesOnSupport (proveC E17 stmtL witL rfl admNormMax) (honestSupport stmtL witL rfl)
#guard vanishesOnSupport (proveC E17 stmtP witP rfl admNormMax) (honestSupport stmtP witP rfl)

-- The executed output on instance 1: `D = x² + 3x + 14 − 3y`.
#guard (proveC E17 stmt₁ wit₁ rfl admNormMax).map (fun o => (o.a.coeffs.take 3, o.b.coeff 0)) ==
  some ([14, 3, 1], 3)

/-- `MsgC.toMsg` reads coefficient lists as polynomials, index `0` first. -/
theorem toMsg_literal :
    (⟨fun _ => 5, ⟨[1, 2]⟩, ⟨[0, 3]⟩⟩ : MsgC E17.q 1).toMsg.polyA = C 1 + C 2 * X ∧
    (⟨fun _ => 5, ⟨[1, 2]⟩, ⟨[0, 3]⟩⟩ : MsgC E17.q 1).toMsg.polyB = C 3 * X ∧
    (⟨fun _ => 5, ⟨[1, 2]⟩, ⟨[0, 3]⟩⟩ : MsgC E17.q 1).toMsg.m 0 = 5 := by
  refine ⟨?_, ?_, rfl⟩ <;> ext n <;>
    simp only [MsgC.toMsg, CoeffPoly.toPolynomial_coeff, CoeffPoly.coeff] <;>
    rcases n with _ | _ | n <;> simp [Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one]

/-! ## Axiom closure -/

/--
info: 'Tests.ProverSmoke.prover_repeated_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_repeated_base

/--
info: 'Tests.ProverSmoke.prover_two_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_two_torsion

/--
info: 'Tests.ProverSmoke.prover_base_neg_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_base_neg_target

/--
info: 'Tests.ProverSmoke.prover_chord_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_chord_endpoint

/--
info: 'Tests.ProverSmoke.prove_max_isSome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prove_max_isSome

/--
info: 'Tests.ProverSmoke.line_none_no_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms line_none_no_admissible

/--
info: 'Tests.ProverSmoke.parker_none_no_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms parker_none_no_admissible

/--
info: 'Tests.ProverSmoke.prover_msg_ma_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_msg_ma_completeness

/--
info: 'Tests.ProverSmoke.prover_msg_ma_completeness_q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_msg_ma_completeness_q

/--
info: 'Tests.ProverSmoke.toMsg_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toMsg_literal

end Tests.ProverSmoke
