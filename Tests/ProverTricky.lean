/-
  Tests/ProverTricky.lean

  The executable prover `proveC` on `y² = x³ − x` over `F₂₃`: `A ≠ 0`, so
  tangent slopes use `curveA`, and full 2-torsion
  `T₁ = (0, 0)`, `T₂ = (1, 0)`, `T₃ = (22, 0)`, `E(F₂₃) ≅ ℤ/2 × ℤ/12`.
  `G = (10, 1)` has order 12; its multiples are

    `G, 2G, …, 11G = (10,1), (3,22), (19,3), (2,11), (14,4), (1,0),`
    `(14,19), (2,12), (19,20), (3,1), (10,22)`,

  so `F = 4G = (2, 11)` is a flex, `3G` has order 4, `2G` order 6.

  The line build pairs neighbours level by level, carrying an odd tail.
  Instances (support = `honestSupport`, `−P` first):

  A. all three 2-torsion points: `T₃ = T₁ + T₂ + 2·T₃`, support
     `[T₃, T₁, T₂, T₃, T₃]`; every running sum is 2-torsion or `O`;
  B. deep tangent chain: `3G = 15·G`, support `[9G, G¹⁵]`; tangents at
     `G, 2G, 4G`, a vertical combine to `O` at level two, `O + 4G` at
     level three, a vertical at the root;
  C. chord meeting `E` again at an endpoint: bases `[−2G, G]`, target `−G`,
     support `[G, 10G, G]`;
  D. duplicate bases and zero scalars, base equal to `P` with scalar `0`;
  E. bases `P` and `−P`: support `[−P, P, P, −P]`, both level-one pairs
     vertical, root combines `O` with `O`;
  F. base `−P` alone: `G = 11·(−G)`, support `[11G¹²]`;
  G. flex `F`: `−F = 2·F`, support `[F³]`; order-4 base with scalar 4;
     order-6 base with scalar 5;
  H. odd length 7 with a vertical root: `T₂ = 6·G`;
  I. normalizers: `admNormLine` `none` on `T₁ = 1·T₁` (`D ∝ x`),
     `admNormParker` `none` on `T₂ = T₂ + 2·T₃` (`D ∝ x² − 1`), and
     `admNormHash r` with `r i = i + 1` `none` on `(3,22) = 2·(18,15)`.

  Every run is checked against its support's exact divisor
  (`Tests.DivisorOracle.divisorExact`), with negative controls for
  swapped `±P` multiplicities. A, B and C also instantiate
  `ma_completeness_prover`.
-/
import Divisor.Headlines
import Tests.CurveFixtures
import Tests.DivisorOracle

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Tests.ProverTricky

open Divisor Tests.DivisorOracle

private abbrev E23 : ECSetup := Tests.CurveFixtures.E23

private abbrev F := ZMod E23.q

/-! ## Group-law helpers -/

private theorem mem (x y : F) (h : y ^ 2 = x ^ 3 + (-1) * x + 0) : (x, y) ∈ E23.points :=
  E23.hComplete x y h

/-- Group law on concrete points, from a chord slope. -/
private theorem add_chord {x₁ y₁ x₂ y₂ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E23.points) (h₂ : (x₂, y₂) ∈ E23.points) (hx : x₁ ≠ x₂)
    (hl : l * (x₁ - x₂) = y₁ - y₂) (h3x : l ^ 2 - x₁ - x₂ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E23 x₁ y₁ + ECPoint.affine E23 x₂ y₂ = ECPoint.affine E23 x₃ y₃ := by
  have n₁ := nonsing_of_mem E23 h₁
  have n₂ := nonsing_of_mem E23 h₂
  have hxy : ¬ (x₁ = x₂ ∧ y₁ = E23.toW.toAffine.negY x₂ y₂) := fun h => hx h.1
  have hs : E23.toW.toAffine.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx), hl]
  rw [ECPoint.affine_of_nonsingular E23 n₁, ECPoint.affine_of_nonsingular E23 n₂,
    WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E23.toW.toAffine.addX x₁ x₂ (E23.toW.toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]
  have hY : E23.toW.toAffine.addY x₁ x₂ y₁ (E23.toW.toAffine.slope x₁ x₂ y₁ y₂) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E23 (nonsingular_add n₁ n₂ hxy)]

/-- Group law on concrete points, doubling with a tangent slope
    `l = (3x² + A) / 2y`, `A = −1`. -/
private theorem add_tangent {x₁ y₁ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E23.points) (hy : y₁ ≠ 0)
    (hl : l * (2 * y₁) = 3 * x₁ ^ 2 - 1) (h3x : l ^ 2 - 2 * x₁ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E23 x₁ y₁ + ECPoint.affine E23 x₁ y₁ = ECPoint.affine E23 x₃ y₃ := by
  have n₁ := nonsing_of_mem E23 h₁
  have hne : y₁ ≠ E23.toW.toAffine.negY x₁ y₁ := by
    rw [toW_negY]; intro h; exact hy ((neg_snd_eq_self_iff E23 y₁).mp h.symm)
  have hxy : ¬ (x₁ = x₁ ∧ y₁ = E23.toW.toAffine.negY x₁ y₁) := fun h => hne h.2
  have h2 : y₁ - -y₁ ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero (two_ne_zero_zmod E23) hy
  have hs : E23.toW.toAffine.slope x₁ x₁ y₁ y₁ = l := by
    rw [slope_of_Y_ne rfl hne, toW_negY, div_eq_iff h2]
    simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
    rw [show E23.curveA = -1 from rfl]
    linear_combination -hl
  rw [ECPoint.affine_of_nonsingular E23 n₁, WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E23.toW.toAffine.addX x₁ x₁ (E23.toW.toAffine.slope x₁ x₁ y₁ y₁) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]; ring
  have hY : E23.toW.toAffine.addY x₁ x₁ y₁ (E23.toW.toAffine.slope x₁ x₁ y₁ y₁) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E23 (nonsingular_add n₁ n₁ hxy)]

private theorem two_torsion_add (x : F) :
    ECPoint.affine E23 x 0 + ECPoint.affine E23 x 0 = 0 := by
  nth_rw 2 [show (0 : F) = -0 by simp]
  rw [← ECPoint.affine_neg, add_neg_cancel]

/-! ## A. All three 2-torsion points: `T₃ = T₁ + T₂ + 2·T₃` -/

private def stmtA : DlogStatement E23.q where
  k := 3
  degBound := 5
  bases := ![(0, 0), (1, 0), (22, 0)]
  target := (22, 0)
  admSet := admSetMax (q := E23.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E23.q)

private def witA : DlogWitness E23.q where
  k := 3
  scalars := ![1, 1, 2]
  degBound := 5
  hRange := by intro i; fin_cases i <;> decide

private theorem validA : relDlog E23 stmtA witA := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E23 22 0 = ∑ i : Fin 3, (![1, 1, 2] i : ℤ) •
    ECPoint.affine E23 (![((0 : F), (0 : F)), (1, 0), (22, 0)] i).1
      (![((0 : F), (0 : F)), (1, 0), (22, 0)] i).2
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, one_zsmul, two_zsmul]
  rw [two_torsion_add, add_zero]
  exact (add_chord (x₁ := 0) (y₁ := 0) (x₂ := 1) (y₂ := 0) (x₃ := 22) (y₃ := 0) (l := 0)
    (mem 0 0 (by decide)) (mem 1 0 (by decide)) (by decide) (by decide) (by decide)
    (by decide)).symm

/-- Instance A: every running sum of the build is 2-torsion or `O`. -/
theorem prover_all_two_torsion :
    ∀ out, proveC E23 stmtA witA rfl admNormMax = some out →
      (maRejectSet E23 stmtA out.toMsg).card ≤ (3 * stmtA.degBound + 4) * E23.points.card :=
  (ma_completeness_prover E23 stmtA witA rfl admNormMax rfl validA (by decide)
    (mem 22 0 (by decide)) (fun i => by fin_cases i <;> exact mem _ _ (by decide))
    (by decide) (by decide)).1

/-! ## B. Deep tangent chain: `3G = 15·G`, Parker normalizer -/

private def stmtB : DlogStatement E23.q where
  k := 1
  degBound := 16
  bases := fun _ => (10, 1)
  target := (19, 3)
  admSet := admSetParker (q := E23.q)
  admSet_excludes_zero := admSetParker_excludes_zero (q := E23.q)

private def witB : DlogWitness E23.q where
  k := 1
  scalars := fun _ => 15
  degBound := 16
  hRange := by intro; decide

private theorem validB : relDlog E23 stmtB witB := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E23 19 3 = ∑ _i : Fin 1, (15 : ℤ) • ECPoint.affine E23 10 1
  rw [Fin.sum_univ_one]
  have h2 := add_tangent (x₁ := 10) (y₁ := 1) (x₃ := 3) (y₃ := 22) (l := 0)
    (mem 10 1 (by decide)) (by decide) (by decide) (by decide) (by decide)
  have h4 := add_tangent (x₁ := 3) (y₁ := 22) (x₃ := 2) (y₃ := 11) (l := 10)
    (mem 3 22 (by decide)) (by decide) (by decide) (by decide) (by decide)
  have h8 := add_tangent (x₁ := 2) (y₁ := 11) (x₃ := 2) (y₃ := 12) (l := 12)
    (mem 2 11 (by decide)) (by decide) (by decide) (by decide) (by decide)
  have h3 := add_chord (x₁ := 3) (y₁ := 22) (x₂ := 10) (y₂ := 1) (x₃ := 19) (y₃ := 3) (l := 20)
    (mem 3 22 (by decide)) (mem 10 1 (by decide)) (by decide) (by decide) (by decide)
    (by decide)
  have hneg : ECPoint.affine E23 2 12 = -ECPoint.affine E23 2 11 := by
    rw [ECPoint.affine_neg, show (-11 : F) = 12 by decide]
  set g := ECPoint.affine E23 10 1
  rw [show (15 : ℤ) • g = (((g + g) + (g + g)) + ((g + g) + (g + g))) +
      ((g + g) + (g + g)) + ((g + g) + g) by abel, h2, h4, h8, h3, hneg, neg_add_cancel,
    zero_add]

/-- Instance B: sixteen support points, tangents at `G`, `2G`, `4G`. -/
theorem prover_deep_tangent :
    ∀ out, proveC E23 stmtB witB rfl admNormParker = some out →
      (maRejectSet E23 stmtB out.toMsg).card ≤ (3 * stmtB.degBound + 4) * E23.points.card :=
  (ma_completeness_prover E23 stmtB witB rfl admNormParker rfl validB (by decide)
    (mem 19 20 (by decide)) (fun _ => mem 10 1 (by decide)) (by decide) (by decide)).1

/-! ## C. Chord meeting `E` again at an endpoint, Line normalizer -/

/-- Bases `[−2G, G] = [(3,1), (10,1)]`, target `−G = (10, 22)`. -/
private def stmtC : DlogStatement E23.q where
  k := 2
  degBound := 3
  bases := ![(3, 1), (10, 1)]
  target := (10, 22)
  admSet := admSetLine (q := E23.q)
  admSet_excludes_zero := admSetLine_excludes_zero (q := E23.q)

private def witC : DlogWitness E23.q where
  k := 2
  scalars := fun _ => 1
  degBound := 3
  hRange := by intro; decide

private theorem validC : relDlog E23 stmtC witC := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E23 10 22 = ∑ i : Fin 2, (1 : ℤ) •
    ECPoint.affine E23 (![((3 : F), (1 : F)), (10, 1)] i).1 (![((3 : F), (1 : F)), (10, 1)] i).2
  simp only [Fin.sum_univ_two, one_zsmul, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (add_chord (x₁ := 3) (y₁ := 1) (x₂ := 10) (y₂ := 1) (x₃ := 10) (y₃ := 22) (l := 0)
    (mem 3 1 (by decide)) (mem 10 1 (by decide)) (by decide) (by decide) (by decide)
    (by decide)).symm

/-- Instance C: the first chord is tangent at `G`. -/
theorem prover_chord_endpoint :
    ∀ out, proveC E23 stmtC witC rfl admNormLine = some out →
      (maRejectSet E23 stmtC out.toMsg).card ≤ (3 * stmtC.degBound + 4) * E23.points.card :=
  (ma_completeness_prover E23 stmtC witC rfl admNormLine rfl validC (by decide)
    (mem 10 1 (by decide)) (fun i => by fin_cases i <;> exact mem _ _ (by decide))
    (by decide) (by decide)).1

/-! ## List-built instances -/

/-- A statement from lists (`admSetMax`; `proveC` takes its normalizer
    separately). -/
private def st (bs : List (F × F)) (P : F × F) : DlogStatement E23.q where
  k := bs.length
  degBound := 20
  bases i := bs[i]
  target := P
  admSet := admSetMax (q := E23.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E23.q)

private def wt (ns : List ℕ) : DlogWitness E23.q where
  k := ns.length
  scalars i := ns[i]
  degBound := ns.sum + 1
  hRange i := by
    simpa using Nat.lt_succ_of_le (List.le_sum_of_mem (List.getElem_mem i.isLt))

/-- Run `proveC` on list data and check the full divisor. -/
private def run (bs : List (F × F)) (ns : List ℕ) (P : F × F) (N : AdmNormalizer E23.q)
    (h : bs.length = ns.length) : Bool :=
  msgExact E23 (proveC E23 (st bs P) (wt ns) h N) (honestSupport (st bs P) (wt ns) h)

#guard (curvePts E23).length = 23

/-! ## Executed runs -/

-- A, B, C: supports and full divisors.
#guard honestSupport stmtA witA rfl = [(22, 0), (0, 0), (1, 0), (22, 0), (22, 0)]
#guard msgExact E23 (proveC E23 stmtA witA rfl admNormMax) (honestSupport stmtA witA rfl)
#guard honestSupport stmtB witB rfl = (19, 20) :: List.replicate 15 (10, 1)
#guard msgExact E23 (proveC E23 stmtB witB rfl admNormParker) (honestSupport stmtB witB rfl)
#guard (proveC E23 stmtB witB rfl (admNormHash fun i => ((i + 1 : ℕ) : F))).isSome
#guard honestSupport stmtC witC rfl = [(10, 1), (3, 1), (10, 1)]
#guard msgExact E23 (proveC E23 stmtC witC rfl admNormLine) (honestSupport stmtC witC rfl)
-- The tangent at `G` has slope `0`, so `D ∝ y − 1` and Parker has no scale.
#guard (proveC E23 stmtC witC rfl admNormParker).isNone

-- A': 2-torsion with `T₁` repeated: `T₁ = 2·T₁ + T₂ + T₃`.
#guard run [(0, 0), (1, 0), (22, 0)] [2, 1, 1] (0, 0) admNormMax rfl

-- D. Duplicate bases, zero scalars, `P` as a base with scalar `0`:
--    `5G = 2·G + 0·5G + 3·G + 0·2G`, support `[7G, G⁵]`.
#guard run [(10, 1), (14, 4), (10, 1), (3, 22)] [2, 0, 3, 0] (14, 4) admNormMax rfl
#guard honestSupport (st [(10, 1), (14, 4), (10, 1), (3, 22)] (14, 4)) (wt [2, 0, 3, 0]) rfl =
  (14, 19) :: List.replicate 5 (10, 1)

-- E. Bases `P, −P, P` with scalars `2, 1, 0`, `P = 3G`: support `[−P, P, P, −P]`.
#guard run [(19, 3), (19, 20), (19, 3)] [2, 1, 0] (19, 3) admNormMax rfl
#guard run [(19, 3), (19, 20), (19, 3)] [2, 1, 0] (19, 3) admNormLine rfl

-- F. Base `−P` alone: `G = 11·(−G)`, twelve copies of `11G`.
#guard run [(10, 22)] [11] (10, 1) admNormMax rfl

-- G. Flex `F = (2, 11)`: `−F = 2·F`, support `[F³]`.
#guard run [(2, 11)] [2] (2, 12) admNormMax rfl
--    Order 4, scalar 4: `G = 4·3G + G`.
#guard run [(19, 3), (10, 1)] [4, 1] (10, 1) admNormMax rfl
--    Order 6, scalar 5: `−2G = 5·2G`, six copies of `2G` (slope-0 tangent).
#guard run [(3, 22)] [5] (3, 1) admNormMax rfl

-- H. Odd length 7, vertical root: `T₂ = 6·G`.
#guard run [(10, 1)] [6] (1, 0) admNormMax rfl
#guard run [(10, 1)] [6] (1, 0) admNormParker rfl

/-! ## I. Normalizers -/

-- Line `none`: `T₁ = 1·T₁`, `D ∝ x`.
#guard (proveC E23 (st [(0, 0)] (0, 0)) (wt [1]) rfl admNormLine).isNone
#guard (proveC E23 (st [(0, 0)] (0, 0)) (wt [1]) rfl admNormParker).isSome
#guard run [(0, 0)] [1] (0, 0) admNormMax rfl

-- Parker `none`: `T₂ = T₂ + 2·T₃`, `D ∝ x² − 1`.
#guard (proveC E23 (st [(1, 0), (22, 0)] (1, 0)) (wt [1, 2]) rfl admNormParker).isNone
#guard (proveC E23 (st [(1, 0), (22, 0)] (1, 0)) (wt [1, 2]) rfl admNormLine).isSome
#guard run [(1, 0), (22, 0)] [1, 2] (1, 0) admNormMax rfl

-- Hash `none` with `r i = i + 1`: `(3, 22) = 2·(18, 15)`, support
-- `[(3,1), (18,15), (18,15)]`.
#guard (proveC E23 (st [(18, 15)] (3, 22)) (wt [2]) rfl
  (admNormHash fun i => ((i + 1 : ℕ) : F))).isNone
#guard run [(18, 15)] [2] (3, 22) admNormMax rfl
#guard run [(18, 15)] [2] (3, 22) admNormParker rfl

-- Negative controls: instance A's output fails against B's support, and C's
-- against its support with one point moved to its negative.
#guard !msgExact E23 (proveC E23 stmtA witA rfl admNormMax) (honestSupport stmtB witB rfl)
#guard !msgExact E23 (proveC E23 stmtC witC rfl admNormMax) [(10, 1), (3, 1), (10, 22)]

-- Opposite multiplicities across `±F`, `F = (2, 11)` the flex: `F = 4·F`, support
-- `[−F, F⁴]`. The output fails against `[F, (−F)⁴]`, which has the same zeros
-- and the same norm.
#guard honestSupport (st [(2, 11)] (2, 11)) (wt [4]) rfl =
  [(2, 12), (2, 11), (2, 11), (2, 11), (2, 11)]
#guard run [(2, 11)] [4] (2, 11) admNormMax rfl
#guard !msgExact E23 (proveC E23 (st [(2, 11)] (2, 11)) (wt [4]) rfl admNormMax)
  [(2, 11), (2, 12), (2, 12), (2, 12), (2, 12)]

/-! ## Axiom closure -/

/--
info: 'Tests.ProverTricky.prover_all_two_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_all_two_torsion

/--
info: 'Tests.ProverTricky.prover_deep_tangent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_deep_tangent

/--
info: 'Tests.ProverTricky.prover_chord_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_chord_endpoint

end Tests.ProverTricky
