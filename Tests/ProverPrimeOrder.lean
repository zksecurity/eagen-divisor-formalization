/-
  Tests/ProverPrimeOrder.lean

  The executable prover `proveC` on `y² = x³ + x + 4` over `F₂₃`, a curve
  of prime order `29`: no 2- or 3-torsion, every affine point generates.
  `G = (0, 2)`; the multiples used are

    `2G = (13,12)`, `4G = (1,12)`, `5G = (7,20)`, `7G = (15,6)`,
    `8G = (14,5)`, `16G = (8,8)`, `24G = (7,3)`, `28G = −G = (0,21)`.

  Since `29` is prime, a running sum of the line build is `O` only when a
  subtree's points sum to zero, so a mid-build `O` needs `±Q` adjacent or
  a zero-sum group of points. Instances (support = `honestSupport`, `−P`
  first):

  A. long multiplicity chain: `−G = 28·G`, support `[G²⁹]` (odd length);
     tangents at `G, 2G, 4G, 8G`, the root sum is `29G = O`;
  B. mixed bases `[G, P, −P, 5G]` with scalars `[4, 2, 1, 5]`, `P = 7G`;
     support length 13;
  C. mid-build `O`: bases `[P, G, 2G, −3G]`, support `[−P, P, G, 2G, −3G]`,
     so the first pair is vertical and `O` is merged with `3G`; and
     bases `[P, Q, −Q]`, support `[−P, P, Q, −Q]`, root combines `O` with `O`;
  D. normalizers: `admNormLine` `none` on `G = 1·G` (`D ∝ x`),
     `admNormParker` `none` on `(1,12) = (1,12) + (22,5) + (22,18)`
     (`D ∝ (x − 1)(x + 1)`), `admNormHash r` with `r i = i + 1` `none` on
     `(4,16) = 2·(22,5)`.

  Every run is checked with `Tests.DivisorOracle.divisorExact`: `D ≠ 0`,
  and at every affine point `Q` of `E` the order of `D` (from a local
  power-series expansion) equals the multiplicity of `Q` in the support,
  so `div D = Σ (Pᵢ) − n·(O)` exactly. Negative controls check that the
  oracle rejects supports with the multiplicities of `Q` and `−Q` swapped.
  A also instantiates `ma_completeness_prover` with every premise
  constructed.
-/
import Divisor.Headlines
import Tests.CurveFixtures
import Tests.DivisorOracle

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Tests.ProverPrimeOrder

open Divisor Tests.DivisorOracle

private abbrev E : ECSetup := Tests.CurveFixtures.E23P

private abbrev F := ZMod E.q

/-! ## Group-law helpers -/

private theorem mem (x y : F) (h : y ^ 2 = x ^ 3 + 1 * x + 4) : (x, y) ∈ E.points :=
  E.hComplete x y h

/-- Group law on concrete points, from a chord slope. -/
private theorem add_chord {x₁ y₁ x₂ y₂ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E.points) (h₂ : (x₂, y₂) ∈ E.points) (hx : x₁ ≠ x₂)
    (hl : l * (x₁ - x₂) = y₁ - y₂) (h3x : l ^ 2 - x₁ - x₂ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E x₁ y₁ + ECPoint.affine E x₂ y₂ = ECPoint.affine E x₃ y₃ := by
  have n₁ := nonsing_of_mem E h₁
  have n₂ := nonsing_of_mem E h₂
  have hxy : ¬ (x₁ = x₂ ∧ y₁ = E.toW.toAffine.negY x₂ y₂) := fun h => hx h.1
  have hs : E.toW.toAffine.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx), hl]
  rw [ECPoint.affine_of_nonsingular E n₁, ECPoint.affine_of_nonsingular E n₂,
    WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E.toW.toAffine.addX x₁ x₂ (E.toW.toAffine.slope x₁ x₂ y₁ y₂) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]
  have hY : E.toW.toAffine.addY x₁ x₂ y₁ (E.toW.toAffine.slope x₁ x₂ y₁ y₂) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E (nonsingular_add n₁ n₂ hxy)]

/-- Group law on concrete points, doubling with a tangent slope
    `l = (3x² + A) / 2y`, `A = 1`. -/
private theorem add_tangent {x₁ y₁ x₃ y₃ l : F}
    (h₁ : (x₁, y₁) ∈ E.points) (hy : y₁ ≠ 0)
    (hl : l * (2 * y₁) = 3 * x₁ ^ 2 + 1) (h3x : l ^ 2 - 2 * x₁ = x₃)
    (h3y : -(l * (x₃ - x₁) + y₁) = y₃) :
    ECPoint.affine E x₁ y₁ + ECPoint.affine E x₁ y₁ = ECPoint.affine E x₃ y₃ := by
  have n₁ := nonsing_of_mem E h₁
  have hne : y₁ ≠ E.toW.toAffine.negY x₁ y₁ := by
    rw [toW_negY]; intro h; exact hy ((neg_snd_eq_self_iff E y₁).mp h.symm)
  have hxy : ¬ (x₁ = x₁ ∧ y₁ = E.toW.toAffine.negY x₁ y₁) := fun h => hne h.2
  have h2 : y₁ - -y₁ ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero (two_ne_zero_zmod E) hy
  have hs : E.toW.toAffine.slope x₁ x₁ y₁ y₁ = l := by
    rw [slope_of_Y_ne rfl hne, toW_negY, div_eq_iff h2]
    simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
    rw [show E.curveA = 1 from rfl]
    linear_combination -hl
  rw [ECPoint.affine_of_nonsingular E n₁, WeierstrassCurve.Affine.Point.add_some hxy]
  have hX : E.toW.toAffine.addX x₁ x₁ (E.toW.toAffine.slope x₁ x₁ y₁ y₁) = x₃ := by
    rw [hs, ← h3x]; simp [Affine.addX]; ring
  have hY : E.toW.toAffine.addY x₁ x₁ y₁ (E.toW.toAffine.slope x₁ x₁ y₁ y₁) = y₃ := by
    rw [Affine.addY, toW_negY, Affine.negAddY, hX, hs, ← h3y]
  subst hX hY
  rw [ECPoint.affine_of_nonsingular E (nonsingular_add n₁ n₁ hxy)]

/-! ## A. Long multiplicity chain: `−G = 28·G`, Hash normalizer -/

/-- Hash challenge `r i = i + 1`. -/
private def r : ℕ → F := fun i => ((i + 1 : ℕ) : F)

private def stmtA : DlogStatement E.q where
  k := 1
  degBound := 29
  bases := fun _ => (0, 2)
  target := (0, 21)
  admSet := admSetHash r
  admSet_excludes_zero := admSetHash_excludes_zero r

private def witA : DlogWitness E.q where
  k := 1
  scalars := fun _ => 28
  degBound := 29
  hRange := by intro; decide

private theorem validA : relDlog E stmtA witA := by
  refine ⟨rfl, ?_⟩
  show ECPoint.affine E 0 21 = ∑ _i : Fin 1, (28 : ℤ) • ECPoint.affine E 0 2
  rw [Fin.sum_univ_one]
  set g := ECPoint.affine E 0 2
  have h2 : (2 : ℤ) • g = ECPoint.affine E 13 12 := by
    rw [two_zsmul]
    exact add_tangent (mem 0 2 (by decide)) (by decide) (l := 6) (by decide) (by decide)
      (by decide)
  have h4 : (4 : ℤ) • g = ECPoint.affine E 1 12 := by
    rw [show (4 : ℤ) • g = (2 : ℤ) • g + (2 : ℤ) • g by abel, h2]
    exact add_tangent (mem 13 12 (by decide)) (by decide) (l := 2) (by decide) (by decide)
      (by decide)
  have h8 : (8 : ℤ) • g = ECPoint.affine E 14 5 := by
    rw [show (8 : ℤ) • g = (4 : ℤ) • g + (4 : ℤ) • g by abel, h4]
    exact add_tangent (mem 1 12 (by decide)) (by decide) (l := 4) (by decide) (by decide)
      (by decide)
  have h16 : (16 : ℤ) • g = ECPoint.affine E 8 8 := by
    rw [show (16 : ℤ) • g = (8 : ℤ) • g + (8 : ℤ) • g by abel, h8]
    exact add_tangent (mem 14 5 (by decide)) (by decide) (l := 6) (by decide) (by decide)
      (by decide)
  have h24 : (24 : ℤ) • g = ECPoint.affine E 7 3 := by
    rw [show (24 : ℤ) • g = (16 : ℤ) • g + (8 : ℤ) • g by abel, h16, h8]
    exact add_chord (mem 8 8 (by decide)) (mem 14 5 (by decide)) (l := 11) (by decide)
      (by decide) (by decide) (by decide)
  rw [show (28 : ℤ) • g = (24 : ℤ) • g + (4 : ℤ) • g by abel, h24, h4]
  exact (add_chord (mem 7 3 (by decide)) (mem 1 12 (by decide)) (l := 10) (by decide)
    (by decide) (by decide) (by decide)).symm

/-- Instance A: 29 copies of `G`, tangents at `G, 2G, 4G, 8G`. -/
theorem prover_prime_order_chain :
    ∀ out, proveC E stmtA witA rfl (admNormHash r) = some out →
      (maRejectSet E stmtA out.toMsg).card ≤ (3 * stmtA.degBound + 4) * E.points.card :=
  (ma_completeness_prover E stmtA witA rfl (admNormHash r) rfl validA (by decide)
    (mem 0 2 (by decide)) (fun _ => mem 0 2 (by decide)) (by decide) (by decide)).1

/-! ## List-built instances -/

/-- A statement from lists (`admSetMax`; `proveC` takes its normalizer
    separately). -/
private def st (bs : List (F × F)) (P : F × F) : DlogStatement E.q where
  k := bs.length
  degBound := 30
  bases i := bs[i]
  target := P
  admSet := admSetMax (q := E.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E.q)

private def wt (ns : List ℕ) : DlogWitness E.q where
  k := ns.length
  scalars i := ns[i]
  degBound := ns.sum + 1
  hRange i := by
    simpa using Nat.lt_succ_of_le (List.le_sum_of_mem (List.getElem_mem i.isLt))

private def prove (bs : List (F × F)) (ns : List ℕ) (P : F × F) (N : AdmNormalizer E.q)
    (h : bs.length = ns.length) : Option (MsgC E.q bs.length) :=
  proveC E (st bs P) (wt ns) h N

/-- Run `proveC` on list data and check the full divisor. -/
private def run (bs : List (F × F)) (ns : List ℕ) (P : F × F) (N : AdmNormalizer E.q)
    (h : bs.length = ns.length) : Bool :=
  msgExact E (prove bs ns P N h) (honestSupport (st bs P) (wt ns) h)

#guard (curvePts E).length = 28

/-! ## Executed runs -/

-- A. `−G = 28·G`: 29 copies of `G`.
#guard honestSupport stmtA witA rfl = List.replicate 29 (0, 2)
#guard msgExact E (proveC E stmtA witA rfl (admNormHash r)) (honestSupport stmtA witA rfl)
#guard (proveC E stmtA witA rfl admNormMax).isSome
#guard (proveC E stmtA witA rfl admNormParker).isSome
#guard (proveC E stmtA witA rfl admNormLine).isSome

-- B. Mixed bases `[G, P, −P, 5G]`, scalars `[4, 2, 1, 5]`, `P = 7G`:
--    `4 + 14 − 7 + 25 = 36 ≡ 7 (mod 29)`.
#guard (honestSupport (st [(0, 2), (15, 6), (15, 17), (7, 20)] (15, 6)) (wt [4, 2, 1, 5])
  rfl).length = 13
#guard run [(0, 2), (15, 6), (15, 17), (7, 20)] [4, 2, 1, 5] (15, 6) admNormMax rfl
#guard run [(0, 2), (15, 6), (15, 17), (7, 20)] [4, 2, 1, 5] (15, 6) admNormParker rfl
#guard run [(0, 2), (15, 6), (15, 17), (7, 20)] [4, 2, 1, 5] (15, 6) admNormLine rfl
#guard run [(0, 2), (15, 6), (15, 17), (7, 20)] [4, 2, 1, 5] (15, 6) (admNormHash r) rfl

-- C. Mid-build `O`: `P = P + G + 2G + (−3G)`, support `[−P, P, G, 2G, −3G]`.
#guard run [(15, 6), (0, 2), (13, 12), (11, 14)] [1, 1, 1, 1] (15, 6) admNormMax rfl
--    `P = P + Q + (−Q)` with `Q = 16G`: support `[−P, P, Q, −Q]`.
#guard run [(15, 6), (8, 8), (8, 15)] [1, 1, 1] (15, 6) admNormMax rfl

/-! ## D. Normalizers -/

-- Line `none`: `G = 1·G`, support `[−G, G]`, `D ∝ x`.
#guard (prove [(0, 2)] [1] (0, 2) admNormLine rfl).isNone
#guard (prove [(0, 2)] [1] (0, 2) admNormParker rfl).isSome
#guard run [(0, 2)] [1] (0, 2) admNormMax rfl

-- Parker `none`: support `[(1,11), (1,12), (22,5), (22,18)]`,
-- `D ∝ (x − 1)(x − 22) = x² − 1`.
#guard (prove [(1, 12), (22, 5), (22, 18)] [1, 1, 1] (1, 12) admNormParker rfl).isNone
#guard (prove [(1, 12), (22, 5), (22, 18)] [1, 1, 1] (1, 12) admNormLine rfl).isSome
#guard run [(1, 12), (22, 5), (22, 18)] [1, 1, 1] (1, 12) admNormMax rfl

-- Hash `none`: `(4, 16) = 2·(22, 5)`, support `[(4,7), (22,5), (22,5)]`.
#guard (prove [(22, 5)] [2] (4, 16) (admNormHash r) rfl).isNone
#guard (prove [(22, 5)] [2] (4, 16) admNormParker rfl).isSome
#guard (prove [(22, 5)] [2] (4, 16) admNormLine rfl).isSome
#guard run [(22, 5)] [2] (4, 16) admNormMax rfl

-- Negative control: A's output fails against a support with one
-- copy of `G` replaced by `−G`.
#guard !msgExact E (proveC E stmtA witA rfl admNormMax) ((0, 21) :: List.replicate 28 (0, 2))

-- Opposite multiplicities across `±G`: `G = 30·G`, support `[−G, G³⁰]`; the
-- output fails against `[G, (−G)³⁰]` (same zeros, same norm).
#guard honestSupport (st [(0, 2)] (0, 2)) (wt [30]) rfl = (0, 21) :: List.replicate 30 (0, 2)
#guard run [(0, 2)] [30] (0, 2) admNormMax rfl
#guard !msgExact E (prove [(0, 2)] [30] (0, 2) admNormMax rfl)
  ((0, 2) :: List.replicate 30 (0, 21))

-- `2G = 3·G + 1·(−G)`: support `[−2G, G³, −G]`; the output fails against
-- `[−2G, G, (−G)³]`.
#guard honestSupport (st [(0, 2), (0, 21)] (13, 12)) (wt [3, 1]) rfl =
  [(13, 11), (0, 2), (0, 2), (0, 2), (0, 21)]
#guard run [(0, 2), (0, 21)] [3, 1] (13, 12) admNormMax rfl
#guard !msgExact E (prove [(0, 2), (0, 21)] [3, 1] (13, 12) admNormMax rfl)
  [(13, 11), (0, 2), (0, 21), (0, 21), (0, 21)]

/-! ## Axiom closure -/

/--
info: 'Tests.ProverPrimeOrder.prover_prime_order_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prover_prime_order_chain

end Tests.ProverPrimeOrder
