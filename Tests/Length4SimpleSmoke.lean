/-
  Tests/Length4SimpleSmoke.lean

  Inhabited length-four simple MA completeness.

  `MAProverMsg.IsHonestForLength4Simple` bundles the explicit
  `lineBuild_length4_explicit` construction together with a list of
  genericity side conditions. This file shows that the record is
  satisfiable: every field is constructed rather than assumed, on a
  concrete curve, and the record then feeds
  `ma_completeness_binary_M_eq_3` and `ma_completeness_for_length4Simple`.

  Instance on `y² = x³ + 1` over `F₄₃`:

      target P = (0, 42),  bases B = [(5, 13), (0, 42), (5, 30)],
      scalars  = [1, 1, 1],  so  P = B₀ + B₁ + B₂  (B₂ = −B₀, B₁ = P).

  Inputs `[−P, B₀, B₁, B₂] = [(0, 1), (5, 13), (0, 42), (5, 30)]`. The two
  chords `L₁ = ℓ((0,1),(5,13))` and `L₂ = ℓ((0,42),(5,30))` have slopes
  `11` and `32` and meet `E` again at `(30, 30)` and `(30, 13) = −(30, 30)`.
  The build `(L₁·L₂)/(x − 30)` is `x·(x − 5)`, of pole order `4`.
-/
import Divisor.Completeness
import Divisor.IsHonestForBinary
import Divisor.CoordRingEltC.Bridge
import Tests.CurveFixtures

open Polynomial

namespace Tests.Length4SimpleSmoke

open Divisor

private abbrev E43 : ECSetup := Tests.CurveFixtures.E43

private abbrev F := ZMod E43.q

private def P₀ : F × F := (0, 1)
private def P₁ : F × F := (5, 13)
private def P₂ : F × F := (0, 42)
private def P₃ : F × F := (5, 30)

private def stmt : DlogStatement E43.q where
  k := 3
  degBound := 4
  bases := ![P₁, P₂, P₃]
  target := (0, 42)
  admSet := admSetMax (q := E43.q)
  admSet_excludes_zero := admSetMax_excludes_zero (q := E43.q)

private def wit : DlogWitness E43.q where
  k := 3
  scalars := fun _ => 1
  degBound := 4
  hRange := by intro i; norm_num

private theorem hk : stmt.k = wit.k := rfl

private noncomputable def msg : MAProverMsg E43.q stmt.k where
  m := fun _ => 1
  polyA := (lineBuild_length4_explicit E43 P₀ P₁ P₂ P₃).a
  polyB := (lineBuild_length4_explicit E43 P₀ P₁ P₂ P₃).b

/-! ## Arithmetic in `F₄₃`

The kernel does not reduce `ZMod` inverses, so the two chord slopes are
pinned once through explicit inverses; everything else is `decide` on
literals. -/

private theorem inv5 : ((5 : F) - 0)⁻¹ = 26 :=
  inv_eq_of_mul_eq_one_right (by decide)

private theorem slope₀₁ : slopeOf P₀.1 P₀.2 P₁.1 P₁.2 = 11 := by
  unfold slopeOf; rw [show P₁.1 - P₀.1 = (5 : F) - 0 from rfl, inv5]; decide

private theorem slope₂₃ : slopeOf P₂.1 P₂.2 P₃.1 P₃.2 = 32 := by
  unfold slopeOf; rw [show P₃.1 - P₂.1 = (5 : F) - 0 from rfl, inv5]; decide

private theorem mem (x y : F) (h : y ^ 2 = x ^ 3 + 0 * x + 1) :
    (x, y) ∈ E43.points :=
  E43.hComplete x y h

/-! ## The honesty record -/

private def honest : MAProverMsg.IsHonestForLength4Simple E43 stmt msg where
  hk_eq_3 := rfl
  P₀ := P₀
  P₁ := P₁
  P₂ := P₂
  P₃ := P₃
  h_P₀_eq := by decide
  h_P₁_eq := rfl
  h_P₂_eq := rfl
  h_P₃_eq := rfl
  h_toD_eq := rfl
  h_m_eq_one := fun _ => rfl
  hP₀ := mem 0 1 (by decide)
  hP₁ := mem 5 13 (by decide)
  hP₂ := mem 0 42 (by decide)
  hP₃ := mem 5 30 (by decide)
  h_xx_01 := by decide
  h_xx_23 := by decide
  h_P₀_ne_A2_01 := by rw [slope₀₁]; decide
  h_P₁_ne_A2_01 := by rw [slope₀₁]; decide
  h_P₂_ne_A2_23 := by rw [slope₂₃]; decide
  h_P₃_ne_A2_23 := by rw [slope₂₃]; decide
  h_P₀_off_L₂ := by rw [slope₂₃]; decide
  h_P₁_off_L₂ := by rw [slope₂₃]; decide
  h_P₂_off_L₁ := by rw [slope₀₁]; decide
  h_P₃_off_L₁ := by rw [slope₀₁]; decide
  h_third_match := by rw [slope₀₁, slope₂₃]; decide
  h_y_match := by rw [slope₀₁, slope₂₃]; decide
  h_Q₀_nontorsion := by rw [slope₀₁]; decide
  h_Q₀_off_L₂_inputs := by simp only [slope₀₁]; decide
  h_negQ₀_off_L₁_inputs := by simp only [slope₀₁]; decide
  h_inputs_distinct := by decide

/-! ## Protocol premises -/

private theorem h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1 := fun _ => rfl

private theorem h_valid : relDlog E43 stmt wit := by
  refine ⟨hk, ?_⟩
  simp only [ECPoint.weightedSum]
  rw [show (Finset.univ : Finset (Fin wit.k))
      = {(⟨0, by decide⟩ : Fin wit.k), ⟨1, by decide⟩, ⟨2, by decide⟩} from
        by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [stmt, wit, ECPoint.zsmul, Fin.cast, P₁, P₂, P₃]
  rw [show (30 : ZMod E43.q) = -(13 : ZMod E43.q) by decide, ← ECPoint.affine_neg E43 (5 : ZMod E43.q) (13 : ZMod E43.q)]
  abel

/-- Computable mirror of the two chords, with the slopes resolved. -/
private def L₁c : CoordRingEltC E43.q :=
  { a := -(CoeffPoly.C 11) * CoeffPoly.X - CoeffPoly.C 1, b := -1 }

private def L₂c : CoordRingEltC E43.q :=
  { a := -(CoeffPoly.C 32) * CoeffPoly.X - CoeffPoly.C 42, b := -1 }

private theorem chord₀₁ : CoordRingEltC.chord E43.curveA P₀ P₁ = L₁c := by
  unfold CoordRingEltC.chord
  rw [if_neg (by decide), show P₁.1 - P₀.1 = (5 : F) - 0 from rfl, inv5]
  decide

private theorem chord₂₃ : CoordRingEltC.chord E43.curveA P₂ P₃ = L₂c := by
  unfold CoordRingEltC.chord
  rw [if_neg (by decide), show P₃.1 - P₂.1 = (5 : F) - 0 from rfl, inv5]
  decide

/-- The build is `x² + 38·x = x·(x − 5)`, with no `y` term. -/
private def Dc : CoordRingEltC E43.q := ⟨⟨[0, 38, 1, 0, 0]⟩, ⟨[0, 0, 0]⟩⟩

private theorem toD_eq_Dc : msg.toD = Dc.toCoordRingElt := by
  have hQ : slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1 = 30 := by
    rw [slope₀₁]; decide
  show lineBuild_length4_explicit E43 P₀ P₁ P₂ P₃ = _
  unfold lineBuild_length4_explicit
  simp only [hQ]
  rw [← CoordRingEltC.chord_toCoordRingElt, ← CoordRingEltC.chord_toCoordRingElt,
    ← CoordRingEltC.mul_toCoordRingElt, ← CoordRingEltC.divLin_toCoordRingElt,
    chord₀₁, chord₂₃]
  congr 1

private theorem Dc_a_natDegree : Dc.a.toPolynomial.natDegree ≤ 2 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
  rw [CoeffPoly.toPolynomial_coeff]
  match n, hn with
  | 3, _ => decide
  | 4, _ => decide
  | n + 5, _ => simp [Dc, CoeffPoly.coeff]

private theorem Dc_b_zero : Dc.b.toPolynomial = 0 := by
  ext n
  rw [CoeffPoly.toPolynomial_coeff, Polynomial.coeff_zero]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 => simp [Dc, CoeffPoly.coeff]

private theorem h_degE : msg.toD.degE ≤ 4 := by
  rw [toD_eq_Dc, CoordRingElt.degE_of_b_eq_zero (by exact Dc_b_zero)]
  have := Dc_a_natDegree
  simp only [CoordRingEltC.toCoordRingElt_a]
  omega

private theorem h_deg : msg.toD.degE ≤ wit.degBound := h_degE

private theorem h_deg_k : msg.toD.degE ≤ stmt.degBound := h_degE

/-- Admissibility: the build is nonzero, witnessed by `D(1, 0) = 39`. -/
private theorem h_adm : stmt.admSet (msg.polyA, msg.polyB) := by
  show (msg.polyA, msg.polyB) ≠ (0, 0)
  intro heq
  rw [Prod.mk.injEq] at heq
  have hev : msg.toD.eval 1 0 = 0 := by
    show msg.polyA.eval 1 - msg.polyB.eval 1 * 0 = 0
    rw [heq.1, heq.2]; simp
  rw [toD_eq_Dc] at hev
  change Polynomial.eval _ Dc.a.toPolynomial - Polynomial.eval _ Dc.b.toPolynomial * _ = 0
    at hev
  rw [CoeffPoly.toPolynomial_eval, CoeffPoly.toPolynomial_eval] at hev
  revert hev
  decide

/-! ## Completeness, instantiated -/

/-- `ma_completeness_binary_M_eq_3`, instantiated. -/
theorem length4_completeness :
    (maRejectSet E43 stmt msg).card
      ≤ (3 * numZeros E43 msg.toD + 4) * E43.numAffine :=
  ma_completeness_binary_M_eq_3 E43 stmt msg wit hk honest h_scalars h_valid
    h_deg h_deg_k h_adm

/-- `ma_completeness_for_length4Simple`, instantiated. -/
theorem length4_completeness_direct :
    (maRejectSet E43 stmt msg).card
      ≤ (3 * numZeros E43 msg.toD + 4) * E43.numAffine :=
  ma_completeness_for_length4Simple E43 stmt msg honest wit hk h_scalars h_valid
    h_deg h_deg_k h_adm

/-! ## Axiom closure -/

/--
info: 'Tests.Length4SimpleSmoke.length4_completeness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length4_completeness

/--
info: 'Tests.Length4SimpleSmoke.length4_completeness_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms length4_completeness_direct

end Tests.Length4SimpleSmoke
