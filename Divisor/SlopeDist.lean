/-
  Divisor/SlopeDist.lean

  Bezout's theorem for lines/cubics, and Lemma 1 (Slope Distribution).
-/
import Divisor.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.LinearCombination

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-- Points on the line y = lam * x + c -/
def pointsOnLine (lam c : ZMod E.q) : Finset (ZMod E.q × ZMod E.q) :=
  E.points.filter (fun p => p.2 = lam * p.1 + c)

/-- The intersection polynomial -/
noncomputable def intersectionPoly (lam c : ZMod E.q) : (ZMod E.q)[X] :=
  X ^ 3 - C (lam ^ 2) * X ^ 2 + C (E.curveA - 2 * lam * c) * X + C (E.curveB - c ^ 2)

/-- Each x-coord of a point on E ∩ line is a root of the intersection polynomial -/
theorem isRoot_of_mem_pointsOnLine {lam c : ZMod E.q}
    {p : ZMod E.q × ZMod E.q} (hp : p ∈ pointsOnLine E lam c) :
    (intersectionPoly E lam c).IsRoot p.1 := by
  simp only [pointsOnLine, Finset.mem_filter] at hp
  have hcurve := E.hOnCurve p hp.1  -- p.2^2 = p.1^3 + A*p.1 + B
  rw [hp.2] at hcurve               -- (lam*p.1+c)^2 = p.1^3 + A*p.1 + B
  simp only [IsRoot, intersectionPoly, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  have h : p.1 ^ 3 + E.curveA * p.1 + E.curveB = (lam * p.1 + c) ^ 2 := hcurve.symm
  linear_combination h

/-- The intersection polynomial has natDegree ≤ 3 -/
theorem natDegree_intersectionPoly_le (lam c : ZMod E.q) :
    (intersectionPoly E lam c).natDegree ≤ 3 := by
  unfold intersectionPoly
  have h1 : natDegree ((X : (ZMod E.q)[X]) ^ 3) ≤ 3 := by simp [natDegree_X_pow]
  have h2 : natDegree (C (lam ^ 2) * (X : (ZMod E.q)[X]) ^ 2) ≤ 3 :=
    (natDegree_C_mul_X_pow_le _ 2).trans (by omega)
  have h3 : natDegree (C (E.curveA - 2 * lam * c) * (X : (ZMod E.q)[X])) ≤ 3 := by
    rw [show (X : (ZMod E.q)[X]) = X ^ 1 from (pow_one _).symm]
    exact (natDegree_C_mul_X_pow_le _ 1).trans (by omega)
  -- For any polynomial expression, we use natDegree_add_le / natDegree_sub_le
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ h3)
    exact (natDegree_sub_le _ _).trans (max_le h1 h2)
  · exact (natDegree_C _).le.trans (Nat.zero_le _)

/-- The intersection polynomial is nonzero (its x^3 coefficient is 1) -/
theorem intersectionPoly_ne_zero (lam c : ZMod E.q) :
    intersectionPoly E lam c ≠ 0 := by
  intro h
  have h3 : (intersectionPoly E lam c).coeff 3 = 0 := by rw [h]; simp
  simp only [intersectionPoly, map_sub, map_add, coeff_sub, coeff_add] at h3
  simp only [coeff_X_pow, coeff_C_mul, coeff_C] at h3
  simp at h3

/-- **Bezout: a line meets E in at most 3 affine rational points.** -/
theorem line_meets_cubic_le_three (lam c : ZMod E.q) :
    (pointsOnLine E lam c).card ≤ 3 := by
  set g := intersectionPoly E lam c
  -- Build a Finset of x-coordinates
  set Z := (pointsOnLine E lam c).image Prod.fst with hZ_def
  -- x-projection is injective on pointsOnLine (y determined by x on line)
  have hinj : Set.InjOn Prod.fst (↑(pointsOnLine E lam c) :
      Set (ZMod E.q × ZMod E.q)) := by
    intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 hx
    simp only [Finset.mem_coe, pointsOnLine, Finset.mem_filter] at h1 h2
    simp only [Prod.fst] at hx
    exact Prod.ext hx (by rw [h1.2, h2.2, hx])
  have hcard : Z.card = (pointsOnLine E lam c).card := Finset.card_image_of_injOn hinj
  -- Z ⊆ roots of g (as a multiset)
  have hZ_sub : Z.val ⊆ g.roots := by
    intro x hx
    have hx' : x ∈ Z := Finset.mem_val.mp hx
    rw [hZ_def, Finset.mem_image] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    rw [mem_roots (intersectionPoly_ne_zero E lam c)]
    exact isRoot_of_mem_pointsOnLine E hp
  -- Chain the bounds
  calc (pointsOnLine E lam c).card
      = Z.card := hcard.symm
    _ ≤ g.natDegree := card_le_degree_of_subset_roots hZ_sub
    _ ≤ 3 := natDegree_intersectionPoly_le E lam c

/-! ## Slope distribution -/

def interceptOf (lam : ZMod E.q) (p : ZMod E.q × ZMod E.q) : ZMod E.q :=
  p.2 - lam * p.1

def pairsWithSlope (lam : ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (distinctPairs E.points).filter (fun p =>
    p.1.1 ≠ p.2.1 ∧ slopeOf p.1.1 p.1.2 p.2.1 p.2.2 = lam)

/-- **Lemma 1 (Slope Distribution).**
    |pairsWithSlope lam| ≤ 2 * numAffine. -/
theorem slope_distribution (lam : ZMod E.q) :
    (pairsWithSlope E lam).card ≤ 2 * E.numAffine := by
  sorry

end Divisor
