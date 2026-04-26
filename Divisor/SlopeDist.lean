/-
  Divisor/SlopeDist.lean

  Bezout's theorem for lines/cubics, and `\ref{lem:slope-dist}` (Slope Distribution).
-/
import Divisor.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
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

/-- A₀ is always on the line through itself with slope lam -/
theorem mem_pointsOnLine_self {lam : ZMod E.q}
    {A₀ : ZMod E.q × ZMod E.q} (h : A₀ ∈ E.points) :
    A₀ ∈ pointsOnLine E lam (interceptOf E lam A₀) := by
  simp [pointsOnLine, interceptOf, Finset.mem_filter, h]

/-- **`\ref{lem:slope-dist}` (Slope Distribution).**
    |pairsWithSlope lam| ≤ 2 * numAffine.

    Proof: use card_le_mul_card_image with Prod.fst.
    Each fiber (fixed A₀) has ≤ 2 elements because
    the valid A₁ lie in pointsOnLine \ {A₀}, which has size ≤ 2
    (since |pointsOnLine| ≤ 3 by Bezout). -/
theorem slope_distribution (lam : ZMod E.q) :
    (pairsWithSlope E lam).card ≤ 2 * E.numAffine := by
  -- Step 1: each first-coordinate fiber has ≤ 2 elements
  have hfiber : ∀ A₀ ∈ (pairsWithSlope E lam).image Prod.fst,
      ((pairsWithSlope E lam).filter (fun p => Prod.fst p = A₀)).card ≤ 2 := by
    intro A₀ hA₀_img
    rw [Finset.mem_image] at hA₀_img
    obtain ⟨p₀, hp₀, rfl⟩ := hA₀_img
    have hA₀ : p₀.1 ∈ E.points := by
      simp only [pairsWithSlope, distinctPairs, Finset.mem_filter, Finset.mem_product] at hp₀
      exact hp₀.1.1.1
    -- Inject the fiber (via Prod.snd) into (pointsOnLine lam c).erase A₀
    set c := interceptOf E lam p₀.1
    -- Prod.snd is injective on the fiber (Prod.fst is constant)
    -- and the image lands in pointsOnLine \ {p₀.1}
    calc ((pairsWithSlope E lam).filter (fun p => Prod.fst p = p₀.1)).card
        ≤ ((pointsOnLine E lam c).erase p₀.1).card := by
          apply Finset.card_le_card_of_injOn Prod.snd
          · -- image in pointsOnLine.erase A₀
            intro ⟨a, b⟩ hab
            rw [Finset.mem_coe, Finset.mem_filter] at hab
            have hab1 := hab.1
            have hfst := hab.2
            unfold pairsWithSlope at hab1
            rw [Finset.mem_filter] at hab1
            have hab2 := hab1.1
            have hx := hab1.2.1
            have hslope := hab1.2.2
            unfold distinctPairs at hab2
            rw [Finset.mem_filter, Finset.mem_product] at hab2
            have ha_mem := hab2.1.1
            have hb_mem := hab2.1.2
            have hne := hab2.2
            -- a = first point, b = second point, hfst : a = p₀.1
            subst hfst  -- replace a by p₀.1
            rw [Finset.mem_coe, Finset.mem_erase]
            constructor
            · exact fun heq => hne heq.symm
            · rw [pointsOnLine, Finset.mem_filter]
              refine ⟨hb_mem, ?_⟩
              -- b is on the line with slope lam through p₀.1
              simp only [slopeOf] at hslope
              have hxne : b.1 - p₀.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
              show b.2 = lam * b.1 + (p₀.1.2 - lam * p₀.1.1)
              -- From hslope: (b.2-p₀.1.2)*(b.1-p₀.1.1)⁻¹ = lam
              -- So b.2 - p₀.1.2 = lam * (b.1 - p₀.1.1)
              -- So b.2 = lam * b.1 + (p₀.1.2 - lam * p₀.1.1)
              have key : b.2 - p₀.1.2 = lam * (b.1 - p₀.1.1) := by
                calc b.2 - p₀.1.2
                    = (b.2 - p₀.1.2) * ((b.1 - p₀.1.1)⁻¹ * (b.1 - p₀.1.1)) := by
                      rw [inv_mul_cancel₀ hxne, mul_one]
                  _ = (b.2 - p₀.1.2) * (b.1 - p₀.1.1)⁻¹ * (b.1 - p₀.1.1) := by ring
                  _ = lam * (b.1 - p₀.1.1) := by rw [hslope]
              linear_combination key
          · -- Prod.snd is injective on the fiber
            intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 hsnd
            have h1f := (Finset.mem_filter.mp h1).2
            have h2f := (Finset.mem_filter.mp h2).2
            exact Prod.ext (h1f.trans h2f.symm) hsnd
      _ = (pointsOnLine E lam c).card - 1 := by
          rw [Finset.card_erase_of_mem (mem_pointsOnLine_self E hA₀)]
      _ ≤ 2 := by
          have := line_meets_cubic_le_three E lam c
          omega
  -- Step 2: total ≤ 2 * |image| ≤ 2 * numAffine
  calc (pairsWithSlope E lam).card
      ≤ 2 * ((pairsWithSlope E lam).image Prod.fst).card :=
        Finset.card_le_mul_card_image _ _ hfiber
    _ ≤ 2 * E.numAffine := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        simp only [pairsWithSlope, distinctPairs, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.1.1

end Divisor
