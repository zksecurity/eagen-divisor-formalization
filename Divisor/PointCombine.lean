/-
  Divisor/PointCombine.lean — the point skeleton of the line build is
  the elliptic-curve group law.

  `pointCombine_eq_add`: the combine that `Accum.combine` performs on
  running points agrees with mathlib's group law on every pair of
  points, unconditionally (every `ECPoint` carries its nonsingularity
  witness, which rules out the junk branches).
-/
import Divisor.LineBuild

open Polynomial Classical

namespace Divisor.LineAccum

variable (E : ECSetup)

/-! ## The skeleton combine is the group law -/

/-- Membership in `E.points` from mathlib nonsingularity. -/
private theorem mem_of_nonsingular {x y : ZMod E.q}
    (h : E.toW.toAffine.Nonsingular x y) : (x, y) ∈ E.points :=
  E.hComplete x y ((E.equation_iff x y).mp (E.equation_iff_nonsingular.mpr h))

/-- The distinct-`x` chord formula computes the group-law sum. -/
private theorem chord_formula_add
    {xa ya xb yb : ZMod E.q}
    (hns_a : E.toW.toAffine.Nonsingular xa ya)
    (hns_b : E.toW.toAffine.Nonsingular xb yb)
    (hxx : xa ≠ xb) :
    ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
        (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
            (ya - slopeOf xa ya xb yb * xa)))
      = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := by
  classical
  have hA : (xa, ya) ∈ E.points := mem_of_nonsingular E hns_a
  have hB : (xb, yb) ∈ E.points := mem_of_nonsingular E hns_b
  have hT : thirdPoint E (xa, ya) (xb, yb) =
      some (slopeOf xa ya xb yb ^ 2 - xa - xb,
        slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
          (ya - slopeOf xa ya xb yb * xa)) := by
    unfold thirdPoint
    rw [if_neg (by exact hxx)]
    rfl
  have hmem := third_point_on_curve E (xa, ya) (xb, yb) hA hB hT
  have hsum := thirdPoint_some_eq_neg_add (E := E) hA hB hT
  calc ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
        (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
            (ya - slopeOf xa ya xb yb * xa)))
      = -(ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
            (slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
              (ya - slopeOf xa ya xb yb * xa))) := by
        rw [ECPoint.affine_neg]
    _ = -(ECPoint.affineOfMem E hmem) := by
        rw [ECPoint.affine_eq_affineOfMem E hmem]
    _ = ECPoint.affineOfMem E hA + ECPoint.affineOfMem E hB := hsum.symm
    _ = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := rfl

/-- The smooth-tangent formula computes the doubling. -/
private theorem tangent_formula_add
    {xa ya : ZMod E.q}
    (hns_a hns_b : E.toW.toAffine.Nonsingular xa ya)
    (hy0 : ¬ ya = 0) :
    ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
        (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa)))
      = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := by
  classical
  have hA : (xa, ya) ∈ E.points := mem_of_nonsingular E hns_a
  have hT : thirdPoint E (xa, ya) (xa, ya) =
      some (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa,
        (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
            (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
          (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa)) := by
    unfold thirdPoint
    rw [if_pos rfl, if_pos rfl, if_neg (by exact hy0)]
  have hmem := third_point_on_curve E (xa, ya) (xa, ya) hA hA hT
  have hsum := thirdPoint_some_eq_neg_add (E := E) hA hA hT
  calc ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
        (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))) =
      -(ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
          ((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
              (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
            (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))) := by
        rw [ECPoint.affine_neg]
    _ = -(ECPoint.affineOfMem E hmem) := by
        rw [ECPoint.affine_eq_affineOfMem E hmem]
    _ = ECPoint.affineOfMem E hA + ECPoint.affineOfMem E hA := hsum.symm
    _ = (WeierstrassCurve.Affine.Point.some _ _ hns_a +
         WeierstrassCurve.Affine.Point.some _ _ hns_b : ECPoint E) := rfl

/-- **The computable point-skeleton combine is mathlib's group law**,
unconditionally: every `ECPoint` carries its nonsingularity witness,
which rules the junk branches out. This upgrades every block point in
the skeleton run to a genuine elliptic-curve subset sum. -/
theorem pointCombine_eq_add (p q : ECPoint E) :
    pointCombine E p q = p + q := by
  classical
  match p, q with
  | WeierstrassCurve.Affine.Point.zero, q =>
      show q = 0 + q
      exact (zero_add q).symm
  | WeierstrassCurve.Affine.Point.some xa ya hns_a, WeierstrassCurve.Affine.Point.zero =>
      show WeierstrassCurve.Affine.Point.some xa ya hns_a
          = WeierstrassCurve.Affine.Point.some xa ya hns_a + 0
      exact (add_zero _).symm
  | WeierstrassCurve.Affine.Point.some xa ya hns_a,
    WeierstrassCurve.Affine.Point.some xb yb hns_b =>
      show (if _h_xx : xa ≠ xb then
              ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
                (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
                    (ya - slopeOf xa ya xb yb * xa)))
            else if _h_yy : ya = -yb then 0
            else if _h_y0 : ya = 0 then 0
            else
              ECPoint.affine E (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa)
                (-((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
                      (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
                    (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa))))
          = WeierstrassCurve.Affine.Point.some xa ya hns_a +
            WeierstrassCurve.Affine.Point.some xb yb hns_b
      have ea : ya ^ 2 = xa ^ 3 + E.curveA * xa + E.curveB :=
        (E.equation_iff xa ya).mp (E.equation_iff_nonsingular.mpr hns_a)
      have eb : yb ^ 2 = xb ^ 3 + E.curveA * xb + E.curveB :=
        (E.equation_iff xb yb).mp (E.equation_iff_nonsingular.mpr hns_b)
      split_ifs with hxx hyy hy0
      · exact chord_formula_add E hns_a hns_b hxx
      · -- Vertical: the two points are inverse.
        have hxe : xa = xb := not_not.mp hxx
        have hyb : yb = -ya := by rw [hyy, neg_neg]
        subst hxe
        subst hyb
        have hneg : (WeierstrassCurve.Affine.Point.some xa (-ya) hns_b : ECPoint E)
            = -(WeierstrassCurve.Affine.Point.some xa ya hns_a) := by
          have h1 : -(WeierstrassCurve.Affine.Point.some xa ya hns_a : ECPoint E)
              = ECPoint.affine E xa (-ya) := by
            rw [← ECPoint.affine_of_nonsingular E hns_a]
            exact ECPoint.affine_neg E xa ya
          rw [h1, ECPoint.affine_of_nonsingular E hns_b]
        rw [hneg, add_neg_cancel]
      · -- Equal `x`, not inverse, `ya = 0`: impossible on the curve.
        exfalso
        have hxe : xa = xb := not_not.mp hxx
        rw [← hxe] at eb
        have hyb2 : yb ^ 2 = 0 := by rw [eb, ← ea, hy0]; ring
        have hyb0 : yb = 0 := pow_eq_zero_iff two_ne_zero |>.mp hyb2
        exact hyy (by rw [hy0, hyb0, neg_zero])
      · -- Smooth tangent: on the curve the operands are equal.
        have hxe : xa = xb := not_not.mp hxx
        subst hxe
        have hyb : yb = ya := by
          have h2 : yb ^ 2 = ya ^ 2 := by rw [eb, ea]
          have h3 : (yb - ya) * (yb + ya) = 0 := by ring_nf; linear_combination h2
          rcases mul_eq_zero.mp h3 with h | h
          · exact sub_eq_zero.mp h
          · exact absurd (by rw [← eq_neg_of_add_eq_zero_right h]) hyy
        subst hyb
        exact tangent_formula_add E hns_a hns_b hy0

end Divisor.LineAccum
