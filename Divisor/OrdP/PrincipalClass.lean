/-
  Divisor/OrdP/PrincipalClass.lean

  Small mathlib-native bridge for the long-term replacement of the
  `ordAt_divisor_isPrincipal` / `principal_divisor_iff` axiom pair.

  Mathlib's `WeierstrassCurve.Affine.Point.toClass` embeds the elliptic
  curve group into the class group of the affine coordinate ring.  This
  file records the immediate consequence needed downstream: a finite
  divisor class that is zero has zero weighted group sum.
-/

import Divisor.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

open Finset
open WeierstrassCurve WeierstrassCurve.Affine

namespace Divisor

variable (E : ECSetup)

/-- The class of a finite-support divisor in
`ClassGroup E.toW.toAffine.CoordinateRing`, computed through mathlib's
point-to-class homomorphism. -/
noncomputable def divisorClass
    (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs)) :
    Additive (ClassGroup E.toW.toAffine.CoordinateRing) :=
  ∑ P ∈ h.toFinset, (coeffs P) • Point.toClass P

/-- `divisorClass` is exactly the image under `Point.toClass` of the
weighted group sum of the same divisor. -/
theorem divisorClass_eq_toClass_weightedSum
    (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs)) :
    divisorClass E coeffs h =
      Point.toClass
        (ECPoint.weightedSum E h.toFinset
          (fun P => ECPoint.zsmul E (coeffs P) P)) := by
  unfold divisorClass
  change (∑ P ∈ h.toFinset, (coeffs P) • Point.toClass P)
      = Point.toClass (∑ P ∈ h.toFinset, (coeffs P) • P : ECPoint E)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro P _hP
  rw [map_zsmul]

/-- If the class of a finite-support divisor is zero, then its weighted
sum in the elliptic-curve group is zero. This replaces the part of the
old `principal_divisor_iff` axiom that the MA extraction path used to
consume. -/
theorem weightedSum_zero_of_divisorClass_zero
    (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs))
    (hZero : divisorClass E coeffs h = 0) :
    ECPoint.weightedSum E h.toFinset
        (fun P => ECPoint.zsmul E (coeffs P) P) = 0 := by
  have hImage : Point.toClass
      (ECPoint.weightedSum E h.toFinset
        (fun P => ECPoint.zsmul E (coeffs P) P)) = 0 := by
    rw [← divisorClass_eq_toClass_weightedSum E coeffs h]
    exact hZero
  exact (Point.toClass_eq_zero _).mp hImage

end Divisor
