/-
  Divisor/EagenBuildComputable/Bridge.lean

  Recursive bridge: the computable `eagenBuildC` agrees with the
  noncomputable `eagenBuild` from `Divisor/EagenBuildRecursive.lean`
  via `CoordRingEltC.toCoordRingElt`.

  Per-step bridges chain through `chord_toCoordRingElt`,
  `mul_toCoordRingElt`, and `divLin_toCoordRingElt`.
-/
import Divisor.EagenBuildComputable
import Divisor.EagenBuildRecursive
import Divisor.CoordRingEltC.Bridge

open Polynomial

namespace Divisor

namespace EagenAccumC

variable {E : ECSetup}

/-- Bridge from a computable accumulator to the noncomputable
    `EagenAccum E`: point unchanged, polynomial bridged. -/
noncomputable def toEagenAccum (a : EagenAccumC E.q) : EagenAccum E :=
  { point := a.point, poly := a.poly.toCoordRingElt }

@[simp] theorem toEagenAccum_point (a : EagenAccumC E.q) :
    (toEagenAccum (E := E) a).point = a.point := rfl

@[simp] theorem toEagenAccum_poly (a : EagenAccumC E.q) :
    (toEagenAccum (E := E) a).poly = a.poly.toCoordRingElt := rfl

/-! ### Per-step bridges -/

theorem fromChordPair_distinct_toEagenAccum
    (P Q : ZMod E.q × ZMod E.q) (h : P.1 ≠ Q.1) :
    toEagenAccum (E := E) (EagenAccumC.fromChordPair_distinct E.curveA P Q)
      = EagenAccum.fromChordPair_distinct E P Q h := by
  show ({ point := _, poly := (CoordRingEltC.chord E.curveA P Q).toCoordRingElt }
        : EagenAccum E)
      = { point := _, poly := chordCoordRingElt E P Q }
  congr 1
  exact CoordRingEltC.chord_toCoordRingElt E P Q

theorem fromChordPair_vertical_toEagenAccum
    (P Q : ZMod E.q × ZMod E.q) (h_xx : P.1 = Q.1) (h_yy : P.2 = -Q.2) :
    toEagenAccum (E := E) (EagenAccumC.fromChordPair_vertical P)
      = EagenAccum.fromChordPair_vertical E P Q h_xx h_yy := by
  show ({ point := P,
          poly := (⟨CoeffPoly.X - CoeffPoly.C P.1, 0⟩ : CoordRingEltC E.q).toCoordRingElt }
        : EagenAccum E)
      = ⟨P, ⟨Polynomial.X - Polynomial.C P.1, 0⟩⟩
  congr 1
  unfold CoordRingEltC.toCoordRingElt
  have h_a : (CoeffPoly.X - CoeffPoly.C P.1 : CoeffPoly E.q).toPolynomial
    = Polynomial.X - Polynomial.C P.1 := CoordRingEltC.toPolynomial_X_sub_C P.1
  have h_b : (0 : CoeffPoly E.q).toPolynomial = 0 := CoeffPoly.toPolynomial_zero
  rw [h_a, h_b]

theorem combine_higher_distinct_toEagenAccum
    (a b : EagenAccumC E.q) (h : a.point.1 ≠ b.point.1) :
    toEagenAccum (E := E)
        (EagenAccumC.combine_higher_distinct E.curveA E.curveB a b)
      = EagenAccum.combine_higher_distinct E
          (toEagenAccum (E := E) a) (toEagenAccum (E := E) b) h := by
  -- Both sides build a `EagenAccum` with .point = (Qx, -Qy) where
  -- Qx, Qy depend on (a.point, b.point) via the same slope formula.
  -- .poly is the chord * a.poly * b.poly / divLin / divLin.
  show ({ point := _,
          poly := (((CoordRingEltC.chord E.curveA a.point b.point).mul
                      E.curveA E.curveB a.poly).mul
                      E.curveA E.curveB b.poly
                  |>.divLin a.point.1
                  |>.divLin b.point.1).toCoordRingElt } : EagenAccum E)
    = { point := _,
        poly := (((mulCoordRingElt E
                    (mulCoordRingElt E (chordCoordRingElt E a.point b.point)
                      a.poly.toCoordRingElt) b.poly.toCoordRingElt))
                  |>.divLin a.point.1
                  |>.divLin b.point.1) }
  congr 1
  rw [CoordRingEltC.divLin_toCoordRingElt,
      CoordRingEltC.divLin_toCoordRingElt,
      CoordRingEltC.mul_toCoordRingElt,
      CoordRingEltC.mul_toCoordRingElt,
      CoordRingEltC.chord_toCoordRingElt]

theorem combine_higher_vertical_toEagenAccum
    (a b : EagenAccumC E.q) (h_xx : a.point.1 = b.point.1)
    (h_yy : a.point.2 = -b.point.2) :
    toEagenAccum (E := E)
        (EagenAccumC.combine_higher_vertical E.curveA E.curveB a b)
      = EagenAccum.combine_higher_vertical E
          (toEagenAccum (E := E) a) (toEagenAccum (E := E) b) h_xx h_yy := by
  show ({ point := a.point,
          poly := ((a.poly.mul E.curveA E.curveB b.poly).divLin
                    a.point.1).toCoordRingElt } : EagenAccum E)
    = { point := a.point,
        poly := (mulCoordRingElt E a.poly.toCoordRingElt b.poly.toCoordRingElt).divLin
                  a.point.1 }
  congr 1
  rw [CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt]

end EagenAccumC

/-! ### Driver bridges -/

/-- Strong-induction shape for `eagenBuild_level0`/`eagenBuild_level0C`:
    both pattern-match on `[] | [P] | P :: Q :: rest`. -/
theorem eagenBuild_level0C_toList (E : ECSetup) :
    ∀ (Ps : List (ZMod E.q × ZMod E.q)),
      (eagenBuild_level0C E.curveA Ps).map (EagenAccumC.toEagenAccum (E := E))
        = eagenBuild_level0 E Ps
  | [] => rfl
  | [P] => by
    show ([EagenAccumC.toEagenAccum (E := E)
            { point := P, poly := ⟨1, 0⟩ }] : List (EagenAccum E))
        = ([{ point := P, poly := ⟨1, 0⟩ }] : List (EagenAccum E))
    show ([{ point := P, poly := (⟨1, 0⟩ : CoordRingEltC E.q).toCoordRingElt }]
            : List (EagenAccum E))
        = ([{ point := P, poly := (⟨1, 0⟩ : CoordRingElt E.q) }]
            : List (EagenAccum E))
    have := CoordRingEltC.toCoordRingElt_one E.q
    rw [this]
  | P :: Q :: rest => by
    have ih := eagenBuild_level0C_toList E rest
    unfold eagenBuild_level0C eagenBuild_level0
    by_cases h_xx : P.1 ≠ Q.1
    · rw [if_pos h_xx, dif_pos h_xx]
      show EagenAccumC.toEagenAccum (E := E)
              (EagenAccumC.fromChordPair_distinct E.curveA P Q)
            :: (eagenBuild_level0C E.curveA rest).map _
          = EagenAccum.fromChordPair_distinct E P Q h_xx
            :: eagenBuild_level0 E rest
      rw [ih, EagenAccumC.fromChordPair_distinct_toEagenAccum P Q h_xx]
    · rw [if_neg h_xx, dif_neg h_xx]
      have h_xx_eq : P.1 = Q.1 := not_not.mp h_xx
      by_cases h_yy : P.2 = -Q.2
      · rw [if_pos h_yy, dif_pos h_yy]
        show EagenAccumC.toEagenAccum (E := E)
                (EagenAccumC.fromChordPair_vertical P)
              :: (eagenBuild_level0C E.curveA rest).map _
            = EagenAccum.fromChordPair_vertical E P Q _ h_yy
              :: eagenBuild_level0 E rest
        rw [ih]
        rw [EagenAccumC.fromChordPair_vertical_toEagenAccum P Q h_xx_eq h_yy]
      · rw [if_neg h_yy, dif_neg h_yy]
        show EagenAccumC.toEagenAccum (E := E)
                { point := P, poly := ⟨1, 0⟩ }
              :: (eagenBuild_level0C E.curveA rest).map _
            = { point := P, poly := (⟨1, 0⟩ : CoordRingElt E.q) }
              :: eagenBuild_level0 E rest
        rw [ih]
        congr 1
        unfold EagenAccumC.toEagenAccum
        congr 1
        exact CoordRingEltC.toCoordRingElt_one E.q
termination_by Ps => Ps.length

theorem eagenBuild_level_stepC_toList (E : ECSetup) :
    ∀ (xs : List (EagenAccumC E.q)),
      (eagenBuild_level_stepC E.curveA E.curveB xs).map
        (EagenAccumC.toEagenAccum (E := E))
        = eagenBuild_level_step E
            (xs.map (EagenAccumC.toEagenAccum (E := E)))
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    have ih := eagenBuild_level_stepC_toList E rest
    -- Reduce the map on the RHS before dispatch.
    show ((eagenBuild_level_stepC E.curveA E.curveB (a :: b :: rest)).map
            (EagenAccumC.toEagenAccum (E := E)) : List (EagenAccum E))
        = eagenBuild_level_step E
            (EagenAccumC.toEagenAccum (E := E) a
              :: EagenAccumC.toEagenAccum (E := E) b
              :: rest.map (EagenAccumC.toEagenAccum (E := E)))
    unfold eagenBuild_level_stepC eagenBuild_level_step
    -- `.point` field is preserved by toEagenAccum (it's a structure
    -- projection): the dispatch conditions agree.
    have hpa : (EagenAccumC.toEagenAccum (E := E) a).point.1 = a.point.1 := rfl
    have hpa2 : (EagenAccumC.toEagenAccum (E := E) a).point.2 = a.point.2 := rfl
    have hpb : (EagenAccumC.toEagenAccum (E := E) b).point.1 = b.point.1 := rfl
    have hpb2 : (EagenAccumC.toEagenAccum (E := E) b).point.2 = b.point.2 := rfl
    by_cases h_xx : a.point.1 ≠ b.point.1
    · rw [if_pos h_xx]
      have h_xx' : (EagenAccumC.toEagenAccum (E := E) a).point.1
            ≠ (EagenAccumC.toEagenAccum (E := E) b).point.1 := by
        rw [hpa, hpb]; exact h_xx
      rw [dif_pos h_xx']
      rw [List.map_cons]
      rw [ih, EagenAccumC.combine_higher_distinct_toEagenAccum a b h_xx]
    · rw [if_neg h_xx]
      have h_xx' : ¬ ((EagenAccumC.toEagenAccum (E := E) a).point.1
              ≠ (EagenAccumC.toEagenAccum (E := E) b).point.1) := by
        rw [hpa, hpb]; exact h_xx
      rw [dif_neg h_xx']
      have h_xx_eq : a.point.1 = b.point.1 := not_not.mp h_xx
      by_cases h_yy : a.point.2 = -b.point.2
      · rw [if_pos h_yy]
        have h_yy' : (EagenAccumC.toEagenAccum (E := E) a).point.2
              = -(EagenAccumC.toEagenAccum (E := E) b).point.2 := by
          rw [hpa2, hpb2]; exact h_yy
        rw [dif_pos h_yy']
        rw [List.map_cons]
        rw [ih, EagenAccumC.combine_higher_vertical_toEagenAccum a b h_xx_eq h_yy]
      · rw [if_neg h_yy]
        have h_yy' : ¬ ((EagenAccumC.toEagenAccum (E := E) a).point.2
              = -(EagenAccumC.toEagenAccum (E := E) b).point.2) := by
          rw [hpa2, hpb2]; exact h_yy
        rw [dif_neg h_yy']
        rw [List.map_cons, List.map_cons]
        rw [ih]
termination_by xs => xs.length

theorem eagenBuild_iterateC_toList (E : ECSetup) (n : ℕ) :
    ∀ (xs : List (EagenAccumC E.q)),
      (eagenBuild_iterateC E.curveA E.curveB n xs).map
        (EagenAccumC.toEagenAccum (E := E))
        = eagenBuild_iterate E n
            (xs.map (EagenAccumC.toEagenAccum (E := E))) := by
  induction n with
  | zero => intro xs; rfl
  | succ k ih =>
    intro xs
    unfold eagenBuild_iterateC eagenBuild_iterate
    by_cases hLen : xs.length ≤ 1
    · rw [if_pos hLen]
      have hLen' : (xs.map (EagenAccumC.toEagenAccum (E := E))).length ≤ 1 := by
        rw [List.length_map]; exact hLen
      rw [if_pos hLen']
    · rw [if_neg hLen]
      have hLen' : ¬ (xs.map (EagenAccumC.toEagenAccum (E := E))).length ≤ 1 := by
        rw [List.length_map]; exact hLen
      rw [if_neg hLen']
      rw [ih]
      rw [eagenBuild_level_stepC_toList]

/-- Top-level bridge: the computable `eagenBuildC` agrees with
    the noncomputable `eagenBuild` via `toCoordRingElt`. -/
theorem eagenBuildC_toCoordRingElt_eq_eagenBuild (E : ECSetup)
    (Ps : List (ZMod E.q × ZMod E.q)) :
    (eagenBuildC E.curveA E.curveB Ps).toCoordRingElt
      = eagenBuild E Ps := by
  have h_iter : (eagenBuild_iterateC E.curveA E.curveB Ps.length
                  (eagenBuild_level0C E.curveA Ps)).map
                (EagenAccumC.toEagenAccum (E := E))
              = eagenBuild_iterate E Ps.length (eagenBuild_level0 E Ps) := by
    rw [eagenBuild_iterateC_toList E Ps.length, eagenBuild_level0C_toList]
  -- Both `eagenBuildC` and `eagenBuild` are `match` on the iteration
  -- list followed by polynomial extraction.  Reduce them via dsimp.
  dsimp only [eagenBuildC, eagenBuild]
  rcases hC : eagenBuild_iterateC E.curveA E.curveB Ps.length
                (eagenBuild_level0C E.curveA Ps) with _ | ⟨single, rest⟩
  · rw [hC] at h_iter
    simp only [List.map_nil] at h_iter
    rw [← h_iter]
    exact CoordRingEltC.toCoordRingElt_one E.q
  · rw [hC] at h_iter
    simp only [List.map_cons] at h_iter
    cases rest with
    | nil =>
      simp only [List.map_nil] at h_iter
      rw [← h_iter]
      rfl
    | cons b rest' =>
      simp only [List.map_cons] at h_iter
      rw [← h_iter]
      exact CoordRingEltC.toCoordRingElt_one E.q

end Divisor
