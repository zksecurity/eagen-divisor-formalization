/-
  Divisor/LineBuildComputable/Bridge.lean

  Recursive bridge: the computable `lineBuildC` agrees with the
  noncomputable `lineBuild` from `Divisor/LineBuildRecursive.lean`
  via `CoordRingEltC.toCoordRingElt`.

  Per-step bridges chain through `chord_toCoordRingElt`,
  `mul_toCoordRingElt`, and `divLin_toCoordRingElt`.
-/
import Divisor.LineBuildComputable
import Divisor.LineBuildRecursive
import Divisor.CoordRingEltC.Bridge

open Polynomial

namespace Divisor

namespace AccumC

variable {E : ECSetup}

/-- Bridge from a computable accumulator to the noncomputable
    `Accum E`: point unchanged, polynomial bridged. -/
noncomputable def toAccum (a : AccumC E.q) : Accum E :=
  { point := a.point, poly := a.poly.toCoordRingElt }

@[simp] theorem toAccum_point (a : AccumC E.q) :
    (toAccum (E := E) a).point = a.point := rfl

@[simp] theorem toAccum_poly (a : AccumC E.q) :
    (toAccum (E := E) a).poly = a.poly.toCoordRingElt := rfl

/-! ### Per-step bridges -/

theorem fromChordPair_distinct_toAccum
    (P Q : ZMod E.q × ZMod E.q) (h : P.1 ≠ Q.1) :
    toAccum (E := E) (AccumC.fromChordPair_distinct E.curveA P Q)
      = Accum.fromChordPair_distinct E P Q h := by
  show ({ point := _, poly := (CoordRingEltC.chord E.curveA P Q).toCoordRingElt }
        : Accum E)
      = { point := _, poly := chordCoordRingElt E P Q }
  congr 1
  exact CoordRingEltC.chord_toCoordRingElt E P Q

theorem fromChordPair_vertical_toAccum
    (P Q : ZMod E.q × ZMod E.q) (h_xx : P.1 = Q.1) (h_yy : P.2 = -Q.2) :
    toAccum (E := E) (AccumC.fromChordPair_vertical P)
      = Accum.fromChordPair_vertical E P Q h_xx h_yy := by
  show ({ point := P,
          poly := (⟨CoeffPoly.X - CoeffPoly.C P.1, 0⟩ : CoordRingEltC E.q).toCoordRingElt }
        : Accum E)
      = ⟨P, ⟨Polynomial.X - Polynomial.C P.1, 0⟩⟩
  congr 1
  unfold CoordRingEltC.toCoordRingElt
  have h_a : (CoeffPoly.X - CoeffPoly.C P.1 : CoeffPoly E.q).toPolynomial
    = Polynomial.X - Polynomial.C P.1 := CoordRingEltC.toPolynomial_X_sub_C P.1
  have h_b : (0 : CoeffPoly E.q).toPolynomial = 0 := CoeffPoly.toPolynomial_zero
  rw [h_a, h_b]

theorem combine_higher_distinct_toAccum
    (a b : AccumC E.q) (h : a.point.1 ≠ b.point.1) :
    toAccum (E := E)
        (AccumC.combine_higher_distinct E.curveA E.curveB a b)
      = Accum.combine_higher_distinct E
          (toAccum (E := E) a) (toAccum (E := E) b) h := by
  -- Both sides build a `Accum` with .point = (Qx, -Qy) where
  -- Qx, Qy depend on (a.point, b.point) via the same slope formula.
  -- .poly is the chord * a.poly * b.poly / divLin / divLin.
  show ({ point := _,
          poly := (((CoordRingEltC.chord E.curveA a.point b.point).mul
                      E.curveA E.curveB a.poly).mul
                      E.curveA E.curveB b.poly
                  |>.divLin a.point.1
                  |>.divLin b.point.1).toCoordRingElt } : Accum E)
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

theorem combine_higher_vertical_toAccum
    (a b : AccumC E.q) (h_xx : a.point.1 = b.point.1)
    (h_yy : a.point.2 = -b.point.2) :
    toAccum (E := E)
        (AccumC.combine_higher_vertical E.curveA E.curveB a b)
      = Accum.combine_higher_vertical E
          (toAccum (E := E) a) (toAccum (E := E) b) h_xx h_yy := by
  show ({ point := a.point,
          poly := ((a.poly.mul E.curveA E.curveB b.poly).divLin
                    a.point.1).toCoordRingElt } : Accum E)
    = { point := a.point,
        poly := (mulCoordRingElt E a.poly.toCoordRingElt b.poly.toCoordRingElt).divLin
                  a.point.1 }
  congr 1
  rw [CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt]

end AccumC

/-! ### Driver bridges -/

/-- Strong-induction shape for `lineBuild_level0`/`lineBuild_level0C`:
    both pattern-match on `[] | [P] | P :: Q :: rest`. -/
theorem lineBuild_level0C_toList (E : ECSetup) :
    ∀ (Ps : List (ZMod E.q × ZMod E.q)),
      (lineBuild_level0C E.curveA Ps).map (AccumC.toAccum (E := E))
        = lineBuild_level0 E Ps
  | [] => rfl
  | [P] => by
    show ([AccumC.toAccum (E := E)
            { point := P, poly := ⟨1, 0⟩ }] : List (Accum E))
        = ([{ point := P, poly := ⟨1, 0⟩ }] : List (Accum E))
    show ([{ point := P, poly := (⟨1, 0⟩ : CoordRingEltC E.q).toCoordRingElt }]
            : List (Accum E))
        = ([{ point := P, poly := (⟨1, 0⟩ : CoordRingElt E.q) }]
            : List (Accum E))
    have := CoordRingEltC.toCoordRingElt_one E.q
    rw [this]
  | P :: Q :: rest => by
    have ih := lineBuild_level0C_toList E rest
    unfold lineBuild_level0C lineBuild_level0
    by_cases h_xx : P.1 ≠ Q.1
    · rw [if_pos h_xx, dif_pos h_xx]
      show AccumC.toAccum (E := E)
              (AccumC.fromChordPair_distinct E.curveA P Q)
            :: (lineBuild_level0C E.curveA rest).map _
          = Accum.fromChordPair_distinct E P Q h_xx
            :: lineBuild_level0 E rest
      rw [ih, AccumC.fromChordPair_distinct_toAccum P Q h_xx]
    · rw [if_neg h_xx, dif_neg h_xx]
      have h_xx_eq : P.1 = Q.1 := not_not.mp h_xx
      by_cases h_yy : P.2 = -Q.2
      · rw [if_pos h_yy, dif_pos h_yy]
        show AccumC.toAccum (E := E)
                (AccumC.fromChordPair_vertical P)
              :: (lineBuild_level0C E.curveA rest).map _
            = Accum.fromChordPair_vertical E P Q _ h_yy
              :: lineBuild_level0 E rest
        rw [ih]
        rw [AccumC.fromChordPair_vertical_toAccum P Q h_xx_eq h_yy]
      · rw [if_neg h_yy, dif_neg h_yy]
        show AccumC.toAccum (E := E)
                { point := P, poly := ⟨1, 0⟩ }
              :: (lineBuild_level0C E.curveA rest).map _
            = { point := P, poly := (⟨1, 0⟩ : CoordRingElt E.q) }
              :: lineBuild_level0 E rest
        rw [ih]
        congr 1
        unfold AccumC.toAccum
        congr 1
        exact CoordRingEltC.toCoordRingElt_one E.q
termination_by Ps => Ps.length

theorem lineBuild_level_stepC_toList (E : ECSetup) :
    ∀ (xs : List (AccumC E.q)),
      (lineBuild_level_stepC E.curveA E.curveB xs).map
        (AccumC.toAccum (E := E))
        = lineBuild_level_step E
            (xs.map (AccumC.toAccum (E := E)))
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    have ih := lineBuild_level_stepC_toList E rest
    -- Reduce the map on the RHS before dispatch.
    show ((lineBuild_level_stepC E.curveA E.curveB (a :: b :: rest)).map
            (AccumC.toAccum (E := E)) : List (Accum E))
        = lineBuild_level_step E
            (AccumC.toAccum (E := E) a
              :: AccumC.toAccum (E := E) b
              :: rest.map (AccumC.toAccum (E := E)))
    unfold lineBuild_level_stepC lineBuild_level_step
    -- `.point` field is preserved by toAccum (it's a structure
    -- projection): the dispatch conditions agree.
    have hpa : (AccumC.toAccum (E := E) a).point.1 = a.point.1 := rfl
    have hpa2 : (AccumC.toAccum (E := E) a).point.2 = a.point.2 := rfl
    have hpb : (AccumC.toAccum (E := E) b).point.1 = b.point.1 := rfl
    have hpb2 : (AccumC.toAccum (E := E) b).point.2 = b.point.2 := rfl
    by_cases h_xx : a.point.1 ≠ b.point.1
    · rw [if_pos h_xx]
      have h_xx' : (AccumC.toAccum (E := E) a).point.1
            ≠ (AccumC.toAccum (E := E) b).point.1 := by
        rw [hpa, hpb]; exact h_xx
      rw [dif_pos h_xx']
      rw [List.map_cons]
      rw [ih, AccumC.combine_higher_distinct_toAccum a b h_xx]
    · rw [if_neg h_xx]
      have h_xx' : ¬ ((AccumC.toAccum (E := E) a).point.1
              ≠ (AccumC.toAccum (E := E) b).point.1) := by
        rw [hpa, hpb]; exact h_xx
      rw [dif_neg h_xx']
      have h_xx_eq : a.point.1 = b.point.1 := not_not.mp h_xx
      by_cases h_yy : a.point.2 = -b.point.2
      · rw [if_pos h_yy]
        have h_yy' : (AccumC.toAccum (E := E) a).point.2
              = -(AccumC.toAccum (E := E) b).point.2 := by
          rw [hpa2, hpb2]; exact h_yy
        rw [dif_pos h_yy']
        rw [List.map_cons]
        rw [ih, AccumC.combine_higher_vertical_toAccum a b h_xx_eq h_yy]
      · rw [if_neg h_yy]
        have h_yy' : ¬ ((AccumC.toAccum (E := E) a).point.2
              = -(AccumC.toAccum (E := E) b).point.2) := by
          rw [hpa2, hpb2]; exact h_yy
        rw [dif_neg h_yy']
        rw [List.map_cons, List.map_cons]
        rw [ih]
termination_by xs => xs.length

theorem lineBuild_iterateC_toList (E : ECSetup) (n : ℕ) :
    ∀ (xs : List (AccumC E.q)),
      (lineBuild_iterateC E.curveA E.curveB n xs).map
        (AccumC.toAccum (E := E))
        = lineBuild_iterate E n
            (xs.map (AccumC.toAccum (E := E))) := by
  induction n with
  | zero => intro xs; rfl
  | succ k ih =>
    intro xs
    unfold lineBuild_iterateC lineBuild_iterate
    by_cases hLen : xs.length ≤ 1
    · rw [if_pos hLen]
      have hLen' : (xs.map (AccumC.toAccum (E := E))).length ≤ 1 := by
        rw [List.length_map]; exact hLen
      rw [if_pos hLen']
    · rw [if_neg hLen]
      have hLen' : ¬ (xs.map (AccumC.toAccum (E := E))).length ≤ 1 := by
        rw [List.length_map]; exact hLen
      rw [if_neg hLen']
      rw [ih]
      rw [lineBuild_level_stepC_toList]

/-- Top-level bridge: the computable `lineBuildC` agrees with
    the noncomputable `lineBuild` via `toCoordRingElt`. -/
theorem lineBuildC_toCoordRingElt_eq_lineBuild (E : ECSetup)
    (Ps : List (ZMod E.q × ZMod E.q)) :
    (lineBuildC E.curveA E.curveB Ps).toCoordRingElt
      = lineBuild E Ps := by
  have h_iter : (lineBuild_iterateC E.curveA E.curveB Ps.length
                  (lineBuild_level0C E.curveA Ps)).map
                (AccumC.toAccum (E := E))
              = lineBuild_iterate E Ps.length (lineBuild_level0 E Ps) := by
    rw [lineBuild_iterateC_toList E Ps.length, lineBuild_level0C_toList]
  -- Both `lineBuildC` and `lineBuild` are `match` on the iteration
  -- list followed by polynomial extraction.  Reduce them via dsimp.
  dsimp only [lineBuildC, lineBuild]
  rcases hC : lineBuild_iterateC E.curveA E.curveB Ps.length
                (lineBuild_level0C E.curveA Ps) with _ | ⟨single, rest⟩
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
