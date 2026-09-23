/-
  Divisor/LineBuildComputable/Singletons.lean — a computable mirror of
  the singleton line build, and its bridge.

  `AccumSC E` carries the running `ECPoint E` and a `CoordRingEltC`
  polynomial. `combineC` follows `Accum.combine` branch for branch
  (both at infinity, one at infinity, chord, vertical, 2-torsion
  tangent, smooth tangent), using `CoordRingEltC.mul/divLin/chord`.
  Everything here is a plain `def`, so `lineBuildC_singletons` runs.

  `lineBuildC_singletons_toCoordRingElt` identifies its output with
  `LineAccum.lineBuild_singletons`.
-/
import Divisor.LineBuild
import Divisor.CoordRingEltC.Bridge

namespace Divisor.LineAccum

variable (E : ECSetup)

/-- Computable singleton-build accumulator. -/
structure AccumSC where
  point : ECPoint E
  poly : CoordRingEltC E.q

variable {E}

/-- The noncomputable accumulator it represents. -/
noncomputable def AccumSC.toAccum (a : AccumSC E) : Accum E :=
  { point := a.point, poly := a.poly.toCoordRingElt }

variable (E)

/-- Computable `Accum.combine_distinct`. -/
def combineC_distinct (a b : AccumSC E) (xa ya xb yb : ZMod E.q) : AccumSC E :=
  let line := CoordRingEltC.chord E.curveA (xa, ya) (xb, yb)
  let lam := slopeOf xa ya xb yb
  let Qx := lam ^ 2 - xa - xb
  let Qy := lam * Qx + (ya - lam * xa)
  let prod := CoordRingEltC.mul E.curveA E.curveB
    (CoordRingEltC.mul E.curveA E.curveB line a.poly) b.poly
  { point := ECPoint.affine E Qx (-Qy), poly := (prod.divLin xa).divLin xb }

/-- Computable `Accum.combine_vertical` (also the 2-torsion tangent). -/
def combineC_vertical (a b : AccumSC E) (xa : ZMod E.q) : AccumSC E :=
  { point := 0, poly := (CoordRingEltC.mul E.curveA E.curveB a.poly b.poly).divLin xa }

/-- Computable `Accum.combine_tangent_smooth`. -/
def combineC_tangent (a b : AccumSC E) (xa ya : ZMod E.q) : AccumSC E :=
  let line := CoordRingEltC.chord E.curveA (xa, ya) (xa, ya)
  let lam : ZMod E.q := (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹
  let Qx := lam ^ 2 - 2 * xa
  let Qy := lam * Qx + (ya - lam * xa)
  let prod := CoordRingEltC.mul E.curveA E.curveB
    (CoordRingEltC.mul E.curveA E.curveB line a.poly) b.poly
  { point := ECPoint.affine E Qx (-Qy), poly := (prod.divLin xa).divLin xa }

/-- Computable `Accum.combine`, branch for branch. -/
def combineC (a b : AccumSC E) : AccumSC E :=
  match a.point, b.point with
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.zero =>
      { point := 0, poly := CoordRingEltC.mul E.curveA E.curveB a.poly b.poly }
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.some _ _ _ =>
      { point := b.point, poly := CoordRingEltC.mul E.curveA E.curveB a.poly b.poly }
  | WeierstrassCurve.Affine.Point.some _ _ _, WeierstrassCurve.Affine.Point.zero =>
      { point := a.point, poly := CoordRingEltC.mul E.curveA E.curveB a.poly b.poly }
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) _,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) _ =>
      if xa ≠ xb then combineC_distinct E a b xa ya xb yb
      else if ya = -yb then combineC_vertical E a b xa
      else if ya = 0 then combineC_vertical E a b xa
      else combineC_tangent E a b xa ya

/-- Computable `levelInitSingleton`. -/
def levelInitSingletonC (P : ZMod E.q × ZMod E.q) : AccumSC E :=
  { point := ECPoint.affine E P.1 P.2, poly := ⟨CoeffPoly.X - CoeffPoly.C P.1, 0⟩ }

/-- Computable `level0_singletons`. -/
def level0_singletonsC (Ps : List (ZMod E.q × ZMod E.q)) : List (AccumSC E) :=
  Ps.map (levelInitSingletonC E)

/-- Computable `level_step`. -/
def levelStepC : List (AccumSC E) → List (AccumSC E)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => combineC E a b :: levelStepC rest

/-- Computable `iterate`. -/
def iterateC : ℕ → List (AccumSC E) → List (AccumSC E)
  | 0, xs => xs
  | n + 1, xs => if xs.length ≤ 1 then xs else iterateC n (levelStepC E xs)

/-- **Computable singleton line build.** -/
def lineBuildC_singletons (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingEltC E.q :=
  match iterateC E Ps.length (level0_singletonsC E Ps) with
  | [a] => a.poly
  | _ => ⟨1, 0⟩

/-! ## Bridge -/

theorem combineC_toAccum (a b : AccumSC E) :
    (combineC E a b).toAccum = Accum.combine E a.toAccum b.toAccum := by
  rcases a with ⟨pa, Da⟩
  rcases b with ⟨pb, Db⟩
  rcases pa with _ | ⟨xa, ya, ha⟩ <;> rcases pb with _ | ⟨xb, yb, hb⟩
  · simp only [combineC, Accum.combine, AccumSC.toAccum, Accum.combine_oo,
      CoordRingEltC.mul_toCoordRingElt]
  · simp only [combineC, Accum.combine, AccumSC.toAccum, Accum.combine_ol,
      CoordRingEltC.mul_toCoordRingElt]
  · simp only [combineC, Accum.combine, AccumSC.toAccum, Accum.combine_or,
      CoordRingEltC.mul_toCoordRingElt]
  · simp only [combineC, Accum.combine, AccumSC.toAccum]
    by_cases hx : xa ≠ xb
    · rw [if_pos hx, dif_pos hx]
      simp only [combineC_distinct, Accum.combine_distinct,
        CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt,
        CoordRingEltC.chord_toCoordRingElt]
    · rw [if_neg hx, dif_neg hx]
      by_cases hy : ya = -yb
      · rw [if_pos hy, dif_pos hy]
        simp only [combineC_vertical, Accum.combine_vertical,
          CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt]
      · rw [if_neg hy, dif_neg hy]
        by_cases h0 : ya = 0
        · rw [if_pos h0, dif_pos h0]
          simp only [combineC_vertical, Accum.combine_tangent_torsion,
            Accum.combine_vertical,
            CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt]
        · rw [if_neg h0, dif_neg h0]
          simp only [combineC_tangent, Accum.combine_tangent_smooth,
            CoordRingEltC.divLin_toCoordRingElt, CoordRingEltC.mul_toCoordRingElt,
            CoordRingEltC.chord_toCoordRingElt]

theorem levelStepC_toAccum :
    ∀ accs : List (AccumSC E),
      (levelStepC E accs).map AccumSC.toAccum = level_step E (accs.map AccumSC.toAccum)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [levelStepC, level_step, List.map_cons, combineC_toAccum,
      levelStepC_toAccum rest]

theorem iterateC_toAccum (n : ℕ) (accs : List (AccumSC E)) :
    (iterateC E n accs).map AccumSC.toAccum = iterate E n (accs.map AccumSC.toAccum) := by
  induction n generalizing accs with
  | zero => rfl
  | succ n ih =>
    show (if accs.length ≤ 1 then accs else iterateC E n (levelStepC E accs)).map _ =
      if (accs.map AccumSC.toAccum).length ≤ 1 then accs.map AccumSC.toAccum
      else iterate E n (level_step E (accs.map AccumSC.toAccum))
    rw [List.length_map]
    split_ifs
    · rfl
    · rw [ih, levelStepC_toAccum]

theorem level0_singletonsC_toAccum (Ps : List (ZMod E.q × ZMod E.q)) :
    (level0_singletonsC E Ps).map AccumSC.toAccum = level0_singletons E Ps := by
  simp only [level0_singletonsC, level0_singletons, List.map_map]
  refine List.map_congr_left fun P _ => ?_
  simp only [Function.comp, AccumSC.toAccum, levelInitSingletonC, levelInitSingleton,
    CoordRingEltC.toCoordRingElt, CoordRingEltC.toPolynomial_X_sub_C,
    CoeffPoly.toPolynomial_zero]

/-- **Bridge**: the computable singleton build computes
    `LineAccum.lineBuild_singletons`. -/
theorem lineBuildC_singletons_toCoordRingElt (Ps : List (ZMod E.q × ZMod E.q)) :
    (lineBuildC_singletons E Ps).toCoordRingElt = lineBuild_singletons E Ps := by
  have h := iterateC_toAccum E Ps.length (level0_singletonsC E Ps)
  rw [level0_singletonsC_toAccum] at h
  unfold lineBuildC_singletons lineBuild_singletons
  simp only
  rw [← h]
  rcases iterateC E Ps.length (level0_singletonsC E Ps) with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact CoordRingEltC.toCoordRingElt_one E.q
  · rfl
  · exact CoordRingEltC.toCoordRingElt_one E.q

end Divisor.LineAccum
