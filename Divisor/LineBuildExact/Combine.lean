/-
  Divisor/LineBuildExact/Combine.lean — exact line-build invariant and
  its preservation by every `Accum.combine` branch.

  The invariant `ExactInv xs a` records the running sum, the ideal
  factorisation `(a.poly) = ∏_{P ∈ xs} ⟨P⟩ · ⟨−a.point⟩`, and the norm
  degree. Chords, tangents (including flexes), verticals and 2-torsion
  are handled uniformly by `span_chord` / `span_verticalElt`; every
  vertical division is exact because the product ideal lies in
  `(X − x₀)`. There are no root-multiplicity caps, no `Nodup`, and no
  `combineCanFire` side conditions.
-/
import Divisor.OrdP.LineDivisor
import Divisor.SafeSupport

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Divisor.LineAccum.Exact

variable (E : ECSetup)

/-! ## The residue list and the invariant -/

/-- The residue point `−R` as a list (empty at infinity). -/
noncomputable def resList (R : ECPoint E) : List (ZMod E.q × ZMod E.q) :=
  (negCoords E R).toList

@[simp] theorem resList_zero : resList E (0 : ECPoint E) = [] := rfl

@[simp] theorem resList_pointZero :
    resList E (WeierstrassCurve.Affine.Point.zero : ECPoint E) = [] := rfl

theorem pointZero_eq : (WeierstrassCurve.Affine.Point.zero : ECPoint E) = 0 := rfl

theorem resList_some {x y : ZMod E.q} (h : E.toW.toAffine.Nonsingular x y) :
    resList E (WeierstrassCurve.Affine.Point.some _ _ h) = [(x, -y)] := rfl

theorem resList_on (R : ECPoint E) : ∀ P ∈ resList E R, P ∈ E.points := by
  intro P hP
  unfold resList at hP
  exact negCoords_mem_points_of_some E (Option.mem_toList.mp hP)

theorem resList_affine {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    resList E (ECPoint.affine E P.1 P.2) = [(P.1, -P.2)] := by
  rw [ECPoint.affine_of_nonsingular E (nonsing_of_mem E hP), resList_some]

theorem affine_ne_zero {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    ECPoint.affine E P.1 P.2 ≠ 0 := by
  rw [ECPoint.affine_of_nonsingular E (nonsing_of_mem E hP)]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- **Exact line-build invariant**: running sum, ideal factorisation with
the residue `−a.point`, and norm degree. -/
def ExactInv (xs : List (ZMod E.q × ZMod E.q)) (a : Accum E) : Prop :=
  a.point = sumOnE E xs ∧
  Ideal.span {a.poly.toCoordinateRing E} = listIdeal E (xs ++ resList E a.point) ∧
  (normPoly E a.poly).natDegree = xs.length + (if a.point = 0 then 0 else 1)

theorem ExactInv.not_both_zero {xs : List (ZMod E.q × ZMod E.q)} {a : Accum E}
    (h : ExactInv E xs a) : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) :=
  not_both_zero_of_span_ne_zero E _ (h.2.1 ▸ listIdeal_ne_zero E _)

/-- The level-0 singleton `(X − x_P, P)` satisfies the invariant. -/
theorem exactInv_levelInitSingleton {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    ExactInv E [P] (levelInitSingleton E P) := by
  refine ⟨?_, ?_, ?_⟩
  · show ECPoint.affine E P.1 P.2 = _
    rw [sumOnE_cons E hP, sumOnE_nil, add_zero, ECPoint.affine_eq_affineOfMem E hP]
  · show Ideal.span {(verticalElt E P.1).toCoordinateRing E} = _
    rw [span_verticalElt E hP]
    show _ = listIdeal E ([P] ++ resList E (ECPoint.affine E P.1 P.2))
    rw [resList_affine E hP]
    rfl
  · show (normPoly E (verticalElt E P.1)).natDegree =
      [P].length + (if ECPoint.affine E P.1 P.2 = 0 then 0 else 1)
    rw [if_neg (affine_ne_zero E hP), normPoly_eq]
    simp [verticalElt]

/-! ## Degree and exact-division helpers -/

theorem natDegree_normPoly_mul (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0)) (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0)) :
    (normPoly E (mulCoordRingElt E D₁ D₂)).natDegree =
      (normPoly E D₁).natDegree + (normPoly E D₂).natDegree := by
  rw [normPoly_mul_eq, Polynomial.natDegree_mul (normPoly_ne_zero E D₁ h₁)
    (normPoly_ne_zero E D₂ h₂)]

/-- **Exact vertical division**: from `(D) = (X − x₀) · J` get
`(D.divLin x₀) = J`, and the norm degree drops by two. -/
theorem divLin_exact (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (J : Ideal E.toW.toAffine.CoordinateRing) (hJ : J ≠ 0)
    (hspan : Ideal.span {D.toCoordinateRing E} = CoordinateRing.XIdeal E.toW.toAffine x₀ * J) :
    Ideal.span {(D.divLin x₀).toCoordinateRing E} = J ∧
      (normPoly E D).natDegree = (normPoly E (D.divLin x₀)).natDegree + 2 := by
  have hle : Ideal.span {D.toCoordinateRing E} ≤ CoordinateRing.XIdeal E.toW.toAffine x₀ :=
    hspan ▸ Ideal.mul_le_left
  have h1 := span_eq_XIdeal_mul_divLin E D x₀ hle
  rw [hspan] at h1
  refine ⟨(mul_left_cancel₀ (XIdeal_ne_zero E x₀) h1).symm, ?_⟩
  obtain ⟨ha, hb⟩ := twin_of_mem_XIdeal E D x₀ (hle (Ideal.subset_span rfl))
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := by
    apply not_both_zero_of_span_ne_zero
    rw [hspan]
    exact mul_ne_zero (XIdeal_ne_zero E x₀) hJ
  have hD' := divLin_not_both_zero E D hD ha hb
  rw [normPoly_divLin_factor E D ha hb, Polynomial.natDegree_mul
    (pow_ne_zero _ (X_sub_C_ne_zero x₀)) (normPoly_ne_zero E _ hD'),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
  ring

/-! ## The chord / tangent / vertical branches -/

/-- The chord branch at the ideal and degree level. -/
theorem span_combine_line (a b : Accum E) {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2))
    (La Lb : List (ZMod E.q × ZMod E.q))
    (ha : Ideal.span {a.poly.toCoordinateRing E} = listIdeal E (La ++ [(A.1, -A.2)]))
    (hb : Ideal.span {b.poly.toCoordinateRing E} = listIdeal E (Lb ++ [(B.1, -B.2)]))
    (na nb : ℕ) (hna : (normPoly E a.poly).natDegree = na + 1)
    (hnb : (normPoly E b.poly).natDegree = nb + 1) :
    let prod := mulCoordRingElt E (mulCoordRingElt E (chordCoordRingElt E A B) a.poly) b.poly
    Ideal.span {((prod.divLin A.1).divLin B.1).toCoordinateRing E} =
        listIdeal E (La ++ Lb ++ [chordThird E A B]) ∧
      (normPoly E ((prod.divLin A.1).divLin B.1)).natDegree = na + nb + 1 := by
  intro prod
  have hXa := xIdeal_eq_mul E hA
  have hXb := xIdeal_eq_mul E hB
  have haD := not_both_zero_of_span_ne_zero E _ (ha ▸ listIdeal_ne_zero E _)
  have hbD := not_both_zero_of_span_ne_zero E _ (hb ▸ listIdeal_ne_zero E _)
  have hlD := not_both_zero_of_span_ne_zero E _
    (span_chord E hA hB hxy ▸ listIdeal_ne_zero E _)
  have hprod : Ideal.span {prod.toCoordinateRing E} =
      CoordinateRing.XIdeal E.toW.toAffine A.1 *
        (CoordinateRing.XIdeal E.toW.toAffine B.1 * listIdeal E (La ++ Lb ++ [chordThird E A B])) := by
    simp only [prod, span_mulCoordRingElt, span_chord E hA hB hxy, ha, hb, hXa, hXb,
      listIdeal_append, listIdeal_cons, listIdeal_nil, ptIdeal]
    ring
  have hdprod : (normPoly E prod).natDegree = na + nb + 5 := by
    rw [natDegree_normPoly_mul E _ _ (mulCoordRingElt_ne_zero E _ _ hlD haD) hbD,
      natDegree_normPoly_mul E _ _ hlD haD, hna, hnb, chordCoordRingElt_eq_lineElt E hA hB hxy,
      natDegree_normPoly_lineElt]
    ring
  obtain ⟨h1, d1⟩ := divLin_exact E prod A.1 _
    (mul_ne_zero (XIdeal_ne_zero E _) (listIdeal_ne_zero E _)) hprod
  obtain ⟨h2, d2⟩ := divLin_exact E _ B.1 _ (listIdeal_ne_zero E _) h1
  exact ⟨h2, by omega⟩

/-- The vertical branch (`B = −A`, including 2-torsion `A = B`). -/
theorem span_combine_vertical (a b : Accum E) {A : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (La Lb : List (ZMod E.q × ZMod E.q))
    (ha : Ideal.span {a.poly.toCoordinateRing E} = listIdeal E (La ++ [(A.1, -A.2)]))
    (hb : Ideal.span {b.poly.toCoordinateRing E} = listIdeal E (Lb ++ [A]))
    (na nb : ℕ) (hna : (normPoly E a.poly).natDegree = na + 1)
    (hnb : (normPoly E b.poly).natDegree = nb + 1) :
    Ideal.span {((mulCoordRingElt E a.poly b.poly).divLin A.1).toCoordinateRing E} =
        listIdeal E (La ++ Lb) ∧
      (normPoly E ((mulCoordRingElt E a.poly b.poly).divLin A.1)).natDegree = na + nb := by
  have hXa := xIdeal_eq_mul E hA
  have haD := not_both_zero_of_span_ne_zero E _ (ha ▸ listIdeal_ne_zero E _)
  have hbD := not_both_zero_of_span_ne_zero E _ (hb ▸ listIdeal_ne_zero E _)
  have hprod : Ideal.span {(mulCoordRingElt E a.poly b.poly).toCoordinateRing E} =
      CoordinateRing.XIdeal E.toW.toAffine A.1 * listIdeal E (La ++ Lb) := by
    simp only [span_mulCoordRingElt, ha, hb, hXa, listIdeal_append, listIdeal_cons,
      listIdeal_nil, ptIdeal]
    ring
  obtain ⟨h1, d1⟩ := divLin_exact E _ A.1 _ (listIdeal_ne_zero E _) hprod
  refine ⟨h1, ?_⟩
  rw [natDegree_normPoly_mul E _ _ haD hbD, hna, hnb] at d1
  omega

/-! ## Coordinates of the chord and tangent residues -/

theorem slope_eq_slopeOf {xa ya xb yb : ZMod E.q} (hx : xa ≠ xb) :
    E.toW.toAffine.slope xa xb ya yb = slopeOf xa ya xb yb := by
  rw [slope_of_X_ne hx, slopeOf, div_eq_mul_inv, ← neg_sub yb ya, ← neg_sub xb xa, inv_neg,
    neg_mul_neg]

theorem chordThird_distinct {xa ya xb yb : ZMod E.q} (hx : xa ≠ xb) :
    chordThird E (xa, ya) (xb, yb) =
      (slopeOf xa ya xb yb ^ 2 - xa - xb,
       slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb) +
         (ya - slopeOf xa ya xb yb * xa)) := by
  simp only [chordThird, slope_eq_slopeOf E hx, Affine.addX, Affine.negAddY,
    ECSetup.toW_a₁, ECSetup.toW_a₂, Prod.mk.injEq]
  constructor <;> ring

theorem chordThird_tangent {xa ya : ZMod E.q} (hy : ya ≠ 0) :
    chordThird E (xa, ya) (xa, ya) =
      (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa,
       (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ *
          (((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa) +
         (ya - (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ * xa)) := by
  have hne : ya ≠ E.toW.toAffine.negY xa ya := by
    rw [toW_negY]; intro h; exact hy ((neg_snd_eq_self_iff E ya).mp h.symm)
  have hs : E.toW.toAffine.slope xa xa ya ya = (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ := by
    rw [slope_of_Y_ne rfl hne, toW_negY]
    simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
    have h2 : (2 : ZMod E.q) * ya ≠ 0 := mul_ne_zero (two_ne_zero_zmod E) hy
    field_simp
    ring
  simp only [chordThird, hs, Affine.addX, Affine.negAddY, ECSetup.toW_a₁, ECSetup.toW_a₂,
    Prod.mk.injEq]
  constructor <;> ring

/-! ## The dispatcher -/

private theorem resList_neg_affine {T : ZMod E.q × ZMod E.q} (hT : T ∈ E.points) :
    resList E (ECPoint.affine E T.1 (-T.2)) = [T] := by
  have h := resList_affine E (neg_snd_mem_points E hT)
  simp only [neg_neg] at h
  exact h

private theorem neg_affine_ne_zero {T : ZMod E.q × ZMod E.q} (hT : T ∈ E.points) :
    ECPoint.affine E T.1 (-T.2) ≠ 0 :=
  affine_ne_zero E (neg_snd_mem_points E hT)

/-- **Every `Accum.combine` branch preserves `ExactInv`**, with no side
conditions: chords (any endpoints, any third point), tangents (flexes
included), verticals, 2-torsion, and the zero-running-sum branches. -/
theorem exactInv_combine {xs ys : List (ZMod E.q × ZMod E.q)} {a b : Accum E}
    (ha : ExactInv E xs a) (hb : ExactInv E ys b) :
    ExactInv E (xs ++ ys) (Accum.combine E a b) := by
  have haD := ha.not_both_zero
  have hbD := hb.not_both_zero
  obtain ⟨hpa_sum, hsa, hda⟩ := ha
  obtain ⟨hpb_sum, hsb, hdb⟩ := hb
  have hpt : (Accum.combine E a b).point = sumOnE E (xs ++ ys) := by
    rw [combine_point_eq_pointCombine, pointCombine_eq_add, sumOnE_append, hpa_sum, hpb_sum]
  refine ⟨hpt, ?_⟩
  rw [List.length_append]
  rcases hpa : a.point with _ | ⟨xa, ya, hns_a⟩ <;>
    rcases hpb : b.point with _ | ⟨xb, yb, hns_b⟩ <;>
    rw [hpa] at hsa hda <;> rw [hpb] at hsb hdb
  · -- both at infinity
    have hc : Accum.combine E a b = Accum.combine_oo E a b := by
      unfold Accum.combine; rw [hpa, hpb]
    rw [hc]
    refine ⟨?_, ?_⟩
    · show Ideal.span {(mulCoordRingElt E a.poly b.poly).toCoordinateRing E} =
        listIdeal E (xs ++ ys ++ resList E 0)
      rw [span_mulCoordRingElt, hsa, hsb]; simp
    · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        _ + (if (0 : ECPoint E) = 0 then 0 else 1)
      rw [natDegree_normPoly_mul E _ _ haD hbD, hda, hdb, if_pos (pointZero_eq E), if_pos rfl]
      omega
  · -- only `a` at infinity
    have hc : Accum.combine E a b = Accum.combine_ol E a b := by
      unfold Accum.combine; rw [hpa, hpb]
    rw [hc]
    refine ⟨?_, ?_⟩
    · show Ideal.span {(mulCoordRingElt E a.poly b.poly).toCoordinateRing E} =
        listIdeal E (xs ++ ys ++ resList E b.point)
      rw [span_mulCoordRingElt, hsa, hsb, hpb]; simp
    · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        _ + (if b.point = 0 then 0 else 1)
      rw [natDegree_normPoly_mul E _ _ haD hbD, hda, hdb, hpb, if_pos (pointZero_eq E),
        if_neg (WeierstrassCurve.Affine.Point.some_ne_zero hns_b)]
      omega
  · -- only `b` at infinity
    have hc : Accum.combine E a b = Accum.combine_or E a b := by
      unfold Accum.combine; rw [hpa, hpb]
    rw [hc]
    refine ⟨?_, ?_⟩
    · show Ideal.span {(mulCoordRingElt E a.poly b.poly).toCoordinateRing E} =
        listIdeal E (xs ++ ys ++ resList E a.point)
      rw [span_mulCoordRingElt, hsa, hsb, hpa]; simp only [listIdeal_append, resList_pointZero,
        listIdeal_nil, mul_one]; ring
    · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        _ + (if a.point = 0 then 0 else 1)
      rw [natDegree_normPoly_mul E _ _ haD hbD, hda, hdb, hpa, if_pos (pointZero_eq E),
        if_neg (WeierstrassCurve.Affine.Point.some_ne_zero hns_a)]
      omega
  · -- both affine
    have hA : (xa, ya) ∈ E.points :=
      E.hComplete xa ya ((E.equation_iff xa ya).mp ((E.equation_iff_nonsingular).mpr hns_a))
    have hB : (xb, yb) ∈ E.points :=
      E.hComplete xb yb ((E.equation_iff xb yb).mp ((E.equation_iff_nonsingular).mpr hns_b))
    rw [resList_some] at hsa hsb
    simp only [reduceCtorEq, if_false] at hda hdb
    by_cases hxx : xa ≠ xb
    · have hc : Accum.combine E a b = Accum.combine_distinct E a b xa ya xb yb hxx := by
        unfold Accum.combine; rw [hpa, hpb]; simp [hxx]
      have hxy : ¬ ((xa, ya).1 = (xb, yb).1 ∧ (xa, ya).2 = -(xb, yb).2) := fun h => hxx h.1
      have hT := chordThird_mem E hA hB hxy
      obtain ⟨hs, hd⟩ := span_combine_line E a b hA hB hxy xs ys hsa hsb _ _ hda hdb
      have hpt' : (Accum.combine_distinct E a b xa ya xb yb hxx).point =
          ECPoint.affine E (chordThird E (xa, ya) (xb, yb)).1
            (-(chordThird E (xa, ya) (xb, yb)).2) := by
        rw [chordThird_distinct E hxx]; rfl
      rw [hc, hpt', resList_neg_affine E hT, if_neg (neg_affine_ne_zero E hT)]
      exact ⟨hs, hd⟩
    · have hxeq : xa = xb := not_not.mp hxx
      subst hxeq
      by_cases hyy : ya = -yb
      · have hc : Accum.combine E a b = Accum.combine_vertical E a b xa := by
          unfold Accum.combine; rw [hpa, hpb]; simp [hyy]
        have hyb : yb = -ya := by rw [hyy, neg_neg]
        subst hyb
        rw [neg_neg] at hsb
        obtain ⟨hs, hd⟩ := span_combine_vertical E a b hA xs ys hsa hsb _ _ hda hdb
        rw [hc]
        refine ⟨?_, ?_⟩
        · show Ideal.span {((mulCoordRingElt E a.poly b.poly).divLin xa).toCoordinateRing E} =
            listIdeal E (xs ++ ys ++ resList E 0)
          rw [hs]; simp
        · show (normPoly E ((mulCoordRingElt E a.poly b.poly).divLin xa)).natDegree =
            _ + (if (0 : ECPoint E) = 0 then 0 else 1)
          rw [hd]; simp
      · have hyeq : ya = yb := by
          rcases ECPoints_same_x_y_eq_or_neg E hA hB with h | h
          · exact h
          · exact absurd h hyy
        subst hyeq
        have hy0 : ya ≠ 0 := fun h => hyy (by rw [h, neg_zero])
        have hc : Accum.combine E a b = Accum.combine_tangent_smooth E a b xa ya hy0 := by
          unfold Accum.combine; rw [hpa, hpb]; simp [hyy, hy0]
        have hxy : ¬ ((xa, ya).1 = (xa, ya).1 ∧ (xa, ya).2 = -(xa, ya).2) :=
          fun h => hyy h.2
        have hT := chordThird_mem E hA hA hxy
        obtain ⟨hs, hd⟩ := span_combine_line E a b hA hA hxy xs ys hsa hsb _ _ hda hdb
        have hpt' : (Accum.combine_tangent_smooth E a b xa ya hy0).point =
            ECPoint.affine E (chordThird E (xa, ya) (xa, ya)).1
              (-(chordThird E (xa, ya) (xa, ya)).2) := by
          rw [chordThird_tangent E hy0]; rfl
        rw [hc, hpt', resList_neg_affine E hT, if_neg (neg_affine_ne_zero E hT)]
        exact ⟨hs, hd⟩

/-! ## Bridge to `AccumInvStrong` -/

theorem on_append {xs ys : List (ZMod E.q × ZMod E.q)}
    (hxs : ∀ P ∈ xs, P ∈ E.points) (hys : ∀ P ∈ ys, P ∈ E.points) :
    ∀ P ∈ xs ++ ys, P ∈ E.points :=
  fun P hP => (List.mem_append.mp hP).elim (hxs P) (hys P)

/-- The strong-invariant target is the multiplicity in `xs ++ resList`. -/
theorem target_eq_count (xs : List (ZMod E.q × ZMod E.q)) (R : ECPoint E)
    (P : ZMod E.q × ZMod E.q) :
    target E xs R P = (xs ++ resList E R).count P := by
  rw [target_def, List.count_append]
  congr 1
  unfold resList
  rcases negCoords E R with _ | Q
  · simp
  · by_cases h : Q = P
    · subst h; simp
    · simp [h]

/-- `ExactInv` gives `AccumInvStrong`, with equality in the pointwise bound. -/
theorem accumInvStrong_of_exactInv {xs : List (ZMod E.q × ZMod E.q)} {a : Accum E}
    (hxs : ∀ P ∈ xs, P ∈ E.points) (h : ExactInv E xs a) : AccumInvStrong E xs a := by
  refine ⟨h.1, fun P hP => ?_, h.2.2⟩
  rw [localMult_eq_ordAt, ordAt_eq_count_of_span_eq_listIdeal E _ _
    (on_append E hxs (resList_on E a.point)) h.2.1 hP,
    target_eq_count]

/-- A nonzero `AccumInvStrong` accumulator already satisfies `ExactInv`:
the pointwise bound plus the degree identity force exact orders and
splitting, hence the ideal factorisation. -/
theorem exactInv_of_accumInvStrong {xs : List (ZMod E.q × ZMod E.q)} {a : Accum E}
    (hxs : ∀ P ∈ xs, P ∈ E.points) (h : AccumInvStrong E xs a)
    (hD : ¬ (a.poly.a = 0 ∧ a.poly.b = 0)) : ExactInv E xs a := by
  classical
  refine ⟨h.1, ?_, h.2.2⟩
  have hord : ∀ P ∈ E.points, ordAt E a.poly P = (xs ++ resList E a.point).count P := by
    intro P hP
    rw [← localMult_eq_ordAt, localMult_eq_target_of_accumInvStrong E xs a hxs h hD P hP,
      target_eq_count]
  have hsum : ∑ P ∈ E.points, ordAt E a.poly P = (normPoly E a.poly).natDegree := by
    rw [← targetMass_eq_natDegree_of_accumInvStrong E xs a hxs h, targetMass]
    exact Finset.sum_congr rfl fun P hP => by rw [hord P hP, target_eq_count]
  have hL : ∀ P ∈ xs ++ resList E a.point, P ∈ E.points :=
    on_append E hxs (resList_on E a.point)
  rw [span_toCoordinateRing_eq_prod E a.poly hD (splitsOnE_of_sum_ordAt_eq E a.poly hD hsum),
    listIdeal, Finset.prod_list_map_count,
    Finset.prod_attach E.points (fun P => CoordinateRing.XYIdeal E.toW.toAffine P.1
      (Polynomial.C P.2) ^ ordAt E a.poly P)]
  rw [← Finset.prod_subset (s₁ := (xs ++ resList E a.point).toFinset)
    (fun P hP => hL P (List.mem_toFinset.mp hP))
    (fun P hP hPn => by
      rw [hord P hP, List.count_eq_zero_of_not_mem (by simpa using hPn), pow_zero])]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [hord P (hL P (List.mem_toFinset.mp hP)), count_beq_eq]
  rfl

/-- **Exact `AccumInvStrong` preservation by every `Accum.combine` branch**:
no root-multiplicity caps, no `Nodup`, no `combineCanFire`. -/
theorem accumInvStrong_combine_exact {xs ys : List (ZMod E.q × ZMod E.q)} {a b : Accum E}
    (hxs : ∀ P ∈ xs, P ∈ E.points) (hys : ∀ P ∈ ys, P ∈ E.points)
    (ha : AccumInvStrong E xs a) (hb : AccumInvStrong E ys b)
    (haD : ¬ (a.poly.a = 0 ∧ a.poly.b = 0)) (hbD : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    AccumInvStrong E (xs ++ ys) (Accum.combine E a b) ∧
      ¬ ((Accum.combine E a b).poly.a = 0 ∧ (Accum.combine E a b).poly.b = 0) := by
  have h := exactInv_combine E (exactInv_of_accumInvStrong E hxs ha haD)
    (exactInv_of_accumInvStrong E hys hb hbD)
  exact ⟨accumInvStrong_of_exactInv E (on_append E hxs hys) h, h.not_both_zero⟩

end Divisor.LineAccum.Exact
