/-
  Divisor/OrdP/LineDivisor.lean — exact divisors of lines and exact
  vertical division, via point-ideal factorisations.

  * `listIdeal`: the ideal `∏_{P ∈ xs} ⟨X − x_P, Y − y_P⟩` of a list of
    rational points (repetitions allowed).
  * `ordAt_eq_count_of_span_eq_listIdeal`: if `(D) = listIdeal xs` then
    `ordAt E D Q = xs.count Q` at every rational `Q`.
  * `splitsOnE_of_sum_ordAt_eq`: full rational order mass forces
    `splitsOnE`.
  * Vertical lines: `ordAt_verticalElt` (1 per sheet, 2 at 2-torsion).
  * Exact division: `ordAt_divLin`, `twin_of_ordAt_ge_vertical`,
    `span_eq_XIdeal_mul_divLin`.
  * Non-vertical lines: `span_chord`, `ordAt_chord`, `normPoly_chord`.
    One statement covers chords, tangents, flexes and 2-torsion
    endpoints; it is mathlib's `XYIdeal_mul_XYIdeal` in our shape.
-/
import Divisor.OrdP.Units
import Divisor.OrdP.LocalRing

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace Divisor

variable (E : ECSetup)

/-! ## Point ideals of lists -/

/-- The maximal ideal `⟨X − x_P, Y − y_P⟩` of a point, as an ideal. -/
noncomputable def ptIdeal (P : ZMod E.q × ZMod E.q) :
    Ideal E.toW.toAffine.CoordinateRing :=
  CoordinateRing.XYIdeal E.toW.toAffine P.1 (C P.2)

/-- The product of the point ideals of a list (with multiplicity). -/
noncomputable def listIdeal (xs : List (ZMod E.q × ZMod E.q)) :
    Ideal E.toW.toAffine.CoordinateRing :=
  (xs.map (ptIdeal E)).prod

@[simp] theorem listIdeal_nil : listIdeal E [] = 1 := rfl

@[simp] theorem listIdeal_cons (P : ZMod E.q × ZMod E.q) (xs : List (ZMod E.q × ZMod E.q)) :
    listIdeal E (P :: xs) = ptIdeal E P * listIdeal E xs := by
  simp [listIdeal]

@[simp] theorem listIdeal_append (xs ys : List (ZMod E.q × ZMod E.q)) :
    listIdeal E (xs ++ ys) = listIdeal E xs * listIdeal E ys := by
  simp [listIdeal]

theorem ptIdeal_ne_zero (P : ZMod E.q × ZMod E.q) : ptIdeal E P ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot]
  exact TauCeti.WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot _ _

theorem listIdeal_ne_zero (xs : List (ZMod E.q × ZMod E.q)) : listIdeal E xs ≠ 0 := by
  induction xs with
  | nil => simp
  | cons P xs ih => rw [listIdeal_cons]; exact mul_ne_zero (ptIdeal_ne_zero E P) ih

/-- A nonzero principal ideal has a nonzero generator. -/
theorem not_both_zero_of_span_ne_zero (D : CoordRingElt E.q)
    (h : Ideal.span {D.toCoordinateRing E} ≠ 0) : ¬ (D.a = 0 ∧ D.b = 0) := by
  rintro ⟨ha, hb⟩
  apply h
  rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot,
    CoordRingElt.toCoordinateRing_eq_smul_basis, ha, hb]
  simp

theorem span_mulCoordRingElt (D₁ D₂ : CoordRingElt E.q) :
    Ideal.span {(mulCoordRingElt E D₁ D₂).toCoordinateRing E} =
      Ideal.span {D₁.toCoordinateRing E} * Ideal.span {D₂.toCoordinateRing E} := by
  rw [toCoordinateRing_mul, Ideal.span_singleton_mul_span_singleton]

/-! ## Orders from a list-ideal factorisation -/

/-- The two `BEq` instances on point pairs give the same `List.count`. -/
theorem count_beq_eq (xs : List (ZMod E.q × ZMod E.q)) (P : ZMod E.q × ZMod E.q) :
    @List.count _ instBEqProd P xs = @List.count _ instBEqOfDecidableEq P xs := by
  congr 1
  exact lawful_beq_subsingleton _ _

/-- `v_Q`-count of a finite product of rational point ideals. -/
theorem count_prod_ptIdeal (s : Finset (ZMod E.q × ZMod E.q)) (f : ZMod E.q × ZMod E.q → ℕ)
    (hs : ∀ P ∈ s, P ∈ E.points) {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    FractionalIdeal.count E.toW.toAffine.FunctionField (E.pointPrime hQ)
      ((∏ P ∈ s, ptIdeal E P ^ f P : Ideal E.toW.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors E.toW.toAffine.CoordinateRing)
          E.toW.toAffine.FunctionField) = if Q ∈ s then (f Q : ℤ) else 0 := by
  classical
  rw [show ((∏ P ∈ s, ptIdeal E P ^ f P : Ideal E.toW.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors E.toW.toAffine.CoordinateRing)
          E.toW.toAffine.FunctionField) =
      ∏ P ∈ s, ((ptIdeal E P : FractionalIdeal
          (nonZeroDivisors E.toW.toAffine.CoordinateRing)
            E.toW.toAffine.FunctionField) ^ f P) from
      (map_prod (FractionalIdeal.coeIdealHom _ _) _ _).trans
        (Finset.prod_congr rfl fun P _ => map_pow _ _ _),
    FractionalIdeal.count_prod]
  · have hterm : ∀ P ∈ s,
        FractionalIdeal.count E.toW.toAffine.FunctionField (E.pointPrime hQ)
          ((ptIdeal E P : FractionalIdeal (nonZeroDivisors E.toW.toAffine.CoordinateRing)
            E.toW.toAffine.FunctionField) ^ f P) =
          if P = Q then (f P : ℤ) else 0 := by
      intro P hP
      have hPon := hs P hP
      rw [FractionalIdeal.count_pow,
        show ptIdeal E P = (E.pointPrime hPon).asIdeal from rfl,
        FractionalIdeal.count_maximal]
      by_cases hPQ : P = Q
      · subst hPQ; simp
      · rw [if_neg (fun h => hPQ (E.pointPrime_injective hPon hQ h)), if_neg hPQ, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  · intro P _
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (by
      rw [← Ideal.zero_eq_bot]; exact ptIdeal_ne_zero E P))

/-- **Orders from the ideal.** If `(D)` is the point-ideal product of an
on-curve list, the order of `D` at a rational point is its multiplicity
in the list. -/
theorem ordAt_eq_count_of_span_eq_listIdeal (D : CoordRingElt E.q)
    (xs : List (ZMod E.q × ZMod E.q)) (hxs : ∀ P ∈ xs, P ∈ E.points)
    (h : Ideal.span {D.toCoordinateRing E} = listIdeal E xs)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ordAt E D Q = xs.count Q := by
  have hne : Ideal.span {D.toCoordinateRing E} ≠ 0 := h ▸ listIdeal_ne_zero E xs
  have hD := not_both_zero_of_span_ne_zero E D hne
  have hc := FractionalIdeal.count_coe E.toW.toAffine.FunctionField (E.pointPrime hQ) hne
  rw [count_pointPrime_eq_ordAt E D hQ hD, h, listIdeal, Finset.prod_list_map_count,
    count_prod_ptIdeal E _ _ (fun P hP => hxs P (List.mem_toFinset.mp hP)) hQ] at hc
  split_ifs at hc with hmem
  · rw [count_beq_eq]; exact_mod_cast hc.symm
  · rw [List.mem_toFinset] at hmem
    rw [List.count_eq_zero_of_not_mem hmem]
    exact_mod_cast hc.symm

/-- Total rational order of a list-ideal generator is the list length. -/
theorem sum_ordAt_eq_length_of_span_eq_listIdeal (D : CoordRingElt E.q)
    (xs : List (ZMod E.q × ZMod E.q)) (hxs : ∀ P ∈ xs, P ∈ E.points)
    (h : Ideal.span {D.toCoordinateRing E} = listIdeal E xs) :
    ∑ P ∈ E.points, ordAt E D P = xs.length := by
  rw [Finset.sum_congr rfl fun P hP => ordAt_eq_count_of_span_eq_listIdeal E D xs hxs h hP]
  rw [← Finset.sum_subset (s₁ := xs.toFinset) (fun P hP => hxs P (List.mem_toFinset.mp hP))
      (fun P _ hP => List.count_eq_zero_of_not_mem (by simpa using hP))]
  simp only [count_beq_eq]
  exact List.sum_toFinset_count_eq_length xs

/-- **Splitting from full order mass**: if the rational orders of `D` add
up to the degree of its norm, then `D` splits over `E`. -/
theorem splitsOnE_of_sum_ordAt_eq (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hsum : ∑ P ∈ E.points, ordAt E D P = (normPoly E D).natDegree) :
    splitsOnE E D := by
  classical
  have hN0 := normPoly_ne_zero E D hD
  have hfibLe : ∀ x₀ ∈ (Finset.univ : Finset (ZMod E.q)),
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P) ≤
        rootMultiplicity x₀ (normPoly E D) :=
    fun x₀ _ => sum_ordAt_fst_eq_le E D hD x₀
  have hroots : ∑ P ∈ E.points, ordAt E D P ≤ Multiset.card (normPoly E D).roots := by
    rw [sum_E_points_eq_sum_fiberwise E, ← sum_rootMultiplicity_eq_card_roots E]
    exact Finset.sum_le_sum hfibLe
  have hc := Polynomial.card_roots' (normPoly E D)
  refine ⟨by unfold normPoly_splits_over_Fq; omega, ?_⟩
  intro α hα
  have hfib : ∀ x₀ ∈ (Finset.univ : Finset (ZMod E.q)),
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P) =
        rootMultiplicity x₀ (normPoly E D) := by
    rw [← Finset.sum_eq_sum_iff_of_le hfibLe, ← sum_E_points_eq_sum_fiberwise E,
      sum_rootMultiplicity_eq_card_roots E]
    omega
  have hpos : 0 < rootMultiplicity α (normPoly E D) :=
    (Polynomial.rootMultiplicity_pos hN0).mpr ((Polynomial.mem_roots hN0).mp hα)
  rw [← hfib α (Finset.mem_univ _)] at hpos
  obtain ⟨P, hP, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter] at hP
  exact ⟨P.2, by rw [← hP.2]; exact hP.1⟩

/-! ## Vertical lines and exact division -/

/-- The vertical line `X − x₀` as a `CoordRingElt`. -/
noncomputable def verticalElt (x₀ : ZMod E.q) : CoordRingElt E.q :=
  { a := X - C x₀, b := 0 }

theorem verticalElt_not_both_zero (x₀ : ZMod E.q) :
    ¬ ((verticalElt E x₀).a = 0 ∧ (verticalElt E x₀).b = 0) :=
  fun h => X_sub_C_ne_zero x₀ h.1

theorem verticalElt_toCoordinateRing (x₀ : ZMod E.q) :
    (verticalElt E x₀).toCoordinateRing E = CoordinateRing.XClass E.toW.toAffine x₀ := by
  unfold verticalElt CoordRingElt.toCoordinateRing CoordRingElt.toBivar
    CoordinateRing.XClass
  simp

/-- `(X − x_P) = ⟨P⟩ · ⟨−P⟩`. -/
theorem span_verticalElt {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    Ideal.span {(verticalElt E P.1).toCoordinateRing E} =
      listIdeal E [P, (P.1, -P.2)] := by
  rw [verticalElt_toCoordinateRing, ← CoordinateRing.XIdeal, xIdeal_eq_mul E hP]
  simp [ptIdeal, mul_comm]

theorem neg_snd_eq_self_iff (y : ZMod E.q) : -y = y ↔ y = 0 := by
  constructor
  · intro h
    have h2 : (2 : ZMod E.q) * y = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero_zmod E)
  · rintro rfl; simp

/-- **Order of a vertical line**: one on each sheet of its fiber, two at a
2-torsion point, zero elsewhere. -/
theorem ordAt_verticalElt (x₀ : ZMod E.q) {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ordAt E (verticalElt E x₀) Q =
      if Q.1 = x₀ then (if Q.2 = 0 then 2 else 1) else 0 := by
  classical
  split_ifs with hx hy
  · subst hx
    have hns := neg_snd_mem_points E hQ
    rw [ordAt_eq_count_of_span_eq_listIdeal E _ _ (by simp [hQ, hns]) (span_verticalElt E hQ) hQ]
    obtain ⟨x, y⟩ := Q
    simp only at hy
    subst hy
    simp
  · subst hx
    have hns := neg_snd_mem_points E hQ
    rw [ordAt_eq_count_of_span_eq_listIdeal E _ _ (by simp [hQ, hns]) (span_verticalElt E hQ) hQ]
    obtain ⟨x, y⟩ := Q
    simp only at hy
    have hne : (x, y) ≠ (x, -y) := by
      intro h
      exact hy ((neg_snd_eq_self_iff E y).mp (congrArg Prod.snd h).symm)
    simp [hne]
  · have hpos := ordAt_pos_iff_zero E (verticalElt E x₀) (verticalElt_not_both_zero E x₀) Q hQ
    have hev : (verticalElt E x₀).eval Q.1 Q.2 ≠ 0 := by
      simp [verticalElt, CoordRingElt.eval, sub_eq_zero, hx]
    by_contra hne
    exact hev (hpos.mp (Nat.pos_of_ne_zero hne))

/-- **`ordAt` under exact vertical division**: when both components vanish
at `x₀`, `D = (X − x₀) · D.divLin x₀` and orders add. -/
theorem ordAt_divLin (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) {x₀ : ZMod E.q}
    (ha : D.a.eval x₀ = 0) (hb : D.b.eval x₀ = 0)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ordAt E D Q = ordAt E (verticalElt E x₀) Q + ordAt E (D.divLin x₀) Q := by
  have hD' := divLin_not_both_zero E D hD ha hb
  have heq : D = mulCoordRingElt E (verticalElt E x₀) (D.divLin x₀) := by
    apply toCoordinateRing_injective E
    rw [toCoordinateRing_mul, verticalElt_toCoordinateRing,
      toCoordinateRing_divLin_of_twin E D ha hb]
  conv_lhs => rw [heq]
  exact ordAt_mul E _ _ (verticalElt_not_both_zero E x₀) hD' hQ

/-- Membership in the vertical ideal forces both components to vanish. -/
theorem twin_of_mem_XIdeal (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (h : D.toCoordinateRing E ∈ CoordinateRing.XIdeal E.toW.toAffine x₀) :
    D.a.eval x₀ = 0 ∧ D.b.eval x₀ = 0 := by
  rw [CoordinateRing.XIdeal, Ideal.mem_span_singleton'] at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq g
  rw [CoordinateRing.XClass, CoordinateRing.smul_basis_mul_C,
    CoordRingElt.toCoordinateRing_eq_smul_basis, ← sub_eq_zero] at hg
  have h' : (p * (X - C x₀) - D.a) • (1 : E.toW.toAffine.CoordinateRing) +
      (q * (X - C x₀) - -D.b) • CoordinateRing.mk E.toW.toAffine Polynomial.X = 0 := by
    rw [← hg, sub_smul, sub_smul]; abel
  obtain ⟨ha, hb⟩ := CoordinateRing.smul_basis_eq_zero h'
  have ha' : D.a = p * (X - C x₀) := (sub_eq_zero.mp ha).symm
  have hb' : D.b = -(q * (X - C x₀)) := by linear_combination hb
  refine ⟨?_, ?_⟩
  · rw [ha']; simp
  · rw [hb']; simp

/-- **Exact division at the ideal level**: if `(D) ⊆ (X − x₀)` then
`(D) = (X − x₀) · (D.divLin x₀)`. -/
theorem span_eq_XIdeal_mul_divLin (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (h : Ideal.span {D.toCoordinateRing E} ≤ CoordinateRing.XIdeal E.toW.toAffine x₀) :
    Ideal.span {D.toCoordinateRing E} =
      CoordinateRing.XIdeal E.toW.toAffine x₀ *
        Ideal.span {(D.divLin x₀).toCoordinateRing E} := by
  obtain ⟨ha, hb⟩ := twin_of_mem_XIdeal E D x₀ (h (Ideal.subset_span rfl))
  rw [toCoordinateRing_divLin_of_twin E D ha hb, CoordinateRing.XIdeal,
    Ideal.span_singleton_mul_span_singleton]

theorem XIdeal_ne_zero (x₀ : ZMod E.q) : CoordinateRing.XIdeal E.toW.toAffine x₀ ≠ 0 := by
  rw [CoordinateRing.XIdeal, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact CoordinateRing.XClass_ne_zero x₀

/-- **Exactness of vertical division from vanishing**: if `D` vanishes at
least as much as `X − x₀` on the (rational) fiber over `x₀`, then both
components of `D` vanish at `x₀`, so `D.divLin x₀` is exact. -/
theorem twin_of_ordAt_ge_vertical (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (h : ∀ Q ∈ E.points, ordAt E (verticalElt E P.1) Q ≤ ordAt E D Q) :
    D.a.eval P.1 = 0 ∧ D.b.eval P.1 = 0 := by
  classical
  have hns := neg_snd_mem_points E hP
  by_cases hy : P.2 = 0
  · obtain ⟨x, y⟩ := P
    simp only at hy
    subst hy
    -- 2-torsion: order ≥ 2 means `D ∈ ⟨P⟩² = (X − x_P)`.
    have h2 : 2 ≤ ordAt E D (x, 0) := by
      have := h (x, 0) hP; rwa [ordAt_verticalElt E x hP, if_pos rfl, if_pos rfl] at this
    have hval := pointPrime_intValuation_toCoordinateRing E D hP hD
    have hmem : D.toCoordinateRing E ∈ (E.pointPrime hP).asIdeal ^ 2 := by
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, hval, WithZero.exp_le_exp]
      omega
    apply twin_of_mem_XIdeal
    rw [xIdeal_eq_mul E hP, neg_zero, ← pow_two]
    exact hmem
  · have h1 := h P hP
    have h1' := h (P.1, -P.2) hns
    rw [ordAt_verticalElt E P.1 hP, if_pos rfl, if_neg hy] at h1
    rw [ordAt_verticalElt E P.1 hns, if_pos rfl, if_neg (by simpa using hy)] at h1'
    have e1 := (ordAt_pos_iff_zero E D hD P hP).mp (by omega)
    have e2 := (ordAt_pos_iff_zero E D hD _ hns).mp (by omega)
    exact eval_a_b_zero_of_twin E hy e1 e2

/-! ## Non-vertical lines -/

/-- The non-vertical line `y = lam·(x − xa) + ya` as `a(x) − b(x)·y`. -/
noncomputable def lineElt (xa ya lam : ZMod E.q) : CoordRingElt E.q :=
  { a := -(C lam) * X - C (ya - lam * xa), b := -1 }

theorem lineElt_not_both_zero (xa ya lam : ZMod E.q) :
    ¬ ((lineElt E xa ya lam).a = 0 ∧ (lineElt E xa ya lam).b = 0) :=
  fun h => one_ne_zero (neg_eq_zero.mp h.2)

theorem lineElt_toCoordinateRing (xa ya lam : ZMod E.q) :
    (lineElt E xa ya lam).toCoordinateRing E =
      CoordinateRing.YClass E.toW.toAffine (linePolynomial xa ya lam) := by
  unfold lineElt CoordRingElt.toCoordinateRing CoordRingElt.toBivar CoordinateRing.YClass
    linePolynomial
  congr 1
  simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_1,
    Polynomial.C_add]
  ring

theorem natDegree_normPoly_lineElt (xa ya lam : ZMod E.q) :
    (normPoly E (lineElt E xa ya lam)).natDegree = 3 := by
  rw [normPoly_natDegree_eq, CoordRingElt.degE_of_b_ne_zero (by simp [lineElt])]
  have ha : (lineElt E xa ya lam).a.natDegree ≤ 1 := by
    unfold lineElt
    simp only
    compute_degree
  have hb : (lineElt E xa ya lam).b.natDegree = 0 := by simp [lineElt]
  omega

theorem leadingCoeff_normPoly_lineElt (xa ya lam : ZMod E.q) :
    (normPoly E (lineElt E xa ya lam)).leadingCoeff = -1 := by
  rw [Polynomial.leadingCoeff, natDegree_normPoly_lineElt, normPoly_eq]
  have ha : ((lineElt E xa ya lam).a ^ 2).natDegree < 3 := by
    unfold lineElt
    simp only
    have : (-(C lam) * X - C (ya - lam * xa)).natDegree ≤ 1 := by compute_degree
    have := Polynomial.natDegree_pow_le (p := -(C lam) * X - C (ya - lam * xa)) (n := 2)
    omega
  rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt ha]
  simp [lineElt, curveX, Polynomial.coeff_X_pow]

/-- For `A ≠ −B` the repo's `chordCoordRingElt` is the line of slope
`W.slope` through `A` (chord or tangent). -/
theorem chordCoordRingElt_eq_lineElt {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2)) :
    chordCoordRingElt E A B = lineElt E A.1 A.2 (E.toW.toAffine.slope A.1 B.1 A.2 B.2) := by
  obtain ⟨xa, ya⟩ := A
  obtain ⟨xb, yb⟩ := B
  simp only at hxy ⊢
  unfold chordCoordRingElt lineElt
  by_cases hx : xa = xb
  · subst hx
    have hy : ya = yb := by
      have h1 := E.hOnCurve _ hA
      have h2 := E.hOnCurve _ hB
      simp only at h1 h2
      have : (ya - yb) * (ya + yb) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd ⟨rfl, eq_neg_of_add_eq_zero_left h⟩ hxy
    subst hy
    have hy0 : ya ≠ 0 := fun h => hxy ⟨rfl, by rw [h, neg_zero]⟩
    have hne : ya ≠ E.toW.toAffine.negY xa ya := by
      rw [toW_negY]; intro h; exact hy0 ((neg_snd_eq_self_iff E ya).mp h.symm)
    have h2 : (2 : ZMod E.q) * ya ≠ 0 := mul_ne_zero (two_ne_zero_zmod E) hy0
    have hs : E.toW.toAffine.slope xa xa ya ya = (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ := by
      rw [slope_of_Y_ne rfl hne, toW_negY]
      simp only [ECSetup.toW_a₁, ECSetup.toW_a₂, ECSetup.toW_a₄]
      field_simp
      ring
    rw [dif_pos rfl, dif_pos rfl, if_neg hy0, hs]
  · have hs : E.toW.toAffine.slope xa xb ya yb = (yb - ya) * (xb - xa)⁻¹ := by
      rw [slope_of_X_ne hx, div_eq_mul_inv, ← neg_sub yb ya, ← neg_sub xb xa, inv_neg,
        neg_mul_neg]
    rw [dif_neg hx, hs]

/-- The third intersection `−(A + B)` of the line through `A`, `B` with `E`. -/
noncomputable def chordThird (A B : ZMod E.q × ZMod E.q) : ZMod E.q × ZMod E.q :=
  (E.toW.toAffine.addX A.1 B.1 (E.toW.toAffine.slope A.1 B.1 A.2 B.2),
   E.toW.toAffine.negAddY A.1 B.1 A.2 (E.toW.toAffine.slope A.1 B.1 A.2 B.2))

theorem chordThird_mem {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2)) :
    chordThird E A B ∈ E.points := by
  have hxy' : ¬ (A.1 = B.1 ∧ A.2 = E.toW.toAffine.negY B.1 B.2) := by
    rw [toW_negY]; exact hxy
  have h := nonsingular_negAdd (nonsing_of_mem E hA) (nonsing_of_mem E hB) hxy'
  exact E.hComplete _ _ ((E.equation_iff _ _).mp ((E.equation_iff_nonsingular).mpr h))

/-- **Line factorisation.** For `A ≠ −B` the chord/tangent through `A`, `B`
generates `⟨A⟩·⟨B⟩·⟨C⟩` with `C = chordThird A B`. One statement for
chords, tangents, flexes and 2-torsion endpoints (mathlib's
`XYIdeal_mul_XYIdeal`, which encodes the group law). -/
theorem span_chord {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2)) :
    Ideal.span {(chordCoordRingElt E A B).toCoordinateRing E} =
      listIdeal E [A, B, chordThird E A B] := by
  classical
  have hA' := nonsing_of_mem E hA
  have hB' := nonsing_of_mem E hB
  have hxy' : ¬ (A.1 = B.1 ∧ A.2 = E.toW.toAffine.negY B.1 B.2) := by
    rw [toW_negY]; exact hxy
  have key := CoordinateRing.XYIdeal_mul_XYIdeal hA'.left hB'.left hxy'
  have hX := CoordinateRing.XYIdeal_neg_mul (nonsingular_add hA' hB' hxy')
  rw [toW_negY] at hX
  rw [← hX, CoordinateRing.YIdeal, ← lineElt_toCoordinateRing,
    ← chordCoordRingElt_eq_lineElt E hA hB hxy] at key
  apply mul_right_cancel₀ (ptIdeal_ne_zero E (E.toW.toAffine.addX A.1 B.1
    (E.toW.toAffine.slope A.1 B.1 A.2 B.2), E.toW.toAffine.addY A.1 B.1 A.2
      (E.toW.toAffine.slope A.1 B.1 A.2 B.2)))
  rw [ptIdeal, ← key, chordThird, Affine.addY, toW_negY, neg_neg]
  simp only [listIdeal_cons, listIdeal_nil, ptIdeal, mul_one]
  ring

/-- **Order of a line** at every rational point: its multiplicity in the
intersection multiset `[A, B, C]`. -/
theorem ordAt_chord {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2))
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ordAt E (chordCoordRingElt E A B) Q = [A, B, chordThird E A B].count Q :=
  ordAt_eq_count_of_span_eq_listIdeal E _ _
    (by simp [hA, hB, chordThird_mem E hA hB hxy]) (span_chord E hA hB hxy) hQ

/-- Fiber sums of list counts are counts of first coordinates. -/
theorem sum_fiber_count_eq_count_fst (l : List (ZMod E.q × ZMod E.q))
    (hl : ∀ P ∈ l, P ∈ E.points) (x₀ : ZMod E.q) :
    ∑ Q ∈ E.points.filter (fun Q => Q.1 = x₀), l.count Q = (l.map Prod.fst).count x₀ := by
  classical
  induction l with
  | nil => simp
  | cons P l ih =>
    have hP := hl P List.mem_cons_self
    have h1 : ∀ Q : ZMod E.q × ZMod E.q,
        (P :: l).count Q = l.count Q + if Q = P then 1 else 0 := by
      intro Q
      rw [List.count_cons]
      by_cases h : Q = P
      · subst h; simp
      · simp [h, Ne.symm h]
    have h2 : ((P :: l).map Prod.fst).count x₀ =
        (l.map Prod.fst).count x₀ + if x₀ = P.1 then 1 else 0 := by
      rw [List.map_cons, List.count_cons]
      by_cases h : x₀ = P.1
      · rw [h]; simp
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl fun Q _ => h1 Q, Finset.sum_add_distrib,
      ih (fun R hR => hl R (List.mem_cons_of_mem _ hR)), h2, Finset.sum_ite_eq']
    congr 1
    simp [Finset.mem_filter, hP, eq_comm]

/-- **Norm of a line**: `N(line) = −(X − x_A)(X − x_B)(X − x_C)`. -/
theorem normPoly_chord {A B : ZMod E.q × ZMod E.q}
    (hA : A ∈ E.points) (hB : B ∈ E.points) (hxy : ¬ (A.1 = B.1 ∧ A.2 = -B.2)) :
    normPoly E (chordCoordRingElt E A B) =
      -((X - C A.1) * (X - C B.1) * (X - C (chordThird E A B).1)) := by
  classical
  set D := chordCoordRingElt E A B with hDdef
  have hT := chordThird_mem E hA hB hxy
  have hl : ∀ P ∈ [A, B, chordThird E A B], P ∈ E.points := by simp [hA, hB, hT]
  have hline : D = lineElt E A.1 A.2 (E.toW.toAffine.slope A.1 B.1 A.2 B.2) :=
    chordCoordRingElt_eq_lineElt E hA hB hxy
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := hline ▸ lineElt_not_both_zero E _ _ _
  have hdeg : (normPoly E D).natDegree = 3 := hline ▸ natDegree_normPoly_lineElt E _ _ _
  have hlc : (normPoly E D).leadingCoeff = -1 := hline ▸ leadingCoeff_normPoly_lineElt E _ _ _
  have hsum := sum_ordAt_eq_length_of_span_eq_listIdeal E D _ hl (span_chord E hA hB hxy)
  have hsplit := splitsOnE_of_sum_ordAt_eq E D hD (by rw [hsum, hdeg]; rfl)
  have hN0 := normPoly_ne_zero E D hD
  have hroots : (normPoly E D).roots = ({A.1, B.1, (chordThird E A B).1} : Multiset _) := by
    ext x
    rw [Polynomial.count_roots]
    by_cases hfib : ∃ P : ZMod E.q × ZMod E.q, P ∈ E.points ∧ P.1 = x
    · rw [← sum_ordAt_fst_eq_eq_rootMult E D hD x hfib,
        Finset.sum_congr rfl fun Q hQ => ordAt_chord E hA hB hxy (Finset.mem_filter.mp hQ).1,
        sum_fiber_count_eq_count_fst E _ hl]
      rw [show ({A.1, B.1, (chordThird E A B).1} : Multiset (ZMod E.q)) =
        ↑[A.1, B.1, (chordThird E A B).1] from rfl, Multiset.coe_count]
      rfl
    · have h0 : rootMultiplicity x (normPoly E D) = 0 := by
        by_contra hne
        have hr : x ∈ (normPoly E D).roots := by
          rw [Polynomial.mem_roots hN0]
          exact (Polynomial.rootMultiplicity_pos hN0).mp (Nat.pos_of_ne_zero hne)
        obtain ⟨y, hy⟩ := hsplit.2 x hr
        exact hfib ⟨(x, y), hy, rfl⟩
      rw [h0]
      have hA1 : A.1 ≠ x := fun h => hfib ⟨A, hA, h⟩
      have hB1 : B.1 ≠ x := fun h => hfib ⟨B, hB, h⟩
      have hT1 : (chordThird E A B).1 ≠ x := fun h => hfib ⟨_, hT, h⟩
      simp [hA1.symm, hB1.symm, hT1.symm]
  have hcard : Multiset.card (normPoly E D).roots = (normPoly E D).natDegree := by
    rw [hroots, hdeg]; rfl
  rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard, hlc, hroots]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_singleton, Multiset.prod_singleton, map_neg, map_one]
  ring

end Divisor
