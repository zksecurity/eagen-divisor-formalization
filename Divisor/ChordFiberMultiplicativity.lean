/-
  Divisor/ChordFiberMultiplicativity.lean

  Twin-step multiplicativity and natDegree induction infrastructure for
  the chord-fibre product. Split out of `Divisor/ChordFiberProductConcrete.lean`
  to keep that file focused on the bivariate plumbing and basic
  evaluation/factorisation theorems.

  Theorems in this file:

  * **Linear-factor extraction**:
      `DLineBiv_eq_X_sub_C_mul_divLin`
      `chord_fiber_product_concrete_eq_resXSubC_mul_of_div`
      `chordCubicBiv_eval_C_natDegree` (private)
      `resultant_chordCubicBiv_X_sub_C_natDegree` (private)
      `chord_fiber_product_concrete_natDegree_eq_of_div`

  * **General-monic factor extraction**:
      `DLineBiv_eq_C_mul_divByMonic`
      `chord_fiber_product_concrete_eq_resPmap_mul_of_div`

  * **normPoly recurrences**:
      `normPoly_eq_X_sub_C_sq_mul_of_div`
      `normPoly_eq_p_sq_mul_of_div`

  * **natDegree-equality inductive steps**:
      `chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step`
      `chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general`

  Combined with the `rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`
  squeeze helper (in `Divisor/PartialFractionExpansion.lean`) and the
  total-multiplicity identity
  `GeometricDivisorData.mult_sum_eq_normPoly_natDegree` (in
  `Divisor/GeomLocalOrder.lean`), this is the inductive infrastructure
  for the divisibility-based discharge of axiom 1
  (`chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image`).
-/
import Divisor.ChordFiberProductConcrete

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Twin-step multiplicativity of `DLineBiv` and `chord_fiber_product`

When both `D.a` and `D.b` are divisible by `(X − C x₀)` (i.e. the "twin"
case in the recursive `ordAt` analysis), `DLineBiv` factors as
`(X − C (C x₀)) · DLineBiv(D')` where `D' = D.divLin x₀`. The chord-fibre
product then factors via mathlib's `Polynomial.resultant_mul_right`,
giving an explicit multiplicativity theorem under one twin step.

This is project infrastructure for a future degree induction on the
`divLin`-recursive structure of `D`. Each twin step contributes
`Res_X(chordCubic, X − C (C x₀))` (a polynomial of natDegree 2 in the
chord-intercept variable) to `chord_fiber_product`, matching the
contribution `(X − x₀)²` to `normPoly`. -/

/-- **DLineBiv multiplicativity under linear factor extraction**:
when `(X − C x₀) ∣ D.a` and `(X − C x₀) ∣ D.b`, `DLineBiv D` factors
as `(X − C (C x₀)) · DLineBiv D'` for the linearly-divided
`D' := { a := D.a /ₘ (X − C x₀), b := D.b /ₘ (X − C x₀) }` (the same
operation as `Divisor.CoordRingElt.divLin`, inlined here to keep
imports minimal). -/
theorem DLineBiv_eq_X_sub_C_mul_divLin
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b) :
    DLineBiv E lam D
      = (Polynomial.X - Polynomial.C (Polynomial.C x₀))
          * DLineBiv E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } := by
  classical
  -- D.a = (X - C x₀) * (D.a /ₘ (X - C x₀)) via `mul_divByMonic_eq_iff_isRoot`.
  have ha_root : (D.a).IsRoot x₀ := Polynomial.dvd_iff_isRoot.mp hda
  have hb_root : (D.b).IsRoot x₀ := Polynomial.dvd_iff_isRoot.mp hdb
  have ha_factor :
      (Polynomial.X - Polynomial.C x₀) *
        (D.a /ₘ (Polynomial.X - Polynomial.C x₀)) = D.a :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha_root
  have hb_factor :
      (Polynomial.X - Polynomial.C x₀) *
        (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) = D.b :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hb_root
  unfold DLineBiv
  conv_lhs => rw [← ha_factor, ← hb_factor]
  rw [Polynomial.map_mul, Polynomial.map_mul]
  rw [show ((Polynomial.X - Polynomial.C x₀ : Polynomial (ZMod E.q)).map
        (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      = Polynomial.X - Polynomial.C (Polynomial.C x₀) by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]]
  ring

/-- **`chord_fiber_product` multiplicativity under linear factor extraction.**

Combining `DLineBiv_eq_X_sub_C_mul_divLin` with mathlib's
`Polynomial.resultant_mul_right`: when `(X − C x₀) ∣ D.a, D.b` and the
linearly-divided `D'` has nonzero `DLineBiv`, the chord-fibre product
factors as the resultant of `chordCubicBiv` against the linear factor
times the chord-fibre product of `D'`. This is the multiplicativity
step in a future degree induction on the `divLin`-recursion. -/
theorem chord_fiber_product_concrete_eq_resXSubC_mul_of_div
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b)
    (hDLne : DLineBiv E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0) :
    chord_fiber_product_concrete E lam D
      = Polynomial.resultant (chordCubicBiv E lam)
          (Polynomial.X - Polynomial.C (Polynomial.C x₀))
          (chordCubicBiv E lam).natDegree 1
        * chord_fiber_product_concrete E lam
            { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
              b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } := by
  classical
  unfold chord_fiber_product_concrete
  rw [DLineBiv_eq_X_sub_C_mul_divLin E lam D x₀ hda hdb]
  set XC := (Polynomial.X - Polynomial.C (Polynomial.C x₀)
              : (ZMod E.q)[X][X]) with hXC
  set DL := DLineBiv E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }
              with hDL_def
  have hXC_natDegree : XC.natDegree = 1 := by
    rw [hXC]; exact Polynomial.natDegree_X_sub_C _
  have hXC_monic : XC.Monic := by
    rw [hXC]; exact Polynomial.monic_X_sub_C _
  have hDLne' : DL ≠ 0 := hDLne
  have hMul_natDegree :
      (XC * DL).natDegree = XC.natDegree + DL.natDegree :=
    Polynomial.natDegree_mul hXC_monic.ne_zero hDLne'
  have hRes :=
    Polynomial.resultant_mul_right (chordCubicBiv E lam) XC DL
      (chordCubicBiv E lam).natDegree le_rfl
  rw [show
      Polynomial.resultant (chordCubicBiv E lam) (XC * DL)
          (chordCubicBiv E lam).natDegree (XC * DL).natDegree
        = Polynomial.resultant (chordCubicBiv E lam) (XC * DL)
          (chordCubicBiv E lam).natDegree (XC.natDegree + DL.natDegree) by
        rw [hMul_natDegree]]
  rw [hRes, hXC_natDegree]

/-- **`chordCubicBiv` evaluated at outer X = C x₀ has natDegree exactly 2.**

Direct via mathlib's `compute_degree` tactic. The polynomial after
substitution is `-T² - 2λx₀ T + (x₀³ - λ²x₀² + Ax₀ + B)`; the leading
T² coefficient is `-1 ≠ 0`. -/
private lemma chordCubicBiv_eval_C_natDegree
    (lam x₀ : ZMod E.q) :
    ((chordCubicBiv E lam).eval (Polynomial.C x₀)).natDegree = 2 := by
  classical
  unfold chordCubicBiv
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  -- After simp, the expression is in (ZMod E.q)[T] form. Compute its degree.
  compute_degree!

/-- **The chord-fibre resultant against `X − C(C x₀)` has natDegree 2.**

Combines `Polynomial.resultant_X_sub_C_right` with the above evaluation
natDegree. -/
private lemma resultant_chordCubicBiv_X_sub_C_natDegree
    (lam x₀ : ZMod E.q) :
    (Polynomial.resultant (chordCubicBiv E lam)
        (Polynomial.X - Polynomial.C (Polynomial.C x₀))
        (chordCubicBiv E lam).natDegree 1).natDegree = 2 := by
  classical
  have hres :
      Polynomial.resultant (chordCubicBiv E lam)
        (Polynomial.X - Polynomial.C (Polynomial.C x₀))
        (chordCubicBiv E lam).natDegree 1
        = (-1) ^ (chordCubicBiv E lam).natDegree
            * (chordCubicBiv E lam).eval (Polynomial.C x₀) :=
    Polynomial.resultant_X_sub_C_right
      (f := chordCubicBiv E lam)
      (m := (chordCubicBiv E lam).natDegree)
      (r := Polynomial.C x₀) le_rfl
  rw [hres, chordCubicBiv_natDegree]
  -- Goal: ((-1)^3 * chordCubicBiv.eval (C x₀)).natDegree = 2.
  rw [show ((-1 : Polynomial (ZMod E.q)) ^ 3) = -1 by ring,
      neg_one_mul, Polynomial.natDegree_neg]
  exact chordCubicBiv_eval_C_natDegree E lam x₀

/-! ### Generalised twin step: arbitrary monic common factor

The linear-factor multiplicativity above is the F_q-rational case
(`p = X − C x₀`). For `D` with non-F_q-rational common factors of
`a, b` (e.g. `X² + 1` over F_5 has roots in F_25 but not F_5), the
divLin recursion gets stuck. The generalised form below extends the
multiplicativity to *arbitrary monic* common factors `p`. -/

/-- **DLineBiv multiplicativity under arbitrary monic common factor**:
when `p ∣ D.a, D.b` and `p` is monic, `DLineBiv D` factors as
`p.map C · DLineBiv D'` for `D' := { a := D.a /ₘ p, b := D.b /ₘ p }`. -/
theorem DLineBiv_eq_C_mul_divByMonic
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b) :
    DLineBiv E lam D
      = p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
          * DLineBiv E lam
              { a := D.a /ₘ p
                b := D.b /ₘ p } := by
  classical
  -- D.a = p * (D.a /ₘ p) using modByMonic_eq_zero_iff_dvd + modByMonic_add_div.
  have ha_factor : p * (D.a /ₘ p) = D.a := by
    have hmod : D.a %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hpm).mpr hpa
    have := Polynomial.modByMonic_add_div D.a hpm
    rw [hmod, zero_add] at this
    exact this
  have hb_factor : p * (D.b /ₘ p) = D.b := by
    have hmod : D.b %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hpm).mpr hpb
    have := Polynomial.modByMonic_add_div D.b hpm
    rw [hmod, zero_add] at this
    exact this
  unfold DLineBiv
  conv_lhs => rw [← ha_factor, ← hb_factor]
  rw [Polynomial.map_mul, Polynomial.map_mul]
  ring

/-- **`chord_fiber_product` multiplicativity under arbitrary monic common
factor.** Generalises `chord_fiber_product_concrete_eq_resXSubC_mul_of_div`
from `p = X − C x₀` to any monic `p ∣ D.a, D.b`. -/
theorem chord_fiber_product_concrete_eq_resPmap_mul_of_div
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hDLne : DLineBiv E lam { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0) :
    chord_fiber_product_concrete E lam D
      = Polynomial.resultant (chordCubicBiv E lam)
          (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
          (chordCubicBiv E lam).natDegree p.natDegree
        * chord_fiber_product_concrete E lam
            { a := D.a /ₘ p, b := D.b /ₘ p } := by
  classical
  unfold chord_fiber_product_concrete
  rw [DLineBiv_eq_C_mul_divByMonic E lam D p hpm hpa hpb]
  set PC := p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]) with hPC
  set DL := DLineBiv E lam { a := D.a /ₘ p, b := D.b /ₘ p } with hDL_def
  have hPC_natDegree : PC.natDegree = p.natDegree := by
    rw [hPC]; exact Polynomial.natDegree_map_eq_of_injective
      (Polynomial.C_injective (R := ZMod E.q)) p
  have hPC_monic : PC.Monic := by
    rw [hPC]; exact hpm.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
  have hDLne' : DL ≠ 0 := hDLne
  have hMul_natDegree : (PC * DL).natDegree = PC.natDegree + DL.natDegree :=
    Polynomial.natDegree_mul hPC_monic.ne_zero hDLne'
  have hRes :=
    Polynomial.resultant_mul_right (chordCubicBiv E lam) PC DL
      (chordCubicBiv E lam).natDegree le_rfl
  rw [show
      Polynomial.resultant (chordCubicBiv E lam) (PC * DL)
          (chordCubicBiv E lam).natDegree (PC * DL).natDegree
        = Polynomial.resultant (chordCubicBiv E lam) (PC * DL)
          (chordCubicBiv E lam).natDegree (PC.natDegree + DL.natDegree) by
        rw [hMul_natDegree]]
  rw [hRes, hPC_natDegree]

/-- **`chord_fiber_product` natDegree increases by exactly 2 per twin step.**

When the linear-factor multiplicativity applies and both factors are
non-zero, taking the natDegree of the multiplicativity equation gives
the recurrence
  `(chord_fiber_product D).natDegree = 2 + (chord_fiber_product D').natDegree`.

This is the inductive step for proving the natDegree-of-chord_fiber_product
equality with `(normPoly).natDegree`: each twin step in `divLin` adds
2 to both `chord_fiber_product.natDegree` (this lemma) and to
`(normPoly).natDegree` (since
`normPoly D = (X − x₀)² · normPoly D'`). -/
theorem chord_fiber_product_concrete_natDegree_eq_of_div
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b)
    (hDLne : DLineBiv E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0)
    (hCFPne : chord_fiber_product_concrete E lam
                { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                  b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0) :
    (chord_fiber_product_concrete E lam D).natDegree
      = 2 + (chord_fiber_product_concrete E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }).natDegree := by
  classical
  rw [chord_fiber_product_concrete_eq_resXSubC_mul_of_div E lam D x₀ hda hdb hDLne]
  -- Now: (Res(chordCubic, X - C(C x₀), _, 1) * chord_fiber_product D').natDegree.
  -- Apply Polynomial.natDegree_mul; both factors are nonzero.
  set RES := Polynomial.resultant (chordCubicBiv E lam)
              (Polynomial.X - Polynomial.C (Polynomial.C x₀))
              (chordCubicBiv E lam).natDegree 1 with hRES
  have hRES_ne : RES ≠ 0 := by
    rw [hRES]
    -- RES has natDegree 2 from `resultant_chordCubicBiv_X_sub_C_natDegree`,
    -- so it is nonzero.
    intro h
    have h0 : (RES).natDegree = 0 := by rw [hRES, h, Polynomial.natDegree_zero]
    have h2 : RES.natDegree = 2 := by
      rw [hRES]
      exact resultant_chordCubicBiv_X_sub_C_natDegree E lam x₀
    omega
  rw [Polynomial.natDegree_mul hRES_ne hCFPne, hRES,
      resultant_chordCubicBiv_X_sub_C_natDegree]

/-- **`normPoly` factors under linear divisibility**:
when `(X − C x₀) ∣ D.a, D.b`, the norm polynomial factors as
`(X − C x₀)² · normPoly D'` for the linearly-divided `D'`. -/
theorem normPoly_eq_X_sub_C_sq_mul_of_div
    (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b) :
    normPoly E D
      = (Polynomial.X - Polynomial.C x₀) ^ 2
          * normPoly E { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀),
                          b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } := by
  classical
  have ha_root : (D.a).IsRoot x₀ := Polynomial.dvd_iff_isRoot.mp hda
  have hb_root : (D.b).IsRoot x₀ := Polynomial.dvd_iff_isRoot.mp hdb
  have ha_factor :
      (Polynomial.X - Polynomial.C x₀) *
        (D.a /ₘ (Polynomial.X - Polynomial.C x₀)) = D.a :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha_root
  have hb_factor :
      (Polynomial.X - Polynomial.C x₀) *
        (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) = D.b :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hb_root
  rw [normPoly_eq, normPoly_eq]
  conv_lhs => rw [← ha_factor, ← hb_factor]
  ring

/-- **Inductive step for the natDegree equality**:
under the linear divisibility, if `chord_fiber_product`'s natDegree
matches `normPoly`'s for the linearly-divided `D'`, then it matches
for `D` itself. This is the natDegree induction step that, combined
with a base case, would close the natDegree comparison stub
(`chord_fiber_product.natDegree ≤ normPoly.natDegree`). -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ (Polynomial.X - Polynomial.C x₀)) = 0
                ∧ (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) = 0))
    (hDLne : DLineBiv E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0)
    (hCFPne : chord_fiber_product_concrete E lam
                { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                  b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0)
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }).natDegree
            = (normPoly E
                { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                  b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree := by
  classical
  rw [chord_fiber_product_concrete_natDegree_eq_of_div E lam D x₀
        hda hdb hDLne hCFPne]
  rw [hIH]
  rw [normPoly_eq_X_sub_C_sq_mul_of_div E D x₀ hda hdb]
  -- Goal: 2 + (normPoly E D').natDegree = ((X - C x₀)^2 * normPoly E D').natDegree
  have hXne : (Polynomial.X - Polynomial.C x₀ : (ZMod E.q)[X]) ≠ 0 :=
    (Polynomial.monic_X_sub_C _).ne_zero
  have hXpow_ne :
      ((Polynomial.X - Polynomial.C x₀ : (ZMod E.q)[X]) ^ 2) ≠ 0 :=
    pow_ne_zero _ hXne
  have hNormD'_ne : normPoly E
      { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
        b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) } ≠ 0 :=
    normPoly_ne_zero E _ hD'ne
  rw [Polynomial.natDegree_mul hXpow_ne hNormD'_ne]
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]

/-- **`normPoly` factors under arbitrary monic divisibility**:
when `p ∣ D.a, D.b` and `p` is monic, `normPoly D = p² · normPoly D'`. -/
theorem normPoly_eq_p_sq_mul_of_div
    (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b) :
    normPoly E D
      = p ^ 2
          * normPoly E { a := D.a /ₘ p, b := D.b /ₘ p } := by
  classical
  have ha_factor : p * (D.a /ₘ p) = D.a := by
    have hmod : D.a %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hpm).mpr hpa
    have := Polynomial.modByMonic_add_div D.a hpm
    rw [hmod, zero_add] at this
    exact this
  have hb_factor : p * (D.b /ₘ p) = D.b := by
    have hmod : D.b %ₘ p = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hpm).mpr hpb
    have := Polynomial.modByMonic_add_div D.b hpm
    rw [hmod, zero_add] at this
    exact this
  rw [normPoly_eq, normPoly_eq]
  conv_lhs => rw [← ha_factor, ← hb_factor]
  ring

/-- **General-monic inductive natDegree-equality step.**

Generalises `chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step`
from the linear factor case to arbitrary monic divisor `p`, given
the natDegree formula for the resultant against `p.map C` as
hypothesis. The hypothesis
`hRES_natDegree : Res(chordCubic, p.map C, 3, p.natDegree).natDegree = 2 · p.natDegree`
is the remaining substantive obligation; it is provable for `p` linear
(by `resultant_chordCubicBiv_X_sub_C_natDegree`) and for `p` monic of
arbitrary degree via splitting-field machinery
(`resultant_eq_prod_eval` reversed by `resultant_comm`, applied over
`Polynomial.SplittingField p`). -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ p) = 0 ∧ (D.b /ₘ p) = 0))
    (hDLne : DLineBiv E lam { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0)
    (hCFPne : chord_fiber_product_concrete E lam
                { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0)
    (hRES_natDegree :
      (Polynomial.resultant (chordCubicBiv E lam)
        (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
        (chordCubicBiv E lam).natDegree p.natDegree).natDegree
        = 2 * p.natDegree)
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
            = (normPoly E
                { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree := by
  classical
  rw [chord_fiber_product_concrete_eq_resPmap_mul_of_div E lam D p hpm hpa hpb hDLne]
  -- LHS: (RES * chord_fiber_product D').natDegree
  set RES := Polynomial.resultant (chordCubicBiv E lam)
              (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
              (chordCubicBiv E lam).natDegree p.natDegree with hRES
  have hRES_ne : RES ≠ 0 := by
    intro h
    -- Distinguish p.natDegree = 0 (where the natDegree formula degenerates).
    rcases Nat.eq_zero_or_pos p.natDegree with hzero | hpos
    · -- p.natDegree = 0, p monic ⇒ p = 1, RES = Polynomial.resultant _ 1 _ 0 = 1.
      have hp1 : p = 1 := (hpm.natDegree_eq_zero).mp hzero
      have hRES_eq_one : RES = 1 := by
        rw [hRES, hp1, Polynomial.map_one]
        simp [Polynomial.resultant_one_right]
      rw [hRES_eq_one] at h
      exact one_ne_zero h
    · -- 0 < p.natDegree ⇒ RES.natDegree = 2 * p.natDegree > 0 ⇒ RES ≠ 0.
      have h0 : RES.natDegree = 0 := by rw [h, Polynomial.natDegree_zero]
      rw [hRES_natDegree] at h0
      omega
  rw [Polynomial.natDegree_mul hRES_ne hCFPne, hRES_natDegree, hIH,
      normPoly_eq_p_sq_mul_of_div E D p hpm hpa hpb]
  -- Goal: 2 * p.natDegree + normPoly D'.natDegree = (p^2 * normPoly D').natDegree
  have hp_ne : p ≠ 0 := hpm.ne_zero
  have hp_pow_ne : p^2 ≠ 0 := pow_ne_zero _ hp_ne
  have hNormD'_ne : normPoly E { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0 :=
    normPoly_ne_zero E _ hD'ne
  rw [Polynomial.natDegree_mul hp_pow_ne hNormD'_ne, Polynomial.natDegree_pow]

/-! ### Streamlined inductive steps with auto-derived non-vanishing

The `_step` theorems above take both `hDLne` and `hCFPne` as explicit
hypotheses. With the project's `DLineBiv_ne_zero` and the production
`chord_fiber_product_concrete_ne_zero` lemmas, both follow from the
single non-degeneracy condition `¬ (D'.a = 0 ∧ D'.b = 0)`. The
streamlined wrappers below let callers pass that single hypothesis. -/

/-- **Streamlined linear-factor inductive step**: takes only
`¬ (D'.a = 0 ∧ D'.b = 0)` and derives the DLineBiv/chord_fiber_product
non-vanishing internally. -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step'
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (hda : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hdb : (Polynomial.X - Polynomial.C x₀) ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ (Polynomial.X - Polynomial.C x₀)) = 0
                ∧ (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) = 0))
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }).natDegree
            = (normPoly E
                { a := D.a /ₘ (Polynomial.X - Polynomial.C x₀)
                  b := D.b /ₘ (Polynomial.X - Polynomial.C x₀) }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree :=
  chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step
    E lam D x₀ hda hdb hD'ne (DLineBiv_ne_zero E lam _ hD'ne)
    (chord_fiber_product_concrete_ne_zero E lam _ hD'ne) hIH

/-- **Streamlined general-monic inductive step**: takes only
`¬ (D'.a = 0 ∧ D'.b = 0)` and derives the DLineBiv/chord_fiber_product
non-vanishing internally. -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general'
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ p) = 0 ∧ (D.b /ₘ p) = 0))
    (hRES_natDegree :
      (Polynomial.resultant (chordCubicBiv E lam)
        (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
        (chordCubicBiv E lam).natDegree p.natDegree).natDegree
        = 2 * p.natDegree)
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
            = (normPoly E
                { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree :=
  chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general
    E lam D p hpm hpa hpb hD'ne (DLineBiv_ne_zero E lam _ hD'ne)
    (chord_fiber_product_concrete_ne_zero E lam _ hD'ne)
    hRES_natDegree hIH

end Divisor
