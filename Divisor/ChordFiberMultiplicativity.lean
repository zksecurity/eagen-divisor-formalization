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
        simp
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

/-! ### natDegree-formula for the resultant against `p.map C`

Closed forms for the resultant natDegree in special cases of `p`. The
general monic case is the remaining substantive obligation; the cases
below close trivial sub-cases that the inductive step degenerates to. -/

/-- **Trivial case**: when `p = 1`, the resultant is `1` and natDegree is `0`. -/
theorem resultant_chordCubicBiv_pmap_C_natDegree_of_eq_one
    (lam : ZMod E.q) (p : Polynomial (ZMod E.q)) (hp1 : p = 1) :
    (Polynomial.resultant (chordCubicBiv E lam)
      (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      (chordCubicBiv E lam).natDegree p.natDegree).natDegree
    = 2 * p.natDegree := by
  subst hp1
  simp [Polynomial.map_one]

/-- **Linear case**: the resultant against `(X - C x₀).map C` has natDegree 2. -/
theorem resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C
    (lam x₀ : ZMod E.q)
    (p : Polynomial (ZMod E.q))
    (hp : p = Polynomial.X - Polynomial.C x₀) :
    (Polynomial.resultant (chordCubicBiv E lam)
      (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      (chordCubicBiv E lam).natDegree p.natDegree).natDegree
    = 2 * p.natDegree := by
  subst hp
  -- p.natDegree = 1, so target is 2 * 1 = 2.
  rw [Polynomial.natDegree_X_sub_C, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
  exact resultant_chordCubicBiv_X_sub_C_natDegree E lam x₀

/-- **Power-of-linear case**: the resultant against `((X - C x₀)^k).map C` has
natDegree `2k`.

Proof via mathlib's `Polynomial.resultant_X_sub_C_pow_right`, which
gives the closed form `(-1)^(m*n) * eval r f ^ n`. The natDegree of
`(eval (C x₀) chordCubicBiv)^k` is `k * 2 = 2k` by power-of-natDegree.
-/
theorem resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C_pow
    (lam x₀ : ZMod E.q) (k : ℕ)
    (p : Polynomial (ZMod E.q))
    (hp : p = (Polynomial.X - Polynomial.C x₀) ^ k) :
    (Polynomial.resultant (chordCubicBiv E lam)
      (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      (chordCubicBiv E lam).natDegree p.natDegree).natDegree
    = 2 * p.natDegree := by
  classical
  subst hp
  -- p.natDegree = k.
  have hp_natDegree :
      ((Polynomial.X - Polynomial.C x₀ : Polynomial (ZMod E.q)) ^ k).natDegree
        = k := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  -- p.map C = ((X - C(C x₀))^k) in (ZMod E.q)[X][X].
  have hpmapC :
      ((Polynomial.X - Polynomial.C x₀ : Polynomial (ZMod E.q)) ^ k).map
          (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
        = (Polynomial.X - Polynomial.C (Polynomial.C x₀)) ^ k := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C]
  rw [hpmapC, hp_natDegree]
  -- By `resultant_X_sub_C_pow_right`:
  --   Res(f, (X - C r)^k, m, k) = (-1)^(m*k) * (eval r f)^k.
  -- For us m = 3, r = C x₀, f = chordCubicBiv.
  rw [Polynomial.resultant_X_sub_C_pow_right (f := chordCubicBiv E lam)
        (r := Polynomial.C x₀) (m := (chordCubicBiv E lam).natDegree)
        (n := k) le_rfl]
  rw [chordCubicBiv_natDegree]
  -- Goal: ((-1)^(3*k) * (eval (C x₀) chordCubicBiv)^k).natDegree = 2 * k.
  -- The factor `(-1)^(3*k) : Polynomial (ZMod E.q)` is `C ((-1)^(3*k))`, a unit
  -- (=±1, nonzero).
  have hC : ((-1 : Polynomial (ZMod E.q)) ^ (3 * k))
          = Polynomial.C ((-1 : ZMod E.q) ^ (3 * k)) := by
    rw [show ((-1 : Polynomial (ZMod E.q))) = Polynomial.C (-1 : ZMod E.q) from
          by simp,
        ← Polynomial.C_pow]
  rw [hC]
  -- Goal: (C ((-1)^(3*k)) * (eval (C x₀) chordCubic)^k).natDegree = 2 * k.
  rw [Polynomial.natDegree_C_mul (by
    -- (-1)^(3*k) ≠ 0 in ZMod E.q (a unit raised to a power).
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]
  rw [Polynomial.natDegree_pow, chordCubicBiv_eval_C_natDegree]
  ring

/-- **Generic splits-natDegree lemma.** Given any `F : R[X][X]` (R a field)
with the property that `Res(F, X − C(C x), F.natDegree, 1).natDegree = 2`
for every `x : R`, and any monic `p : R[X]` that splits over `R`, the
resultant `Res(F, p.map C, F.natDegree, p.natDegree)` has natDegree
`2 · p.natDegree`. The proof is multiset induction on `p.roots`, using
mathlib's `resultant_mul_right` plus `Splits.eq_prod_roots_of_monic`.

This generic form is parameterised over `F` and the linear-case
natDegree hypothesis, allowing future extension to non-`ZMod E.q`
base rings (e.g. lifting to a splitting field of `p`). -/
theorem resultant_pmap_C_natDegree_of_splits_generic
    {R : Type*} [Field R] [DecidableEq R]
    (F : Polynomial (Polynomial R))
    (hF_lin : ∀ x : R,
      (Polynomial.resultant F (Polynomial.X - Polynomial.C (Polynomial.C x))
        F.natDegree 1).natDegree = 2)
    (p : Polynomial R) (hpm : p.Monic) (hsplit : p.Splits) :
    (Polynomial.resultant F
      (p.map (Polynomial.C : R →+* R[X]))
      F.natDegree p.natDegree).natDegree = 2 * p.natDegree := by
  classical
  let L : R → Polynomial (Polynomial R) :=
    fun x => Polynomial.X - Polynomial.C (Polynomial.C x)
  have hL_natDegree : ∀ x : R, (L x).natDegree = 1 := by
    intro x; simp [L]
  have hL_monic : ∀ x : R, (L x).Monic := fun x => Polynomial.monic_X_sub_C _
  have hprod_monic : ∀ s : Multiset R, ((s.map L).prod).Monic :=
    fun s => Polynomial.monic_multiset_prod_of_monic s L (fun x _ => hL_monic x)
  have hprod_natDegree : ∀ s : Multiset R,
      ((s.map L).prod).natDegree = s.card := by
    intro s
    rw [Polynomial.natDegree_multiset_prod_of_monic]
    · simp [hL_natDegree]
    · intro q hq
      rcases Multiset.mem_map.mp hq with ⟨x, _, rfl⟩
      exact hL_monic x
  have hlin_deg : ∀ x : R,
      (Polynomial.resultant F (L x) F.natDegree).natDegree = 2 := by
    intro x; simpa [L, hL_natDegree x] using hF_lin x
  have hlin_ne : ∀ x : R,
      Polynomial.resultant F (L x) F.natDegree ≠ 0 := by
    intro x h
    have hdeg := hlin_deg x
    rw [h, Polynomial.natDegree_zero] at hdeg; omega
  have hres : ∀ s : Multiset R,
      Polynomial.resultant F (s.map L).prod F.natDegree ≠ 0 ∧
      (Polynomial.resultant F (s.map L).prod F.natDegree).natDegree = 2 * s.card := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
        have hmul_natDegree :
            (L x * (s.map L).prod).natDegree =
              (L x).natDegree + ((s.map L).prod).natDegree :=
          Polynomial.natDegree_mul (hL_monic x).ne_zero (hprod_monic s).ne_zero
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
            hmul_natDegree,
            Polynomial.resultant_mul_right F (L x) (s.map L).prod F.natDegree le_rfl]
        exact ⟨mul_ne_zero (hlin_ne x) ih.1, by
          rw [Polynomial.natDegree_mul (hlin_ne x) ih.1, hlin_deg x, ih.2]
          omega⟩
  have hres_deg_card : ∀ s : Multiset R,
      (Polynomial.resultant F (s.map L).prod F.natDegree s.card).natDegree
        = 2 * s.card := by
    intro s
    simpa [hprod_natDegree s] using (hres s).2
  have hp : p = (p.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hsplit.eq_prod_roots_of_monic hpm
  rw [hp, Polynomial.map_multiset_prod, Multiset.map_map]
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  change (Polynomial.resultant F
      (Multiset.map (fun x : R =>
        (Polynomial.X - Polynomial.C x : Polynomial R).map
          (Polynomial.C : R →+* R[X])) p.roots).prod
      F.natDegree p.roots.card).natDegree = 2 * p.roots.card
  have hmap :
      (Multiset.map (fun x : R =>
        (Polynomial.X - Polynomial.C x : Polynomial R).map
          (Polynomial.C : R →+* R[X])) p.roots).prod
        = (p.roots.map L).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro x _; simp [L]
  rw [hmap]
  exact hres_deg_card p.roots

theorem resultant_chordCubicBiv_pmap_C_natDegree_of_splits
    (lam : ZMod E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hsplit : p.Splits) :
    (Polynomial.resultant (chordCubicBiv E lam)
      (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      (chordCubicBiv E lam).natDegree p.natDegree).natDegree
    = 2 * p.natDegree :=
  resultant_pmap_C_natDegree_of_splits_generic (chordCubicBiv E lam)
    (fun x => resultant_chordCubicBiv_X_sub_C_natDegree E lam x)
    p hpm hsplit

/-! ### K-version: chord cubic over an extension field

To handle monic `p : (ZMod E.q)[X]` with non-`F_q`-rational factors, we
lift `chordCubicBiv` along an extension `K / F_q` (later `K =
SplittingField p`) and re-prove the linear-case natDegree-of-eval
hypothesis over `K`. Everything else flows through the generic
splits-over-`R` theorem `resultant_pmap_C_natDegree_of_splits_generic`. -/

/-- **Explicit form of `chordCubicBiv` after coefficient lift to `K[X][X]`.**

Pushing the coefficient ring map `ψ : ZMod E.q →+* K` through the inner
polynomial ring gives a polynomial in `K[X][X]` of the same shape as
`chordCubicBiv`. -/
private lemma chordCubicBiv_map_eq
    {K : Type*} [Field K] (ψ : ZMod E.q →+* K) (lam : ZMod E.q) :
    (chordCubicBiv E lam).map (Polynomial.mapRingHom ψ)
      = Polynomial.X ^ 3
          - Polynomial.C (Polynomial.C (ψ (lam ^ 2))) * Polynomial.X ^ 2
          + Polynomial.C (Polynomial.C (ψ E.curveA)
                          - Polynomial.C (ψ (2 * lam)) * Polynomial.X)
              * Polynomial.X
          + Polynomial.C (Polynomial.C (ψ E.curveB) - Polynomial.X ^ 2) := by
  classical
  unfold chordCubicBiv
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
        Polynomial.coe_mapRingHom]

/-- **K-version of `chordCubicBiv_eval_C_natDegree`.** After lifting
coefficients to `K` and evaluating the outer chord variable at
`Polynomial.C α` for `α : K`, the resulting polynomial in `K[X]` has
natDegree exactly 2. The leading inner-X² coefficient is `-1`, which
is nonzero in any field. -/
private lemma chordCubicBivMapped_eval_C_natDegree
    {K : Type*} [Field K] (ψ : ZMod E.q →+* K) (lam : ZMod E.q) (α : K) :
    (((chordCubicBiv E lam).map (Polynomial.mapRingHom ψ)).eval
        (Polynomial.C α)).natDegree = 2 := by
  classical
  rw [chordCubicBiv_map_eq E ψ lam]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  compute_degree!

/-- **K-version of `resultant_chordCubicBiv_X_sub_C_natDegree`.** The
linear-case resultant with respect to `K`-coefficients, used as the
`hF_lin` hypothesis for `resultant_pmap_C_natDegree_of_splits_generic`
applied to `chordCubicBiv` lifted to `K`. -/
private lemma resultant_chordCubicBivMapped_X_sub_C_natDegree
    {K : Type*} [Field K] (ψ : ZMod E.q →+* K) (lam : ZMod E.q) (α : K) :
    (Polynomial.resultant
        ((chordCubicBiv E lam).map (Polynomial.mapRingHom ψ))
        (Polynomial.X - Polynomial.C (Polynomial.C α))
        ((chordCubicBiv E lam).map (Polynomial.mapRingHom ψ)).natDegree
        1).natDegree = 2 := by
  classical
  set F := (chordCubicBiv E lam).map (Polynomial.mapRingHom ψ) with hF
  have hres :
      Polynomial.resultant F
          (Polynomial.X - Polynomial.C (Polynomial.C α))
          F.natDegree 1
        = (-1) ^ F.natDegree * F.eval (Polynomial.C α) :=
    Polynomial.resultant_X_sub_C_right (f := F) (m := F.natDegree)
      (r := Polynomial.C α) le_rfl
  have hF_natDegree : F.natDegree = 3 := by
    rw [hF, chordCubicBiv_map_eq E ψ lam]
    compute_degree!
  rw [hres, hF_natDegree]
  rw [show ((-1 : Polynomial K) ^ 3) = -1 by ring,
      neg_one_mul, Polynomial.natDegree_neg]
  exact chordCubicBivMapped_eval_C_natDegree E ψ lam α

/-- **General-monic-`p` natDegree formula.** Without the
`p.Splits`-over-`ZMod E.q` hypothesis, by lifting to the splitting
field of `p` over `ZMod E.q`. The argument is:

1. Let `K := p.SplittingField`, `ψ := algebraMap (ZMod E.q) K`. Then
   `p.map ψ` is monic and splits over `K`.
2. Apply `resultant_pmap_C_natDegree_of_splits_generic` to
   `chordCubicBiv.map (mapRingHom ψ)` over `K`, using the K-version of
   the linear-case natDegree hypothesis. This gives the natDegree
   identity over `K`.
3. By `Polynomial.resultant_map_map`, the resultant on the `K`-side is
   the image of the original resultant under `mapRingHom ψ`. Injectivity
   of `mapRingHom ψ` (since `ψ` is injective on a field embedding)
   pulls the natDegree back to `(ZMod E.q)`. -/
theorem resultant_chordCubicBiv_pmap_C_natDegree_of_monic
    (lam : ZMod E.q) (p : Polynomial (ZMod E.q)) (hpm : p.Monic) :
    (Polynomial.resultant (chordCubicBiv E lam)
      (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
      (chordCubicBiv E lam).natDegree p.natDegree).natDegree
    = 2 * p.natDegree := by
  classical
  set K := p.SplittingField with hK
  let ψ : ZMod E.q →+* K := algebraMap (ZMod E.q) K
  have hψ_inj : Function.Injective ψ := ψ.injective
  let φ : (ZMod E.q)[X] →+* K[X] := Polynomial.mapRingHom ψ
  have hφ_inj : Function.Injective φ := Polynomial.map_injective _ hψ_inj
  have hpK_split : (p.map ψ).Splits := Polynomial.SplittingField.splits p
  have hpK_monic : (p.map ψ).Monic := hpm.map ψ
  have hpK_natDegree : (p.map ψ).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hψ_inj p
  -- Apply the generic splits theorem over K to chordCubicBiv lifted via φ.
  have key :=
    resultant_pmap_C_natDegree_of_splits_generic
      (F := (chordCubicBiv E lam).map φ)
      (fun x => resultant_chordCubicBivMapped_X_sub_C_natDegree E ψ lam x)
      (p.map ψ) hpK_monic hpK_split
  -- key : (Res(F_K, (p.map ψ).map C, F_K.natDegree, (p.map ψ).natDegree)).natDegree
  --       = 2 * (p.map ψ).natDegree
  -- Bookkeeping: relate the K-resultant to the F_q-resultant via resultant_map_map.
  -- First, identify (p.map ψ).map C with (p.map C).map φ.
  have hpmapC_commute :
      (p.map ψ).map (Polynomial.C : K →+* K[X])
        = (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])).map φ := by
    ext n
    simp [φ, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
          Polynomial.map_C]
  -- Identify F.natDegree with F_K.natDegree.
  have hF_natDegree_eq :
      ((chordCubicBiv E lam).map φ).natDegree = (chordCubicBiv E lam).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφ_inj _
  rw [hpmapC_commute] at key
  rw [hF_natDegree_eq, hpK_natDegree] at key
  -- Now key has the form: (Res(F.map φ, G.map φ, F.natDegree, p.natDegree)).natDegree
  --                       = 2 * p.natDegree.
  -- Apply resultant_map_map and natDegree_map_eq_of_injective.
  rw [Polynomial.resultant_map_map] at key
  -- After resultant_map_map, the K-resultant becomes φ (resultant ...).
  -- φ = mapRingHom ψ on K[X], and natDegree under .map ψ-injective is preserved.
  rw [show (φ (Polynomial.resultant (chordCubicBiv E lam)
              (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
              (chordCubicBiv E lam).natDegree p.natDegree)).natDegree
        = (Polynomial.resultant (chordCubicBiv E lam)
              (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
              (chordCubicBiv E lam).natDegree p.natDegree).natDegree from ?_] at key
  · exact key
  · -- φ a = a.map ψ; natDegree preserved under map of injective.
    show (Polynomial.map ψ _).natDegree = _
    exact Polynomial.natDegree_map_eq_of_injective hψ_inj _

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

/-- **Combinator**: inductive natDegree-equality step for the
`(X − C x₀)^k` factor case. Combines `_step_general'` with the
closed-form natDegree theorem
`resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C_pow`. -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_X_sub_C_pow
    (lam : ZMod E.q) (D : CoordRingElt E.q) (x₀ : ZMod E.q) (k : ℕ)
    (hda : ((Polynomial.X - Polynomial.C x₀) ^ k) ∣ D.a)
    (hdb : ((Polynomial.X - Polynomial.C x₀) ^ k) ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k)) = 0
                ∧ (D.b /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k)) = 0))
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k),
                b := D.b /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k) }).natDegree
            = (normPoly E
                { a := D.a /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k),
                  b := D.b /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k) }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree :=
  chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general'
    E lam D ((Polynomial.X - Polynomial.C x₀) ^ k)
    ((Polynomial.monic_X_sub_C x₀).pow k) hda hdb hD'ne
    (resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C_pow E lam x₀ k _ rfl)
    hIH

/-- **Combinator**: inductive natDegree-equality step for any monic `p`
that splits over `ZMod E.q`. Combines `_step_general'` with the
`_of_splits` natDegree formula. -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_splits
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hsplit : p.Splits) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ p) = 0 ∧ (D.b /ₘ p) = 0))
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
            = (normPoly E
                { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree :=
  chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general'
    E lam D p hpm hpa hpb hD'ne
    (resultant_chordCubicBiv_pmap_C_natDegree_of_splits E lam p hpm hsplit)
    hIH

/-! ### natDegree-inequality step

When proving the natDegree *bound* `chord_fiber_product.natDegree ≤
normPoly.natDegree`, the inductive step is structurally identical to
the equality version but uses `Polynomial.natDegree_mul_le` (always
holds) in place of `Polynomial.natDegree_mul` (requires nonzero
factors). This is the form needed by the squeeze helper. -/

/-- **General-monic inductive natDegree-inequality step.** Given the
inequality at the divLin-recursive child `D'` and a monic common
divisor `p`, the inequality at `D` follows. -/
theorem chord_fiber_product_concrete_natDegree_le_normPoly_natDegree_step_monic
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ p) = 0 ∧ (D.b /ₘ p) = 0))
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
            ≤ (normPoly E
                { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      ≤ (normPoly E D).natDegree := by
  classical
  have hDLne : DLineBiv E lam
                { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0 :=
    DLineBiv_ne_zero E lam _ hD'ne
  have hRES_natDegree :=
    resultant_chordCubicBiv_pmap_C_natDegree_of_monic E lam p hpm
  rw [chord_fiber_product_concrete_eq_resPmap_mul_of_div E lam D p hpm hpa hpb hDLne]
  set RES := Polynomial.resultant (chordCubicBiv E lam)
              (p.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
              (chordCubicBiv E lam).natDegree p.natDegree with hRES
  -- LHS bound: natDegree(RES * chord_fiber_product D') ≤ RES.natDegree + (cfp D').natDegree.
  have hMul_le := Polynomial.natDegree_mul_le
                    (p := RES)
                    (q := chord_fiber_product_concrete E lam
                              { a := D.a /ₘ p, b := D.b /ₘ p })
  -- RHS structure: normPoly D = p² · normPoly D'.
  have hNorm_eq := normPoly_eq_p_sq_mul_of_div E D p hpm hpa hpb
  have hp_ne : p ≠ 0 := hpm.ne_zero
  have hp_pow_ne : p^2 ≠ 0 := pow_ne_zero _ hp_ne
  have hNormD'_ne : normPoly E { a := D.a /ₘ p, b := D.b /ₘ p } ≠ 0 :=
    normPoly_ne_zero E _ hD'ne
  have hNorm_natDegree :
      (normPoly E D).natDegree
        = 2 * p.natDegree
          + (normPoly E { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree := by
    rw [hNorm_eq, Polynomial.natDegree_mul hp_pow_ne hNormD'_ne,
        Polynomial.natDegree_pow]
  rw [hNorm_natDegree]
  calc (RES * chord_fiber_product_concrete E lam
          { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
      ≤ RES.natDegree
          + (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree := hMul_le
    _ = 2 * p.natDegree
          + (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree := by
            rw [hRES_natDegree]
    _ ≤ 2 * p.natDegree
          + (normPoly E { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree := by
            exact Nat.add_le_add_left hIH _

/-- **Combinator**: inductive natDegree-equality step for *any* monic `p`
(no splits hypothesis). Combines `_step_general'` with the
splitting-field-derived natDegree formula `_of_monic`. -/
theorem chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_monic
    (lam : ZMod E.q) (D : CoordRingElt E.q) (p : Polynomial (ZMod E.q))
    (hpm : p.Monic) (hpa : p ∣ D.a) (hpb : p ∣ D.b)
    (hD'ne : ¬ ((D.a /ₘ p) = 0 ∧ (D.b /ₘ p) = 0))
    (hIH : (chord_fiber_product_concrete E lam
              { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree
            = (normPoly E
                { a := D.a /ₘ p, b := D.b /ₘ p }).natDegree) :
    (chord_fiber_product_concrete E lam D).natDegree
      = (normPoly E D).natDegree :=
  chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general'
    E lam D p hpm hpa hpb hD'ne
    (resultant_chordCubicBiv_pmap_C_natDegree_of_monic E lam p hpm)
    hIH

end Divisor
