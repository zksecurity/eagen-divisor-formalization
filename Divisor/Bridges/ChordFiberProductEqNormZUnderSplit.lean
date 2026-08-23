/-
  Divisor/Bridges/ChordFiberProductEqNormZUnderSplit.lean

  Concrete proof of the split-rational chord-fiber-product/normZ
  proportionality.  This file is deliberately phrased against
  `chord_fiber_product_concrete`, so `ChordFiberProductNormZ.lean` can
  import it without creating a cycle with the bar-factorisation module
  that mentions `chord_fiber_product`.
-/
import Divisor.Bridges.ChordFiberDivisibility
import Divisor.ChordFiberWeightedDegree
import Divisor.FunctionFieldZ
import Divisor.PartialFractionExpansion

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Small base-change helpers -/

/-- The algebra map from `ZMod E.q` into its algebraic closure is injective. -/
private lemma fqToBar_injective :
    Function.Injective (algebraMap (ZMod E.q) (Fqbar E)) :=
  RingHom.injective _

/-- Zero is reflected by `fqToBar`. -/
private lemma fqToBar_eq_zero_iff (x : ZMod E.q) :
    fqToBar E x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (fqToBar_injective E)

/-- A root of a base-changed split polynomial comes from a base-field root. -/
private theorem exists_root_of_map_root_of_roots_card_eq_natDegree
    {K L : Type} [Field K] [Field L]
    (φ : K →+* L) (hφ : Function.Injective φ)
    (p : K[X]) (hpne : p ≠ 0)
    (hroots : p.roots.card = p.natDegree)
    {β : L} (hβ : (p.map φ).IsRoot β) :
    ∃ α ∈ p.roots, φ α = β := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfac : C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have hmap := congrArg (Polynomial.map φ) hfac
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod] at hmap
  have hEval : Polynomial.eval β (Polynomial.map φ p) = 0 := hβ
  rw [← hmap] at hEval
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod] at hEval
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hEval
  have hLC : φ p.leadingCoeff ≠ 0 := by
    intro h
    exact Polynomial.leadingCoeff_ne_zero.mpr hpne (hφ (by simpa using h))
  have hProd : ((p.roots.map fun a => β - φ a)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    rw [Multiset.mem_map] at hzero
    rcases hzero with ⟨a, hamem, hqeval⟩
    exact hnone a hamem (sub_eq_zero.mp hqeval).symm
  exact mul_ne_zero hLC hProd hEval

private theorem normPolyBar_root_in_base_of_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    {x : Fqbar E} (hx : (normPolyBar E D).IsRoot x) :
    ∃ α ∈ (normPoly E D).roots, x = fqToBar E α := by
  have hx' :
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) (normPoly E D)).IsRoot x := by
    simpa [normPolyBar] using hx
  obtain ⟨α, hα, hmap⟩ :=
    exists_root_of_map_root_of_roots_card_eq_natDegree
      (algebraMap (ZMod E.q) (Fqbar E))
      (fqToBar_injective E)
      (normPoly E D)
      (normPoly_ne_zero E D hD)
      hSplitOnE.toSplits
      hx'
  exact ⟨α, hα, hmap.symm⟩

private theorem geomEval_eq_fqToBar_of_coords
    (D : CoordRingElt E.q) (Q : GeomPoint E)
    (P : ZMod E.q × ZMod E.q)
    (hx : Q.x = fqToBar E P.1) (hy : Q.y = fqToBar E P.2) :
    D.geomEval E Q = fqToBar E (D.eval P.1 P.2) := by
  unfold CoordRingElt.geomEval CoordRingElt.eval
  rw [hx, hy]
  simp [fqToBar, map_sub, map_mul]

/-- Rational lift of an affine base-field point to the algebraic closure. -/
private noncomputable def rationalLift
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) : GeomPoint E :=
  ⟨fqToBar E P.1, fqToBar E P.2, by
    unfold fqToBar
    rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
    exact congrArg _ (E.hOnCurve P hP)⟩

@[simp] private theorem rationalLift_x
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    (rationalLift E P hP).x = fqToBar E P.1 := rfl

@[simp] private theorem rationalLift_y
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    (rationalLift E P hP).y = fqToBar E P.2 := rfl

private theorem geomPoint_eq_rationalLift_of_coords
    (Q : GeomPoint E) (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points)
    (hx : Q.x = fqToBar E P.1) (hy : Q.y = fqToBar E P.2) :
    Q = rationalLift E P hP := by
  cases Q
  simp only [rationalLift, GeomPoint.mk.injEq] at hx hy ⊢
  exact ⟨hx, hy⟩

/-- For each rational point `P` on `E`, the geometric evaluation at the
lifted geometric point equals `fqToBar` of the rational evaluation. -/
private theorem geomEval_lift_eq_fqToBar
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hOn : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB) :
    D.geomEval E (⟨fqToBar E P.1, fqToBar E P.2, by
        unfold fqToBar
        rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
        exact congrArg _ hOn⟩ : GeomPoint E) =
      fqToBar E (D.eval P.1 P.2) := by
  unfold CoordRingElt.geomEval CoordRingElt.eval
  simp [fqToBar, map_sub, map_mul]

/-- For each rational zero `P` of `D`, the corresponding lifted geometric
point lies in `gd.support`. -/
private theorem support_lift_of_rational_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) (hPpts : P ∈ E.points)
    (hPzero : D.eval P.1 P.2 = 0) :
    rationalLift E P hPpts ∈ gd.support := by
  apply gd.eval_zero_mem_support
  rw [show rationalLift E P hPpts =
      (⟨fqToBar E P.1, fqToBar E P.2, by
        unfold fqToBar
        rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
        exact congrArg _ (E.hOnCurve P hPpts)⟩ : GeomPoint E) from rfl]
  rw [geomEval_lift_eq_fqToBar E D P (E.hOnCurve P hPpts), hPzero]
  simp [fqToBar]

/-! ## Rational `ordAt` versus geometric `geomLocalOrder` -/

/-- Root multiplicity of `normPolyBar` at the lift of a base-field point
coincides with the rational root multiplicity of `normPoly`. -/
private theorem rootMult_normPolyBar_at_fqToBar
    (D : CoordRingElt E.q) (β : ZMod E.q) :
    (normPolyBar E D).rootMultiplicity (fqToBar E β)
      = (normPoly E D).rootMultiplicity β := by
  unfold normPolyBar fqToBar
  exact (Polynomial.eq_rootMultiplicity_map (fqToBar_injective E) β).symm

/-- Rational counterpart of `commonRootMultiplicity`. -/
private noncomputable def commonRootMultRatGS
    (D : CoordRingElt E.q) (β : ZMod E.q) : ℕ :=
  if D.a = 0 then D.b.rootMultiplicity β
  else if D.b = 0 then D.a.rootMultiplicity β
  else min (D.a.rootMultiplicity β) (D.b.rootMultiplicity β)

private theorem commonRootMultiplicity_at_fqToBar_eq
    (D : CoordRingElt E.q) (β : ZMod E.q) :
    commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) (fqToBar E β)
      = commonRootMultRatGS E D β := by
  classical
  unfold commonRootMultiplicity commonRootMultRatGS
  have ha : (geomAPoly E D = 0) ↔ (D.a = 0) := by
    unfold geomAPoly
    exact Polynomial.map_eq_zero_iff (fqToBar_injective E)
  have hb : (geomBPoly E D = 0) ↔ (D.b = 0) := by
    unfold geomBPoly
    exact Polynomial.map_eq_zero_iff (fqToBar_injective E)
  have hRMa : (geomAPoly E D).rootMultiplicity (fqToBar E β)
      = D.a.rootMultiplicity β := by
    unfold geomAPoly fqToBar
    exact (Polynomial.eq_rootMultiplicity_map (fqToBar_injective E) β).symm
  have hRMb : (geomBPoly E D).rootMultiplicity (fqToBar E β)
      = D.b.rootMultiplicity β := by
    unfold geomBPoly fqToBar
    exact (Polynomial.eq_rootMultiplicity_map (fqToBar_injective E) β).symm
  by_cases h_a : D.a = 0
  · simp only [ha.mpr h_a, h_a, if_true, hRMb]
  · simp only [if_neg ((Iff.not ha).mpr h_a), if_neg h_a]
    by_cases h_b : D.b = 0
    · simp only [hb.mpr h_b, h_b, if_true, hRMa]
    · simp only [if_neg ((Iff.not hb).mpr h_b), if_neg h_b, hRMa, hRMb]

/-- Rational a-tilde: `D.a` after removing the common `(X - C β)`-factor. -/
private noncomputable def aTildeRat (D : CoordRingElt E.q) (β : ZMod E.q) :
    Polynomial (ZMod E.q) :=
  D.a /ₘ (Polynomial.X - Polynomial.C β) ^ commonRootMultRatGS E D β

/-- Rational b-tilde: `D.b` after removing the common `(X - C β)`-factor. -/
private noncomputable def bTildeRat (D : CoordRingElt E.q) (β : ZMod E.q) :
    Polynomial (ZMod E.q) :=
  D.b /ₘ (Polynomial.X - Polynomial.C β) ^ commonRootMultRatGS E D β

/-- Rational branch value: residual `D`-evaluation after exhausting the
common factor at `P.1`. -/
private noncomputable def branchRat
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (aTildeRat E D P.1).eval P.1 - (bTildeRat E D P.1).eval P.1 * P.2

private theorem geomATilde_at_fqToBar
    (D : CoordRingElt E.q) (β : ZMod E.q) :
    geomATilde E D (fqToBar E β)
      = Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) (aTildeRat E D β) := by
  unfold geomATilde aTildeRat
  rw [commonRootMultiplicity_at_fqToBar_eq E D β]
  set k := commonRootMultRatGS E D β
  have hpm : ((Polynomial.X - Polynomial.C β : (ZMod E.q)[X]) ^ k).Monic :=
    (monic_X_sub_C _).pow _
  have hmap_pow :
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          ((Polynomial.X - Polynomial.C β) ^ k)
        = (Polynomial.X - Polynomial.C (fqToBar E β)) ^ k := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [Polynomial.map_divByMonic _ hpm, hmap_pow]
  rfl

private theorem geomBTilde_at_fqToBar
    (D : CoordRingElt E.q) (β : ZMod E.q) :
    geomBTilde E D (fqToBar E β)
      = Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) (bTildeRat E D β) := by
  unfold geomBTilde bTildeRat
  rw [commonRootMultiplicity_at_fqToBar_eq E D β]
  set k := commonRootMultRatGS E D β
  have hpm : ((Polynomial.X - Polynomial.C β : (ZMod E.q)[X]) ^ k).Monic :=
    (monic_X_sub_C _).pow _
  have hmap_pow :
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          ((Polynomial.X - Polynomial.C β) ^ k)
        = (Polynomial.X - Polynomial.C (fqToBar E β)) ^ k := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [Polynomial.map_divByMonic _ hpm, hmap_pow]
  rfl

private theorem geomBranch_at_fqToBar
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    (geomATilde E D (fqToBar E P.1)).eval (fqToBar E P.1)
        - (geomBTilde E D (fqToBar E P.1)).eval (fqToBar E P.1) * (fqToBar E P.2)
      = fqToBar E (branchRat E D P) := by
  rw [geomATilde_at_fqToBar E D P.1, geomBTilde_at_fqToBar E D P.1]
  unfold branchRat fqToBar
  rw [Polynomial.eval_map, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
  rw [map_sub, map_mul]

/-- 2-torsion case: geometric local order at the rational lift is the
rational `rootMultiplicity` of the norm. -/
private theorem geomLocalOrder_rationalLift_two_torsion
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 = 0) :
    geomLocalOrder E D (rationalLift E P hP)
      = (normPoly E D).rootMultiplicity P.1 := by
  unfold geomLocalOrder
  have hQy_zero : (rationalLift E P hP).y = 0 := by
    show fqToBar E P.2 = 0
    rw [hY]; exact map_zero _
  rw [if_pos hQy_zero]
  show (normPolyBar E D).rootMultiplicity (fqToBar E P.1) = _
  exact rootMult_normPolyBar_at_fqToBar E D P.1

/-- Non-2-torsion case: geometric local order at a rational lift in
closed form on the rational level. -/
private theorem geomLocalOrder_rationalLift_non_two_torsion
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0) :
    geomLocalOrder E D (rationalLift E P hP)
      = (let k := commonRootMultRatGS E D P.1
         let m := (normPoly E D).rootMultiplicity P.1
         if branchRat E D P = 0 then m - k else k) := by
  classical
  unfold geomLocalOrder
  have hQy_ne : (rationalLift E P hP).y ≠ 0 := by
    show fqToBar E P.2 ≠ 0
    exact (fqToBar_eq_zero_iff E _).not.mpr hY
  rw [if_neg hQy_ne]
  have hm : (normPolyBar E D).rootMultiplicity (rationalLift E P hP).x
      = (normPoly E D).rootMultiplicity P.1 := by
    show (normPolyBar E D).rootMultiplicity (fqToBar E P.1) = _
    exact rootMult_normPolyBar_at_fqToBar E D P.1
  have hk : commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D)
              (rationalLift E P hP).x
      = commonRootMultRatGS E D P.1 := by
    show commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) (fqToBar E P.1) = _
    exact commonRootMultiplicity_at_fqToBar_eq E D P.1
  have hbranch_eq : ((geomATilde E D (rationalLift E P hP).x).eval
                      (rationalLift E P hP).x
                    - (geomBTilde E D (rationalLift E P hP).x).eval
                      (rationalLift E P hP).x * (rationalLift E P hP).y)
                  = fqToBar E (branchRat E D P) := by
    show (geomATilde E D (fqToBar E P.1)).eval (fqToBar E P.1)
          - (geomBTilde E D (fqToBar E P.1)).eval (fqToBar E P.1) * (fqToBar E P.2) = _
    exact geomBranch_at_fqToBar E D P
  rw [hm, hk]
  by_cases hBranch : branchRat E D P = 0
  · have hbranch_zero :
        (geomATilde E D (rationalLift E P hP).x).eval (rationalLift E P hP).x
          - (geomBTilde E D (rationalLift E P hP).x).eval (rationalLift E P hP).x
            * (rationalLift E P hP).y = 0 := by
      rw [hbranch_eq, hBranch]; exact map_zero _
    rw [if_pos hbranch_zero]
    simp only [hBranch, if_true]
  · have hbranch_ne :
        (geomATilde E D (rationalLift E P hP).x).eval (rationalLift E P hP).x
          - (geomBTilde E D (rationalLift E P hP).x).eval (rationalLift E P hP).x
            * (rationalLift E P hP).y ≠ 0 := by
      rw [hbranch_eq]
      exact (fqToBar_eq_zero_iff E _).not.mpr hBranch
    rw [if_neg hbranch_ne]
    simp only [hBranch, if_false]

/-! #### Common-factor count and branch value under `divLin` -/

private theorem one_le_commonRootMultRatGS_of_both_eval_zero
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (β : ZMod E.q) (ha : D.a.eval β = 0) (hb : D.b.eval β = 0) :
    1 ≤ commonRootMultRatGS E D β := by
  classical
  unfold commonRootMultRatGS
  by_cases h_a : D.a = 0
  · rw [if_pos h_a]
    have hbz : D.b ≠ 0 := fun h => hDnz ⟨h_a, h⟩
    exact (Polynomial.rootMultiplicity_pos hbz).mpr hb
  · rw [if_neg h_a]
    by_cases h_b : D.b = 0
    · rw [if_pos h_b]
      exact (Polynomial.rootMultiplicity_pos h_a).mpr ha
    · rw [if_neg h_b]
      exact le_min ((Polynomial.rootMultiplicity_pos h_a).mpr ha)
        ((Polynomial.rootMultiplicity_pos h_b).mpr hb)

/-- For a polynomial `p` divisible by `(X - C β)`, the rootMultiplicity at
`β` of `p /ₘ (X - C β)` is one less. -/
private theorem rootMultiplicity_div_X_sub_C
    {β : ZMod E.q} {p : Polynomial (ZMod E.q)}
    (hp : p ≠ 0) (hroot : p.eval β = 0) :
    (p /ₘ (Polynomial.X - Polynomial.C β)).rootMultiplicity β
      = p.rootMultiplicity β - 1 := by
  classical
  have hroot_pos : 0 < p.rootMultiplicity β :=
    (Polynomial.rootMultiplicity_pos hp).mpr hroot
  have hMonic : (Polynomial.X - Polynomial.C β : (ZMod E.q)[X]).Monic :=
    monic_X_sub_C _
  have h_dvd : (Polynomial.X - Polynomial.C β) ∣ p :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  have h_eq : p = (Polynomial.X - Polynomial.C β) *
      (p /ₘ (Polynomial.X - Polynomial.C β)) := by
    have := Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C β)
    have hmod : p %ₘ (Polynomial.X - Polynomial.C β) = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hMonic).mpr h_dvd
    rw [hmod, zero_add] at this
    exact this.symm
  have h_quot_ne : p /ₘ (Polynomial.X - Polynomial.C β) ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at h_eq
    exact hp h_eq
  have h_rm := Polynomial.rootMultiplicity_mul (p := Polynomial.X - Polynomial.C β)
    (q := p /ₘ (Polynomial.X - Polynomial.C β)) (x := β)
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) h_quot_ne)
  rw [← h_eq] at h_rm
  rw [Polynomial.rootMultiplicity_X_sub_C_self] at h_rm
  omega

/-- Iterated divByMonic by a monic polynomial: dividing by `q^k` then `q`
gives the same as dividing by `q^(k+1)`. -/
private theorem divByMonic_pow_succ
    (p : Polynomial (ZMod E.q)) {q : Polynomial (ZMod E.q)} (hq : q.Monic) (k : ℕ) :
    (p /ₘ q ^ k) /ₘ q = p /ₘ q ^ (k + 1) := by
  classical
  by_cases hq1 : q = 1
  · subst hq1; simp [Polynomial.divByMonic_one, one_pow]
  have hq_deg_pos : 0 < q.natDegree := by
    rcases Nat.eq_zero_or_pos q.natDegree with h | h
    · exact absurd (hq.natDegree_eq_zero.mp h) hq1
    · exact h
  have hqp : (q ^ k).Monic := hq.pow _
  have hqp1 : (q ^ (k + 1)).Monic := hq.pow _
  set d := (p /ₘ q ^ k) /ₘ q with hd_def
  set r := q ^ k * ((p /ₘ q ^ k) %ₘ q) + (p %ₘ q ^ k) with hr_def
  have hp_eq : r + q ^ (k + 1) * d = p := by
    have h1 := Polynomial.modByMonic_add_div p (q ^ k)
    have h2 := Polynomial.modByMonic_add_div (p /ₘ q ^ k) q
    rw [show q ^ (k + 1) = q ^ k * q from pow_succ q k]
    linear_combination h1 + q^k * h2
  have hr_deg : r.degree < (q ^ (k + 1)).degree := by
    have hq_ne_zero : q ≠ 0 := hq.ne_zero
    have hqk_natDeg : (q ^ k).natDegree = k * q.natDegree := hq.natDegree_pow k
    have hqk1_natDeg : (q ^ (k + 1)).natDegree = (k + 1) * q.natDegree :=
      hq.natDegree_pow (k+1)
    have hqk1_deg : (q ^ (k + 1)).degree = ((k + 1) * q.natDegree : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hqp1.ne_zero, hqk1_natDeg]
    have hqk_deg : (q ^ k).degree = (k * q.natDegree : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hqp.ne_zero, hqk_natDeg]
    have h_mod_q_natDeg : ((p /ₘ q ^ k) %ₘ q).natDegree < q.natDegree :=
      Polynomial.natDegree_modByMonic_lt _ hq hq1
    have hk1_eq : (k + 1) * q.natDegree = k * q.natDegree + q.natDegree := by ring
    have h_mul_deg : (q ^ k * ((p /ₘ q ^ k) %ₘ q)).degree
        < (q ^ (k + 1)).degree := by
      by_cases hmod_zero : (p /ₘ q ^ k) %ₘ q = 0
      · rw [hmod_zero, mul_zero, Polynomial.degree_zero, hqk1_deg]
        exact WithBot.bot_lt_coe _
      · have h_mul_nz : q ^ k * ((p /ₘ q ^ k) %ₘ q) ≠ 0 :=
          mul_ne_zero hqp.ne_zero hmod_zero
        rw [Polynomial.degree_eq_natDegree h_mul_nz, hqk1_deg]
        have h_mul_natDeg : (q ^ k * ((p /ₘ q ^ k) %ₘ q)).natDegree
            ≤ (q ^ k).natDegree + ((p /ₘ q ^ k) %ₘ q).natDegree :=
          Polynomial.natDegree_mul_le
        rw [hqk_natDeg] at h_mul_natDeg
        exact_mod_cast (by omega : (q ^ k * ((p /ₘ q ^ k) %ₘ q)).natDegree
          < (k + 1) * q.natDegree)
    have h_mod_pq_deg : (p %ₘ q ^ k).degree < (q ^ (k + 1)).degree := by
      rw [hqk1_deg]
      by_cases hk : k = 0
      · subst hk
        rw [pow_zero, Polynomial.modByMonic_one, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · have hqk_ne_one : q ^ k ≠ 1 := by
          intro h
          have h_natDeg : (q ^ k).natDegree = 0 := by rw [h]; simp
          rw [hqk_natDeg] at h_natDeg
          rcases Nat.mul_eq_zero.mp h_natDeg with h0 | h0
          · exact hk h0
          · omega
        have h_natDeg_lt : (p %ₘ q ^ k).natDegree < (q ^ k).natDegree :=
          Polynomial.natDegree_modByMonic_lt _ hqp hqk_ne_one
        rw [hqk_natDeg] at h_natDeg_lt
        by_cases hr_z : p %ₘ q ^ k = 0
        · rw [hr_z, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
        · rw [Polynomial.degree_eq_natDegree hr_z]
          exact_mod_cast (by omega : (p %ₘ q ^ k).natDegree < (k + 1) * q.natDegree)
    rw [hr_def]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    exact max_lt h_mul_deg h_mod_pq_deg
  exact (Polynomial.div_modByMonic_unique d r hqp1 ⟨hp_eq, hr_deg⟩).1.symm

/-- `commonRootMultRatGS` of `D.divLin β` is one less than that of `D`,
when both `a` and `b` vanish at `β`. -/
private theorem commonRootMultRatGS_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    {β : ZMod E.q} (ha : D.a.eval β = 0) (hb : D.b.eval β = 0) :
    commonRootMultRatGS E (D.divLin β) β = commonRootMultRatGS E D β - 1 := by
  classical
  unfold commonRootMultRatGS
  have hDdivLnz : ¬ ((D.divLin β).a = 0 ∧ (D.divLin β).b = 0) :=
    divLin_not_both_zero E D hDnz ha hb
  by_cases h_a : D.a = 0
  · have hbz : D.b ≠ 0 := fun h => hDnz ⟨h_a, h⟩
    have h_da_div : (D.divLin β).a = 0 := by
      show D.a /ₘ (Polynomial.X - Polynomial.C β) = 0
      rw [h_a]; exact Polynomial.zero_divByMonic _
    have h_db_div : (D.divLin β).b ≠ 0 := fun h => hDdivLnz ⟨h_da_div, h⟩
    rw [if_pos h_a, if_pos h_da_div]
    show (D.b /ₘ (Polynomial.X - Polynomial.C β)).rootMultiplicity β
      = D.b.rootMultiplicity β - 1
    exact rootMultiplicity_div_X_sub_C E hbz hb
  · by_cases h_b : D.b = 0
    · have h_db_div : (D.divLin β).b = 0 := by
        show D.b /ₘ (Polynomial.X - Polynomial.C β) = 0
        rw [h_b]; exact Polynomial.zero_divByMonic _
      have h_da_div : (D.divLin β).a ≠ 0 := fun h => hDdivLnz ⟨h, h_db_div⟩
      rw [if_neg h_a, if_pos h_b, if_neg h_da_div, if_pos h_db_div]
      show (D.a /ₘ (Polynomial.X - Polynomial.C β)).rootMultiplicity β
        = D.a.rootMultiplicity β - 1
      exact rootMultiplicity_div_X_sub_C E h_a ha
    · have h_da_div : (D.divLin β).a ≠ 0 := by
        intro hq
        have hMonic : (Polynomial.X - Polynomial.C β : (ZMod E.q)[X]).Monic :=
          monic_X_sub_C _
        have h_dvd : (Polynomial.X - Polynomial.C β) ∣ D.a :=
          Polynomial.dvd_iff_isRoot.mpr ha
        have hmod : D.a %ₘ (Polynomial.X - Polynomial.C β) = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd hMonic).mpr h_dvd
        have h_eq2 := Polynomial.modByMonic_add_div D.a (Polynomial.X - Polynomial.C β)
        rw [hmod, zero_add] at h_eq2
        rw [show (D.divLin β).a = D.a /ₘ (Polynomial.X - Polynomial.C β) from rfl] at hq
        rw [← h_eq2, hq, mul_zero] at h_a
        exact h_a rfl
      have h_db_div : (D.divLin β).b ≠ 0 := by
        intro hq
        have hMonic : (Polynomial.X - Polynomial.C β : (ZMod E.q)[X]).Monic :=
          monic_X_sub_C _
        have h_dvd : (Polynomial.X - Polynomial.C β) ∣ D.b :=
          Polynomial.dvd_iff_isRoot.mpr hb
        have hmod : D.b %ₘ (Polynomial.X - Polynomial.C β) = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd hMonic).mpr h_dvd
        have h_eq2 := Polynomial.modByMonic_add_div D.b (Polynomial.X - Polynomial.C β)
        rw [hmod, zero_add] at h_eq2
        rw [show (D.divLin β).b = D.b /ₘ (Polynomial.X - Polynomial.C β) from rfl] at hq
        rw [← h_eq2, hq, mul_zero] at h_b
        exact h_b rfl
      rw [if_neg h_a, if_neg h_b, if_neg h_da_div, if_neg h_db_div]
      show min
        ((D.a /ₘ (Polynomial.X - Polynomial.C β)).rootMultiplicity β)
        ((D.b /ₘ (Polynomial.X - Polynomial.C β)).rootMultiplicity β)
      = min (D.a.rootMultiplicity β) (D.b.rootMultiplicity β) - 1
      rw [rootMultiplicity_div_X_sub_C E h_a ha, rootMultiplicity_div_X_sub_C E h_b hb]
      have ha_pos : 0 < D.a.rootMultiplicity β :=
        (Polynomial.rootMultiplicity_pos h_a).mpr ha
      have hb_pos : 0 < D.b.rootMultiplicity β :=
        (Polynomial.rootMultiplicity_pos h_b).mpr hb
      omega

/-- Iterated commutativity for `divByMonic` by powers of a monic factor:
`(p /ₘ q) /ₘ q^n = (p /ₘ q^n) /ₘ q`. Both equal `p /ₘ q^(n+1)`. -/
private theorem divByMonic_X_sub_C_comm_pow
    (p : Polynomial (ZMod E.q)) (β : ZMod E.q) (n : ℕ) :
    (p /ₘ (Polynomial.X - Polynomial.C β))
        /ₘ (Polynomial.X - Polynomial.C β) ^ n
      = (p /ₘ (Polynomial.X - Polynomial.C β) ^ n)
          /ₘ (Polynomial.X - Polynomial.C β) := by
  have hMonic : (Polynomial.X - Polynomial.C β : (ZMod E.q)[X]).Monic :=
    monic_X_sub_C _
  induction n with
  | zero => simp [Polynomial.divByMonic_one]
  | succ n IH =>
    rw [← divByMonic_pow_succ E _ hMonic]
    rw [IH]
    rw [divByMonic_pow_succ E _ hMonic]

/-- `aTildeRat` is invariant under `divLin`. -/
private theorem aTildeRat_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    {β : ZMod E.q} (ha : D.a.eval β = 0) (hb : D.b.eval β = 0) :
    aTildeRat E (D.divLin β) β = aTildeRat E D β := by
  classical
  unfold aTildeRat
  rw [commonRootMultRatGS_divLin E D hDnz ha hb]
  set k := commonRootMultRatGS E D β with hk_def
  have hk_pos : 1 ≤ k := one_le_commonRootMultRatGS_of_both_eval_zero E D hDnz β ha hb
  show D.a /ₘ (Polynomial.X - Polynomial.C β)
      /ₘ (Polynomial.X - Polynomial.C β) ^ (k - 1)
    = D.a /ₘ (Polynomial.X - Polynomial.C β) ^ k
  rw [divByMonic_X_sub_C_comm_pow E D.a β (k - 1)]
  rw [divByMonic_pow_succ E D.a (monic_X_sub_C _) (k - 1)]
  congr 2
  omega

private theorem bTildeRat_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    {β : ZMod E.q} (ha : D.a.eval β = 0) (hb : D.b.eval β = 0) :
    bTildeRat E (D.divLin β) β = bTildeRat E D β := by
  classical
  unfold bTildeRat
  rw [commonRootMultRatGS_divLin E D hDnz ha hb]
  set k := commonRootMultRatGS E D β with hk_def
  have hk_pos : 1 ≤ k := one_le_commonRootMultRatGS_of_both_eval_zero E D hDnz β ha hb
  show D.b /ₘ (Polynomial.X - Polynomial.C β)
      /ₘ (Polynomial.X - Polynomial.C β) ^ (k - 1)
    = D.b /ₘ (Polynomial.X - Polynomial.C β) ^ k
  rw [divByMonic_X_sub_C_comm_pow E D.b β (k - 1)]
  rw [divByMonic_pow_succ E D.b (monic_X_sub_C _) (k - 1)]
  congr 2
  omega

/-- `branchRat` is invariant under `divLin` in the twin case. -/
private theorem branchRat_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q)
    (ha : D.a.eval P.1 = 0) (hb : D.b.eval P.1 = 0) :
    branchRat E (D.divLin P.1) P = branchRat E D P := by
  unfold branchRat
  rw [aTildeRat_divLin E D hDnz ha hb, bTildeRat_divLin E D hDnz ha hb]

/-- `(normPoly E (D.divLin β)).rootMultiplicity β = (normPoly E D).rootMult β - 2`
when both `a` and `b` vanish at `β`. -/
private theorem rootMult_normPoly_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    {β : ZMod E.q} (ha : D.a.eval β = 0) (hb : D.b.eval β = 0) :
    (normPoly E (D.divLin β)).rootMultiplicity β
      = (normPoly E D).rootMultiplicity β - 2 := by
  classical
  have hDdivLnz : ¬ ((D.divLin β).a = 0 ∧ (D.divLin β).b = 0) :=
    divLin_not_both_zero E D hDnz ha hb
  have hN_div_ne : normPoly E (D.divLin β) ≠ 0 := normPoly_ne_zero E _ hDdivLnz
  have hXsubCNZ : (Polynomial.X - Polynomial.C β : (ZMod E.q)[X]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hsq : ((Polynomial.X - Polynomial.C β : (ZMod E.q)[X])) ^ 2 ≠ 0 :=
    pow_ne_zero _ hXsubCNZ
  have hMul : ((Polynomial.X - Polynomial.C β : (ZMod E.q)[X])) ^ 2 *
      normPoly E (D.divLin β) ≠ 0 := mul_ne_zero hsq hN_div_ne
  have hN_factor := normPoly_divLin_factor E D ha hb
  rw [hN_factor]
  rw [Polynomial.rootMultiplicity_mul hMul]
  rw [show ((Polynomial.X - Polynomial.C β : (ZMod E.q)[X])) ^ 2
      = (Polynomial.X - Polynomial.C β) * (Polynomial.X - Polynomial.C β) from sq _]
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hXsubCNZ hXsubCNZ)]
  rw [Polynomial.rootMultiplicity_X_sub_C_self]
  omega

/-! #### Geometric local order: recursion under `divLin` for non-2-torsion -/

/-- In the lone case, the rational `commonRootMultRatGS` is zero. -/
private theorem commonRootMultRatGS_eq_zero_of_lone
    (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hY : P.2 ≠ 0)
    (hZero : D.eval P.1 P.2 = 0) (hZneg : D.eval P.1 (-P.2) ≠ 0) :
    commonRootMultRatGS E D P.1 = 0 := by
  classical
  unfold commonRootMultRatGS
  have h_a_ne : D.a.eval P.1 ≠ 0 := by
    intro ha
    apply hZneg
    show D.a.eval P.1 - D.b.eval P.1 * (-P.2) = 0
    have hZ' : D.a.eval P.1 - D.b.eval P.1 * P.2 = 0 := hZero
    rw [ha] at hZ' ⊢
    have hb_zero : D.b.eval P.1 * P.2 = 0 := by linear_combination -hZ'
    rcases mul_eq_zero.mp hb_zero with hb_eval | hY_zero
    · rw [hb_eval]; ring
    · exact absurd hY_zero hY
  have h_a_poly_ne : D.a ≠ 0 := by
    intro h; apply h_a_ne; rw [h]; exact Polynomial.eval_zero
  have h_a_rm_zero : D.a.rootMultiplicity P.1 = 0 :=
    Polynomial.rootMultiplicity_eq_zero h_a_ne
  rw [if_neg h_a_poly_ne]
  by_cases h_b : D.b = 0
  · rw [if_pos h_b]; exact h_a_rm_zero
  · rw [if_neg h_b, h_a_rm_zero]
    exact Nat.min_eq_left (Nat.zero_le _)

/-- In the lone case, `branchRat = D.eval P = 0`. -/
private theorem branchRat_eq_zero_of_lone
    (D : CoordRingElt E.q)
    {P : ZMod E.q × ZMod E.q} (hY : P.2 ≠ 0)
    (hZero : D.eval P.1 P.2 = 0) (hZneg : D.eval P.1 (-P.2) ≠ 0) :
    branchRat E D P = 0 := by
  unfold branchRat aTildeRat bTildeRat
  rw [commonRootMultRatGS_eq_zero_of_lone E D hY hZero hZneg]
  rw [pow_zero, Polynomial.divByMonic_one, Polynomial.divByMonic_one]
  exact hZero

/-- The rational analogue of `rootMultiplicity_normPolyBar_ge_twice_common`:
twice the common-factor count is at most the rational `normPoly` root
multiplicity at the same point. -/
private theorem rootMultiplicity_normPoly_ge_twice_commonRootMultRatGS
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (β : ZMod E.q) :
    2 * commonRootMultRatGS E D β ≤ (normPoly E D).rootMultiplicity β := by
  classical
  have hN_ne : normPoly E D ≠ 0 := normPoly_ne_zero E D hDnz
  set k := commonRootMultRatGS E D β
  have h_dvd_a : (Polynomial.X - Polynomial.C β) ^ k ∣ D.a := by
    unfold commonRootMultRatGS at *
    by_cases h_a : D.a = 0
    · rw [h_a]; exact dvd_zero _
    · exact dvd_trans (pow_dvd_pow _
        (show k ≤ D.a.rootMultiplicity β by
          show (if D.a = 0 then D.b.rootMultiplicity β
            else if D.b = 0 then D.a.rootMultiplicity β
            else min (D.a.rootMultiplicity β) (D.b.rootMultiplicity β))
            ≤ D.a.rootMultiplicity β
          rw [if_neg h_a]
          by_cases h_b : D.b = 0
          · rw [if_pos h_b]
          · rw [if_neg h_b]; exact min_le_left _ _))
        (Polynomial.pow_rootMultiplicity_dvd D.a β)
  have h_dvd_b : (Polynomial.X - Polynomial.C β) ^ k ∣ D.b := by
    unfold commonRootMultRatGS at *
    by_cases h_a : D.a = 0
    · show (Polynomial.X - Polynomial.C β) ^ k ∣ D.b
      have : k = D.b.rootMultiplicity β := by
        show (if D.a = 0 then D.b.rootMultiplicity β
            else if D.b = 0 then D.a.rootMultiplicity β
            else min (D.a.rootMultiplicity β) (D.b.rootMultiplicity β))
            = D.b.rootMultiplicity β
        rw [if_pos h_a]
      rw [this]; exact Polynomial.pow_rootMultiplicity_dvd D.b β
    · by_cases h_b : D.b = 0
      · rw [h_b]; exact dvd_zero _
      · exact dvd_trans (pow_dvd_pow _
          (show k ≤ D.b.rootMultiplicity β by
            show (if D.a = 0 then D.b.rootMultiplicity β
              else if D.b = 0 then D.a.rootMultiplicity β
              else min (D.a.rootMultiplicity β) (D.b.rootMultiplicity β))
              ≤ D.b.rootMultiplicity β
            rw [if_neg h_a, if_neg h_b]; exact min_le_right _ _))
          (Polynomial.pow_rootMultiplicity_dvd D.b β)
  have h_sq_dvd_a : (Polynomial.X - Polynomial.C β) ^ (2 * k) ∣ D.a ^ 2 := by
    rw [show (2 * k : ℕ) = k + k from by ring, pow_add, sq]
    exact mul_dvd_mul h_dvd_a h_dvd_a
  have h_sq_dvd_b : (Polynomial.X - Polynomial.C β) ^ (2 * k) ∣ D.b ^ 2 := by
    rw [show (2 * k : ℕ) = k + k from by ring, pow_add, sq]
    exact mul_dvd_mul h_dvd_b h_dvd_b
  have h_dvd_norm : (Polynomial.X - Polynomial.C β) ^ (2 * k) ∣ normPoly E D := by
    rw [normPoly_eq]
    exact dvd_sub h_sq_dvd_a (dvd_mul_of_dvd_left h_sq_dvd_b _)
  exact (Polynomial.le_rootMultiplicity_iff hN_ne).mpr h_dvd_norm

/-- Recursion: `geomLocalOrder` at a non-2-torsion rational lift drops by
exactly 1 when both `a` and `b` vanish at `P.1`. -/
private theorem geomLocalOrder_rationalLift_divLin
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (ha : D.a.eval P.1 = 0) (hb : D.b.eval P.1 = 0) :
    geomLocalOrder E D (rationalLift E P hP) =
      geomLocalOrder E (D.divLin P.1) (rationalLift E P hP) + 1 := by
  classical
  rw [geomLocalOrder_rationalLift_non_two_torsion E D P hP hY]
  rw [geomLocalOrder_rationalLift_non_two_torsion E (D.divLin P.1) P hP hY]
  have hk : commonRootMultRatGS E (D.divLin P.1) P.1 = commonRootMultRatGS E D P.1 - 1 :=
    commonRootMultRatGS_divLin E D hDnz ha hb
  have hm : (normPoly E (D.divLin P.1)).rootMultiplicity P.1
      = (normPoly E D).rootMultiplicity P.1 - 2 :=
    rootMult_normPoly_divLin E D hDnz ha hb
  have hbranch : branchRat E (D.divLin P.1) P = branchRat E D P :=
    branchRat_divLin E D hDnz P ha hb
  have hk_pos : 1 ≤ commonRootMultRatGS E D P.1 :=
    one_le_commonRootMultRatGS_of_both_eval_zero E D hDnz P.1 ha hb
  have hm_ge_2k : 2 * commonRootMultRatGS E D P.1
      ≤ (normPoly E D).rootMultiplicity P.1 :=
    rootMultiplicity_normPoly_ge_twice_commonRootMultRatGS E D hDnz P.1
  rw [hbranch]
  by_cases hB : branchRat E D P = 0
  · simp only [hB, if_true, hk, hm]
    omega
  · simp only [hB, if_false, hk]
    omega

/-! #### `ordAt` recursion and bridge -/

private theorem ordAt_nonTwoTorsion_aux_succ (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (n : ℕ) :
    ordAt_nonTwoTorsion_aux E (n + 1) D P =
      (if D.a = 0 ∧ D.b = 0 then 0
        else if D.eval P.1 P.2 ≠ 0 then 0
        else if D.eval P.1 (-P.2) ≠ 0 then
          Polynomial.rootMultiplicity P.1 (normPoly E D)
        else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P) := rfl

/-- Auxiliary: bridge for the fuel-form on non-2-torsion. -/
private theorem ordAt_nonTwoTorsion_aux_eq_geomLocalOrder
    (n : ℕ) (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (hFuel : D.a.natDegree + D.b.natDegree < n)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0) :
    ordAt_nonTwoTorsion_aux E n D P
      = geomLocalOrder E D (rationalLift E P hP) := by
  classical
  induction n generalizing D with
  | zero => omega
  | succ n IH =>
    rw [ordAt_nonTwoTorsion_aux_succ]
    rw [if_neg hDnz]
    by_cases hEvalP : D.eval P.1 P.2 = 0
    · rw [if_neg (not_not.mpr hEvalP)]
      by_cases hEvalNegP : D.eval P.1 (-P.2) = 0
      · rw [if_neg (not_not.mpr hEvalNegP)]
        obtain ⟨ha, hb⟩ :=
          Da_Db_eval_zero_of_both_sheets_zero E D hY hEvalP hEvalNegP
        have hDdivLnz : ¬ ((D.divLin P.1).a = 0 ∧ (D.divLin P.1).b = 0) :=
          divLin_not_both_zero E D hDnz ha hb
        have hLT := divLin_natDegree_sum_lt E D hDnz ha hb
        have hFuel' : (D.divLin P.1).a.natDegree + (D.divLin P.1).b.natDegree < n := by
          omega
        have hIH := IH (D.divLin P.1) hDdivLnz hFuel'
        rw [hIH]
        have h_eq := geomLocalOrder_rationalLift_divLin E D hDnz P hP hY ha hb
        omega
      · push_neg at hEvalNegP
        rw [if_pos hEvalNegP]
        rw [geomLocalOrder_rationalLift_non_two_torsion E D P hP hY]
        have hk : commonRootMultRatGS E D P.1 = 0 :=
          commonRootMultRatGS_eq_zero_of_lone E D hY hEvalP hEvalNegP
        have hbr : branchRat E D P = 0 :=
          branchRat_eq_zero_of_lone E D hY hEvalP hEvalNegP
        simp only [hbr, if_true, hk, Nat.sub_zero]
    · push_neg at hEvalP
      rw [if_pos hEvalP]
      have hGeomZero_iff_evalZero :
          D.geomEval E (rationalLift E P hP) = fqToBar E (D.eval P.1 P.2) := by
        show D.geomEval E (⟨fqToBar E P.1, fqToBar E P.2, _⟩ : GeomPoint E)
            = fqToBar E (D.eval P.1 P.2)
        exact geomEval_lift_eq_fqToBar E D P (E.hOnCurve P hP)
      have hGeomNonZero : D.geomEval E (rationalLift E P hP) ≠ 0 := by
        rw [hGeomZero_iff_evalZero]
        exact (fqToBar_eq_zero_iff E _).not.mpr hEvalP
      exact (geomLocalOrder_eq_zero_of_geomEval_ne_zero E D hDnz _ hGeomNonZero).symm

/-- `ordAt` agrees with `geomLocalOrder` at a rational lift. -/
private theorem ordAt_eq_geomLocalOrder_at_rationalLift
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    ordAt E D P = geomLocalOrder E D (rationalLift E P hP) := by
  classical
  by_cases hY : P.2 = 0
  · rw [ordAt_eq_dispatch E D hP hDnz, if_pos hY]
    rw [ordAt_twoTorsion_eq_rootMult_normPoly E D hDnz hP hY]
    exact (geomLocalOrder_rationalLift_two_torsion E D P hP hY).symm
  · rw [ordAt_eq_dispatch E D hP hDnz, if_neg hY]
    show ordAt_nonTwoTorsion E D P = _
    unfold ordAt_nonTwoTorsion
    exact ordAt_nonTwoTorsion_aux_eq_geomLocalOrder E
      (D.a.natDegree + D.b.natDegree + 1) D hDnz (by omega) P hP hY

private theorem gd_mult_rationalLift_eq_betaTrue
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    gd.mult (rationalLift E P hP) = betaTrue E D hD P := by
  rw [gd.mult_eq_geomLocalOrder]
  rw [← ordAt_eq_geomLocalOrder_at_rationalLift E D hD P hP]
  rfl

/-! ## Split rationality of the geometric support -/

set_option maxHeartbeats 800000 in
private theorem support_point_unique_rational_zero_of_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    ∃! P : ZMod E.q × ZMod E.q,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 := by
  have hGeomZero : D.geomEval E Q = 0 := gd.support_eval_zero Q hQ
  have hxRoot : (normPolyBar E D).IsRoot Q.x :=
    normPolyBar_eval_zero_of_geomEval_zero E D Q hGeomZero
  obtain ⟨α, hαroot, hxα⟩ :=
    normPolyBar_root_in_base_of_split E D hD hSplitOnE hxRoot
  obtain ⟨y, hyPoint⟩ := hSplitOnE.2 α hαroot
  have hySq : Q.y ^ 2 = (fqToBar E y) ^ 2 := by
    calc
      Q.y ^ 2 = Q.x ^ 3 + fqToBar E E.curveA * Q.x + fqToBar E E.curveB := Q.onCurve
      _ = (fqToBar E α) ^ 3 + fqToBar E E.curveA * (fqToBar E α) +
          fqToBar E E.curveB := by rw [hxα]
      _ = fqToBar E (α ^ 3 + E.curveA * α + E.curveB) := by
          unfold fqToBar
          rw [map_add, map_add, map_pow, map_mul]
      _ = fqToBar E (y ^ 2) := by rw [← E.hOnCurve (α, y) hyPoint]
      _ = (fqToBar E y) ^ 2 := by
          unfold fqToBar
          rw [map_pow]
  have hprod : (Q.y - fqToBar E y) * (Q.y + fqToBar E y) = 0 := by
    rw [show (Q.y - fqToBar E y) * (Q.y + fqToBar E y)
        = Q.y ^ 2 - (fqToBar E y) ^ 2 by ring]
    exact sub_eq_zero.mpr hySq
  have hExists :
      ∃ P : ZMod E.q × ZMod E.q,
        P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 := by
    rcases mul_eq_zero.mp hprod with hy | hy
    · refine ⟨(α, y), ?_, hxα, ?_⟩
      · rw [zerosFinset, zeros, Finset.mem_filter]
        refine ⟨hyPoint, ?_⟩
        have hEvalBar := geomEval_eq_fqToBar_of_coords E D Q (α, y) hxα (sub_eq_zero.mp hy)
        rw [hEvalBar] at hGeomZero
        exact (fqToBar_eq_zero_iff E _).mp hGeomZero
      · exact sub_eq_zero.mp hy
    · have hyNegPoint : (α, -y) ∈ E.points := by
        apply E.hComplete
        rw [show (-y) ^ 2 = y ^ 2 by ring]
        exact E.hOnCurve (α, y) hyPoint
      refine ⟨(α, -y), ?_, hxα, ?_⟩
      · rw [zerosFinset, zeros, Finset.mem_filter]
        refine ⟨hyNegPoint, ?_⟩
        have hyQ : Q.y = fqToBar E (-y) := by
          have hy' : Q.y = -fqToBar E y := by
            exact eq_neg_of_add_eq_zero_left hy
          rw [hy']
          unfold fqToBar
          rw [map_neg]
        have hEvalBar := geomEval_eq_fqToBar_of_coords E D Q (α, -y) hxα hyQ
        rw [hEvalBar] at hGeomZero
        exact (fqToBar_eq_zero_iff E _).mp hGeomZero
      · have hy' : Q.y = -fqToBar E y := eq_neg_of_add_eq_zero_left hy
        rw [hy']
        unfold fqToBar
        rw [map_neg]
  rcases hExists with ⟨P, hPzero, hPx, hPy⟩
  refine ⟨P, ⟨hPzero, hPx, hPy⟩, ?_⟩
  intro P' hP'
  have hx : fqToBar E P'.1 = fqToBar E P.1 := by rw [← hP'.2.1, hPx]
  have hy : fqToBar E P'.2 = fqToBar E P.2 := by rw [← hP'.2.2, hPy]
  exact Prod.ext ((fqToBar_injective E) hx) ((fqToBar_injective E) hy)

private theorem geom_prod_eq_normZ_bar_prod_under_split
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P)
    (gd : GeometricDivisorData E D) :
    (∏ Q ∈ gd.support,
        (X - C (zLambdaBar E lam Q)) ^ gd.mult Q : Polynomial (Fqbar E))
      =
    ∏ P ∈ zerosFinset E D,
        (X - C (fqToBar E (zLambda E lam P))) ^ β_fun P := by
  classical
  let f : (Q : GeomPoint E) → Q ∈ gd.support → ZMod E.q × ZMod E.q :=
    fun Q hQ => (support_point_unique_rational_zero_of_split E D hD hSplitOnE gd Q hQ).choose
  have hSpec : ∀ Q (hQ : Q ∈ gd.support),
      f Q hQ ∈ zerosFinset E D ∧ Q.x = fqToBar E (f Q hQ).1 ∧
        Q.y = fqToBar E (f Q hQ).2 :=
    fun Q hQ => (support_point_unique_rational_zero_of_split E D hD hSplitOnE gd Q hQ).choose_spec.1
  have hUniq : ∀ Q (hQ : Q ∈ gd.support) P,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 →
      P = f Q hQ :=
    fun Q hQ P hP =>
      (support_point_unique_rational_zero_of_split E D hD hSplitOnE gd Q hQ).choose_spec.2 P hP
  refine Finset.prod_bij f ?_ ?_ ?_ ?_
  · intro Q hQ
    exact (hSpec Q hQ).1
  · intro Q₁ hQ₁ Q₂ hQ₂ heq
    have hP₁ := hSpec Q₁ hQ₁
    have hP₂ := hSpec Q₂ hQ₂
    have hx : Q₁.x = Q₂.x := by rw [hP₁.2.1, heq, ← hP₂.2.1]
    have hy : Q₁.y = Q₂.y := by rw [hP₁.2.2, heq, ← hP₂.2.2]
    cases Q₁
    cases Q₂
    simp only [GeomPoint.mk.injEq] at hx hy ⊢
    exact ⟨hx, hy⟩
  · intro P hP
    change P ∈ zeros D E.points at hP
    rw [zeros, Finset.mem_filter] at hP
    obtain ⟨hPpts, hPzero⟩ := hP
    refine ⟨rationalLift E P hPpts,
      support_lift_of_rational_zero E D gd P hPpts hPzero, ?_⟩
    exact (hUniq (rationalLift E P hPpts)
      (support_lift_of_rational_zero E D gd P hPpts hPzero)
      P ⟨by
          change P ∈ zeros D E.points
          rw [zeros, Finset.mem_filter]
          exact ⟨hPpts, hPzero⟩,
        rfl, rfl⟩).symm
  · intro Q hQ
    have hPmem := (hSpec Q hQ).1
    have hPpts : f Q hQ ∈ E.points := by
      change f Q hQ ∈ zeros D E.points at hPmem
      rw [zeros, Finset.mem_filter] at hPmem
      exact hPmem.1
    have hQeq : Q = rationalLift E (f Q hQ) hPpts :=
      geomPoint_eq_rationalLift_of_coords E Q (f Q hQ) hPpts
        (hSpec Q hQ).2.1 (hSpec Q hQ).2.2
    have hz :
        zLambdaBar E lam Q = fqToBar E (zLambda E lam (f Q hQ)) := by
      unfold zLambdaBar zLambda
      rw [(hSpec Q hQ).2.2, (hSpec Q hQ).2.1]
      unfold fqToBar
      rw [map_sub, map_mul]
    have hm :
        gd.mult Q = β_fun (f Q hQ) := by
      calc
        gd.mult Q = gd.mult (rationalLift E (f Q hQ) hPpts) := congrArg gd.mult hQeq
        _ = betaTrue E D hD (f Q hQ) :=
            gd_mult_rationalLift_eq_betaTrue E D hD gd (f Q hQ) hPpts
        _ = β_fun (f Q hQ) := (hβtrue (f Q hQ)).symm
    rw [hz, hm]

/-! ## Concrete bar factorisation, local to this bridge -/

private theorem concrete_bar_zfiber_sum_eq_zero_of_not_image
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (gd : GeometricDivisorData E D) {z : Fqbar E}
    (hz : z ∉ gd.support.image (zLambdaBar E lam)) :
    (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro Q hQ
  exfalso
  rcases Finset.mem_filter.mp hQ with ⟨hQs, hQe⟩
  exact hz (Finset.mem_image.mpr ⟨Q, hQs, hQe⟩)

private theorem concrete_bar_rootMultiplicity_eq_zero_of_not_image
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) {z : Fqbar E}
    (hz : z ∉ gd.support.image (zLambdaBar E lam)) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
      (chord_fiber_product_concrete E lam D)).rootMultiplicity z = 0 := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hroots :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
      E lam D hD gd
  have hnot_root : ¬ p.IsRoot z := by
    intro hroot
    apply hz
    rw [← hroots]
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots' (p := p)).mpr ⟨hpne, hroot⟩)
  exact Polynomial.rootMultiplicity_eq_zero hnot_root

private theorem concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z ∈ gd.support.image (zLambdaBar E lam),
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hroots :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
      E lam D hD gd
  have hdvd : ∀ z ∈ gd.support.image (zLambdaBar E lam),
      (Polynomial.X - Polynomial.C z) ^
        (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
        ∣ p :=
    fun z _ =>
      chord_fiber_product_concrete_bar_zfiber_pow_dvd E D lam hD gd z
  have hdeg : p.natDegree ≤ ∑ Q ∈ gd.support, gd.mult Q := by
    rw [GeometricDivisorData.mult_sum_eq_normPoly_natDegree E D hD gd]
    rw [hp_def, Polynomial.natDegree_map_eq_of_injective
          (algebraMap (ZMod E.q) (Fqbar E)).injective]
    exact chord_fiber_product_concrete_natDegree_le_normPoly_natDegree E lam D hD
  exact fun z hz =>
    Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le
      p gd.support (zLambdaBar E lam) gd.mult hpne hroots hdvd hdeg z

private theorem concrete_bar_rootMultiplicity_eq_zfiber
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  classical
  intro z
  by_cases hz : z ∈ gd.support.image (zLambdaBar E lam)
  · exact concrete_bar_rootMultiplicity_eq_zfiber_of_mem_image E D lam hD gd z hz
  · rw [concrete_bar_rootMultiplicity_eq_zero_of_not_image E D lam hD gd hz,
        concrete_bar_zfiber_sum_eq_zero_of_not_image E D lam gd hz]

private theorem concrete_bar_eq_geom_prod
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hpsplit : p.Splits := IsAlgClosed.splits _
  have hcard : p.roots.card = p.natDegree := hpsplit.natDegree_eq_card_roots.symm
  refine ⟨p.leadingCoeff, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hfac :
      C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hrootSet :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image E lam D hD gd
  have hZ := concrete_bar_rootMultiplicity_eq_zfiber E D lam hD gd
  have hMaps : ∀ Q ∈ gd.support, zLambdaBar E lam Q ∈
      gd.support.image (zLambdaBar E lam) :=
    fun Q hQ => Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
  have hprod :
      (p.roots.map fun a => X - C a).prod =
        ∏ Q ∈ gd.support, (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
    rw [Finset.prod_multiset_map_count]
    rw [hrootSet]
    have hcount_eq : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (X - C z) ^ (p.roots.count z) =
        (X - C z) ^
          (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
            gd.mult Q) := by
      intro z _
      rw [Polynomial.count_roots, hZ]
    rw [Finset.prod_congr rfl hcount_eq]
    rw [Finset.prod_congr rfl
      (fun z _ => (Finset.prod_pow_eq_pow_sum
        (gd.support.filter (fun Q => zLambdaBar E lam Q = z))
        gd.mult (X - C z)).symm)]
    have hZreplace : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (X - C z) ^ (gd.mult Q)) =
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)) := by
      intro z _
      refine Finset.prod_congr rfl ?_
      intro Q hQ
      rw [(Finset.mem_filter.mp hQ).2]
    rw [Finset.prod_congr rfl hZreplace]
    exact Finset.prod_fiberwise_of_maps_to hMaps
      (fun Q => (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q))
  conv_lhs => rw [← hfac]
  rw [hprod]

private theorem normZ_map_eq_C_mul_bar_prod
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ) :
    (normZ E lam D β_fun).map (algebraMap (ZMod E.q) (Fqbar E)) =
      C (fqToBar E (normPoly E D).leadingCoeff) *
        ∏ P ∈ zerosFinset E D,
          (X - C (fqToBar E (zLambda E lam P))) ^ β_fun P := by
  classical
  unfold normZ fqToBar
  simp [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem concrete_bar_eq_normZ_bar_under_split
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P) :
    ∃ cBar : Fqbar E, cBar ≠ 0 ∧
      (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E)) =
        C cBar *
          (normZ E lam D β_fun).map (algebraMap (ZMod E.q) (Fqbar E)) := by
  classical
  obtain ⟨support, hSupportZero, hZeroSupport⟩ :=
    exists_geometric_zero_support E D hD
  obtain ⟨gd, _hgd⟩ :=
    exists_geometricDivisorData_of_support E D hD support hSupportZero hZeroSupport
  obtain ⟨cGeom, hcGeom, hGeom⟩ := concrete_bar_eq_geom_prod E D lam hD gd
  have hProd :=
    geom_prod_eq_normZ_bar_prod_under_split E D lam hD hSplitOnE β_fun hβtrue gd
  have hNormMap := normZ_map_eq_C_mul_bar_prod E D lam β_fun
  set lcBar : Fqbar E := fqToBar E (normPoly E D).leadingCoeff
  have hlcBar_ne : lcBar ≠ 0 := by
    unfold lcBar fqToBar
    exact fun h => normPoly_leadingCoeff_ne_zero E D hD ((fqToBar_eq_zero_iff E _).mp h)
  refine ⟨cGeom * lcBar⁻¹, mul_ne_zero hcGeom (inv_ne_zero hlcBar_ne), ?_⟩
  rw [hGeom, hProd, hNormMap]
  show C cGeom *
      (∏ P ∈ zerosFinset E D, (X - C (fqToBar E (zLambda E lam P))) ^ β_fun P) =
    C (cGeom * lcBar⁻¹) *
      (C lcBar *
        ∏ P ∈ zerosFinset E D, (X - C (fqToBar E (zLambda E lam P))) ^ β_fun P)
  rw [← mul_assoc, ← C_mul]
  rw [mul_assoc, inv_mul_cancel₀ hlcBar_ne, mul_one]

/-- Concrete chord-fiber product as a scalar multiple of `normZ` under
split-rational true multiplicities. -/
theorem chord_fiber_product_concrete_eq_normZ_under_split
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplitOnE : splitsOnE E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (_hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (_hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (_hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree)
    (hβtrue : ∀ P, β_fun P = betaTrue E D hD P) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      chord_fiber_product_concrete E lam D = C c * normZ E lam D β_fun := by
  classical
  set f := chord_fiber_product_concrete E lam D with hf_def
  set g := normZ E lam D β_fun with hg_def
  have hf_ne : f ≠ 0 := chord_fiber_product_concrete_ne_zero E lam D hD
  have hg_ne : g ≠ 0 := normZ_ne_zero E lam D hD β_fun
  obtain ⟨cBar, _hcBar_ne, hbar⟩ :=
    concrete_bar_eq_normZ_bar_under_split E D lam hD hSplitOnE β_fun hβtrue
  set φ : ZMod E.q →+* Fqbar E := algebraMap (ZMod E.q) (Fqbar E)
  have hφ_inj : Function.Injective φ :=
    (algebraMap (ZMod E.q) (Fqbar E)).injective
  have hlc_eq : φ f.leadingCoeff = cBar * φ g.leadingCoeff := by
    have h_lc :
        (f.map φ).leadingCoeff =
          (Polynomial.C cBar * g.map φ).leadingCoeff := by rw [hbar]
    have _hg_map_ne : g.map φ ≠ 0 := Polynomial.map_ne_zero hg_ne
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h_lc
    rw [Polynomial.leadingCoeff_map_of_injective hφ_inj f,
        Polynomial.leadingCoeff_map_of_injective hφ_inj g] at h_lc
    exact h_lc
  have hg_lc_ne : g.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hg_ne
  refine ⟨f.leadingCoeff * g.leadingCoeff⁻¹, ?_, ?_⟩
  · have hf_lc_ne : f.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hf_ne
    exact mul_ne_zero hf_lc_ne (inv_ne_zero hg_lc_ne)
  · have hφc : φ (f.leadingCoeff * g.leadingCoeff⁻¹) = cBar := by
      rw [map_mul, map_inv₀]
      have hφg_ne : φ g.leadingCoeff ≠ 0 := by
        rw [Ne, ← map_zero φ]; exact fun h => hg_lc_ne (hφ_inj h)
      rw [hlc_eq]
      field_simp
    have hmap_eq :
        f.map φ = (Polynomial.C (f.leadingCoeff * g.leadingCoeff⁻¹) * g).map φ := by
      rw [Polynomial.map_mul, Polynomial.map_C]
      rw [hφc]
      exact hbar
    exact Polynomial.map_injective φ hφ_inj hmap_eq

end Divisor
