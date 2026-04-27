/-
  Divisor/GeometricSoundness.lean

  Geometric-zero replacement path for the log-derivative soundness proof.

  The older tight proof routed through `zerosAt : Fin d → E(F_q)` and a
  rational-point multiplicity function. That is the wrong abstraction for
  arbitrary cheating divisors: the zero divisor of `D` naturally lives over
  `F_qbar`, and only the final cleared polynomial should descend to `F_q`.

  This file introduces the clean geometric API and records the hard proof
  obligations as named theorems with `sorry`. The headline theorem imports
  these branch theorems instead of carrying `splitsOnE` as an external
  hypothesis.
-/
import Divisor.ExtractorBridge
import Divisor.TightBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Algebraic-closure model -/

/-- The algebraic closure of the base field of `E`. -/
abbrev Fqbar : Type := AlgebraicClosure (ZMod E.q)

/-- Four-variable polynomials after base-change to `F_qbar`. -/
abbrev FourVarPolyBar : Type := MvPolynomial (Fin 4) (Fqbar E)

/-- Coefficient base-change for the existing four-variable polynomial ring. -/
noncomputable def baseChangeFourVar (f : FourVarPoly E.q) : FourVarPolyBar E :=
  MvPolynomial.map (algebraMap (ZMod E.q) (Fqbar E)) f

/-- Embed a base-field scalar into `F_qbar`. -/
noncomputable def fqToBar (x : ZMod E.q) : Fqbar E :=
  algebraMap (ZMod E.q) (Fqbar E) x

/-- The norm polynomial after coefficient base-change to `F_qbar`. -/
noncomputable def normPolyBar (D : CoordRingElt E.q) : Polynomial (Fqbar E) :=
  Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) (normPoly E D)

/-- An affine geometric point on the base-changed short Weierstrass curve. -/
structure GeomPoint where
  x : Fqbar E
  y : Fqbar E
  onCurve :
    y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB

namespace CoordRingElt

/-- Evaluation of a coordinate-ring element at a geometric point. -/
noncomputable def geomEval (D : CoordRingElt E.q) (Q : GeomPoint E) : Fqbar E :=
  D.a.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x
    - D.b.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x * Q.y

end CoordRingElt

/-! ## Geometric divisor data -/

/--
`n` is the geometric local zero multiplicity of `D` at `Q`.

This is the local-order interface. The intended implementation is the
order of vanishing of the base-changed coordinate-ring element in the
completed local ring at the smooth affine point `Q`. The root-multiplicity
bound records the part that can be related directly to mathlib's
univariate `Polynomial.rootMultiplicity`; the remaining local-order
content is carried by the named existence and stability lemmas below.
-/
def IsGeometricZeroMultiplicity (D : CoordRingElt E.q) (Q : GeomPoint E)
    (n : ℕ) : Prop :=
  D.geomEval E Q = 0 ∧
  0 < n ∧
  n ≤ (normPolyBar E D).rootMultiplicity Q.x

/--
Finite geometric zero divisor of a nonzero `CoordRingElt`.

The support is over `F_qbar`, not `E(F_q)`. Multiplicities are local
orders. The Frobenius-stability field is stated without constructing a
separate geometric-point Frobenius map; this keeps the interface close to
the descent proof that the final product has coefficients in `F_q`.
-/
structure GeometricDivisorData (D : CoordRingElt E.q) where
  support : Finset (GeomPoint E)
  mult : GeomPoint E → ℕ
  support_eval_zero : ∀ Q ∈ support, D.geomEval E Q = 0
  eval_zero_mem_support : ∀ Q, D.geomEval E Q = 0 → Q ∈ support
  multiplicity_spec :
    ∀ Q ∈ support, IsGeometricZeroMultiplicity E D Q (mult Q)
  mult_pos_on_support : ∀ Q ∈ support, 0 < mult Q
  mult_zero_off_support : ∀ Q, Q ∉ support → mult Q = 0
  accounting_le_degE : (∑ Q ∈ support, mult Q) ≤ D.degE
  fiber_accounting :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), mult Q)
        = (normPolyBar E D).rootMultiplicity α
  frobenius_stable :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧ mult Q' = mult Q

/--
Finite geometric zero support.

This is the support-only part of the construction. It should be proved by
mapping geometric zeros of `D` into roots of `normPolyBar E D` and using
the fact that each affine fiber of `x : E → A¹` has at most two points.
-/
private theorem normPolyBar_eval_zero_of_geomEval_zero
    (D : CoordRingElt E.q) (Q : GeomPoint E)
    (hQ : D.geomEval E Q = 0) :
    (normPolyBar E D).eval Q.x = 0 := by
  unfold CoordRingElt.geomEval normPolyBar at *
  rw [normPoly_eq]
  simp_all +decide [sub_eq_iff_eq_add, Polynomial.eval_map]
  unfold curveX
  simp +decide [mul_pow, Q.onCurve]
  exact Or.inl rfl

private theorem geom_zero_set_finite'
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    Set.Finite {Q : GeomPoint E | D.geomEval E Q = 0} := by
  have hne : normPolyBar E D ≠ 0 := by
    unfold normPolyBar
    exact Polynomial.map_ne_zero (normPoly_ne_zero E D hDnz)
  have h_roots_finite : Set.Finite {x : Fqbar E | (normPolyBar E D).IsRoot x} := by
    convert ((normPolyBar E D).roots.toFinset |> Finset.finite_toSet) using 1
    ext x
    simp [Polynomial.mem_roots hne]
  have h_fiber_finite : ∀ x : Fqbar E,
      Set.Finite {y : Fqbar E |
        y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB} := by
    intro x
    set b := x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB
    have h_poly : ∀ y : Fqbar E, y ^ 2 = b →
        y ∈ (Polynomial.X ^ 2 - Polynomial.C b : Polynomial (Fqbar E)).roots.toFinset := by
      intro y hy
      simp only [Multiset.mem_toFinset]
      rw [Polynomial.mem_roots (by exact ne_of_apply_ne Polynomial.natDegree (by norm_num))]
      simp [Polynomial.IsRoot, sub_eq_zero]
      exact hy
    exact Set.Finite.subset (Multiset.finite_toSet _) h_poly
  have h_image_finite : Set.Finite
      (Set.image (fun Q : GeomPoint E => (Q.x, Q.y))
        {Q : GeomPoint E | D.geomEval E Q = 0}) := by
    apply Set.Finite.subset
      (h_roots_finite.biUnion fun x _ => (h_fiber_finite x).image fun y => (x, y))
    intro p hp
    simp only [Set.mem_image, Set.mem_setOf_eq] at hp
    obtain ⟨Q, hQ, hQp⟩ := hp
    rw [← hQp]
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq]
    exact
      ⟨Q.x, normPolyBar_eval_zero_of_geomEval_zero E D Q hQ,
        Q.y, Q.onCurve, rfl, rfl⟩
  exact h_image_finite.of_finite_image
    (fun Q1 _ Q2 _ h => by
      cases Q1
      cases Q2
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      subst h2
      rfl)

theorem exists_geometric_zero_support
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ support : Finset (GeomPoint E),
      (∀ Q ∈ support, D.geomEval E Q = 0) ∧
      (∀ Q, D.geomEval E Q = 0 → Q ∈ support) := by
  have hfin := geom_zero_set_finite' E D hDnz
  exact ⟨hfin.toFinset,
    fun Q hQ => by rwa [Set.Finite.mem_toFinset] at hQ,
    fun Q hQ => by rwa [Set.Finite.mem_toFinset]⟩

/--
Construction of the geometric zero divisor over a fixed finite support.

This is the hard local-algebra obligation. The multiplicity function must
be the true order of vanishing of the base-changed coordinate-ring element
at each smooth geometric point, not a pointwise arbitrary choice. The
fields of `GeometricDivisorData` record the global properties needed
downstream: positivity, zero off support, fiber accounting against
`rootMultiplicity (normPolyBar E D)`, total degree accounting, and
Frobenius stability.
-/
theorem exists_geometricDivisorData_of_support
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∃ gd : GeometricDivisorData E D, gd.support = support := by
  sorry

/--
Existence of the geometric zero divisor of a nonzero coordinate-ring
element.

PROVIDED SOLUTION
Base-change the affine coordinate ring of `E` to `F_qbar`. For nonzero
`D`, its principal divisor has finite affine zero support. Define
`mult Q` as the local order at the smooth point `Q`. Finiteness and
`accounting_le_degE` follow from the degree of the x-norm/intersection
with the affine Weierstrass model. Since `D` has coefficients in `F_q`,
Frobenius carries zeros to zeros and preserves local order.
-/
theorem exists_geometricDivisorData
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ _gd : GeometricDivisorData E D, True := by
  classical
  obtain ⟨support, hSupportZero, hZeroSupport⟩ :=
    exists_geometric_zero_support E D hDnz
  obtain ⟨gd, _hgd⟩ :=
    exists_geometricDivisorData_of_support E D hDnz support hSupportZero hZeroSupport
  exact ⟨gd, trivial⟩

/-! ## Geometric `polyGFull` over `F_qbar` -/

/-- Geometric version of `lineEvalNumAtFull`, with a geometric point as
the fixed point on the line. -/
noncomputable def lineEvalNumAtFullBar (Q : GeomPoint E) : FourVarPolyBar E :=
  ((MvPolynomial.C Q.y : FourVarPolyBar E) - (MvPolynomial.X 1 : FourVarPolyBar E))
      * ((MvPolynomial.X 2 : FourVarPolyBar E) - (MvPolynomial.X 0 : FourVarPolyBar E))
    - ((MvPolynomial.C Q.x : FourVarPolyBar E) - (MvPolynomial.X 0 : FourVarPolyBar E))
      * ((MvPolynomial.X 3 : FourVarPolyBar E) - (MvPolynomial.X 1 : FourVarPolyBar E))

/-- Same line factor, but for a base-field point embedded into `F_qbar`. -/
noncomputable def lineEvalNumAtFullBarOfFq
    (P : ZMod E.q × ZMod E.q) : FourVarPolyBar E :=
  ((MvPolynomial.C (fqToBar E P.2) : FourVarPolyBar E)
      - (MvPolynomial.X 1 : FourVarPolyBar E))
      * ((MvPolynomial.X 2 : FourVarPolyBar E) - (MvPolynomial.X 0 : FourVarPolyBar E))
    - ((MvPolynomial.C (fqToBar E P.1) : FourVarPolyBar E)
      - (MvPolynomial.X 0 : FourVarPolyBar E))
      * ((MvPolynomial.X 3 : FourVarPolyBar E) - (MvPolynomial.X 1 : FourVarPolyBar E))

/-! ### Degree accounting over `F_qbar` -/

private def bar_total_degree_le (f : FourVarPolyBar E) (D : ℕ) : Prop :=
  f.totalDegree ≤ D

private theorem bar_total_degree_le.add
    {f g : FourVarPolyBar E} {D : ℕ}
    (hf : bar_total_degree_le E f D) (hg : bar_total_degree_le E g D) :
    bar_total_degree_le E (f + g) D :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le hf hg)

private theorem bar_total_degree_le.sub
    {f g : FourVarPolyBar E} {D : ℕ}
    (hf : bar_total_degree_le E f D) (hg : bar_total_degree_le E g D) :
    bar_total_degree_le E (f - g) D := by
  exact (MvPolynomial.totalDegree_sub f g).trans (max_le hf hg)

private theorem bar_total_degree_le.mul
    {f g : FourVarPolyBar E} {Df Dg : ℕ}
    (hf : bar_total_degree_le E f Df) (hg : bar_total_degree_le E g Dg) :
    bar_total_degree_le E (f * g) (Df + Dg) :=
  (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hf hg)

private theorem bar_total_degree_le.C (c : Fqbar E) :
    bar_total_degree_le E (MvPolynomial.C c : FourVarPolyBar E) 0 := by
  unfold bar_total_degree_le
  rw [MvPolynomial.totalDegree_C]

private theorem bar_total_degree_le.X (i : Fin 4) :
    bar_total_degree_le E (MvPolynomial.X i : FourVarPolyBar E) 1 := by
  unfold bar_total_degree_le
  rw [MvPolynomial.totalDegree_X]

private theorem bar_total_degree_le.mono
    {f : FourVarPolyBar E} {D D' : ℕ}
    (hf : bar_total_degree_le E f D) (h : D ≤ D') :
    bar_total_degree_le E f D' :=
  hf.trans h

private theorem bar_total_degree_le.sum
    {α : Type*} (s : Finset α) (f : α → FourVarPolyBar E)
    {D : ℕ} (hf : ∀ i ∈ s, bar_total_degree_le E (f i) D) :
    bar_total_degree_le E (∑ i ∈ s, f i) D :=
  MvPolynomial.totalDegree_finsetSum_le hf

private theorem bar_total_degree_le.prod_const
    {α : Type*} (s : Finset α) (f : α → FourVarPolyBar E)
    {D : ℕ} (hf : ∀ i ∈ s, bar_total_degree_le E (f i) D) :
    bar_total_degree_le E (∏ i ∈ s, f i) (s.card * D) := by
  refine (MvPolynomial.totalDegree_finset_prod s f).trans ?_
  calc (∑ i ∈ s, (f i).totalDegree)
      ≤ ∑ _i ∈ s, D := Finset.sum_le_sum hf
    _ = s.card * D := by rw [Finset.sum_const]; ring

private theorem lineEvalNumAtFullBar_total_degree_le (Q : GeomPoint E) :
    bar_total_degree_le E (lineEvalNumAtFullBar E Q) 2 := by
  unfold lineEvalNumAtFullBar
  refine bar_total_degree_le.sub E ?_ ?_
  · exact bar_total_degree_le.mul E
      (bar_total_degree_le.sub E
        (bar_total_degree_le.mono E (bar_total_degree_le.C E Q.y) (Nat.zero_le _))
        (bar_total_degree_le.X E 1))
      (bar_total_degree_le.sub E (bar_total_degree_le.X E 2) (bar_total_degree_le.X E 0))
  · exact bar_total_degree_le.mul E
      (bar_total_degree_le.sub E
        (bar_total_degree_le.mono E (bar_total_degree_le.C E Q.x) (Nat.zero_le _))
        (bar_total_degree_le.X E 0))
      (bar_total_degree_le.sub E (bar_total_degree_le.X E 3) (bar_total_degree_le.X E 1))

private theorem lineEvalNumAtFullBarOfFq_total_degree_le
    (P : ZMod E.q × ZMod E.q) :
    bar_total_degree_le E (lineEvalNumAtFullBarOfFq E P) 2 := by
  unfold lineEvalNumAtFullBarOfFq
  refine bar_total_degree_le.sub E ?_ ?_
  · exact bar_total_degree_le.mul E
      (bar_total_degree_le.sub E
        (bar_total_degree_le.mono E (bar_total_degree_le.C E (fqToBar E P.2)) (Nat.zero_le _))
        (bar_total_degree_le.X E 1))
      (bar_total_degree_le.sub E (bar_total_degree_le.X E 2) (bar_total_degree_le.X E 0))
  · exact bar_total_degree_le.mul E
      (bar_total_degree_le.sub E
        (bar_total_degree_le.mono E (bar_total_degree_le.C E (fqToBar E P.1)) (Nat.zero_le _))
        (bar_total_degree_le.X E 0))
      (bar_total_degree_le.sub E (bar_total_degree_le.X E 3) (bar_total_degree_le.X E 1))

/--
The geometric `polyGFull` numerator over `F_qbar`.

The first sum ranges over the geometric support of `D`; the second sum
ranges over the prescribed rational divisor points `R`.
-/
noncomputable def geomPolyGFullBar
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    FourVarPolyBar E := by
  classical
  exact
    (∑ Q ∈ gd.support,
      (MvPolynomial.C ((gd.mult Q : ℕ) : Fqbar E) : FourVarPolyBar E)
        * (∏ Q' ∈ gd.support.erase Q, lineEvalNumAtFullBar E Q')
        * (∏ j : Fin M, lineEvalNumAtFullBarOfFq E (R j))) +
    (∑ j : Fin M,
      (MvPolynomial.C (fqToBar E (m j)) : FourVarPolyBar E)
        * (∏ Q ∈ gd.support, lineEvalNumAtFullBar E Q)
        * (∏ j' ∈ (Finset.univ (α := Fin M)).erase j,
            lineEvalNumAtFullBarOfFq E (R j')))

private theorem geomPolyGFullBar_total_degree_le
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    bar_total_degree_le E (geomPolyGFullBar E D gd R m)
      (2 * (gd.support.card + M - 1)) := by
  classical
  unfold geomPolyGFullBar
  refine bar_total_degree_le.add E ?_ ?_
  · refine bar_total_degree_le.sum E _ _ ?_
    intro Q hQ
    have hCoeff :
        bar_total_degree_le E
          (MvPolynomial.C ((gd.mult Q : ℕ) : Fqbar E) : FourVarPolyBar E) 0 :=
      bar_total_degree_le.C E _
    have hErase :
        bar_total_degree_le E
          (∏ Q' ∈ gd.support.erase Q, lineEvalNumAtFullBar E Q')
          ((gd.support.erase Q).card * 2) := by
      refine bar_total_degree_le.prod_const E _ _ ?_
      intro Q' _
      exact lineEvalNumAtFullBar_total_degree_le E Q'
    have hR :
        bar_total_degree_le E
          (∏ j : Fin M, lineEvalNumAtFullBarOfFq E (R j))
          ((Finset.univ (α := Fin M)).card * 2) := by
      refine bar_total_degree_le.prod_const E _ _ ?_
      intro j _
      exact lineEvalNumAtFullBarOfFq_total_degree_le E (R j)
    have hMul := bar_total_degree_le.mul E (bar_total_degree_le.mul E hCoeff hErase) hR
    refine bar_total_degree_le.mono E hMul ?_
    have hEraseCard : (gd.support.erase Q).card = gd.support.card - 1 := by
      rw [Finset.card_erase_of_mem hQ]
    have hUniv : (Finset.univ (α := Fin M)).card = M := by simp
    rw [hEraseCard, hUniv]
    have hSupportPos : 1 ≤ gd.support.card := Finset.card_pos.mpr ⟨Q, hQ⟩
    omega
  · refine bar_total_degree_le.sum E _ _ ?_
    intro j _
    have hCoeff :
        bar_total_degree_le E
          (MvPolynomial.C (fqToBar E (m j)) : FourVarPolyBar E) 0 :=
      bar_total_degree_le.C E _
    have hSupport :
        bar_total_degree_le E
          (∏ Q ∈ gd.support, lineEvalNumAtFullBar E Q)
          (gd.support.card * 2) := by
      refine bar_total_degree_le.prod_const E _ _ ?_
      intro Q _
      exact lineEvalNumAtFullBar_total_degree_le E Q
    have hErase :
        bar_total_degree_le E
          (∏ j' ∈ (Finset.univ (α := Fin M)).erase j,
            lineEvalNumAtFullBarOfFq E (R j'))
          (((Finset.univ (α := Fin M)).erase j).card * 2) := by
      refine bar_total_degree_le.prod_const E _ _ ?_
      intro j' _
      exact lineEvalNumAtFullBarOfFq_total_degree_le E (R j')
    have hMul := bar_total_degree_le.mul E (bar_total_degree_le.mul E hCoeff hSupport) hErase
    refine bar_total_degree_le.mono E hMul ?_
    have hEraseCard :
        ((Finset.univ (α := Fin M)).erase j).card = M - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
      simp
    rw [hEraseCard]
    have hSucc : j.val.succ ≤ M := Nat.succ_le_of_lt j.isLt
    have hMpos : 1 ≤ M :=
      Nat.le_trans (Nat.succ_le_succ (Nat.zero_le j.val)) hSucc
    omega

private theorem totalDegree_baseChangeFourVar
    (G : FourVarPoly E.q) :
    (baseChangeFourVar E G).totalDegree = G.totalDegree := by
  unfold baseChangeFourVar
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective G (RingHom.injective _)]

private theorem total_degree_le_of_baseChange_eq
    (G : FourVarPoly E.q) (F : FourVarPolyBar E) {Ddeg : ℕ}
    (hG : baseChangeFourVar E G = F)
    (hF : bar_total_degree_le E F Ddeg) :
    total_degree_le E G Ddeg := by
  unfold total_degree_le
  rw [← totalDegree_baseChangeFourVar E G, hG]
  exact hF

/--
Coefficient descent of the geometric numerator.

PROVIDED SOLUTION
The geometric support and multiplicities are Frobenius-stable. Frobenius
permutes the support factors in the first product and fixes the rational
`R`-factors and the coefficients `m`. Hence every coefficient of
`geomPolyGFullBar` is fixed by Frobenius. Use the fixed-field
characterization of the algebraic closure of a finite field to descend the
coefficient vector to `ZMod E.q`.
-/
theorem geomPolyGFull_descends_coefficients
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    ∃ G : FourVarPoly E.q,
      baseChangeFourVar E G = geomPolyGFullBar E D gd R m := by
  sorry

/--
Galois descent of the geometric numerator.

The coefficient-descent theorem supplies a polynomial over `F_q`; the
total-degree bound is mechanical and follows from the product formula
over `F_qbar`, since coefficient base-change preserves support.
-/
theorem geomPolyGFull_descends
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    ∃ G : FourVarPoly E.q,
      baseChangeFourVar E G = geomPolyGFullBar E D gd R m ∧
      total_degree_le E G (2 * (gd.support.card + M - 1)) := by
  obtain ⟨G, hG⟩ := geomPolyGFull_descends_coefficients E D gd R m
  refine ⟨G, hG, ?_⟩
  exact total_degree_le_of_baseChange_eq E G (geomPolyGFullBar E D gd R m) hG
    (geomPolyGFullBar_total_degree_le E D gd R m)

/-- The descended geometric numerator over `F_q`. -/
noncomputable def geomPolyGFull
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    FourVarPoly E.q :=
  Classical.choose (geomPolyGFull_descends E D gd R m)

theorem baseChange_geomPolyGFull
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    baseChangeFourVar E (geomPolyGFull E D gd R m)
      = geomPolyGFullBar E D gd R m :=
  (Classical.choose_spec (geomPolyGFull_descends E D gd R m)).1

theorem geomPolyGFull_total_degree_le_tight
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    total_degree_le E (geomPolyGFull E D gd R m)
      (2 * (gd.support.card + M - 1)) :=
  (Classical.choose_spec (geomPolyGFull_descends E D gd R m)).2

/-! ## Base-change evaluation helpers -/

/-- The algebra map from `ZMod E.q` into its algebraic closure is injective. -/
private lemma fqToBar_injective :
    Function.Injective (algebraMap (ZMod E.q) (Fqbar E)) :=
  RingHom.injective _

/-- Zero is reflected by `fqToBar`. -/
private lemma fqToBar_eq_zero_iff (x : ZMod E.q) :
    fqToBar E x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (fqToBar_injective E)

/-- Assignment for evaluating a four-variable polynomial over `F_qbar` at
    rational points embedded from `F_q`. -/
noncomputable def barBivEval₂Fun
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Fin 4 → Fqbar E :=
  fun i => fqToBar E (bivEval₂Fun A₀ A₁ i)

/-- Base change commutes with bivariate evaluation at rational points. -/
private lemma fqToBar_bivEval₂_eq_eval_baseChange
    (f : FourVarPoly E.q) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    fqToBar E (bivEval₂ f A₀ A₁)
      = MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (baseChangeFourVar E f) := by
  unfold bivEval₂ baseChangeFourVar barBivEval₂Fun fqToBar
  rw [MvPolynomial.eval_map]
  symm
  show MvPolynomial.eval₂ (algebraMap (ZMod E.q) (Fqbar E))
      (fun i => (algebraMap (ZMod E.q) (Fqbar E)) (bivEval₂Fun A₀ A₁ i)) f =
    (algebraMap (ZMod E.q) (Fqbar E)) (MvPolynomial.eval (bivEval₂Fun A₀ A₁) f)
  have h :
      (fun i => (algebraMap (ZMod E.q) (Fqbar E)) (bivEval₂Fun A₀ A₁ i)) =
        (algebraMap (ZMod E.q) (Fqbar E)) ∘ bivEval₂Fun A₀ A₁ := rfl
  rw [h]
  have hEval := MvPolynomial.eval₂_comp_left
    (algebraMap (ZMod E.q) (Fqbar E)) (RingHom.id _) (bivEval₂Fun A₀ A₁) f
  simp at hEval
  exact hEval.symm

/--
Core geometric chord-sum identity at rational challenge points.

This is the real function-field obligation behind the geometric rewrite:
`geomPolyGFullBar` is the cleared numerator of the residue/log-derivative
identity over `F_qbar`, and at defined nonvertical rational pairs its
vanishing is equivalent to the verifier's scalar log-derivative check.
-/
private theorem geomPolyGFullBar_eval_zero_iff_logDerivCheckFn
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
        (geomPolyGFullBar E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))) = 0
      ↔ logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  sorry

/-! ## Geometric branch theorems -/

/--
Evaluation compatibility with the verifier's log-derivative check.

PROVIDED SOLUTION
Evaluate the descended polynomial at rational `A₀,A₁`, base-change that
scalar equality to `F_qbar`, and unfold `geomPolyGFullBar`. The geometric
product is the cleared residue numerator of `(dD / D)` on the chord.
At defined nonvertical pairs the denominator is nonzero, so zero of the
cleared numerator is equivalent to zero of `logDerivCheckFn`.
-/
theorem geomPolyGFull_eval_eq_logDerivCheckFn
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    bivEval₂ (geomPolyGFull E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
        A₀ A₁ = 0
      ↔ logDerivCheckFn E D P k B m A₀ A₁ = 0 := by
  rw [show bivEval₂ _ A₀ A₁ = 0 ↔ fqToBar E (bivEval₂ _ A₀ A₁) = 0 from
    (fqToBar_eq_zero_iff E _).symm]
  rw [fqToBar_bivEval₂_eq_eval_baseChange]
  rw [baseChange_geomPolyGFull]
  exact geomPolyGFullBar_eval_zero_iff_logDerivCheckFn E D gd P B m A₀ A₁
    hA₀ hA₁ hNV hDef

/--
Tight core bound for the nonzero-discrepancy branch, using the geometric
descended numerator instead of the old rational-point `polyGFull`.

PROVIDED SOLUTION
Let `gd` be the geometric divisor data of `D`. The bad defined pairs are
contained in the zero set of `geomPolyGFull E D gd ...` by
`geomPolyGFull_eval_eq_logDerivCheckFn`. The witness in `hNV` gives a
nonzero evaluation of the same polynomial. Apply
`bivariate_poly_zeros_on_ExE_le` with the descended degree bound and use
`gd.accounting_le_degE` to replace `gd.support.card` by `D.degE`.
-/
theorem log_deriv_sz_paper_core_tight_geometric
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          A₀ne_A₁x_cleared_pair E D P B m p)).card
      ≤ 18 * (D.degE + k) * E.q := by
  classical
  have hDnz : ¬ (D.a = 0 ∧ D.b = 0) := by
    obtain ⟨A₀, A₁, _, _, _, hDef, _⟩ := hNV
    intro ⟨ha, hb⟩
    apply hDef
    show logDerivCheckFnDenom E D P B A₀ A₁ = 0
    unfold logDerivCheckFnDenom CoordRingElt.eval
    simp only [ha, hb, Polynomial.eval_zero, zero_mul, mul_zero, sub_zero]
  obtain ⟨gd, _⟩ := exists_geometricDivisorData E D hDnz
  set G := geomPolyGFull E D gd
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
  have hBadSub : (E.points ×ˢ E.points).filter
      (fun p => A₀ne_A₁x_cleared_pair E D P B m p) ⊆
    (E.points ×ˢ E.points).filter
      (fun p => bivEval₂ G p.1 p.2 = 0) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    obtain ⟨hNVx, hDenom, hCheck⟩ := hp.2
    have hprod := Finset.mem_product.mp hp.1
    rw [geomPolyGFull_eval_eq_logDerivCheckFn E D gd P B m
      p.1 p.2 hprod.1 hprod.2 hNVx hDenom]
    exact hCheck
  obtain ⟨wA₀, wA₁, hwA₀, hwA₁, hwNV, hwDef, hwCheck⟩ := hNV
  have hWitness : ∃ a₀ a₁, a₀ ∈ E.points ∧ a₁ ∈ E.points ∧
      bivEval₂ G a₀ a₁ ≠ 0 := by
    refine ⟨wA₀, wA₁, hwA₀, hwA₁, ?_⟩
    intro hContra
    rw [geomPolyGFull_eval_eq_logDerivCheckFn E D gd P B m
      wA₀ wA₁ hwA₀ hwA₁ hwNV hwDef] at hContra
    exact hwCheck hContra
  have hTD := geomPolyGFull_total_degree_le_tight E D gd
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
  have hSC : gd.support.card ≤ D.degE := by
    calc gd.support.card
        = ∑ _ ∈ gd.support, 1 := by simp
      _ ≤ ∑ Q ∈ gd.support, gd.mult Q :=
          Finset.sum_le_sum (fun Q hQ => gd.mult_pos_on_support Q hQ)
      _ ≤ D.degE := gd.accounting_le_degE
  have hdM1 : gd.support.card + (k + 1) - 1 = gd.support.card + k := by omega
  have hTD' : total_degree_le E G (2 * (gd.support.card + k)) := by
    rwa [hdM1] at hTD
  have hDKL := bivariate_poly_zeros_on_ExE_le E G
    (2 * (gd.support.card + k)) hTD' hWitness
  calc ((E.points ×ˢ E.points).filter
        (fun p => A₀ne_A₁x_cleared_pair E D P B m p)).card
      ≤ ((E.points ×ˢ E.points).filter
          (fun p => bivEval₂ G p.1 p.2 = 0)).card :=
        Finset.card_le_card hBadSub
    _ ≤ 9 * (2 * (gd.support.card + k)) * E.q := hDKL
    _ = 18 * (gd.support.card + k) * E.q := by ring
    _ ≤ 18 * (D.degE + k) * E.q := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega

/--
Paper-tight `event_NotEq` bound, now unconditional in `D`.

This replaces `log_deriv_sz_paper_tight` at the headline call site. The
old theorem remains available for comparison, but this is the intended
soundness lemma.
-/
theorem log_deriv_sz_paper_tight_geometric
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNV : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (eventNotEq E D P B (fun i => m i)).card
      ≤ 18 * (D.degE + k) * E.q +
        (3 * D.degE + 9 * k + 71) * E.points.card := by
  classical
  have hDnz : ¬ (D.a = 0 ∧ D.b = 0) := by
    obtain ⟨A₀, A₁, _, _, _, hDef, _⟩ := hNV
    intro ⟨ha, hb⟩
    apply hDef
    show logDerivCheckFnDenom E D P B A₀ A₁ = 0
    unfold logDerivCheckFnDenom CoordRingElt.eval
    simp only [ha, hb, Polynomial.eval_zero, zero_mul, mul_zero, sub_zero]
  have hSub : eventNotEq E D P B (fun i => m i) ⊆
      (E.points ×ˢ E.points).filter
        (fun p => A₀ne_A₁x_cleared_pair E D P B m p) ∪
      (E.points ×ˢ E.points).filter
        (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) := by
    intro p hp
    simp only [eventNotEq, Finset.mem_filter] at hp
    obtain ⟨hVP, hCheck⟩ := hp
    have hDP : p ∈ distinctPairs E.points := (Finset.mem_filter.mp hVP).1
    have hEE : p ∈ E.points ×ˢ E.points := (Finset.mem_filter.mp hDP).1
    have hNeq : p.1.1 ≠ p.2.1 := ((Finset.mem_filter.mp hVP).2).1
    by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨hEE, hNeq, hDef, hCheck⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hEE, hDef⟩))
  have hCoreBound := log_deriv_sz_paper_core_tight_geometric E D P B m hDeg hNV
  have hUndefBound := logDerivCheckFn_undefined_set_bound_tight E D P k B hDnz
  calc (eventNotEq E D P B (fun i => m i)).card
      ≤ ((E.points ×ˢ E.points).filter
          (fun p => A₀ne_A₁x_cleared_pair E D P B m p)).card +
        ((E.points ×ˢ E.points).filter
          (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card :=
        le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
    _ ≤ 18 * (D.degE + k) * E.q +
          (3 * D.degE + 9 * k + 71) * E.points.card :=
        Nat.add_le_add hCoreBound hUndefBound

/--
Geometric all-zero branch: if the verifier discrepancy vanishes on every
defined nonvertical rational challenge, then the extractor succeeds and
returns a valid dlog witness.

PROVIDED SOLUTION
Use geometric divisor data for `msg.toD`. The all-zero hypothesis implies
the descended geometric numerator vanishes on all rational nonvertical
pairs. The DKL/Lang-Weil threshold promotes this to the polynomial
identity needed for residue matching. Match the geometric divisor support
against the prescribed rational divisor `(-P) + Σ m_j B_j`; Frobenius
stability and the fact that the right side is rational force the matched
support to be rational where it contributes to the extractor. Then reuse
the existing grouped extractor algebra, but with multiplicities supplied
by the geometric divisor data rather than `zerosAt`/`β_fun`.
-/
theorem extractor_of_logDerivCheck_all_zero_geometric
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (hDenomNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm),
            distinctR E stmt msg hkm j ≠ A₀) →
        denomScaledPoly (E := E) msg.toD stmt.target
          (baseImageCount E stmt msg hkm)
          (baseAt E stmt msg hkm) A₀ %ₘ curveEqPoly E ≠ 0)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg stmt.degBound hd hkm = some wit
      ∧ relDlog E stmt wit := by
  sorry

end Divisor
