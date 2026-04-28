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
import Divisor.GeomLocalOrder

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

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
