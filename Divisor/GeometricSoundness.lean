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
import Divisor.CoeffDescent

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

/-! ### Auxiliary lemmas for the Frobenius proof -/

private theorem geomPoint_ext (Q Q' : GeomPoint E)
    (hx : Q.x = Q'.x) (hy : Q.y = Q'.y) : Q = Q' := by
  cases Q
  cases Q'
  simp only at hx hy
  subst hx
  subst hy
  rfl

private theorem pow_q_injective_fqbar :
    Function.Injective (fun (x : Fqbar E) => x ^ E.q) := by
  intro a b hab
  exact (frobenius (Fqbar E) E.q).injective (by
    simp only [frobenius_def]
    exact hab)

private theorem finset_surjOn_of_injOn_self {α : Type*} [DecidableEq α]
    {S : Finset α} (f : (a : α) → a ∈ S → α)
    (hf : ∀ a (ha : a ∈ S), f a ha ∈ S)
    (hinj : ∀ a₁ (ha₁ : a₁ ∈ S) a₂ (ha₂ : a₂ ∈ S),
      f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) :
    ∀ b ∈ S, ∃ a, ∃ (ha : a ∈ S), f a ha = b := by
  intro b hb
  let g : { x // x ∈ S } → { x // x ∈ S } :=
    fun ⟨a, ha⟩ => ⟨f a ha, hf a ha⟩
  have hinj' : Function.Injective g := by
    intro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h
    simp [g] at h
    exact Subtype.ext (hinj a₁ ha₁ a₂ ha₂ h)
  obtain ⟨⟨a, ha⟩, hab⟩ := Finite.surjective_of_injective hinj' ⟨b, hb⟩
  exact ⟨a, ha, by simpa [g] using hab⟩

private theorem frob_support_injective
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q1 : GeomPoint E) (hQ1 : Q1 ∈ gd.support)
    (Q2 : GeomPoint E) (hQ2 : Q2 ∈ gd.support)
    (heq : (gd.frobenius_stable Q1 hQ1).choose =
           (gd.frobenius_stable Q2 hQ2).choose) :
    Q1 = Q2 := by
  have hx1 := (gd.frobenius_stable Q1 hQ1).choose_spec.2.1
  have hy1 := (gd.frobenius_stable Q1 hQ1).choose_spec.2.2.1
  have hx2 := (gd.frobenius_stable Q2 hQ2).choose_spec.2.1
  have hy2 := (gd.frobenius_stable Q2 hQ2).choose_spec.2.2.1
  have hxeq : Q1.x ^ E.q = Q2.x ^ E.q := by
    calc Q1.x ^ E.q
        = (gd.frobenius_stable Q1 hQ1).choose.x := hx1.symm
      _ = (gd.frobenius_stable Q2 hQ2).choose.x := by rw [heq]
      _ = Q2.x ^ E.q := hx2
  have hyeq : Q1.y ^ E.q = Q2.y ^ E.q := by
    calc Q1.y ^ E.q
        = (gd.frobenius_stable Q1 hQ1).choose.y := hy1.symm
      _ = (gd.frobenius_stable Q2 hQ2).choose.y := by rw [heq]
      _ = Q2.y ^ E.q := hy2
  exact geomPoint_ext E Q1 Q2
    (pow_q_injective_fqbar E hxeq) (pow_q_injective_fqbar E hyeq)

/-! ### Frobenius action on geometric support -/

/-- The Frobenius image chosen by `gd.frobenius_stable` is the canonical
`frobGeomPoint E Q` (componentwise `q`-power). -/
private theorem frobenius_stable_choose_eq_frobGeomPoint
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    (gd.frobenius_stable Q hQ).choose = frobGeomPoint E Q := by
  apply geomPoint_ext
  · show (gd.frobenius_stable Q hQ).choose.x = Q.x ^ E.q
    exact (gd.frobenius_stable Q hQ).choose_spec.2.1
  · show (gd.frobenius_stable Q hQ).choose.y = Q.y ^ E.q
    exact (gd.frobenius_stable Q hQ).choose_spec.2.2.1

/-- `frobGeomPoint Q ∈ gd.support` for every `Q ∈ gd.support`. -/
private theorem frobGeomPoint_mem_support
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    frobGeomPoint E Q ∈ gd.support := by
  rw [← frobenius_stable_choose_eq_frobGeomPoint E D gd Q hQ]
  exact (gd.frobenius_stable Q hQ).choose_spec.1

/-- Multiplicity is preserved under Frobenius on geometric support. -/
private theorem mult_frobGeomPoint_eq
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    gd.mult (frobGeomPoint E Q) = gd.mult Q := by
  rw [← frobenius_stable_choose_eq_frobGeomPoint E D gd Q hQ]
  exact (gd.frobenius_stable Q hQ).choose_spec.2.2.2

/-- A geometric point with rational coordinates is fixed by Frobenius. -/
private theorem frobGeomPoint_of_rational
    (Q : GeomPoint E) (P : ZMod E.q × ZMod E.q)
    (hPx : Q.x = fqToBar E P.1) (hPy : Q.y = fqToBar E P.2) :
    frobGeomPoint E Q = Q := by
  apply geomPoint_ext
  · show Q.x ^ E.q = Q.x
    rw [hPx]; exact fqToBar_frob_fixed E P.1
  · show Q.y ^ E.q = Q.y
    rw [hPy]; exact fqToBar_frob_fixed E P.2

/-- A Frobenius-fixed geometric point has rational coordinates. -/
private theorem rational_of_frobGeomPoint_fixed
    (Q : GeomPoint E) (hFix : frobGeomPoint E Q = Q) :
    ∃ P : ZMod E.q × ZMod E.q,
      Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 := by
  have hx : Q.x ^ E.q = Q.x := by
    have := congr_arg GeomPoint.x hFix
    exact this
  have hy : Q.y ^ E.q = Q.y := by
    have := congr_arg GeomPoint.y hFix
    exact this
  obtain ⟨a, ha⟩ := fqbar_fixed_by_frob_in_range E Q.x hx
  obtain ⟨b, hb⟩ := fqbar_fixed_by_frob_in_range E Q.y hy
  exact ⟨(a, b), ha.symm, hb.symm⟩

/-! ### Frobenius-fixedness of line factors -/

/-- Frobenius on coefficients sends `lineEvalNumAtFullBar E Q` to
`lineEvalNumAtFullBar E (frobGeomPoint E Q)`. -/
private theorem frobMvPoly_lineEvalNumAtFullBar (Q : GeomPoint E) :
    frobMvPoly E (lineEvalNumAtFullBar E Q) =
      lineEvalNumAtFullBar E (frobGeomPoint E Q) := by
  unfold lineEvalNumAtFullBar frobGeomPoint
  simp only [frobMvPoly, map_sub, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, frobEnd_apply]

/-- Frobenius on coefficients fixes `lineEvalNumAtFullBarOfFq`. -/
private theorem frobMvPoly_lineEvalNumAtFullBarOfFq
    (P : ZMod E.q × ZMod E.q) :
    frobMvPoly E (lineEvalNumAtFullBarOfFq E P) =
      lineEvalNumAtFullBarOfFq E P := by
  unfold lineEvalNumAtFullBarOfFq
  simp only [frobMvPoly, map_sub, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, frobEnd_apply, fqToBar_frob_fixed]

/-- Frobenius on coefficients fixes the product of base-field line factors. -/
private theorem frobMvPoly_prod_R
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q)
    (s : Finset (Fin M)) :
    frobMvPoly E (∏ j ∈ s, lineEvalNumAtFullBarOfFq E (R j)) =
      ∏ j ∈ s, lineEvalNumAtFullBarOfFq E (R j) := by
  simp_rw [map_prod, frobMvPoly_lineEvalNumAtFullBarOfFq]

/-- Frobenius permutes the product of line factors over the geometric support. -/
private theorem frobMvPoly_prod_support
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) :
    frobMvPoly E (∏ Q ∈ gd.support, lineEvalNumAtFullBar E Q) =
      ∏ Q ∈ gd.support, lineEvalNumAtFullBar E Q := by
  rw [map_prod]
  simp_rw [frobMvPoly_lineEvalNumAtFullBar]
  let fs := gd.frobenius_stable
  apply Finset.prod_bij (fun Q hQ => (fs Q hQ).choose)
  · intro Q hQ
    exact (fs Q hQ).choose_spec.1
  · exact fun Q1 hQ1 Q2 hQ2 heq =>
      frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq
  · exact finset_surjOn_of_injOn_self
      (fun Q hQ => (fs Q hQ).choose)
      (fun Q hQ => (fs Q hQ).choose_spec.1)
      (fun Q1 hQ1 Q2 hQ2 heq =>
        frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq)
  · intro Q hQ
    unfold lineEvalNumAtFullBar frobGeomPoint
    simp only
    rw [(fs Q hQ).choose_spec.2.1, (fs Q hQ).choose_spec.2.2.1]

/-- Frobenius maps the erased support product to the erased product at the image point. -/
private theorem frobMvPoly_prod_erase_support
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    (∏ Q' ∈ gd.support.erase Q,
      lineEvalNumAtFullBar E (frobGeomPoint E Q')) =
    (∏ Q' ∈ gd.support.erase (gd.frobenius_stable Q hQ).choose,
      lineEvalNumAtFullBar E Q') := by
  let fs := gd.frobenius_stable
  apply Finset.prod_bij (fun Q' hQ' => (fs Q' (Finset.mem_of_mem_erase hQ')).choose)
  · intro Q' hQ'
    have hmem := (fs Q' (Finset.mem_of_mem_erase hQ')).choose_spec.1
    rw [Finset.mem_erase]
    refine ⟨?_, hmem⟩
    intro heq
    have := Finset.ne_of_mem_erase hQ'
    apply this
    exact frob_support_injective E D gd Q' (Finset.mem_of_mem_erase hQ') Q hQ (by
      rw [heq])
  · intro Q1 hQ1 Q2 hQ2 heq
    exact frob_support_injective E D gd
      Q1 (Finset.mem_of_mem_erase hQ1)
      Q2 (Finset.mem_of_mem_erase hQ2) heq
  · intro b hb
    have hb_mem := Finset.mem_of_mem_erase hb
    have hb_ne := Finset.ne_of_mem_erase hb
    obtain ⟨a, ha, hab⟩ := finset_surjOn_of_injOn_self
      (fun Q' hQ' => (fs Q' hQ').choose)
      (fun Q' hQ' => (fs Q' hQ').choose_spec.1)
      (fun Q1 hQ1 Q2 hQ2 heq =>
        frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq)
      b hb_mem
    refine ⟨a, ?_, hab⟩
    rw [Finset.mem_erase]
    refine ⟨fun haq => ?_, ha⟩
    subst haq
    exact hb_ne hab.symm
  · intro Q' hQ'
    unfold lineEvalNumAtFullBar frobGeomPoint
    simp only
    rw [(fs Q' (Finset.mem_of_mem_erase hQ')).choose_spec.2.1,
      (fs Q' (Finset.mem_of_mem_erase hQ')).choose_spec.2.2.1]

set_option maxHeartbeats 800000 in
/-- Frobenius on coefficients fixes `geomPolyGFullBar`. -/
theorem frobMvPoly_geomPolyGFullBar
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    frobMvPoly E (geomPolyGFullBar E D gd R m) =
      geomPolyGFullBar E D gd R m := by
  classical
  unfold geomPolyGFullBar
  simp only [map_add, map_sum, map_mul, map_prod,
    frobMvPoly_lineEvalNumAtFullBar,
    frobMvPoly_lineEvalNumAtFullBarOfFq,
    frobMvPoly_C_natCast, frobMvPoly_C_fqToBar]
  congr 1
  · let fs := gd.frobenius_stable
    apply Finset.sum_bij (fun Q hQ => (fs Q hQ).choose)
    · intro Q hQ
      exact (fs Q hQ).choose_spec.1
    · exact fun Q1 hQ1 Q2 hQ2 heq =>
        frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq
    · exact finset_surjOn_of_injOn_self
        (fun Q hQ => (fs Q hQ).choose)
        (fun Q hQ => (fs Q hQ).choose_spec.1)
        (fun Q1 hQ1 Q2 hQ2 heq =>
          frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq)
    · intro Q hQ
      congr 1
      congr 1
      · congr 1
        congr 1
        exact (fs Q hQ).choose_spec.2.2.2.symm
      · exact frobMvPoly_prod_erase_support E D gd Q hQ
  · apply Finset.sum_congr rfl
    intro _j _
    congr 1
    congr 1
    · let fs := gd.frobenius_stable
      apply Finset.prod_bij (fun Q hQ => (fs Q hQ).choose)
      · intro Q hQ
        exact (fs Q hQ).choose_spec.1
      · exact fun Q1 hQ1 Q2 hQ2 heq =>
          frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq
      · exact finset_surjOn_of_injOn_self
          (fun Q hQ => (fs Q hQ).choose)
          (fun Q hQ => (fs Q hQ).choose_spec.1)
          (fun Q1 hQ1 Q2 hQ2 heq =>
            frob_support_injective E D gd Q1 hQ1 Q2 hQ2 heq)
      · intro Q hQ
        unfold lineEvalNumAtFullBar frobGeomPoint
        simp only
        rw [(fs Q hQ).choose_spec.2.1, (fs Q hQ).choose_spec.2.2.1]

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
  have hfix := frobMvPoly_geomPolyGFullBar E D gd R m
  have hcoeffs := coeffs_descend_of_frob_fixed E _ hfix
  have ⟨G, hG⟩ := mvpoly_in_range_of_coeffs_in_range
    (algebraMap (ZMod E.q) (Fqbar E)) _ hcoeffs
  exact ⟨G, hG⟩

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

/-- Direct evaluation formula for the geometric line factor. -/
@[simp] theorem lineEvalNumAtFullBar_eval
    (Q : GeomPoint E) (A₀ A₁ : ZMod E.q × ZMod E.q) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) =
      (Q.y - fqToBar E A₀.2) * fqToBar E (A₁.1 - A₀.1)
        - (Q.x - fqToBar E A₀.1) * fqToBar E (A₁.2 - A₀.2) := by
  unfold lineEvalNumAtFullBar barBivEval₂Fun bivEval₂Fun fqToBar
  simp

/-- Direct evaluation formula for a base-field line factor after embedding into `F_qbar`. -/
@[simp] theorem lineEvalNumAtFullBarOfFq_eval
    (P A₀ A₁ : ZMod E.q × ZMod E.q) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P) =
      fqToBar E ((P.2 - A₀.2) * (A₁.1 - A₀.1)
        - (P.1 - A₀.1) * (A₁.2 - A₀.2)) := by
  unfold lineEvalNumAtFullBarOfFq barBivEval₂Fun bivEval₂Fun fqToBar
  simp

/-- The geometric rational line factor is exactly the base-change of the
existing four-variable line factor. -/
theorem baseChange_lineEvalNumAtFull
    (P : ZMod E.q × ZMod E.q) :
  baseChangeFourVar E (lineEvalNumAtFull E P) =
      lineEvalNumAtFullBarOfFq E P := by
  unfold baseChangeFourVar lineEvalNumAtFull lineEvalNumAtFullBarOfFq
  unfold embedScalarFull
  unfold lamDenFull lamNumFull
  unfold varA₀y varA₀x varA₁y varA₁x
  simp [fqToBar]

/-- Evaluation of a rational geometric line factor agrees with base-field
evaluation followed by `fqToBar`. -/
theorem lineEvalNumAtFullBarOfFq_eval_eq_fqToBar_bivEval₂
    (P A₀ A₁ : ZMod E.q × ZMod E.q) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P) =
      fqToBar E (bivEval₂ (lineEvalNumAtFull E P) A₀ A₁) := by
  rw [fqToBar_bivEval₂_eq_eval_baseChange, baseChange_lineEvalNumAtFull]

/-- On nonvertical pairs, the rational geometric line factor evaluates to
`(A₁.x - A₀.x)` times the usual affine line evaluation, embedded in `F_qbar`. -/
theorem lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P) =
      fqToBar E (A₁.1 - A₀.1) *
        fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2) := by
  rw [lineEvalNumAtFullBarOfFq_eval_eq_fqToBar_bivEval₂,
    bivEval₂_lineEvalNumAtFull_eq_bivEval,
    bivEval_lineEvalNumAt_eq_mul E A₀ P A₁ hNV]
  simp [fqToBar]

/-- For nonvertical pairs, nonvanishing of the geometric rational line factor
is equivalent to nonvanishing of the usual affine line evaluation. -/
theorem lineEvalNumAtFullBarOfFq_eval_ne_zero_iff
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P) ≠ 0
      ↔ (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0 := by
  rw [lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul E P A₀ A₁ hNV]
  have hx : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E (A₁.1 - A₀.1)).not.mpr (sub_ne_zero.mpr hNV.symm)
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨_, hline⟩
    exact (fqToBar_eq_zero_iff E _).not.mp hline
  · intro hline
    exact ⟨hx, (fqToBar_eq_zero_iff E _).not.mpr hline⟩

/-- At a rational lift `Q` of `P` (i.e., `Q.x = fqToBar P.1` and
`Q.y = fqToBar P.2`), the geometric line factor coincides with the
rational line factor. -/
theorem lineEvalNumAtFullBar_eq_lineEvalNumAtFullBarOfFq_of_rational
    (Q : GeomPoint E) (P : ZMod E.q × ZMod E.q)
    (hPx : Q.x = fqToBar E P.1) (hPy : Q.y = fqToBar E P.2) :
    lineEvalNumAtFullBar E Q = lineEvalNumAtFullBarOfFq E P := by
  unfold lineEvalNumAtFullBar lineEvalNumAtFullBarOfFq
  rw [hPx, hPy]

/-! ### Geometric μ-coordinate (Step C of the chord-sum sub-plan)

The level sets of `zLambdaBar lam` over `F_qbar` are the projective
chords of slope `lam`. The bridge lemma below recasts the geometric
line factor `lineEvalNumAtFullBar` as `-(A₁.1 − A₀.1) · (μ −
zLambdaBar lam Q)`, the geometric analogue of the rational identity
for `ellP`. This is the substitution that lets the residue sum from
the chord-fiber-product log-derivative match the geometric-line-factor
sum that appears in `geometric_chord_sum_eq_residue_sum`.
-/

/-- On a non-vertical chord, the geometric line factor evaluation at
`(Q, A₀, A₁)` equals `-(A₁.1 − A₀.1) · (μ − zLambdaBar lam Q)`, where
`lam` is the chord slope and `μ = fqToBar (zLambda lam A₀)` is the
chord intercept embedded in `Fqbar`.

This is the geometric counterpart of the rational identity expressing
`ellP P A₀ A₁` as `-(A₁.1 − A₀.1) · (μ − zLambda lam P)`. -/
theorem lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff
    (Q : GeomPoint E) (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)
      = -(fqToBar E (A₁.1 - A₀.1)) *
          (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
            - zLambdaBar E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q) := by
  rw [lineEvalNumAtFullBar_eval]
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  -- Slope identity in `ZMod E.q`.
  have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    rw [hLam, slopeOf]
    rw [mul_assoc, inv_mul_cancel₀ hX, mul_one]
  -- Lift the slope identity to `Fqbar`.
  have hSlopeBar : fqToBar E (A₁.2 - A₀.2)
      = fqToBar E lam * fqToBar E (A₁.1 - A₀.1) := by
    rw [← hSlope]; simp [fqToBar]
  rw [hSlopeBar]
  -- Expand `zLambdaBar` and `zLambda` to scalars in `Fqbar`.
  unfold zLambdaBar zLambda
  have hZL : fqToBar E (A₀.2 - lam * A₀.1)
      = fqToBar E A₀.2 - fqToBar E lam * fqToBar E A₀.1 := by
    simp [fqToBar]
  rw [hZL]
  ring

/-! ### Geometric partial-fraction expansion (Step B of the chord-sum sub-plan)

Logarithmic derivative of the `Fqbar`-product
`∏ Q ∈ gd.support, (X − C (zLambdaBar lam Q))^(gd.mult Q)` at any
`μ ∈ Fqbar` not in the image of `zLambdaBar lam` on the support. The
identity is a clean partial-fraction expansion:

  `eval μ (derivative ∏) = (eval μ ∏) · ∑ Q ∈ gd.support, (mult Q) ·
                                       (μ − zLambdaBar lam Q)⁻¹`.

This is the geometric analogue of `normZ_logDeriv_at_nonroot` in
`Divisor/NormZDecomp.lean`, lifted from `(ZMod E.q)[X]` to
`(Fqbar E)[X]` and indexed by `gd.support` instead of `zerosFinset`.
-/

/-- Per-`Q` summand identity inside the PFE: at non-root `μ`, the
`Q`-summand of the derivative of `∏ Q', (X − C (zLambdaBar lam Q'))^(mult Q')`
equals `(mult Q : Fqbar) · (full product evaluated) · (μ − zLambdaBar lam Q)⁻¹`.
Mirror of `summand_eq_full_prod_div`. -/
private theorem geom_summand_eq_full_prod_div
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) (lam : ZMod E.q)
    (μ : Fqbar E) {Q : GeomPoint E} (hQ : Q ∈ gd.support)
    (hDiffQ : μ - zLambdaBar E lam Q ≠ 0) :
    ((gd.mult Q : ℕ) : Fqbar E) *
        (μ - zLambdaBar E lam Q) ^ ((gd.mult Q) - 1) *
        ∏ Q' ∈ gd.support.erase Q,
          (μ - zLambdaBar E lam Q') ^ (gd.mult Q') =
      ((gd.mult Q : ℕ) : Fqbar E) *
        (∏ Q' ∈ gd.support,
          (μ - zLambdaBar E lam Q') ^ (gd.mult Q'))
        * (μ - zLambdaBar E lam Q)⁻¹ := by
  classical
  set y := μ - zLambdaBar E lam Q with hy_def
  set m := gd.mult Q with hm_def
  set Pol := ∏ Q' ∈ gd.support.erase Q,
      (μ - zLambdaBar E lam Q') ^ (gd.mult Q') with hPol_def
  have hFull :
      (∏ Q' ∈ gd.support,
        (μ - zLambdaBar E lam Q') ^ (gd.mult Q'))
        = y ^ m * Pol := by
    rw [hy_def, hm_def, hPol_def]
    exact (Finset.mul_prod_erase gd.support
          (fun Q' => (μ - zLambdaBar E lam Q') ^ (gd.mult Q')) hQ).symm
  rw [hFull]
  by_cases hM : m = 0
  · rw [hM]; simp
  · have hMpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hM
    have hPow : y ^ (m - 1) = y ^ m * y⁻¹ := by
      have hy : y ≠ 0 := hDiffQ
      have := pow_succ y (m - 1)
      rw [Nat.sub_add_cancel hMpos] at this
      field_simp
      rw [this]
    calc ((m : ℕ) : Fqbar E) * y ^ (m - 1) * Pol
        = ((m : ℕ) : Fqbar E) * (y ^ m * y⁻¹) * Pol := by rw [hPow]
      _ = ((m : ℕ) : Fqbar E) * (y ^ m * Pol) * y⁻¹ := by ring

/-- **Partial-fraction expansion of the geometric product log-derivative
at a non-root `μ`** (Step B). -/
theorem prod_X_sub_C_zLambdaBar_logDeriv_at_nonroot
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) (lam : ZMod E.q)
    (μ : Fqbar E)
    (hNonRoot : ∀ Q ∈ gd.support, μ - zLambdaBar E lam Q ≠ 0) :
    eval μ (derivative
        (∏ Q ∈ gd.support,
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)))
      = eval μ (∏ Q ∈ gd.support,
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q)) *
          ∑ Q ∈ gd.support,
            ((gd.mult Q : ℕ) : Fqbar E) *
              (μ - zLambdaBar E lam Q)⁻¹ := by
  classical
  rw [derivative_prod_X_sub_C_pow_indexed gd.support
        (fun Q => zLambdaBar E lam Q) gd.mult]
  rw [eval_finset_sum]
  have hProdEval :
      eval μ (∏ Q ∈ gd.support,
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q))
        = ∏ Q ∈ gd.support, (μ - zLambdaBar E lam Q) ^ (gd.mult Q) := by
    rw [eval_prod]
    apply Finset.prod_congr rfl
    intro Q _
    rw [eval_pow, eval_sub, eval_X, eval_C]
  rw [hProdEval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  -- Evaluate per-summand on the LHS (after derivative_prod_X_sub_C_pow_indexed).
  rw [eval_mul, eval_mul, eval_C]
  rw [show eval μ ((X - C (zLambdaBar E lam Q)) ^ (gd.mult Q - 1))
      = (μ - zLambdaBar E lam Q) ^ (gd.mult Q - 1) from by
    rw [eval_pow, eval_sub, eval_X, eval_C]]
  rw [show eval μ (∏ Q' ∈ gd.support.erase Q,
        (X - C (zLambdaBar E lam Q')) ^ (gd.mult Q'))
      = ∏ Q' ∈ gd.support.erase Q, (μ - zLambdaBar E lam Q') ^ (gd.mult Q')
      from by
    rw [eval_prod]
    apply Finset.prod_congr rfl
    intro Q' _
    rw [eval_pow, eval_sub, eval_X, eval_C]]
  have hSum := geom_summand_eq_full_prod_div E D gd lam μ hQ (hNonRoot Q hQ)
  linear_combination hSum

/-! #### Phase 1 helpers (rationality bridge) -/

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
  unfold CoordRingElt.geomEval CoordRingElt.eval fqToBar
  simp only [Polynomial.eval₂_at_apply]
  rw [map_sub, map_mul]

/-- For each rational zero `P` of `D`, the corresponding lifted geometric
point lies in `gd.support`. -/
private theorem support_lift_of_rational_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) (hPpts : P ∈ E.points)
    (hPzero : D.eval P.1 P.2 = 0) :
    (⟨fqToBar E P.1, fqToBar E P.2, by
        unfold fqToBar
        rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
        exact congrArg _ (E.hOnCurve P hPpts)⟩ : GeomPoint E) ∈ gd.support := by
  apply gd.eval_zero_mem_support
  rw [geomEval_lift_eq_fqToBar E D P (E.hOnCurve P hPpts), hPzero]
  simp [fqToBar]

/-- Every multiplicity in the geometric divisor is strictly less than
`E.q` (used to translate `(mult : Fqbar) = 0` into `mult = 0`). -/
private theorem gd_mult_lt_q
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (hDeg : D.degE < E.q)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    gd.mult Q < E.q := by
  have hSingle : gd.mult Q ≤ ∑ Q' ∈ gd.support, gd.mult Q' :=
    Finset.single_le_sum (f := gd.mult) (fun _ _ => Nat.zero_le _) hQ
  exact lt_of_le_of_lt (hSingle.trans gd.accounting_le_degE) hDeg

/-- For `Q ∈ gd.support` and `D.degE < E.q`, the multiplicity cast to
`ZMod E.q` is non-zero. Combines `mult_pos_on_support` with `gd_mult_lt_q`. -/
private theorem gd_mult_natCast_ne_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (hDeg : D.degE < E.q)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    ((gd.mult Q : ℕ) : ZMod E.q) ≠ 0 := by
  haveI : NeZero E.q := ⟨E.hq_prime.ne_zero⟩
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hDvd
  have hPos : 0 < gd.mult Q := gd.mult_pos_on_support Q hQ
  have hLt : gd.mult Q < E.q := gd_mult_lt_q E D gd hDeg Q hQ
  exact absurd (Nat.le_of_dvd hPos hDvd) (Nat.not_le.mpr hLt)

/-- The same in `Fqbar E`: `(gd.mult Q : Fqbar E) ≠ 0` when `Q ∈ gd.support`
and `D.degE < E.q`. -/
private theorem gd_mult_fqbar_ne_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (hDeg : D.degE < E.q)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    ((gd.mult Q : ℕ) : Fqbar E) ≠ 0 := by
  haveI : NeZero E.q := ⟨E.hq_prime.ne_zero⟩
  intro h
  have h' : ((gd.mult Q : ℕ) : ZMod E.q) ≠ 0 :=
    gd_mult_natCast_ne_zero E D gd hDeg Q hQ
  apply h'
  apply (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E))
  rw [map_zero, map_natCast]
  exact h

/-- **Vieta factorisation of the chord-fiber cubic.** Given two distinct
chord-fiber points `A₀, A₁ ∈ E.points`, the chord-fiber cubic
`intersectionPoly E lam (zLambda lam A₀)` factors as
`(X − A₀.1)(X − A₁.1)(X − chordX₂ A₀ A₁)` over `(ZMod E.q)[X]`. Direct
consequence of Vieta + the existing `chord_x_pairwise_sum` and
`chord_x_triple_product` identities. -/
private theorem intersectionPoly_factorisation
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1) :
    intersectionPoly E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
        (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
      = (X - C A₀.1) * (X - C A₁.1) * (X - C (chordX₂ A₀ A₁)) := by
  have he₂ := chord_x_pairwise_sum E A₀ A₁ hA₀ hA₁ hNV
  have he₃ := chord_x_triple_product E A₀ A₁ hA₀ hA₁ hNV
  simp only [] at he₂ he₃
  -- Expand `(X − C α)(X − C β)(X − C γ)` symbolically.
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  set mu : ZMod E.q := A₀.2 - lam * A₀.1
  set x₂ : ZMod E.q := lam ^ 2 - A₀.1 - A₁.1
  have hChordX₂_eq : chordX₂ A₀ A₁ = x₂ := rfl
  have hMu_eq : zLambda E lam A₀ = mu := rfl
  rw [hChordX₂_eq, hMu_eq]
  unfold intersectionPoly
  have hKey :
      (X - C A₀.1) * (X - C A₁.1) * (X - C x₂)
        = X ^ 3 - C (A₀.1 + A₁.1 + x₂) * X ^ 2
            + C (A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂) * X
            - C (A₀.1 * A₁.1 * x₂) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  rw [hKey]
  -- Substitute Vieta identities.
  have hSum : A₀.1 + A₁.1 + x₂ = lam ^ 2 := by show A₀.1 + A₁.1 + (lam^2 - A₀.1 - A₁.1) = _; ring
  rw [hSum]
  rw [show A₀.1 * A₁.1 + A₀.1 * x₂ + A₁.1 * x₂ = E.curveA - 2 * lam * mu from he₂]
  rw [show A₀.1 * A₁.1 * x₂ = mu ^ 2 - E.curveB from he₃]
  -- Match: X³ - C lam² X² + C(A - 2λμ) X − C(μ² − B) = X³ - C lam² X² + C(A - 2λμ) X + C(B − μ²)
  rw [show E.curveB - mu ^ 2 = -(mu ^ 2 - E.curveB) from by ring, Polynomial.C_neg]
  ring

set_option maxHeartbeats 800000 in
/--
Bezout-style helper: under the rational `logDerivCheckFnDefined`
hypothesis, no `Q ∈ gd.support` lies on the chord through `(A₀, A₁)`.

PROVIDED SOLUTION
The rational chord meets `E` over `F_qbar` in at most 3 points
(Bezout: line · cubic = 3); the chord-cubic in `x` factors as
`(x − A₀.1)(x − A₁.1)(x − x₂)` by Vieta. Base-changing to `Fqbar`
preserves this factorisation, so the geometric chord-fiber consists
precisely of the lifts of `A₀, A₁, (x₂, y₂)`. By `hDef`, `D.eval`
at each of these three rational points is nonzero, hence (by
`geomEval_lift_eq_fqToBar`) `D.geomEval` at each lifted point is
nonzero, so no lifted point lies in `gd.support`. Therefore no
`Q ∈ gd.support` is on the chord, which by Step C
(`lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff`) is equivalent to
`fqToBar (zLambda lam A₀) − zLambdaBar lam Q ≠ 0`. -/
private theorem geom_support_avoids_chord
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    ∀ Q ∈ gd.support,
      fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        - zLambdaBar E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q ≠ 0 := by
  classical
  intro Q hQ hZero
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu_def
  -- Extract D-non-vanishing at A₀, A₁, and the chord-third point (chordX₂, chordY₂).
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have hProdNZ := hDef
  have hLeftOf7 := left_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have hLeftOf6 := left_ne_zero_of_mul hLeftOf7
  have hLeftOf5 := left_ne_zero_of_mul hLeftOf6
  have hLeftOf4 := left_ne_zero_of_mul hLeftOf5
  have hLeftOf3 := left_ne_zero_of_mul hLeftOf4
  have h3 : D.eval (lam ^ 2 - A₀.1 - A₁.1)
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)) ≠ 0 :=
    right_ne_zero_of_mul hLeftOf4
  have h2 : D.eval A₁.1 A₁.2 ≠ 0 := right_ne_zero_of_mul hLeftOf3
  have h1 : D.eval A₀.1 A₀.2 ≠ 0 := left_ne_zero_of_mul hLeftOf3
  -- From `hZero`: `Q.y = fqToBar lam · Q.x + fqToBar μ` (Q lies on the rational chord).
  have hChord : Q.y = fqToBar E lam * Q.x + fqToBar E μ := by
    have h : zLambdaBar E lam Q = fqToBar E μ := by
      linear_combination -hZero
    unfold zLambdaBar at h
    linear_combination h
  -- Q is on E (over Fqbar): Q.y² = Q.x³ + fqToBar A · Q.x + fqToBar B.
  have hOn := Q.onCurve
  -- Substituting hChord into the curve equation gives that `Q.x` is a root of
  -- `(intersectionPoly E lam μ).map fqToBar` over `Fqbar`.
  have hRoot : eval Q.x
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (intersectionPoly E lam μ)) = 0 := by
    -- Expand the base-changed polynomial directly.
    rw [show (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (intersectionPoly E lam μ))
        = X ^ 3 - C (fqToBar E (lam ^ 2)) * X ^ 2
            + C (fqToBar E (E.curveA - 2 * lam * μ)) * X
            + C (fqToBar E (E.curveB - μ ^ 2)) from by
      unfold intersectionPoly fqToBar
      simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
            Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]]
    rw [eval_add, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_C, eval_pow,
        eval_X, eval_mul, eval_C, eval_X]
    -- Substitute hChord into hOn (curve equation) and rearrange.
    have hOn' : Q.y ^ 2 = Q.x ^ 3 + fqToBar E E.curveA * Q.x + fqToBar E E.curveB := hOn
    rw [hChord] at hOn'
    -- Goal: Q.x^3 - fqToBar(lam^2) * Q.x^2 + fqToBar(A - 2λμ) * Q.x + fqToBar(B - μ^2) = 0.
    -- Use ring + the two ring-hom identities for fqToBar.
    have hfqLam : fqToBar E (lam ^ 2) = (fqToBar E lam) ^ 2 := by
      unfold fqToBar; rw [map_pow]
    have hfqMu : fqToBar E (μ ^ 2) = (fqToBar E μ) ^ 2 := by
      unfold fqToBar; rw [map_pow]
    have hfqAm : fqToBar E (E.curveA - 2 * lam * μ)
        = fqToBar E E.curveA - 2 * fqToBar E lam * fqToBar E μ := by
      unfold fqToBar
      rw [map_sub, map_mul, map_mul]
      have : (algebraMap (ZMod E.q) (Fqbar E)) 2 = 2 := by
        show (algebraMap (ZMod E.q) (Fqbar E)) (2 : ZMod E.q) = (2 : Fqbar E)
        rw [show (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) from by norm_cast]
        rw [map_natCast]; rfl
      rw [this]
    have hfqBm : fqToBar E (E.curveB - μ ^ 2)
        = fqToBar E E.curveB - (fqToBar E μ) ^ 2 := by
      unfold fqToBar
      rw [map_sub, map_pow]
    rw [hfqLam, hfqAm, hfqBm]
    linear_combination -hOn'
  -- Apply Vieta factorisation to identify Q.x as one of three rational lifts.
  have hFact := intersectionPoly_factorisation E A₀ A₁ hA₀ hA₁ hNV
  rw [show μ = zLambda E lam A₀ from rfl] at hRoot
  rw [hFact] at hRoot
  -- Compute base-change: factorisation transports to (X - C fqA₀)(X - C fqA₁)(X - C fqx₂).
  rw [show Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        ((X - C A₀.1) * (X - C A₁.1) * (X - C (chordX₂ A₀ A₁)))
      = (X - C (fqToBar E A₀.1)) * (X - C (fqToBar E A₁.1)) *
          (X - C (fqToBar E (chordX₂ A₀ A₁))) from by
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, fqToBar]] at hRoot
  rw [eval_mul, eval_mul, eval_sub, eval_X, eval_C,
      eval_sub, eval_X, eval_C, eval_sub, eval_X, eval_C] at hRoot
  -- Generic helper: from Q.x = fqToBar p₁ and Q.y = fqToBar p₂, derive
  -- `D.geomEval E Q = fqToBar E (D.eval p₁ p₂)`.
  have geomEvalRewrite : ∀ p₁ p₂ : ZMod E.q, Q.x = fqToBar E p₁ → Q.y = fqToBar E p₂ →
      D.geomEval E Q = fqToBar E (D.eval p₁ p₂) := by
    intro p₁ p₂ hx hy
    show D.a.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x
        - D.b.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) Q.x * Q.y
        = algebraMap (ZMod E.q) (Fqbar E) (D.eval p₁ p₂)
    rw [hx, hy]
    show D.a.eval₂ (algebraMap (ZMod E.q) (Fqbar E))
            (algebraMap (ZMod E.q) (Fqbar E) p₁)
        - D.b.eval₂ (algebraMap (ZMod E.q) (Fqbar E))
            (algebraMap (ZMod E.q) (Fqbar E) p₁) *
              algebraMap (ZMod E.q) (Fqbar E) p₂
        = algebraMap (ZMod E.q) (Fqbar E) (D.eval p₁ p₂)
    rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
    unfold CoordRingElt.eval
    rw [map_sub, map_mul]
  -- D.geomEval Q = 0 (since Q ∈ gd.support).
  have hZeroQ : D.geomEval E Q = 0 := gd.support_eval_zero Q hQ
  -- Q.x is a root: one of the three factors is 0.
  rcases mul_eq_zero.mp hRoot with hL | hR
  rcases mul_eq_zero.mp hL with h₀ | h₁
  -- Case 1: Q.x = fqToBar A₀.1, so Q.y = fqToBar A₀.2 by chord identity.
  · have hQx : Q.x = fqToBar E A₀.1 := by linear_combination h₀
    have hQy : Q.y = fqToBar E A₀.2 := by
      rw [hChord, hQx]
      show fqToBar E lam * fqToBar E A₀.1 + fqToBar E μ = fqToBar E A₀.2
      have hRing : lam * A₀.1 + (A₀.2 - lam * A₀.1) = A₀.2 := by ring
      have h1' : fqToBar E lam * fqToBar E A₀.1 + fqToBar E μ
          = fqToBar E (lam * A₀.1 + μ) := by
        unfold fqToBar; rw [map_add, map_mul]
      rw [h1', show μ = A₀.2 - lam * A₀.1 from rfl, hRing]
    have hGeomQ := geomEvalRewrite A₀.1 A₀.2 hQx hQy
    rw [hGeomQ] at hZeroQ
    exact h1 ((fqToBar_eq_zero_iff E _).mp hZeroQ)
  -- Case 2: Q.x = fqToBar A₁.1, so Q.y = fqToBar A₁.2.
  · have hQx : Q.x = fqToBar E A₁.1 := by linear_combination h₁
    have hSlope : lam * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
      rw [hLam, slopeOf]
      rw [mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hNV)), mul_one]
    have hQy : Q.y = fqToBar E A₁.2 := by
      rw [hChord, hQx]
      have h1' : fqToBar E lam * fqToBar E A₁.1 + fqToBar E μ
          = fqToBar E (lam * A₁.1 + μ) := by
        unfold fqToBar; rw [map_add, map_mul]
      have hRing : lam * A₁.1 + (A₀.2 - lam * A₀.1) = A₁.2 := by linear_combination hSlope
      rw [h1', show μ = A₀.2 - lam * A₀.1 from rfl, hRing]
    have hGeomQ := geomEvalRewrite A₁.1 A₁.2 hQx hQy
    rw [hGeomQ] at hZeroQ
    exact h2 ((fqToBar_eq_zero_iff E _).mp hZeroQ)
  -- Case 3: Q.x = fqToBar (chordX₂ A₀ A₁), so Q.y = fqToBar (chordY₂ A₀ A₁).
  · -- The rational chord-third coords (in ZMod E.q).
    have hQx : Q.x = fqToBar E (lam ^ 2 - A₀.1 - A₁.1) := by
      have h := hR
      have hChordX₂eq : chordX₂ A₀ A₁ = lam ^ 2 - A₀.1 - A₁.1 := rfl
      rw [hChordX₂eq] at h
      linear_combination h
    have hQy : Q.y = fqToBar E
        (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)) := by
      rw [hChord, hQx]
      have h1' : fqToBar E lam * fqToBar E (lam ^ 2 - A₀.1 - A₁.1) + fqToBar E μ
          = fqToBar E (lam * (lam ^ 2 - A₀.1 - A₁.1) + μ) := by
        unfold fqToBar; rw [map_add, map_mul]
      rw [h1', show μ = A₀.2 - lam * A₀.1 from rfl]
    have hGeomQ := geomEvalRewrite
      (lam ^ 2 - A₀.1 - A₁.1)
      (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      hQx hQy
    rw [hGeomQ] at hZeroQ
    exact h3 ((fqToBar_eq_zero_iff E _).mp hZeroQ)

/--
Geometric trace/log-derivative identity on one nonvertical chord.

This is the geometric replacement for the split-only
`chord_sum_eq_residue_sum`: the three `logDerivTerm`s on the rational
chord fiber equal the residue sum over the full geometric zero divisor
of `D` in `F_qbar`, with multiplicities supplied by `GeometricDivisorData`.

The theorem is intentionally separated from the denominator-clearing
algebra in `geomPolyGFullBar_eval_zero_iff_logDerivCheckFn`. It is the
function-field trace step Aristotle should attack directly.

The line factor `lineEvalNumAtFullBar E Q` is the scaled line evaluation:
at `(A₀, A₁)` it contributes `(A₁.1 - A₀.1) * lineThrough(A₀,A₁)(Q)`.
The residue sum below therefore includes the corresponding
`fqToBar E (A₁.1 - A₀.1)` factor.
-/
theorem geometric_chord_sum_eq_residue_sum
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    fqToBar E
        (logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀
          + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₁
          + logDerivTerm E D E.curveA (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
              (chordX₂ A₀ A₁, chordY₂ A₀ A₁))
      =
        -(fqToBar E (A₁.1 - A₀.1)) * ∑ Q ∈ gd.support,
          ((gd.mult Q : ℕ) : Fqbar E) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBar E Q))⁻¹ := by
  classical
  -- Step D: assembly of the chord-sum identity.
  -- Setup: chord slope and intercept.
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  -- Bezout: no Q ∈ gd.support is on the chord.
  have hAvoid := geom_support_avoids_chord E D gd P B A₀ A₁ hA₀ hA₁ hNV hDef
  -- Rewrite each (line factor)⁻¹ as -(fqToBar(A₁.1-A₀.1))⁻¹ · (μ_bar - zLambdaBar Q)⁻¹.
  have hLineRewrite : ∀ Q ∈ gd.support,
      (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹
        = -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹ := by
    intro Q _hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    show (-(fqToBar E (A₁.1 - A₀.1)) * (fqToBar E μ - zLambdaBar E lam Q))⁻¹
        = -(fqToBar E (A₁.1 - A₀.1))⁻¹ * (fqToBar E μ - zLambdaBar E lam Q)⁻¹
    rw [neg_mul, inv_neg, mul_inv]
    ring
  -- Extract D-nonzero and individual chord-fiber non-vanishing conditions from `hDef`.
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have hProdNZ := hDef
  have hBlineProd : (Finset.univ : Finset (Fin k)).prod
        (fun j => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hProdNZ
  have h7 : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have hLeftOf7 := left_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have h6 : 3 * (lam ^ 2 - A₀.1 - A₁.1) ^ 2 + E.curveA -
        2 * lam * (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)) ≠ 0 :=
    right_ne_zero_of_mul hLeftOf7
  have hLeftOf6 := left_ne_zero_of_mul hLeftOf7
  have h5 : 3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf6
  have hLeftOf5 := left_ne_zero_of_mul hLeftOf6
  have h4 : 3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf5
  have hLeftOf4 := left_ne_zero_of_mul hLeftOf5
  have h3 : D.eval (lam ^ 2 - A₀.1 - A₁.1)
              (lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)) ≠ 0 :=
    right_ne_zero_of_mul hLeftOf4
  have hLeftOf3 := left_ne_zero_of_mul hLeftOf4
  have h2 : D.eval A₁.1 A₁.2 ≠ 0 := right_ne_zero_of_mul hLeftOf3
  have h1 : D.eval A₀.1 A₀.2 ≠ 0 := left_ne_zero_of_mul hLeftOf3
  have hDnz : ¬ (D.a = 0 ∧ D.b = 0) := by
    intro ⟨ha, hb⟩
    apply h1
    unfold CoordRingElt.eval
    simp [ha, hb]
  have hDen : ∀ pt : ZMod E.q × ZMod E.q,
      pt = A₀ ∨ pt = A₁ ∨
      pt = (lam ^ 2 - A₀.1 - A₁.1,
            lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1))
      → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0 := by
    rintro pt (rfl | rfl | rfl) <;> assumption
  -- Geometric factorisation of `chord_fiber_product` over `Fqbar`.
  obtain ⟨c, hc_ne, hcfp_eq⟩ :=
    chord_fiber_product_bar_factorisation E D lam hDnz gd
  -- Non-vanishing: `eval μ_bar (∏ Q (X − C zLambdaBar Q)^(mult Q)) ≠ 0` from `hAvoid`.
  set Pol : Polynomial (Fqbar E) :=
      ∏ Q ∈ gd.support, (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) with hPol_def
  have hPolEval : eval (fqToBar E μ) Pol =
      ∏ Q ∈ gd.support, (fqToBar E μ - zLambdaBar E lam Q) ^ (gd.mult Q) := by
    rw [hPol_def, eval_prod]
    apply Finset.prod_congr rfl
    intro Q _
    rw [eval_pow, eval_sub, eval_X, eval_C]
  have hPolNe : eval (fqToBar E μ) Pol ≠ 0 := by
    rw [hPolEval]
    refine Finset.prod_ne_zero_iff.mpr (fun Q hQ => ?_)
    exact pow_ne_zero _ (hAvoid Q hQ)
  have hCfpBarEval : eval (fqToBar E μ)
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)) = c * eval (fqToBar E μ) Pol := by
    rw [hcfp_eq]; rw [eval_mul, eval_C]
  have hCfpBarNe : eval (fqToBar E μ)
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product E lam D)) ≠ 0 := by
    rw [hCfpBarEval]; exact mul_ne_zero hc_ne hPolNe
  -- The rational chord_fiber_product also has nonzero value at μ (via fqToBar injectivity).
  have hCfpRatNe : (chord_fiber_product E lam D).eval μ ≠ 0 := by
    intro hZero
    apply hCfpBarNe
    rw [show (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)).eval (fqToBar E μ)
        = fqToBar E ((chord_fiber_product E lam D).eval μ) from by
      simp [fqToBar, Polynomial.eval_map, Polynomial.eval₂_at_apply]]
    rw [hZero]; simp [fqToBar]
  -- Rational chord-sum identity (axiom).
  have hRatLHS := chord_sum_eq_chord_fiber_product_logDeriv E D A₀ A₁ hA₀ hA₁ hNV
    hDnz h1 h2 h3 hDen hCfpRatNe
  -- Lift `eval μ p = ...` to Fqbar via the algebra map.
  have hEvalMap : ∀ p : (ZMod E.q)[X],
      eval (fqToBar E μ) (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) p)
        = fqToBar E (eval μ p) := by
    intro p
    simp [fqToBar, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hDerivMap : Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (derivative (chord_fiber_product E lam D))
      = derivative (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)) := by
    rw [Polynomial.derivative_map]
  -- LHS_rat = N_rat / D_rat with N_rat = eval μ (derivative cfp), D_rat = eval μ cfp.
  -- Apply fqToBar to the rational identity.
  have hRatLHSBar : fqToBar E
        (logDerivTerm E D E.curveA lam A₀
          + logDerivTerm E D E.curveA lam A₁
          + logDerivTerm E D E.curveA lam
              (lam ^ 2 - A₀.1 - A₁.1,
               lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
      = fqToBar E (eval μ (derivative (chord_fiber_product E lam D)))
          / fqToBar E ((chord_fiber_product E lam D).eval μ) := by
    rw [hRatLHS]
    rw [show fqToBar E
        (eval μ (derivative (chord_fiber_product E lam D))
          / (chord_fiber_product E lam D).eval μ)
        = fqToBar E (eval μ (derivative (chord_fiber_product E lam D)))
            / fqToBar E ((chord_fiber_product E lam D).eval μ) from ?_]
    show fqToBar E (eval μ (derivative (chord_fiber_product E lam D))
        / (chord_fiber_product E lam D).eval μ) = _
    rw [show fqToBar E = (algebraMap (ZMod E.q) (Fqbar E) :
            ZMod E.q →+* Fqbar E) from rfl, map_div₀]
  -- Unfold chordX₂/chordY₂ in the goal and re-fold lam to match hRatLHSBar.
  show fqToBar E
        (logDerivTerm E D E.curveA lam A₀
          + logDerivTerm E D E.curveA lam A₁
          + logDerivTerm E D E.curveA lam
              (lam ^ 2 - A₀.1 - A₁.1,
               lam * (lam ^ 2 - A₀.1 - A₁.1) + (A₀.2 - lam * A₀.1)))
      = -(fqToBar E (A₁.1 - A₀.1)) * ∑ Q ∈ gd.support,
          ((gd.mult Q : ℕ) : Fqbar E) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBar E Q))⁻¹
  -- Express the Fqbar-side via Polynomial.map + factorisation.
  rw [hRatLHSBar]
  rw [← hEvalMap, ← hEvalMap, hDerivMap]
  -- Substitute the factorisation `Polynomial.map _ cfp = C c * Pol`.
  rw [hcfp_eq]
  -- Distribute derivative: `derivative (C c * Pol) = C c * derivative Pol`.
  rw [Polynomial.derivative_C_mul]
  -- Evaluate `eval μ_bar (C c * derivative Pol)` and `eval μ_bar (C c * Pol)`.
  rw [eval_mul, eval_mul, eval_C]
  -- Cancel the `c` constant from numerator and denominator.
  rw [mul_div_mul_left _ _ hc_ne]
  -- Use Step B (PFE).
  rw [prod_X_sub_C_zLambdaBar_logDeriv_at_nonroot E D gd lam (fqToBar E μ) hAvoid]
  -- (Pol_eval * S) / Pol_eval = S, since Pol_eval ≠ 0.
  rw [mul_comm (eval (fqToBar E μ) Pol) _, mul_div_assoc, div_self hPolNe, mul_one]
  -- Convert (μ_bar - zLambdaBar Q)⁻¹ to (line factor)⁻¹ form via hLineRewrite.
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [hLineRewrite Q hQ]
  -- Goal: (mult Q) · (μ_bar - zLambdaBar Q)⁻¹
  --     = -fqToBar(A₁.1-A₀.1) · ((mult Q) · (-(fqToBar(A₁.1-A₀.1))⁻¹ · (μ_bar - zLambdaBar Q)⁻¹))
  field_simp

/-- **Bar-eval factorisation of `geomPolyGFullBar`.** When every line factor
is nonzero at the bar-evaluation point, `geomPolyGFullBar` evaluated equals
the product of all line factors times the residue-divided form. -/
private theorem geomPolyGFullBar_eval_eq_residue_clear
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hQline : ∀ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) ≠ 0)
    (hRline : ∀ j,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) ≠ 0) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (geomPolyGFullBar E D gd R m)
      = (∏ Q ∈ gd.support,
          MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))
        * (∏ j,
          MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)))
        * ((∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
              (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
            + (∑ j, fqToBar E (m j) *
              (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
                (lineEvalNumAtFullBarOfFq E (R j)))⁻¹)) := by
  classical
  set evalQ : GeomPoint E → Fqbar E := fun Q =>
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) with hevalQ
  set evalR : Fin M → Fqbar E := fun j =>
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) with hevalR
  -- Per-Q rewrite: ∏_{Q'≠Q} evalQ Q' = ProdQ · (evalQ Q)⁻¹ when evalQ Q ≠ 0.
  have hEraseQ : ∀ Q ∈ gd.support,
      (∏ Q' ∈ gd.support.erase Q, evalQ Q')
        = (∏ Q' ∈ gd.support, evalQ Q') * (evalQ Q)⁻¹ := by
    intro Q hQ
    have h : evalQ Q * (∏ Q' ∈ gd.support.erase Q, evalQ Q')
        = (∏ Q' ∈ gd.support, evalQ Q') :=
      Finset.mul_prod_erase gd.support evalQ hQ
    rw [← h]
    rw [mul_comm (evalQ Q), mul_assoc, mul_inv_cancel₀ (hQline Q hQ), mul_one]
  -- Per-j rewrite analogously.
  have hEraseR : ∀ j : Fin M,
      (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, evalR j')
        = (∏ j', evalR j') * (evalR j)⁻¹ := by
    intro j
    have h : evalR j * (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, evalR j')
        = (∏ j', evalR j') :=
      Finset.mul_prod_erase (Finset.univ : Finset (Fin M)) evalR (Finset.mem_univ j)
    rw [← h]
    rw [mul_comm (evalR j), mul_assoc, mul_inv_cancel₀ (hRline j), mul_one]
  unfold geomPolyGFullBar
  simp only [map_add, map_sum, map_mul, map_prod, MvPolynomial.eval_C]
  rw [show (∑ Q ∈ gd.support,
        ((gd.mult Q : ℕ) : Fqbar E)
          * (∏ Q' ∈ gd.support.erase Q, evalQ Q')
          * (∏ j, evalR j))
      = ((∏ Q ∈ gd.support, evalQ Q) * (∏ j, evalR j)) *
          ∑ Q ∈ gd.support,
            ((gd.mult Q : ℕ) : Fqbar E) * (evalQ Q)⁻¹ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [hEraseQ Q hQ]
    ring]
  rw [show (∑ j, fqToBar E (m j)
          * (∏ Q ∈ gd.support, evalQ Q)
          * (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, evalR j'))
      = ((∏ Q ∈ gd.support, evalQ Q) * (∏ j, evalR j)) *
          ∑ j, fqToBar E (m j) * (evalR j)⁻¹ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hEraseR j]
    ring]
  ring

set_option maxHeartbeats 800000 in
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
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu_def
  set R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B with hR
  set m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j) with hM'
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  -- Extract individual non-vanishing from hDef.
  have hAvoid := geom_support_avoids_chord E D gd P B A₀ A₁ hA₀ hA₁ hNV hDef
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have hProdNZ := hDef
  have hBlineProd : (Finset.univ : Finset (Fin k)).prod
        (fun j => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hProdNZ
  have h7 : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have hBline : ∀ j : Fin k,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0 := by
    intro j hj
    exact hBlineProd (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  -- ℓ_Q non-vanishing for Q ∈ gd.support: via Step C + geom_support_avoids_chord.
  have hLineQ : ∀ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) ≠ 0 := by
    intro Q hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr hXBar
    · exact hAvoid Q hQ
  -- ℓ_R_j non-vanishing for j ∈ Fin (k+1).
  have hLineR : ∀ j : Fin (k + 1),
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) ≠ 0 := by
    intro j
    rw [lineEvalNumAtFullBarOfFq_eval_ne_zero_iff E _ A₀ A₁ hNV]
    refine Fin.cases ?_ ?_ j
    · -- j = 0: R 0 = (P.1, -P.2). lineThrough doesn't vanish at -P (h7).
      show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R 0).1 (R 0).2 ≠ 0
      rw [hR]; simp [Fin.cons_zero]; exact h7
    · -- j = i.succ: R i.succ = B i. lineThrough doesn't vanish at B_i (hBline i).
      intro i
      show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R i.succ).1 (R i.succ).2 ≠ 0
      rw [hR]; simp [Fin.cons_succ]; exact hBline i
  -- ∏_Q ℓ_Q ≠ 0 and ∏_j ℓ_R_j ≠ 0.
  have hProdQ_ne : (∏ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hLineQ
  have hProdR_ne : (∏ j : Fin (k + 1),
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_; intro j _; exact hLineR j
  -- Apply bar-eval factorisation.
  rw [geomPolyGFullBar_eval_eq_residue_clear E D gd R m' A₀ A₁ hLineQ hLineR]
  -- Identify the residue-divided sum S with -fqToBar(logDerivCheckFn)/fqToBar(Δx).
  -- Step a: Σ_Q (mult Q) · ℓ_Q⁻¹ = -fqToBar(LHS_rat)/fqToBar(Δx) via chord-sum identity.
  have hSumQ : (∑ Q ∈ gd.support,
        ((gd.mult Q : ℕ) : Fqbar E) *
          (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
      = -fqToBar E
          (logDerivTerm E D E.curveA lam A₀
            + logDerivTerm E D E.curveA lam A₁
            + logDerivTerm E D E.curveA lam
                (chordX₂ A₀ A₁, chordY₂ A₀ A₁)) *
            (fqToBar E (A₁.1 - A₀.1))⁻¹ := by
    have hChord := geometric_chord_sum_eq_residue_sum E D gd P B A₀ A₁ hA₀ hA₁ hNV
      (by show logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0; exact hDef)
    -- hChord : fqToBar (logDerivTerm sum) = -fqToBar(Δx) · Σ (mult Q : Fqbar) · ℓ_Q⁻¹.
    -- Rearrange: Σ ... = -fqToBar(LHS) * fqToBar(Δx)⁻¹.
    set S : Fqbar E := ∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹
    set L : Fqbar E := fqToBar E
        (logDerivTerm E D E.curveA lam A₀
          + logDerivTerm E D E.curveA lam A₁
          + logDerivTerm E D E.curveA lam (chordX₂ A₀ A₁, chordY₂ A₀ A₁))
    show S = -L * (fqToBar E (A₁.1 - A₀.1))⁻¹
    have hL_eq : L = -fqToBar E (A₁.1 - A₀.1) * S := hChord
    rw [hL_eq]
    have : -(-fqToBar E (A₁.1 - A₀.1) * S) * (fqToBar E (A₁.1 - A₀.1))⁻¹
        = (fqToBar E (A₁.1 - A₀.1) * (fqToBar E (A₁.1 - A₀.1))⁻¹) * S := by ring
    rw [this, mul_inv_cancel₀ hXBar, one_mul]
  -- Step b: Σ_j fqToBar(m_j') · ℓ_R_j⁻¹ via Fin.cons + slope identity.
  have hLineR_eval : ∀ j : Fin (k + 1),
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j))
        = fqToBar E (A₁.1 - A₀.1) *
            fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2) := by
    intro j; exact lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul E _ A₀ A₁ hNV
  have hSumR : (∑ j : Fin (k + 1), fqToBar E (m' j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)))⁻¹)
      = fqToBar E (-((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
          + (Finset.univ : Finset (Fin k)).sum (fun j =>
              -(m j) * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹))
        * (fqToBar E (A₁.1 - A₀.1))⁻¹ := by
    -- Sub-claim: each summand simplifies via hLineR_eval.
    have hSumand : ∀ j : Fin (k + 1),
        fqToBar E (m' j)
          * (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)))⁻¹
        = fqToBar E (m' j *
            ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹)
          * (fqToBar E (A₁.1 - A₀.1))⁻¹ := by
      intro j
      have hL : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2 ≠ 0 := by
        have := hLineR j
        rw [hLineR_eval] at this
        rcases mul_ne_zero_iff.mp this with ⟨_, hF⟩
        exact (fqToBar_eq_zero_iff E _).not.mp hF
      rw [hLineR_eval]
      rw [mul_inv]
      have hfq_inv : fqToBar E
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹
          = (fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2))⁻¹ := by
        unfold fqToBar; exact map_inv₀ _ _
      have hfq_mul : fqToBar E (m' j *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹)
          = fqToBar E (m' j) *
              fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹ := by
        unfold fqToBar; rw [map_mul]
      rw [hfq_mul, hfq_inv]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hSumand j)]
    rw [← Finset.sum_mul]
    -- Combine the sum: factor (fqToBar E ...) inside.
    rw [show (∑ j : Fin (k + 1), fqToBar E (m' j *
              ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹))
        = fqToBar E (∑ j : Fin (k + 1), m' j *
              ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹) from by
      unfold fqToBar; rw [map_sum]]
    -- Unfold Fin.cons via Fin.sum_univ_succ.
    rw [show (∑ j : Fin (k + 1), m' j *
              ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹)
        = m' 0 * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R 0).1 (R 0).2)⁻¹
          + (Finset.univ : Finset (Fin k)).sum (fun i =>
              m' i.succ * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R i.succ).1 (R i.succ).2)⁻¹)
        from Fin.sum_univ_succ _]
    rw [hM', hR]
    simp [Fin.cons_zero, Fin.cons_succ]
  -- Combine hSumQ + hSumR via fqToBar additivity.
  have hLDF_eq : fqToBar E (logDerivCheckFn E D P k B m A₀ A₁)
      = fqToBar E
            (logDerivTerm E D E.curveA lam A₀
              + logDerivTerm E D E.curveA lam A₁
              + logDerivTerm E D E.curveA lam (chordX₂ A₀ A₁, chordY₂ A₀ A₁))
        - fqToBar E
            (-((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2))⁻¹
              + (Finset.univ : Finset (Fin k)).sum (fun j =>
                  -(m j) * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2)⁻¹)) := by
    unfold fqToBar
    rw [← map_sub]
    rfl
  -- S = -fqToBar(logDerivCheckFn) · fqToBar(Δx)⁻¹.
  have hS_eq : (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
      + (∑ j : Fin (k + 1), fqToBar E (m' j) *
          (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
            (lineEvalNumAtFullBarOfFq E (R j)))⁻¹)
      = -fqToBar E (logDerivCheckFn E D P k B m A₀ A₁) *
          (fqToBar E (A₁.1 - A₀.1))⁻¹ := by
    rw [hSumQ, hSumR, hLDF_eq]
    ring
  -- Conclude iff.
  rw [show (∏ Q ∈ gd.support,
          MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)) *
            (∏ j,
              MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)))
        * ((∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
              (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
            + (∑ j, fqToBar E (m' j) *
              (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
                (lineEvalNumAtFullBarOfFq E (R j)))⁻¹))
      = (∏ Q ∈ gd.support,
          MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)) *
            (∏ j,
              MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)))
        * (-fqToBar E (logDerivCheckFn E D P k B m A₀ A₁) *
            (fqToBar E (A₁.1 - A₀.1))⁻¹) from by rw [hS_eq]]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hProds | hRes
    · rcases mul_eq_zero.mp hProds with hPQ | hPR
      · exact absurd hPQ hProdQ_ne
      · exact absurd hPR hProdR_ne
    · rcases mul_eq_zero.mp hRes with hL | hX_inv
      · exact (fqToBar_eq_zero_iff E _).mp (neg_eq_zero.mp hL)
      · exact absurd hX_inv (inv_ne_zero hXBar)
  · intro h
    rw [h]
    simp [fqToBar]

/--
Residue identity at a defined non-vertical chord: under `logDerivCheckFn = 0`,
the bar-evaluation of `geomPolyGFullBar` (with R = `Fin.cons (-P_aff) B` and
`m' = Fin.cons (-1) (-m_j)`) vanishes.

Direct corollary of `geomPolyGFullBar_eval_zero_iff_logDerivCheckFn` plus
the all-zero hypothesis on defined non-vertical pairs.
-/
private theorem geomPolyGFullBar_eval_zero_of_hAllZero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
        (geomPolyGFullBar E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))) = 0 :=
  (geomPolyGFullBar_eval_zero_iff_logDerivCheckFn E D gd P B m A₀ A₁
      hA₀ hA₁ hNV hDef).mpr (hAllZero A₀ A₁ hA₀ hA₁ hNV hDef)

/-- Predicate: every `Q ∈ gd.support` has `F_q`-rational coordinates. -/
def gd_support_rational (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) : Prop :=
  ∀ Q ∈ gd.support, ∃ P : ZMod E.q × ZMod E.q,
    P ∈ E.points ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2

/-- Rationality of `gd.support` is equivalent to every support point being
fixed by Frobenius. -/
private theorem gd_support_rational_iff_frob_fixed
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) :
    gd_support_rational E D gd ↔
      (∀ Q ∈ gd.support, frobGeomPoint E Q = Q) := by
  constructor
  · intro hRat Q hQ
    obtain ⟨P, _, hPx, hPy⟩ := hRat Q hQ
    exact frobGeomPoint_of_rational E Q P hPx hPy
  · intro hFix Q hQ
    obtain ⟨P, hPx, hPy⟩ := rational_of_frobGeomPoint_fixed E Q (hFix Q hQ)
    refine ⟨P, ?_, hPx, hPy⟩
    -- P ∈ E.points: deduce from Q.onCurve via fqToBar injectivity.
    apply E.hComplete
    have hCurve : Q.y ^ 2 = Q.x ^ 3 + fqToBar E E.curveA * Q.x + fqToBar E E.curveB :=
      Q.onCurve
    rw [hPx, hPy] at hCurve
    have hLhs : (fqToBar E P.2) ^ 2 = fqToBar E (P.2 ^ 2) := by
      unfold fqToBar; rw [map_pow]
    have hRhs : (fqToBar E P.1) ^ 3 + fqToBar E E.curveA * fqToBar E P.1 +
        fqToBar E E.curveB =
          fqToBar E (P.1 ^ 3 + E.curveA * P.1 + E.curveB) := by
      unfold fqToBar; rw [map_add, map_add, map_pow, map_mul]
    rw [hLhs, hRhs] at hCurve
    exact (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E)) hCurve

/-- If every geometric support point has rational coordinates, then `D`'s
norm polynomial splits over `F_q` and every root has a rational lift —
i.e., `splitsOnE E D`. -/
private theorem splitsOnE_of_gd_support_rational
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hRat : gd_support_rational E D gd) :
    splitsOnE E D := by
  classical
  -- Strategy:
  -- 1. Every root α of normPolyBar has rootMultiplicity > 0; by
  --    gd.fiber_accounting, ∃ Q ∈ gd.support with Q.x = α and gd.mult Q > 0.
  -- 2. By hRat, Q.x = fqToBar β for some rational β; so α = fqToBar β.
  -- 3. Every Fqbar-root of normPolyBar is in fqToBar(ZMod E.q), and by
  --    fqToBar injectivity, normPoly E D splits over F_q.
  -- 4. Each F_q-root α has a rational lift Q ∈ E.points with Q.x = α
  --    (from the rational point P with P.1 = α derived from hRat).
  refine ⟨?_, ?_⟩
  · -- normPoly_splits_over_Fq E D: card roots = natDegree.
    unfold normPoly_splits_over_Fq
    have hNormBar_ne : normPolyBar E D ≠ 0 := normPolyBar_ne_zero E D hDnz
    have hNorm_ne : normPoly E D ≠ 0 := normPoly_ne_zero E D hDnz
    -- Every Fqbar-root of normPolyBar is in image fqToBar (via fiber_accounting + hRat).
    have hRootInImage : ∀ β ∈ (normPolyBar E D).roots,
        ∃ α : ZMod E.q, β = fqToBar E α := by
      intro β hβ
      have hMul : (normPolyBar E D).rootMultiplicity β > 0 :=
        (Polynomial.rootMultiplicity_pos hNormBar_ne).mpr
          ((Polynomial.mem_roots hNormBar_ne).mp hβ)
      have hSum := gd.fiber_accounting β
      have hPos : 0 <
          (∑ Q ∈ gd.support.filter (fun Q => Q.x = β), gd.mult Q) := by
        rw [hSum]; exact hMul
      have hNonempty : (gd.support.filter (fun Q => Q.x = β)).Nonempty := by
        by_contra hEmp
        rw [Finset.not_nonempty_iff_eq_empty] at hEmp
        rw [hEmp, Finset.sum_empty] at hPos
        exact lt_irrefl _ hPos
      obtain ⟨Q, hQ⟩ := hNonempty
      have hQmem : Q ∈ gd.support := (Finset.mem_filter.mp hQ).1
      have hQx : Q.x = β := (Finset.mem_filter.mp hQ).2
      obtain ⟨P, _, hPx, _⟩ := hRat Q hQmem
      exact ⟨P.1, by rw [← hQx, hPx]⟩
    -- Multiset equality: normPolyBar.roots = normPoly.roots.map fqToBar.
    have hRootsEq : (normPolyBar E D).roots = (normPoly E D).roots.map (fqToBar E) := by
      apply Multiset.ext.mpr
      intro β
      by_cases hβImg : ∃ α : ZMod E.q, β = fqToBar E α
      · obtain ⟨α, hαβ⟩ := hβImg
        subst hαβ
        -- Compute the multiset count on each side and reduce to eq_rootMultiplicity_map.
        have hLHS :
            Multiset.count (fqToBar E α) (normPolyBar E D).roots
              = (normPoly E D).rootMultiplicity α := by
          rw [Polynomial.count_roots]
          unfold normPolyBar fqToBar
          exact (Polynomial.eq_rootMultiplicity_map (RingHom.injective _) α).symm
        have hRHS :
            Multiset.count (fqToBar E α) ((normPoly E D).roots.map (fqToBar E))
              = (normPoly E D).rootMultiplicity α := by
          rw [Multiset.count_map]
          have hFilter :
              ((normPoly E D).roots.filter
                  (fun a => fqToBar E α = fqToBar E a)).card
                = Multiset.count α (normPoly E D).roots := by
            rw [Multiset.count]
            rw [Multiset.countP_eq_card_filter]
            congr 1
            apply Multiset.filter_congr
            intro a _
            constructor
            · intro h
              exact (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E)) h
            · intro h; rw [h]
          rw [hFilter]
          rw [Polynomial.count_roots]
        rw [hLHS, hRHS]
      · -- β not in image: count β LHS = 0 (since β ∉ roots by hRootInImage); count β RHS = 0.
        have hLHS : Multiset.count β (normPolyBar E D).roots = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hMem
          exact hβImg (hRootInImage β hMem)
        have hRHS : Multiset.count β ((normPoly E D).roots.map (fqToBar E)) = 0 := by
          rw [Multiset.count_map]
          apply Multiset.card_eq_zero.mpr
          rw [Multiset.filter_eq_nil]
          intro α' _
          intro hαβ
          exact hβImg ⟨α', hαβ⟩
        rw [hLHS, hRHS]
    -- card LHS = card RHS = card normPoly.roots.
    have hCardEq : (normPolyBar E D).roots.card = (normPoly E D).roots.card := by
      rw [hRootsEq, Multiset.card_map]
    -- card normPolyBar.roots = natDegree normPolyBar (alg closed).
    have hCardBar : (normPolyBar E D).roots.card = (normPolyBar E D).natDegree := by
      have hSplits : (normPolyBar E D).Splits := IsAlgClosed.splits _
      exact hSplits.natDegree_eq_card_roots.symm
    have hNatBar : (normPolyBar E D).natDegree = (normPoly E D).natDegree := by
      unfold normPolyBar
      exact Polynomial.natDegree_map _
    rw [← hCardEq, hCardBar, hNatBar]
  · intro α hα
    -- α is an F_q-root of normPoly E D. Want: ∃ y ∈ ZMod E.q, (α, y) ∈ E.points.
    -- Step 1: lift α to fqToBar α, a Fqbar-root of normPolyBar E D.
    have hNormBar_ne : normPolyBar E D ≠ 0 := normPolyBar_ne_zero E D hDnz
    have hNorm_ne : normPoly E D ≠ 0 := normPoly_ne_zero E D hDnz
    have hRootBar_isRoot : (normPolyBar E D).IsRoot (fqToBar E α) := by
      unfold normPolyBar fqToBar Polynomial.IsRoot
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      have hEval0 : (normPoly E D).eval α = 0 := by
        rw [← Polynomial.IsRoot]
        exact (Polynomial.mem_roots hNorm_ne).mp hα
      rw [hEval0]
      simp
    have hRootBar : (normPolyBar E D).rootMultiplicity (fqToBar E α) > 0 :=
      (Polynomial.rootMultiplicity_pos hNormBar_ne).mpr hRootBar_isRoot
    -- Step 2: by gd.fiber_accounting, ∃ Q ∈ support with Q.x = fqToBar α and mult Q > 0.
    have hSum := gd.fiber_accounting (fqToBar E α)
    have hSum_pos : 0 <
        (∑ Q ∈ gd.support.filter (fun Q => Q.x = fqToBar E α), gd.mult Q) := by
      rw [hSum]; exact hRootBar
    have hNonempty :
        (gd.support.filter (fun Q => Q.x = fqToBar E α)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty] at hSum_pos
      exact lt_irrefl _ hSum_pos
    obtain ⟨Q, hQfilter⟩ := hNonempty
    have hQmem : Q ∈ gd.support := (Finset.mem_filter.mp hQfilter).1
    have hQx_eq : Q.x = fqToBar E α := (Finset.mem_filter.mp hQfilter).2
    -- Step 3: Q is rational by hRat; the rational lift gives the y-coordinate.
    obtain ⟨P, hPpts, hPx, hPy⟩ := hRat Q hQmem
    -- P.1 = α by injectivity.
    have hP1 : P.1 = α := by
      have : fqToBar E P.1 = fqToBar E α := hPx ▸ hQx_eq
      exact (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E)) this
    refine ⟨P.2, ?_⟩
    rw [← hP1]; exact hPpts

/-! ## Geometric residue-matching via specialization over `F_qbar`

Inspired by the paper's `residue-matching-cleared` lemma: from
identical vanishing of the cleared numerator `geomPolyGFullBar`, fix a
geometric support point `R₀`, choose `A₁` avoiding the finite set of other
line factors, evaluate at `A₀ = R₀`, and observe that only the
`R₀`-summand survives. This does not require support points to be
`F_q`-rational or `splitsOnE`.
-/

/-- Four-variable evaluation at a geometric point pair `(A₀, A₁)` over `F_qbar`. -/
noncomputable def geomBarEvalFun
    (A₀ : GeomPoint E) (a₁x a₁y : Fqbar E) : Fin 4 → Fqbar E :=
  ![A₀.x, A₀.y, a₁x, a₁y]

/-- `lineEvalNumAtFullBar Q` evaluates to zero when `A₀ = Q`. -/
theorem lineEvalNumAtFullBar_self_zero
    (Q : GeomPoint E) (a₁x a₁y : Fqbar E) :
    MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
      (lineEvalNumAtFullBar E Q) = 0 := by
  unfold lineEvalNumAtFullBar geomBarEvalFun
  simp [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `lineEvalNumAtFullBarOfFq P` self-vanishes at the `F_qbar`-embedding of `P`. -/
theorem lineEvalNumAtFullBarOfFq_self_zero
    (P : ZMod E.q × ZMod E.q) (a₁x a₁y : Fqbar E)
    (Q : GeomPoint E) (hx : Q.x = fqToBar E P.1) (hy : Q.y = fqToBar E P.2) :
    MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
      (lineEvalNumAtFullBarOfFq E P) = 0 := by
  unfold lineEvalNumAtFullBarOfFq geomBarEvalFun
  simp [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hx, hy]
  ring

/--
When `geomPolyGFullBar` is evaluated at `A₀ = Q₀` for `Q₀ ∈ gd.support`,
all terms vanish except the `Q₀` summand in the geometric-support sum.
-/
theorem geomPolyGFullBar_eval_at_support_point
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (Q₀ : GeomPoint E) (hQ₀ : Q₀ ∈ gd.support)
    (a₁x a₁y : Fqbar E) :
    MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
        (geomPolyGFullBar E D gd R m) =
      ((gd.mult Q₀ : ℕ) : Fqbar E) *
        (∏ Q' ∈ gd.support.erase Q₀,
          MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
            (lineEvalNumAtFullBar E Q')) *
        (∏ j : Fin M,
          MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
            (lineEvalNumAtFullBarOfFq E (R j))) := by
  classical
  unfold geomPolyGFullBar
  simp only [map_add, map_sum, map_mul, map_prod, MvPolynomial.eval_C]
  have hSelfZero := lineEvalNumAtFullBar_self_zero E Q₀ a₁x a₁y
  have hFirstOther : ∀ Q ∈ gd.support, Q ≠ Q₀ →
      ((gd.mult Q : ℕ) : Fqbar E) *
        (∏ Q' ∈ gd.support.erase Q,
          MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
            (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) = 0 := by
    intro Q _hQ hne
    have hQ₀mem : Q₀ ∈ gd.support.erase Q :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, hQ₀⟩
    have hp : ∏ Q' ∈ gd.support.erase Q,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q') = 0 :=
      Finset.prod_eq_zero hQ₀mem hSelfZero
    simp [hp]
  have hSecondAll : ∀ j : Fin M,
      fqToBar E (m j) *
        (∏ Q ∈ gd.support,
          MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
            (lineEvalNumAtFullBar E Q)) *
      (∏ j' ∈ Finset.univ.erase j,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j'))) = 0 := by
    intro j
    have hp : ∏ Q ∈ gd.support,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q) = 0 :=
      Finset.prod_eq_zero hQ₀ hSelfZero
    simp [hp]
  rw [Finset.sum_eq_single Q₀
    (fun Q hQ hne => hFirstOther Q hQ hne)
    (fun h => absurd hQ₀ h)]
  rw [Finset.sum_eq_zero (fun j _ => hSecondAll j)]
  ring

/--
If `geomPolyGFullBar = 0` and the product of remaining line factors is
nonzero at `(Q₀, A₁)`, then the geometric residue coefficient at `Q₀`
vanishes in `F_qbar`.
-/
theorem geom_residue_coeff_zero_of_poly_vanishing
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hVanish : geomPolyGFullBar E D gd R m = 0)
    (Q₀ : GeomPoint E) (hQ₀ : Q₀ ∈ gd.support)
    (a₁x a₁y : Fqbar E)
    (hProd :
      (∏ Q' ∈ gd.support.erase Q₀,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0) :
    ((gd.mult Q₀ : ℕ) : Fqbar E) = 0 := by
  have hEval := geomPolyGFullBar_eval_at_support_point E D gd R m Q₀ hQ₀ a₁x a₁y
  rw [hVanish, map_zero] at hEval
  rw [eq_comm, mul_assoc] at hEval
  exact (mul_eq_zero.mp hEval).resolve_right hProd

/--
If `geomPolyGFullBar = 0`, a rational residue point outside the geometric
support has zero coefficient, provided the remaining line-factor product
is nonzero at the specialization point.
-/
theorem geom_residue_rational_coeff_zero_of_poly_vanishing
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hVanish : geomPolyGFullBar E D gd R m = 0)
    (j₀ : Fin M)
    (Q_Rj₀ : GeomPoint E)
    (hx : Q_Rj₀.x = fqToBar E (R j₀).1)
    (hy : Q_Rj₀.y = fqToBar E (R j₀).2)
    (_hNotSupport : Q_Rj₀ ∉ gd.support)
    (a₁x a₁y : Fqbar E)
    (hProd :
      (∏ Q ∈ gd.support,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q)) *
      (∏ j' ∈ (Finset.univ (α := Fin M)).erase j₀,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j'))) ≠ 0) :
    fqToBar E (m j₀) = 0 := by
  classical
  have hEval : MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
      (geomPolyGFullBar E D gd R m) = 0 := by
    rw [hVanish]
    exact map_zero _
  unfold geomPolyGFullBar at hEval
  simp only [map_add, map_sum, map_mul, map_prod, MvPolynomial.eval_C] at hEval
  have hFqSelf : MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
      (lineEvalNumAtFullBarOfFq E (R j₀)) = 0 :=
    lineEvalNumAtFullBarOfFq_self_zero E (R j₀) a₁x a₁y Q_Rj₀ hx hy
  have hFirstAll : ∀ Q ∈ gd.support,
      ((gd.mult Q : ℕ) : Fqbar E) *
        (∏ Q' ∈ gd.support.erase Q,
          MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
            (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) = 0 := by
    intro Q _
    have hp : ∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) hFqSelf
    simp [hp]
  have hSecondOther : ∀ j : Fin M, j ≠ j₀ →
      fqToBar E (m j) *
        (∏ Q ∈ gd.support,
          MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
            (lineEvalNumAtFullBar E Q)) *
      (∏ j' ∈ Finset.univ.erase j,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j'))) = 0 := by
    intro j hne
    have hj₀mem : j₀ ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    have hp : ∏ j' ∈ Finset.univ.erase j,
        MvPolynomial.eval (geomBarEvalFun E Q_Rj₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j')) = 0 :=
      Finset.prod_eq_zero hj₀mem hFqSelf
    simp [hp]
  rw [Finset.sum_eq_zero hFirstAll, zero_add] at hEval
  rw [Finset.sum_eq_single j₀
    (fun j _ hne => hSecondOther j hne)
    (fun h => absurd (Finset.mem_univ j₀) h)] at hEval
  rw [mul_assoc] at hEval
  exact (mul_eq_zero.mp hEval).resolve_right hProd

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

/-
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
/-! ### Geometric residue matching

The all-zero branch of the soundness proof now follows the geometric
residue path. The key intermediate object is the descended polynomial
`geomPolyGFull` over `F_q`: by `geomPolyGFull_eval_eq_logDerivCheckFn`,
it vanishes on every defined non-vertical rational pair where
`logDerivCheckFn` vanishes (which, under `hAllZero`, is every defined
non-vertical pair of `E.points × E.points`).

For each rational zero `P` of `D`, the corresponding lifted geometric
point `Q_P = (fqToBar P.1, fqToBar P.2)` lies in `gd.support` because
the geometric support contains every geometric zero, and `Q_P` is a
geometric zero by `D.geomEval Q_P = 0`. Specialising
`geomPolyGFullBar` at `A₀ := P` with a carefully chosen rational `A₁`
isolates the `Q_P` summand, yielding either
`(gd.mult Q_P : Fqbar E) = 0` (which combined with `mult < E.q`
forces a contradiction) or matches `Q_P` against one of the
distinguished `distinctR` indices. The Frobenius stability of
`gd.support` and `F_q`-rationality of `(-P) + Σ m_j B_j` force the
matching to be onto rational points, yielding `splitsOnE E D`.

The single helper `geometric_residue_match` encapsulates this entire
residue-matching argument, taking the all-zero hypothesis, the
geometric divisor data, and the rational divisor data, and producing
both `splitsOnE` and the σ extractor data.
-/

/-! #### Phase 1 helpers -/

/-- Phase 1.1: the descended geometric numerator vanishes at every
defined non-vertical rational pair on which `logDerivCheckFn` vanishes. -/
private theorem geomPolyGFull_zero_at_defined_pair
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    bivEval₂ (geomPolyGFull E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
        A₀ A₁ = 0 :=
  (geomPolyGFull_eval_eq_logDerivCheckFn E D gd P B m A₀ A₁ hA₀ hA₁ hNV hDef).mpr hCheck

/-- Under `gd_support_rational`, the rational image of `gd.support`
coincides with `zerosFinset E D`. Each `Q ∈ gd.support` rationalizes to
a unique rational zero of `D`, and conversely every rational zero lifts
to a unique support point. -/
private theorem gd_support_eq_zerosFinset_image
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hRat : gd_support_rational E D gd)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support) :
    ∃! P : ZMod E.q × ZMod E.q,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 := by
  obtain ⟨P, hPpts, hPx, hPy⟩ := hRat Q hQ
  refine ⟨P, ?_, ?_⟩
  · refine ⟨?_, hPx, hPy⟩
    -- P ∈ zerosFinset E D: D.eval P = 0 (from D.geomEval Q = 0 + injectivity).
    rw [zerosFinset, zeros, Finset.mem_filter]
    refine ⟨hPpts, ?_⟩
    have hGeomZero : D.geomEval E Q = 0 := gd.support_eval_zero Q hQ
    have hLift : D.geomEval E
          (⟨fqToBar E P.1, fqToBar E P.2, by
              unfold fqToBar
              rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
              exact congrArg _ (E.hOnCurve P hPpts)⟩ : GeomPoint E)
          = fqToBar E (D.eval P.1 P.2) :=
      geomEval_lift_eq_fqToBar E D P (E.hOnCurve P hPpts)
    -- The lifted GeomPoint equals Q (same x, y).
    have hQeq : Q = (⟨fqToBar E P.1, fqToBar E P.2, by
        unfold fqToBar
        rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
        exact congrArg _ (E.hOnCurve P hPpts)⟩ : GeomPoint E) := by
      cases Q with
      | mk x y onCurve => exact GeomPoint.mk.injEq .. |>.mpr ⟨hPx, hPy⟩
    rw [hQeq] at hGeomZero
    rw [hLift] at hGeomZero
    -- hGeomZero: fqToBar E (D.eval P.1 P.2) = 0 ⇒ D.eval P.1 P.2 = 0.
    exact (fqToBar_eq_zero_iff E _).mp hGeomZero
  · rintro P' ⟨_, hP'x, hP'y⟩
    -- Uniqueness: P' has same coords as P after fqToBar.
    have h1 : fqToBar E P'.1 = fqToBar E P.1 := hP'x ▸ hPx
    have h2 : fqToBar E P'.2 = fqToBar E P.2 := hP'y ▸ hPy
    have e1 : P'.1 = P.1 :=
      (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E)) h1
    have e2 : P'.2 = P.2 :=
      (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E)) h2
    exact Prod.ext e1 e2

/-- Under `gd_support_rational`, the rationalize map sends each
`Q ∈ gd.support` to a rational zero of `D`. Used for the bijection
between `gd.support` and `zerosFinset E D`. -/
private noncomputable def gd_support_rationalize
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (hRat : gd_support_rational E D gd)
    {Q : GeomPoint E} (hQ : Q ∈ gd.support) :
    {P // P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2} :=
  ⟨(gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose,
    (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.1⟩

/-- Under `gd_support_rational`, the cardinality of `gd.support`
equals the number of rational zeros of `D`. -/
private theorem gd_support_card_eq_zerosCard
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (hRat : gd_support_rational E D gd) :
    gd.support.card = zerosCard E D := by
  classical
  unfold zerosCard
  let f : (Q : GeomPoint E) → Q ∈ gd.support → ZMod E.q × ZMod E.q :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose
  have hSpec : ∀ Q (hQ : Q ∈ gd.support),
      f Q hQ ∈ zerosFinset E D ∧ Q.x = fqToBar E (f Q hQ).1 ∧ Q.y = fqToBar E (f Q hQ).2 :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.1
  have hUniq : ∀ Q (hQ : Q ∈ gd.support) P,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 →
      P = f Q hQ :=
    fun Q hQ P hP =>
      (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.2 P hP
  refine Finset.card_bij f ?_ ?_ ?_
  · -- Maps to zerosFinset.
    intro Q hQ
    exact (hSpec Q hQ).1
  · -- Injective.
    intro Q₁ hQ₁ Q₂ hQ₂ heq
    have hP₁ := hSpec Q₁ hQ₁
    have hP₂ := hSpec Q₂ hQ₂
    have hx : Q₁.x = Q₂.x := by rw [hP₁.2.1, heq, ← hP₂.2.1]
    have hy : Q₁.y = Q₂.y := by rw [hP₁.2.2, heq, ← hP₂.2.2]
    exact GeomPoint.mk.injEq .. |>.mpr ⟨hx, hy⟩
  · -- Surjective onto zerosFinset.
    intro P hP
    rw [zerosFinset, zeros, Finset.mem_filter] at hP
    obtain ⟨hPpts, hPzero⟩ := hP
    set Q : GeomPoint E := ⟨fqToBar E P.1, fqToBar E P.2, by
      unfold fqToBar
      rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
      exact congrArg _ (E.hOnCurve P hPpts)⟩
    have hQmem : Q ∈ gd.support :=
      support_lift_of_rational_zero E D gd P hPpts hPzero
    refine ⟨Q, hQmem, ?_⟩
    -- f Q hQmem = P (by uniqueness clause).
    have hPmem : P ∈ zerosFinset E D := by
      rw [zerosFinset, zeros, Finset.mem_filter]
      exact ⟨hPpts, hPzero⟩
    exact (hUniq Q hQmem P ⟨hPmem, rfl, rfl⟩).symm

/-- The canonical rational lift of `P` as a `GeomPoint`, given that
`P ∈ E.points`. -/
private noncomputable def rationalLift
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) : GeomPoint E :=
  ⟨fqToBar E P.1, fqToBar E P.2, by
    unfold fqToBar
    rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
    exact congrArg _ (E.hOnCurve P hP)⟩

@[simp] theorem rationalLift_x
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    (rationalLift E P hP).x = fqToBar E P.1 := rfl

@[simp] theorem rationalLift_y
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    (rationalLift E P hP).y = fqToBar E P.2 := rfl

/-- The geometric multiplicity at the rational lift of `P`, when `P` is
a rational zero of `D`; otherwise zero. -/
private noncomputable def rationalMultAt
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) : ℕ :=
  if hP : P ∈ E.points ∧ D.eval P.1 P.2 = 0 then
    gd.mult (rationalLift E P hP.1)
  else 0

theorem rationalMultAt_eq_gd_mult_at_lift
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hZero : D.eval P.1 P.2 = 0) :
    rationalMultAt E D gd P = gd.mult (rationalLift E P hP) := by
  unfold rationalMultAt
  rw [dif_pos ⟨hP, hZero⟩]

/-- Under `gd_support_rational`, any `Fqbar`-valued sum over `gd.support`
that depends on `Q` only through `(Q.x, Q.y)` re-indexes to a sum over
`zerosFinset E D` over the rational lifts. -/
private theorem sum_gd_support_eq_zerosFinset_under_rational
    {α : Type*} [AddCommMonoid α]
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hRat : gd_support_rational E D gd)
    (φ : ZMod E.q × ZMod E.q → α)
    (ψ : GeomPoint E → α)
    (h_compat : ∀ Q ∈ gd.support, ∀ P : ZMod E.q × ZMod E.q,
        Q.x = fqToBar E P.1 → Q.y = fqToBar E P.2 → ψ Q = φ P) :
    ∑ Q ∈ gd.support, ψ Q = ∑ P ∈ zerosFinset E D, φ P := by
  classical
  let f : (Q : GeomPoint E) → Q ∈ gd.support → ZMod E.q × ZMod E.q :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose
  have hSpec : ∀ Q (hQ : Q ∈ gd.support),
      f Q hQ ∈ zerosFinset E D ∧ Q.x = fqToBar E (f Q hQ).1 ∧ Q.y = fqToBar E (f Q hQ).2 :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.1
  have hUniq : ∀ Q (hQ : Q ∈ gd.support) P,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 →
      P = f Q hQ :=
    fun Q hQ P hP =>
      (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.2 P hP
  refine Finset.sum_bij f ?_ ?_ ?_ ?_
  · intro Q hQ; exact (hSpec Q hQ).1
  · intro Q₁ hQ₁ Q₂ hQ₂ heq
    have hP₁ := hSpec Q₁ hQ₁
    have hP₂ := hSpec Q₂ hQ₂
    have hx : Q₁.x = Q₂.x := by rw [hP₁.2.1, heq, ← hP₂.2.1]
    have hy : Q₁.y = Q₂.y := by rw [hP₁.2.2, heq, ← hP₂.2.2]
    exact GeomPoint.mk.injEq .. |>.mpr ⟨hx, hy⟩
  · intro P hP
    rw [zerosFinset, zeros, Finset.mem_filter] at hP
    obtain ⟨hPpts, hPzero⟩ := hP
    set Q : GeomPoint E := ⟨fqToBar E P.1, fqToBar E P.2, by
      unfold fqToBar
      rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
      exact congrArg _ (E.hOnCurve P hPpts)⟩ with hQ_def
    have hQmem : Q ∈ gd.support :=
      support_lift_of_rational_zero E D gd P hPpts hPzero
    refine ⟨Q, hQmem, ?_⟩
    have hPmem : P ∈ zerosFinset E D := by
      rw [zerosFinset, zeros, Finset.mem_filter]
      exact ⟨hPpts, hPzero⟩
    exact (hUniq Q hQmem P ⟨hPmem, rfl, rfl⟩).symm
  · intro Q hQ
    exact h_compat Q hQ (f Q hQ) (hSpec Q hQ).2.1 (hSpec Q hQ).2.2

/-- Under `gd_support_rational`, the bar-level product of geometric line
factors over `gd.support` equals the product of rational line factors
over `zerosFinset E D` (re-indexed via the bijection `Q ↦ rational lift`). -/
private theorem prod_lineEvalNumAtFullBar_support_eq_under_rational
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hRat : gd_support_rational E D gd) :
    ∏ Q ∈ gd.support, lineEvalNumAtFullBar E Q
      = ∏ P ∈ zerosFinset E D, lineEvalNumAtFullBarOfFq E P := by
  classical
  let f : (Q : GeomPoint E) → Q ∈ gd.support → ZMod E.q × ZMod E.q :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose
  have hSpec : ∀ Q (hQ : Q ∈ gd.support),
      f Q hQ ∈ zerosFinset E D ∧ Q.x = fqToBar E (f Q hQ).1 ∧ Q.y = fqToBar E (f Q hQ).2 :=
    fun Q hQ => (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.1
  have hUniq : ∀ Q (hQ : Q ∈ gd.support) P,
      P ∈ zerosFinset E D ∧ Q.x = fqToBar E P.1 ∧ Q.y = fqToBar E P.2 →
      P = f Q hQ :=
    fun Q hQ P hP =>
      (gd_support_eq_zerosFinset_image E D hDnz gd hRat Q hQ).choose_spec.2 P hP
  refine Finset.prod_bij f ?_ ?_ ?_ ?_
  · intro Q hQ; exact (hSpec Q hQ).1
  · intro Q₁ hQ₁ Q₂ hQ₂ heq
    have hP₁ := hSpec Q₁ hQ₁
    have hP₂ := hSpec Q₂ hQ₂
    have hx : Q₁.x = Q₂.x := by rw [hP₁.2.1, heq, ← hP₂.2.1]
    have hy : Q₁.y = Q₂.y := by rw [hP₁.2.2, heq, ← hP₂.2.2]
    exact GeomPoint.mk.injEq .. |>.mpr ⟨hx, hy⟩
  · intro P hP
    rw [zerosFinset, zeros, Finset.mem_filter] at hP
    obtain ⟨hPpts, hPzero⟩ := hP
    set Q : GeomPoint E := ⟨fqToBar E P.1, fqToBar E P.2, by
      unfold fqToBar
      rw [← map_pow, ← map_pow, ← map_mul, ← map_add, ← map_add]
      exact congrArg _ (E.hOnCurve P hPpts)⟩ with hQ_def
    have hQmem : Q ∈ gd.support :=
      support_lift_of_rational_zero E D gd P hPpts hPzero
    refine ⟨Q, hQmem, ?_⟩
    have hPmem : P ∈ zerosFinset E D := by
      rw [zerosFinset, zeros, Finset.mem_filter]
      exact ⟨hPpts, hPzero⟩
    exact (hUniq Q hQmem P ⟨hPmem, rfl, rfl⟩).symm
  · intro Q hQ
    exact lineEvalNumAtFullBar_eq_lineEvalNumAtFullBarOfFq_of_rational E Q (f Q hQ)
      (hSpec Q hQ).2.1 (hSpec Q hQ).2.2

/-- Under `gd_support_rational`, the bar-level residue sum
`Σ_Q (mult Q : Fqbar) · (lineEvalNumAtFullBar Q evaluated)⁻¹` re-indexes
to `Σ_P ∈ zerosFinset (rationalMultAt P : Fqbar) · (lineEvalNumAtFullBarOfFq P evaluated)⁻¹`. -/
private theorem geom_residue_sum_re_index_under_rational
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hRat : gd_support_rational E D gd)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
      = ∑ P ∈ zerosFinset E D,
          ((rationalMultAt E D gd P : ℕ) : Fqbar E) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBarOfFq E P))⁻¹ := by
  classical
  refine sum_gd_support_eq_zerosFinset_under_rational E D hDnz gd hRat
    (fun P =>
      ((rationalMultAt E D gd P : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E P))⁻¹)
    (fun Q =>
      ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
    ?_
  intro Q hQ P hPx hPy
  -- Need: ψ Q = φ P, i.e. the geometric summand at Q equals the rational
  -- summand at P. P comes from the bijection so P ∈ zerosFinset; in
  -- particular P ∈ E.points and D.eval P = 0.
  -- Q is the rational lift of P, so gd.mult Q = rationalMultAt P.
  have hPgeom : ∃ P', P' ∈ E.points ∧ Q.x = fqToBar E P'.1 ∧ Q.y = fqToBar E P'.2 :=
    hRat Q hQ
  obtain ⟨P', hP'pts, hP'x, hP'y⟩ := hPgeom
  -- P' has same bar-image as P, hence equal.
  have hP_eq : P = P' := by
    apply Prod.ext <;>
      apply (FaithfulSMul.algebraMap_injective (ZMod E.q) (Fqbar E))
    · exact hPx.symm.trans hP'x
    · exact hPy.symm.trans hP'y
  have hPpts : P ∈ E.points := hP_eq ▸ hP'pts
  have hPzero : D.eval P.1 P.2 = 0 := by
    have hGeomZero : D.geomEval E Q = 0 := gd.support_eval_zero Q hQ
    have hLift : D.geomEval E (rationalLift E P hPpts) = fqToBar E (D.eval P.1 P.2) :=
      geomEval_lift_eq_fqToBar E D P (E.hOnCurve P hPpts)
    have hQeq : Q = rationalLift E P hPpts :=
      geomPoint_ext E Q (rationalLift E P hPpts) hPx hPy
    rw [hQeq] at hGeomZero
    rw [hLift] at hGeomZero
    exact (fqToBar_eq_zero_iff E _).mp hGeomZero
  -- Now use Q = rationalLift E P hPpts to bridge gd.mult Q = rationalMultAt P.
  have hQeq : Q = rationalLift E P hPpts :=
    geomPoint_ext E Q (rationalLift E P hPpts) hPx hPy
  have hMultEq : gd.mult Q = rationalMultAt E D gd P := by
    rw [hQeq, rationalMultAt_eq_gd_mult_at_lift E D gd P hPpts hPzero]
  have hLineEq : lineEvalNumAtFullBar E Q = lineEvalNumAtFullBarOfFq E P :=
    lineEvalNumAtFullBar_eq_lineEvalNumAtFullBarOfFq_of_rational E Q P hPx hPy
  show ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹
      = ((rationalMultAt E D gd P : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P))⁻¹
  rw [hMultEq, hLineEq]

/--
**Residue identity at defined non-vertical chords.** Under `hAllZero`,
the residue-divided sum
`Σ_Q (mult Q : Fqbar) · ℓ_Q⁻¹ + Σ_j fqToBar(m_j') · ℓ_R_j⁻¹`
vanishes at every defined non-vertical rational pair, where
`ℓ_Q := eval lineEvalNumAtFullBar Q` and
`ℓ_R_j := eval lineEvalNumAtFullBarOfFq R_j` are the line factors
evaluated at `(A₀, A₁)`.

Direct corollary of `geomPolyGFullBar_eval_zero_of_hAllZero` +
`geomPolyGFullBar_eval_eq_residue_clear` + line-factor non-vanishing
(from `geom_support_avoids_chord` and `hDef`).
-/
private theorem geom_residue_sum_zero_of_hAllZero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
    + (∑ j : Fin (k + 1),
        fqToBar E ((Fin.cons (-1) (fun j => -m j) : Fin (k + 1) → ZMod E.q) j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E
            ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j)))⁻¹) = 0 := by
  classical
  set R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B with hR_def
  set m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j) with hM'_def
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  -- Line factor non-vanishing on gd.support and on R.
  have hAvoid := geom_support_avoids_chord E D gd P B A₀ A₁ hA₀ hA₁ hNV hDef
  have hDef' : (have lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2;
      have L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2;
      have x₂ := lam ^ 2 - A₀.1 - A₁.1;
      have y₂ := lam * x₂ + (A₀.2 - lam * A₀.1);
      D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 * D.eval x₂ y₂ *
              (3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2) *
            (3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2) *
          (3 * x₂ ^ 2 + E.curveA - 2 * lam * y₂) *
        L.eval P.1 (-P.2) *
      ∏ j, L.eval (B j).1 (B j).2) ≠ 0 := hDef
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have h7 : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hDef)
  have hBlineProd : (Finset.univ : Finset (Fin k)).prod
        (fun j => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hDef
  have hBline : ∀ j : Fin k,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0 := by
    intro j hj
    exact hBlineProd (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hLineQ : ∀ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) ≠ 0 := by
    intro Q hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    apply mul_ne_zero (neg_ne_zero.mpr hXBar) (hAvoid Q hQ)
  have hLineR : ∀ j : Fin (k + 1),
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) ≠ 0 := by
    intro j
    rw [lineEvalNumAtFullBarOfFq_eval_ne_zero_iff E _ A₀ A₁ hNV]
    refine Fin.cases ?_ ?_ j
    · show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R 0).1 (R 0).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_zero]; exact h7
    · intro i
      show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R i.succ).1 (R i.succ).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_succ]; exact hBline i
  have hProdQ_ne : (∏ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hLineQ
  have hProdR_ne : (∏ j : Fin (k + 1),
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_; intro j _; exact hLineR j
  -- bar-eval = ProdQ · ProdR · S = 0; ProdQ, ProdR ≠ 0 ⇒ S = 0.
  have hZero : MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
      (geomPolyGFullBar E D gd R m') = 0 :=
    geomPolyGFullBar_eval_zero_of_hAllZero E D gd P B m hAllZero A₀ A₁ hA₀ hA₁ hNV hDef'
  rw [geomPolyGFullBar_eval_eq_residue_clear E D gd R m' A₀ A₁ hLineQ hLineR] at hZero
  rcases mul_eq_zero.mp hZero with hProds | hRes
  · rcases mul_eq_zero.mp hProds with hPQ | hPR
    · exact absurd hPQ hProdQ_ne
    · exact absurd hPR hProdR_ne
  · exact hRes

/-- A rational scalar-weighted summand of the bar-level residue identity
descends to `fqToBar` of a rational expression, when the line factor is
nonzero. -/
private theorem bar_residue_summand_descends_fq
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (c : ZMod E.q) (hLine : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0) :
    fqToBar E c *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P))⁻¹
      = fqToBar E (c *
          ((A₁.1 - A₀.1) *
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2)⁻¹) := by
  rw [lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul E P A₀ A₁ hNV]
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hPow : (fqToBar E (A₁.1 - A₀.1) *
      fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2))⁻¹
        = fqToBar E (((A₁.1 - A₀.1) *
              (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2)⁻¹) := by
    unfold fqToBar
    rw [← map_mul, map_inv₀]
  rw [hPow]
  unfold fqToBar
  rw [← map_mul]

/-- A rational `ℕ`-weighted summand (e.g. with `rationalMultAt`) of the
bar-level residue identity descends to `fqToBar` of a rational expression. -/
private theorem bar_residue_summand_descends
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (n : ℕ) (hLine : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0) :
    ((n : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P))⁻¹
      = fqToBar E ((n : ZMod E.q) *
          ((A₁.1 - A₀.1) *
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2)⁻¹) := by
  rw [lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul E P A₀ A₁ hNV]
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  have hLineBar : fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hLine
  -- (fqToBar Δx · fqToBar L.eval P)⁻¹ = fqToBar((Δx · L.eval P)⁻¹).
  have hPow : (fqToBar E (A₁.1 - A₀.1) *
      fqToBar E ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2))⁻¹
        = fqToBar E (((A₁.1 - A₀.1) *
              (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2)⁻¹) := by
    have hProdFq : (A₁.1 - A₀.1) *
        (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0 :=
      mul_ne_zero hX hLine
    unfold fqToBar
    rw [← map_mul, map_inv₀]
  rw [hPow]
  -- (n : Fqbar) = fqToBar (n : ZMod q).
  have hNat : ((n : ℕ) : Fqbar E) = fqToBar E ((n : ZMod E.q)) := by
    unfold fqToBar
    rw [map_natCast]
  rw [hNat]
  unfold fqToBar
  rw [← map_mul]

/-- **Re-indexed rational residue identity at defined non-vertical chords.**
Under `hAllZero` + `gd_support_rational`, the bar-level residue sum re-indexes
to a sum over `zerosFinset E D` with `rationalMultAt` weights, plus the
existing rational sum, and vanishes at every defined non-vertical rational
pair. -/
private theorem geom_residue_sum_zero_re_indexed_of_hAllZero
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (hRat : gd_support_rational E D gd)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    (∑ P' ∈ zerosFinset E D, ((rationalMultAt E D gd P' : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E P'))⁻¹)
    + (∑ j : Fin (k + 1),
        fqToBar E ((Fin.cons (-1) (fun j => -m j) : Fin (k + 1) → ZMod E.q) j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E
            ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j)))⁻¹) = 0 := by
  rw [← geom_residue_sum_re_index_under_rational E D hDnz gd hRat A₀ A₁]
  exact geom_residue_sum_zero_of_hAllZero E D gd P B m hAllZero A₀ A₁ hA₀ hA₁ hNV hDef

/-- **Descended rational residue identity.** Under `hAllZero` +
`gd_support_rational`, the descended pure `ZMod E.q` residue identity
vanishes at every defined non-vertical rational pair. -/
private theorem rational_residue_identity_zero_of_hAllZero
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (hRat : gd_support_rational E D gd)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁) :
    (∑ P' ∈ zerosFinset E D, (rationalMultAt E D gd P' : ZMod E.q) *
          ((A₁.1 - A₀.1) *
            (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P'.1 P'.2)⁻¹)
    + (∑ j : Fin (k + 1),
        ((Fin.cons (-1) (fun j => -m j) : Fin (k + 1) → ZMod E.q) j) *
        ((A₁.1 - A₀.1) *
          (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
            ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j).1
            ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j).2)⁻¹)
      = 0 := by
  classical
  set R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B with hR_def
  set m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j) with hM'_def
  -- Step 1: bar-level identity.
  have hBar := geom_residue_sum_zero_re_indexed_of_hAllZero E D hDnz gd hRat
    P B m hAllZero A₀ A₁ hA₀ hA₁ hNV hDef
  -- Step 2: chord avoids rational D-zeros and R-positions.
  have hDenom : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0 := hDef
  have h_chord_avoid : ∀ P' ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P'.1 P'.2 ≠ 0 :=
    chord_avoids_D_zeros_of_denom_defined D P B A₀ A₁ hA₀ hA₁ hNV hDenom
  -- For R-positions: from hDef.
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have h_negP_line : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hDef)
  have h_B_lineProd : (Finset.univ : Finset (Fin k)).prod
        (fun j => (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hDef
  have h_B_line : ∀ j : Fin k,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (B j).1 (B j).2 ≠ 0 := by
    intro j hj
    exact h_B_lineProd (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have h_R_line : ∀ j : Fin (k + 1),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2 ≠ 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R 0).1 (R 0).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_zero]; exact h_negP_line
    · intro i
      show (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R i.succ).1 (R i.succ).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_succ]; exact h_B_line i
  -- Step 3: descend each summand using descent lemmas.
  have h_first_descend :
      (∑ P' ∈ zerosFinset E D, ((rationalMultAt E D gd P' : ℕ) : Fqbar E) *
          (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
            (lineEvalNumAtFullBarOfFq E P'))⁻¹)
        = fqToBar E (∑ P' ∈ zerosFinset E D,
            (rationalMultAt E D gd P' : ZMod E.q) *
              ((A₁.1 - A₀.1) *
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P'.1 P'.2)⁻¹) := by
    rw [Finset.sum_congr rfl
      (fun P' hP' => bar_residue_summand_descends E P' A₀ A₁ hNV
        (rationalMultAt E D gd P') (h_chord_avoid P' hP'))]
    unfold fqToBar
    rw [map_sum]
  have h_second_descend :
      (∑ j : Fin (k + 1),
          fqToBar E (m' j) *
          (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
            (lineEvalNumAtFullBarOfFq E (R j)))⁻¹)
        = fqToBar E (∑ j : Fin (k + 1),
            m' j *
              ((A₁.1 - A₀.1) *
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹) := by
    rw [Finset.sum_congr rfl
      (fun j _ => bar_residue_summand_descends_fq E (R j) A₀ A₁ hNV
        (m' j) (h_R_line j))]
    unfold fqToBar
    rw [map_sum]
  rw [h_first_descend, h_second_descend] at hBar
  -- Combine the two fqToBar terms via map_add.
  rw [show (fqToBar E (∑ P' ∈ zerosFinset E D,
              (rationalMultAt E D gd P' : ZMod E.q) *
                ((A₁.1 - A₀.1) * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P'.1 P'.2)⁻¹))
            + fqToBar E (∑ j, m' j * ((A₁.1 - A₀.1) *
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹)
          = fqToBar E ((∑ P' ∈ zerosFinset E D,
              (rationalMultAt E D gd P' : ZMod E.q) *
                ((A₁.1 - A₀.1) * (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P'.1 P'.2)⁻¹)
            + (∑ j, m' j * ((A₁.1 - A₀.1) *
                (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (R j).1 (R j).2)⁻¹)) from by
    unfold fqToBar; rw [map_add]] at hBar
  exact (fqToBar_eq_zero_iff E _).mp hBar

/-- The sum of geometric multiplicities equals the natDegree of `normPoly`. -/
private theorem gd_mult_sum_eq_natDegree
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    (∑ Q ∈ gd.support, gd.mult Q) = (normPoly E D).natDegree := by
  classical
  have hNormBar_ne : normPolyBar E D ≠ 0 := normPolyBar_ne_zero E D hDnz
  have hSplits : (normPolyBar E D).Splits := IsAlgClosed.splits _
  have hCardBar : (normPolyBar E D).natDegree = (normPolyBar E D).roots.card :=
    hSplits.natDegree_eq_card_roots
  have hNatBar : (normPolyBar E D).natDegree = (normPoly E D).natDegree := by
    unfold normPolyBar; exact Polynomial.natDegree_map _
  -- Re-index: ∑_Q mult Q = ∑_α (∑_{Q : Q.x = α} mult Q) = ∑_α rootMultiplicityBar α.
  -- The sum over α ranges over (normPolyBar.roots).toFinset.
  have hSumOverRoots :
      (∑ Q ∈ gd.support, gd.mult Q)
        = ∑ α ∈ (normPolyBar E D).roots.toFinset,
            ∑ Q ∈ gd.support.filter (fun Q => Q.x = α), gd.mult Q := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext Q
      simp only [Finset.mem_biUnion, Finset.mem_filter, Multiset.mem_toFinset]
      constructor
      · intro hQ
        refine ⟨Q.x, ?_, hQ, rfl⟩
        rw [Polynomial.mem_roots hNormBar_ne]
        exact normPolyBar_eval_zero_of_geomEval_zero E D Q (gd.support_eval_zero Q hQ)
      · rintro ⟨_, _, hQ, _⟩; exact hQ
    · intro α _ β _ hαβ
      refine Finset.disjoint_left.mpr (fun Q hQ₁ hQ₂ => ?_)
      simp only [Finset.mem_filter] at hQ₁ hQ₂
      exact hαβ (hQ₁.2 ▸ hQ₂.2)
  rw [hSumOverRoots]
  -- Apply fiber_accounting per α.
  rw [Finset.sum_congr rfl (fun α _ => gd.fiber_accounting α)]
  -- Now LHS = ∑_α rootMultiplicityBar α = card normPolyBar.roots.
  rw [show (∑ α ∈ (normPolyBar E D).roots.toFinset, (normPolyBar E D).rootMultiplicity α)
      = (normPolyBar E D).roots.card from by
    rw [← Multiset.toFinset_sum_count_eq]
    apply Finset.sum_congr rfl
    intro α _
    rw [Polynomial.count_roots]]
  rw [← hCardBar, hNatBar]

/-! ### Residue-matching extraction of `splitsOnE` and σ-data

Two private helpers compose into `geometric_residue_match`:
1. `gd_support_rational_of_hAllZero`: under `hAllZero`, every `Q ∈
   gd.support` has `F_q`-rational coordinates. Deep residue
   specialisation argument: at each defined non-vertical rational
   pair the residue identity (from `geomPolyGFullBar_eval_zero_of_hAllZero`
   + `geomPolyGFullBar_eval_eq_residue_clear`) constrains `gd.support`
   pointwise; Frobenius-orbit analysis rules out non-rational support
   points.
2. `sigma_data_of_gd_support_rational`: under `gd_support_rational`,
   produce the σ embedding matching `zerosAt` against `distinctR` and
   the multiplicity-cancellation / off-range vanishing identities.

`geometric_residue_match` is the composition: gd_support_rational ⇒
splitsOnE (via `splitsOnE_of_gd_support_rational`) + σ-matching.
-/

/-- **Deep residue-specialisation helper.** Produces the σ-matching data
under the hypothesis `gd_support_rational`. The proof requires
specialised residue extraction: for each rational zero `P` of `D`,
evaluating the residue identity at carefully chosen rational `(A₀, A₁)`
isolates the `P`-summand and matches it to a unique `distinctR` index;
unmatched `distinctR` indices have `distinctM' = 0` by the reverse
specialisation. -/
private theorem sigma_data_of_gd_support_rational
    (stmt : DlogStatement E.q) (_hd : stmt.degBound < E.q)
    (msg : MAProverMsg E.q) (_hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (_hTargetOnE : stmt.target ∈ E.points)
    (_hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (_hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (_hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (gd : GeometricDivisorData E msg.toD)
    (_hRat : gd_support_rational E msg.toD gd)
    (_hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ∃ (σ : Fin (zerosCard E msg.toD) ↪
            Fin (1 + baseImageCount E stmt msg hkm)),
      (∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k)) ∧
      (∀ k, ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q)
            + distinctM' E stmt msg hkm (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) := by
  classical
  let _ := gd
  -- Step 1: every rational zero of D coincides with some distinctR position.
  -- Deep residue-specialisation: poles of the rational chord-sum identity
  -- at rational zeros of D must cancel against poles at distinctR positions.
  have h_zeros_in_distinctR :
      ∀ k : Fin (zerosCard E msg.toD),
        ∃ j : Fin (1 + baseImageCount E stmt msg hkm),
          zerosAt E msg.toD k = distinctR E stmt msg hkm j := by
    sorry
  -- Step 2: define σ_fn via Classical.choose.
  let σ_fn : Fin (zerosCard E msg.toD) → Fin (1 + baseImageCount E stmt msg hkm) :=
    fun k => (h_zeros_in_distinctR k).choose
  have hσ_spec : ∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ_fn k) :=
    fun k => (h_zeros_in_distinctR k).choose_spec
  -- Step 3: σ_fn is injective. Follows from injectivity of zerosAt
  -- and distinctR (the latter needs hNoNegP).
  have hσ_inj : Function.Injective σ_fn := by
    intro k₁ k₂ heq
    have h1 := hσ_spec k₁
    have h2 := hσ_spec k₂
    have hzeros : zerosAt E msg.toD k₁ = zerosAt E msg.toD k₂ := by
      rw [h1, h2, heq]
    exact zerosAt_injective E msg.toD hzeros
  -- Step 4: multiplicity matching at each k. Comes from the residue
  -- coefficient at the matched index: under hRat + hAllZero, the residue
  -- at the chord through the rational zero P_k cancels exactly the
  -- distinctM'-coefficient at σ k.
  have h_mult_match :
      ∀ k, ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q)
            + distinctM' E stmt msg hkm (σ_fn k) = 0 := by
    sorry
  -- Step 5: off-range vanishing of distinctM'. Reverse specialisation:
  -- at distinctR positions not hit by any rational zero of D, the
  -- residue contribution must vanish, forcing distinctM' j = 0.
  have h_off_range :
      ∀ j, j ∉ Set.range σ_fn → distinctM' E stmt msg hkm j = 0 := by
    sorry
  refine ⟨⟨σ_fn, hσ_inj⟩, ?_, ?_, ?_⟩
  · intro k; exact hσ_spec k
  · intro k; exact h_mult_match k
  · intro j hj
    apply h_off_range
    intro ⟨k, hk⟩
    exact hj ⟨k, hk⟩

/-- **Rationality of the geometric support under `hAllZero`.** The all-zero
hypothesis on `logDerivCheckFn` over rational defined non-vertical pairs
(combined with the `chord_fiber_product_bar_factorisation` axiom) forces
every `Q ∈ gd.support` to have `F_q`-rational coordinates. The argument
is a Frobenius-orbit / Bezout combination over `Fqbar` outlined in
`plan_geometric_residue_match.md`. -/
private theorem gd_support_rational_of_hAllZero
    (stmt : DlogStatement E.q) (_hd : stmt.degBound < E.q)
    (msg : MAProverMsg E.q) (_hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (_hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (_hTargetOnE : stmt.target ∈ E.points)
    (_hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (_hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (_hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (gd : GeometricDivisorData E msg.toD)
    (_hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    gd_support_rational E msg.toD gd := by
  classical
  let _ := hDnz
  -- Reduction via Frobenius-fixedness: gd_support_rational ↔ every Q
  -- in gd.support is fixed by frobGeomPoint (componentwise q-power Frobenius).
  rw [gd_support_rational_iff_frob_fixed]
  intro Q hQ
  -- Suppose for contradiction Q is not Frobenius-fixed: then its
  -- Frobenius orbit has size ≥ 2 inside gd.support, with constant
  -- multiplicity (by `mult_frobGeomPoint_eq`). The pooled orbital
  -- residue contribution to the bar-level chord-sum identity must
  -- vanish (Galois descent — non-rational orbit summands have no
  -- rational counterpart on the RHS). Combined with `gd_mult_natCast_ne_zero`
  -- and the orbit size bound (each |orbit| < q), the pooled multiplicity
  -- mod q is non-zero, contradicting forced vanishing.
  --
  -- Mechanizing this requires the residue specialisation argument from
  -- Stichtenoth GTM 254 §3 (function-field Galois descent at algebraic
  -- closure) — see `plan_remaining_residue_match.md`.
  sorry

private theorem geometric_residue_match
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
    (_hDenomNZ : ∀ A₀ ∈ E.points, A₀ ∉ zerosFinset E msg.toD →
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
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    splitsOnE E msg.toD ∧
    ∃ (σ : Fin (zerosCard E msg.toD) ↪
            Fin (1 + baseImageCount E stmt msg hkm)),
      (∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k)) ∧
      (∀ k, ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q)
            + distinctM' E stmt msg hkm (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) := by
  classical
  let _ := hd2
  have hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  obtain ⟨gd, _⟩ := exists_geometricDivisorData E msg.toD hDnz
  -- Step 1: gd.support is rational under hAllZero (deep residue-specialisation).
  have hRat : gd_support_rational E msg.toD gd :=
    gd_support_rational_of_hAllZero E stmt hd msg hDeg hkm hSmooth hTargetOnE
      hBasesOnE hLargeQ hNoNegP hDnz gd hAllZero
  -- Step 2: splitsOnE follows from rational support.
  have hSplit : splitsOnE E msg.toD :=
    splitsOnE_of_gd_support_rational E msg.toD hDnz gd hRat
  -- Step 3: σ-matching from rational support + chord-sum identity.
  have hσ := sigma_data_of_gd_support_rational E stmt hd msg hDeg hkm hTargetOnE
    hBasesOnE hLargeQ hNoNegP hDnz gd hRat hAllZero
  exact ⟨hSplit, hσ⟩

/--
Geometric σ-matching theorem (used by
`extractor_of_logDerivCheck_all_zero_geometric_general`).

The proof is a thin wrapper around the residue-matching helper
`geometric_residue_match`; see that helper for the mathematical
content and `PROVIDED SOLUTION` outline.
-/
private theorem geometric_sigma_matching
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
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    splitsOnE E msg.toD ∧
    ∃ (σ : Fin (zerosCard E msg.toD) ↪
            Fin (1 + baseImageCount E stmt msg hkm)),
      (∀ k, zerosAt E msg.toD k = distinctR E stmt msg hkm (σ k)) ∧
      (∀ k, ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q)
            + distinctM' E stmt msg hkm (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → distinctM' E stmt msg hkm j = 0) :=
  geometric_residue_match E stmt hd hd2 msg hDeg hkm hSmooth hDenomNZ
    hTargetOnE hBasesOnE hLargeQ hAdm hNoNegP hAllZero

set_option maxHeartbeats 800000 in
theorem extractor_of_logDerivCheck_all_zero_geometric_general
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
    (hNoNegP : ¬ (negPIndexSet E stmt msg hkm).Nonempty)
    (hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ∃ wit : DlogWitness E.q,
      maExtractor E stmt msg stmt.degBound hd hkm = some wit
      ∧ relDlog E stmt wit := by
  classical
  have hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) :=
    admSet_implies_toD_nonzero stmt msg hAdm
  obtain ⟨hSplit, σ, hσ_eq, hσ_betam, hσ_off⟩ :=
    geometric_sigma_matching E stmt hd hd2 msg hDeg hkm hSmooth hDenomNZ
      hTargetOnE hBasesOnE hLargeQ hAdm hNoNegP hAllZero
  have hβsup := betaCanonical_support E msg.toD
  have hβcov := betaCanonical_covers E msg.toD hDnz
  have hβsum := betaCanonical_sum_le_degE E msg.toD
  have hβgroup := betaCanonical_group_sum_zero E msg.toD hSplit
  obtain ⟨hBound, hCanon, hNonCanon⟩ :=
    extractorCoeffFromSigma_satisfies_D3 E stmt msg stmt.degBound hDeg hkm hNoNegP
      (betaCanonical E msg.toD) hβsup hβcov hβsum σ hσ_eq hσ_betam hσ_off
  obtain ⟨hSucc, _⟩ :=
    extractorSucceeds_of_natural_witness E stmt msg stmt.degBound hd hkm hNoNegP
      (extractorCoeffFromSigma E stmt msg hkm (betaCanonical E msg.toD) σ)
      hBound hCanon hNonCanon
  have hEq : extractorDivisorCoeffs E stmt msg hkm =
      dCoeffs E msg.toD (betaCanonical E msg.toD) :=
    funext fun P =>
      extractorDivisorCoeffs_eq_dCoeffs E stmt msg stmt.degBound hDeg hd hkm
        hNoNegP (betaCanonical E msg.toD) hβsup hβcov hβsum σ hσ_eq hσ_betam
        hσ_off P
  have hβsup_P : ∀ P, betaCanonical E msg.toD P ≠ 0 → P ∈ E.points :=
    fun P hP => (hβsup P hP).1
  have hFinSupp :=
    dCoeffs_finiteSupport E msg.toD (betaCanonical E msg.toD) hβsup_P
  have hGSup :=
    dCoeffs_groupSum_zero E msg.toD (betaCanonical E msg.toD) hβsup_P hβgroup hFinSupp
  have hSupSub : Function.support (dCoeffs E msg.toD (betaCanonical E msg.toD))
      ⊆ ↑(extractorDivisorCandidate E stmt msg hkm) := fun P hP =>
    extractorDivisorCoeffs_support_subset_candidate E stmt msg hkm
      (show extractorDivisorCoeffs E stmt msg hkm P ≠ 0 by rw [hEq]; exact hP)
  have hFinSupp_sub : hFinSupp.toFinset ⊆ extractorDivisorCandidate E stmt msg hkm :=
    fun P hP => hSupSub ((Set.Finite.mem_toFinset hFinSupp).mp hP)
  have hPad : ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
          (fun P => ECPoint.zsmul E (dCoeffs E msg.toD (betaCanonical E msg.toD) P) P)
        = ECPoint.weightedSum E hFinSupp.toFinset
            (fun P => ECPoint.zsmul E (dCoeffs E msg.toD (betaCanonical E msg.toD) P) P) :=
    ECPoint.weightedSum_subset_of_zero_outside E hFinSupp_sub
      (fun P _ hPnotSup => by
        rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
        rw [hPnotSup]
        exact ECPoint.zsmul_zero E P)
  have hWSum : ECPoint.weightedSum E (extractorDivisorCandidate E stmt msg hkm)
      (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) = 0 := by
    have : (fun P => ECPoint.zsmul E (extractorDivisorCoeffs E stmt msg hkm P) P) =
        fun P => ECPoint.zsmul E (dCoeffs E msg.toD (betaCanonical E msg.toD) P) P := by
      ext P
      rw [congr_fun hEq P]
    rw [this, hPad]
    exact hGSup
  have hTarget :=
    target_eq_weightedSum_of_weightedSum E stmt msg hkm hTargetOnE hBasesOnE
      hNoNegP hWSum
  exact ⟨⟨msg.k, extractedScalars E stmt msg hkm, stmt.degBound, hSucc⟩,
    by
      unfold maExtractor
      rw [dif_pos hSucc],
    ⟨hkm, hTarget⟩⟩

/--
Geometric all-zero branch, including the degenerate case where `-P` is
already one of the advertised bases.
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
  classical
  by_cases hNegP : (negPIndexSet E stmt msg hkm).Nonempty
  · have hSucc : extractorSucceeds E stmt msg stmt.degBound hkm :=
      extractorSucceeds_special E stmt msg stmt.degBound hkm hNegP hd2
    refine ⟨⟨msg.k, extractedScalars E stmt msg hkm, stmt.degBound, hSucc⟩,
      ?_, ⟨hkm, ?_⟩⟩
    · unfold maExtractor
      rw [dif_pos hSucc]
    · exact extracted_scalars_valid_special E stmt msg hkm hNegP
  · exact extractor_of_logDerivCheck_all_zero_geometric_general E stmt hd hd2
      msg hDeg hkm hSmooth hDenomNZ hTargetOnE hBasesOnE hLargeQ hAdm hNegP hAllZero

end Divisor
