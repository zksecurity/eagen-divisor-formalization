/-
  Divisor/GeometricSoundness.lean

  Geometric-zero replacement path for the log-derivative soundness proof.

  The older tight proof routed through `zerosAt : Fin d → E(F_q)` and a
  rational-point multiplicity function. That is the wrong abstraction for
  arbitrary cheating divisors: the zero divisor of `D` naturally lives over
  `F_qbar`, and only the final cleared polynomial should descend to `F_q`.

  This file introduces the clean geometric API and proves the branch
  theorems needed by the headline statement, instead of carrying
  `splitsOnE` as an external hypothesis.
-/
import Divisor.ExtractorBridge
import Divisor.HDenomNZBound
import Divisor.TightBound
import Divisor.GeomLocalOrder
import Divisor.CoeffDescent
import Divisor.PartialFractionExpansion
import Divisor.SlopeChoice
import Divisor.Axioms.AxiomChordFiberProductBarFactored

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
  refine congrArg₂ (· + ·) ?_ ?_
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
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) rfl
      · exact congrArg
          (fun n : ℕ => (MvPolynomial.C ((n : ℕ) : Fqbar E) : FourVarPolyBar E))
          (fs Q hQ).choose_spec.2.2.2.symm
      · exact frobMvPoly_prod_erase_support E D gd Q hQ
  · apply Finset.sum_congr rfl
    intro _j _
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) rfl
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

/--
Rational non-vanishing of the chord-fiber product.

`chord_fiber_product` is a concrete definition (the X-resultant of
the chord cubic against the D-on-line lift; see
`Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`). Its
non-vanishing for nonzero `D` is the function-field statement that
the norm `N_{F_q(E)/F_q(z)}(D)` of a nonzero rational function in the
upper field is a nonzero rational function in the base field. This is
the basic field-norm nonvanishing fact for finite extensions. The
divisor-accounting citations for the surrounding fiber-product bridge
are Stacks 02RS plus Stichtenoth Prop. 3.1.9 / Thm. 3.1.11.

This is the smallest sharp obligation isolating the rational
nonvanishing half of the bar fiber-accounting bundle.
-/
theorem chord_fiber_product_ne_zero
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    chord_fiber_product E lam D ≠ 0 := by
  classical
  -- Extract a geometric divisor data witness from `hD`.
  obtain ⟨gd, _⟩ := exists_geometricDivisorData E D hD
  -- Apply the (theorem-backed) factored-form bridge over `Fqbar E`.
  obtain ⟨c, hc, hEq⟩ :=
    chord_fiber_product_bar_eq_geom_prod E D lam hD gd
  -- The RHS of the bridge is nonzero (nonzero scalar times a product of
  -- nonzero linear-factor powers in a domain), hence the base-changed
  -- chord-fiber product is nonzero.
  have hRhsNe :
      C c * ∏ Q ∈ gd.support,
          (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (X_sub_C_ne_zero _))
  have hMapNe :
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D) ≠ 0 := by
    rw [hEq]; exact hRhsNe
  -- Pull non-vanishing back through the polynomial base-change.
  intro hZero
  exact hMapNe (by rw [hZero, Polynomial.map_zero])

/--
Per-`z` root-multiplicity equality for the base-changed chord-fiber
product over `F_qbar`.

For each `z : Fqbar E`, the local multiplicity of the base-changed
chord-fiber product at `z` equals the sum of geometric multiplicities
`gd.mult Q` over the geometric support points `Q` whose chord
projection `zLambdaBar E lam Q` equals `z`.

This is the per-place reading of the divisor-of-norm formula
`div(N(D)) = π_*(div D)` evaluated at the base place `(z)` of the
function-field extension `F_qbar(E) / F_qbar(zLambdaBar lam)`. Stated
pointwise in `z` so it can be discharged by a per-place push-forward
identity, independently of the global non-vanishing claim.
-/
theorem chord_fiber_product_bar_rootMultiplicity_eq_zfiber
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product E lam D)).rootMultiplicity z =
      ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          gd.mult Q := by
  classical
  -- Apply the narrow factored-form bridge axiom over `Fqbar E`...
  obtain ⟨c, hc, hEq⟩ :=
    chord_fiber_product_bar_eq_geom_prod E D lam hD gd
  rw [hEq]
  -- ...and read off the root multiplicity via the generic helper
  -- `rootMultiplicity_C_mul_prod_X_sub_C_pow` from
  -- `Divisor/PartialFractionExpansion.lean`.
  exact rootMultiplicity_C_mul_prod_X_sub_C_pow gd.support
    (zLambdaBar E lam) gd.mult hc z

/--
Z-fiber accounting for the base-changed chord-fiber product.

The base-changed `chord_fiber_product E lam D` is nonzero, and at each
`z : Fqbar E` its root multiplicity equals the sum of `gd.mult Q` over
the geometric support points `Q` whose chord-projection
`zLambdaBar E lam Q` equals `z`.

This is the precise norm push-forward / z-fiber accounting obligation
for the function-field extension `F_qbar(E) / F_qbar(zLambdaBar lam)`:
`div(N(D)) = π_*(div D)`, evaluated at each prime divisor `(z)` of the
base. The full geometric factorisation
`chord_fiber_product_bar_factorisation` is derived from this bundle
below by splitting the polynomial over the algebraically closed
`Fqbar E` and reorganising linear factors by the `zLambdaBar lam` map.

This bundle is now derived directly from the two sharper helpers
`chord_fiber_product_ne_zero` (rational non-vanishing) and
`chord_fiber_product_bar_rootMultiplicity_eq_zfiber` (per-`z`
push-forward), via injectivity of the algebraic-closure base change
on the polynomial ring.
-/
theorem chord_fiber_product_bar_z_fiber_accounting
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product E lam D) ≠ 0 ∧
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
            gd.mult Q := by
  refine ⟨?_, fun z =>
    chord_fiber_product_bar_rootMultiplicity_eq_zfiber E D lam hD gd z⟩
  exact Polynomial.map_ne_zero (chord_fiber_product_ne_zero E D lam hD)

/--
Geometric divisor-of-norm factorisation over `F_qbar`.

Now a thin wrapper over `chord_fiber_product_bar_eq_geom_prod`: the
narrow factored-form bridge axiom states this exact factorisation,
so the previous derivation through `chord_fiber_product_bar_z_fiber_accounting`
+ `splits_factorization_of_roots_card_eq` + `prod_fiberwise_of_maps_to`
is no longer needed.

The bundled theorem is retained as a stable downstream entry point.
-/
theorem chord_fiber_product_bar_factorisation
    (D : CoordRingElt E.q) (lam : ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product E lam D)
        = C c * ∏ Q ∈ gd.support,
            (X - C (zLambdaBar E lam Q)) ^ (gd.mult Q) :=
  chord_fiber_product_bar_eq_geom_prod E D lam hD gd

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
  -- Rational chord-sum identity, derived from the narrower trace axiom.
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
          intro α' _ hαβ
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

/-- Direct geometric evaluation formula for `lineEvalNumAtFullBar`. -/
theorem lineEvalNumAtFullBar_geom_eval
    (Q A₀ : GeomPoint E) (a₁x a₁y : Fqbar E) :
    MvPolynomial.eval (geomBarEvalFun E A₀ a₁x a₁y)
      (lineEvalNumAtFullBar E Q) =
        (Q.y - A₀.y) * (a₁x - A₀.x) -
          (Q.x - A₀.x) * (a₁y - A₀.y) := by
  unfold lineEvalNumAtFullBar geomBarEvalFun
  simp [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Direct geometric evaluation formula for a rational line factor. -/
theorem lineEvalNumAtFullBarOfFq_geom_eval
    (P : ZMod E.q × ZMod E.q) (A₀ : GeomPoint E) (a₁x a₁y : Fqbar E) :
    MvPolynomial.eval (geomBarEvalFun E A₀ a₁x a₁y)
      (lineEvalNumAtFullBarOfFq E P) =
        (fqToBar E P.2 - A₀.y) * (a₁x - A₀.x) -
          (fqToBar E P.1 - A₀.x) * (a₁y - A₀.y) := by
  unfold lineEvalNumAtFullBarOfFq geomBarEvalFun
  simp [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]

/--
Finite line-factor avoidance at an unmatched geometric support point.
For `A₀ = Q`, choose `A₁ = (Q.x + 1, Q.y + t)` with `t` outside the
finite set of bad slopes determined by all other support points and all
rational `R j`.
-/
theorem line_factor_avoidance_at_unmatched_support
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q)
    (Q : GeomPoint E)
    (hNoMatch :
      ∀ j : Fin M, ¬ (Q.x = fqToBar E (R j).1 ∧ Q.y = fqToBar E (R j).2)) :
    ∃ a₁x a₁y : Fqbar E,
      (∏ Q' ∈ gd.support.erase Q,
        MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
          (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0 := by
  classical
  let badSlopes : Finset (Fqbar E) :=
    (gd.support.erase Q).image
        (fun Q' : GeomPoint E => (Q'.y - Q.y) * (Q'.x - Q.x)⁻¹) ∪
      (Finset.univ : Finset (Fin M)).image
        (fun j : Fin M => (fqToBar E (R j).2 - Q.y) *
          (fqToBar E (R j).1 - Q.x)⁻¹)
  obtain ⟨t, ht⟩ := Finset.exists_notMem badSlopes
  refine ⟨Q.x + 1, Q.y + t, ?_⟩
  apply mul_ne_zero
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro Q' hQ'
    have hQ'ne : Q' ≠ Q := Finset.ne_of_mem_erase hQ'
    have ht_ne : t ≠ (Q'.y - Q.y) * (Q'.x - Q.x)⁻¹ := by
      intro ht_eq
      apply ht
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨Q', hQ', ht_eq.symm⟩))
    rw [lineEvalNumAtFullBar_geom_eval]
    have hEval :
        (Q'.y - Q.y) * (Q.x + 1 - Q.x) -
            (Q'.x - Q.x) * (Q.y + t - Q.y)
          = (Q'.y - Q.y) - (Q'.x - Q.x) * t := by ring
    rw [hEval]
    by_cases hx : Q'.x - Q.x = 0
    · have hy : Q'.y - Q.y ≠ 0 := by
        intro hy
        have hx' : Q'.x = Q.x := by linear_combination hx
        have hy' : Q'.y = Q.y := by linear_combination hy
        exact hQ'ne (geomPoint_ext E Q' Q hx' hy')
      rw [hx, zero_mul, sub_zero]
      exact hy
    · intro hzero
      have hdy : Q'.y - Q.y = (Q'.x - Q.x) * t := by linear_combination hzero
      have ht_eq : t = (Q'.y - Q.y) * (Q'.x - Q.x)⁻¹ := by
        calc t = (Q'.x - Q.x)⁻¹ * ((Q'.x - Q.x) * t) := by
              rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
          _ = (Q'.x - Q.x)⁻¹ * (Q'.y - Q.y) := by rw [← hdy]
          _ = (Q'.y - Q.y) * (Q'.x - Q.x)⁻¹ := by ring
      exact ht_ne ht_eq
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    have ht_ne :
        t ≠ (fqToBar E (R j).2 - Q.y) * (fqToBar E (R j).1 - Q.x)⁻¹ := by
      intro ht_eq
      apply ht
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ht_eq.symm⟩))
    rw [lineEvalNumAtFullBarOfFq_geom_eval]
    have hEval :
        (fqToBar E (R j).2 - Q.y) * (Q.x + 1 - Q.x) -
            (fqToBar E (R j).1 - Q.x) * (Q.y + t - Q.y)
          = (fqToBar E (R j).2 - Q.y) -
              (fqToBar E (R j).1 - Q.x) * t := by ring
    rw [hEval]
    by_cases hx : fqToBar E (R j).1 - Q.x = 0
    · have hy : fqToBar E (R j).2 - Q.y ≠ 0 := by
        intro hy
        apply hNoMatch j
        constructor
        · linear_combination -hx
        · linear_combination -hy
      rw [hx, zero_mul, sub_zero]
      exact hy
    · intro hzero
      have hdy :
          fqToBar E (R j).2 - Q.y = (fqToBar E (R j).1 - Q.x) * t := by
        linear_combination hzero
      have ht_eq :
          t = (fqToBar E (R j).2 - Q.y) *
              (fqToBar E (R j).1 - Q.x)⁻¹ := by
        calc t = (fqToBar E (R j).1 - Q.x)⁻¹ *
                  ((fqToBar E (R j).1 - Q.x) * t) := by
              rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
          _ = (fqToBar E (R j).1 - Q.x)⁻¹ *
                (fqToBar E (R j).2 - Q.y) := by rw [← hdy]
          _ = (fqToBar E (R j).2 - Q.y) *
                (fqToBar E (R j).1 - Q.x)⁻¹ := by ring
      exact ht_ne ht_eq

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

/--
Pointwise residue isolation at a geometric support point. If the cleared
bar numerator vanishes at the specialization `A₀ = Q₀` and the remaining
line factors are nonzero there, then the geometric residue coefficient at
`Q₀` is zero.
-/
theorem geom_residue_coeff_zero_of_eval_vanishing
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (Q₀ : GeomPoint E) (hQ₀ : Q₀ ∈ gd.support)
    (a₁x a₁y : Fqbar E)
    (hEvalZero :
      MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
        (geomPolyGFullBar E D gd R m) = 0)
    (hProd :
      (∏ Q' ∈ gd.support.erase Q₀,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0) :
    ((gd.mult Q₀ : ℕ) : Fqbar E) = 0 := by
  have hEval := geomPolyGFullBar_eval_at_support_point E D gd R m Q₀ hQ₀ a₁x a₁y
  rw [hEval, mul_assoc] at hEvalZero
  exact (mul_eq_zero.mp hEvalZero).resolve_right hProd

/--
An unmatched support point is impossible once a residue-isolating
specialization is known. This packages the coefficient isolation with the
`degE < q` nonzero-multiplicity fact.
-/
theorem geomPolyGFullBar_rules_out_unmatched_support
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDeg : D.degE < E.q)
    (Q₀ : GeomPoint E) (hQ₀ : Q₀ ∈ gd.support)
    (a₁x a₁y : Fqbar E)
    (hEvalZero :
      MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
        (geomPolyGFullBar E D gd R m) = 0)
    (hProd :
      (∏ Q' ∈ gd.support.erase Q₀,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBar E Q')) *
      (∏ j : Fin M,
        MvPolynomial.eval (geomBarEvalFun E Q₀ a₁x a₁y)
          (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0) :
    False := by
  exact gd_mult_fqbar_ne_zero E D gd hDeg Q₀ hQ₀
    (geom_residue_coeff_zero_of_eval_vanishing E D gd R m Q₀ hQ₀ a₁x a₁y
      hEvalZero hProd)

/--
Residue-specialization rationality criterion. If every unmatched support
point admits a specialization that avoids all remaining geometric and
rational line factors, and the cleared numerator vanishes at those
specializations, then every geometric support point is one of the rational
`R j`.
-/
theorem support_rational_of_residue_specializations_vanish
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hRpts : ∀ j : Fin M, R j ∈ E.points)
    (hVanishAt :
      ∀ Q ∈ gd.support, ∀ a₁x a₁y : Fqbar E,
        MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
          (geomPolyGFullBar E D gd R m) = 0)
    (hAvoidUnmatched :
      ∀ Q ∈ gd.support,
        (∀ j : Fin M, ¬ (Q.x = fqToBar E (R j).1 ∧ Q.y = fqToBar E (R j).2)) →
        ∃ a₁x a₁y : Fqbar E,
          (∏ Q' ∈ gd.support.erase Q,
            MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
              (lineEvalNumAtFullBar E Q')) *
          (∏ j : Fin M,
            MvPolynomial.eval (geomBarEvalFun E Q a₁x a₁y)
              (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0) :
    gd_support_rational E D gd := by
  classical
  intro Q hQ
  by_cases hMatch :
      ∃ j : Fin M, Q.x = fqToBar E (R j).1 ∧ Q.y = fqToBar E (R j).2
  · obtain ⟨j, hx, hy⟩ := hMatch
    exact ⟨R j, hRpts j, hx, hy⟩
  · have hNoMatch :
        ∀ j : Fin M, ¬ (Q.x = fqToBar E (R j).1 ∧ Q.y = fqToBar E (R j).2) := by
      intro j hj
      exact hMatch ⟨j, hj⟩
    obtain ⟨a₁x, a₁y, hProd⟩ := hAvoidUnmatched Q hQ hNoMatch
    exact False.elim (geomPolyGFullBar_rules_out_unmatched_support E D gd R m
      hDeg Q hQ a₁x a₁y (hVanishAt Q hQ a₁x a₁y) hProd)

/--
Identity-level version of `support_rational_of_residue_specializations_vanish`.
It is the residue/partial-fraction uniqueness step under a clean
`geomPolyGFullBar = 0` hypothesis. The required line-factor avoidance is
supplied by `line_factor_avoidance_at_unmatched_support`.
-/
theorem support_rational_of_residues_vanish
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hRpts : ∀ j : Fin M, R j ∈ E.points)
    (hVanish : geomPolyGFullBar E D gd R m = 0) :
    gd_support_rational E D gd := by
  refine support_rational_of_residue_specializations_vanish E D gd R m
    hDeg hRpts ?_ ?_
  · intro Q _hQ a₁x a₁y
    rw [hVanish]
    exact map_zero _
  · intro Q _hQ hNoMatch
    exact line_factor_avoidance_at_unmatched_support E D gd R Q hNoMatch

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
theorem log_deriv_sz_paper_core_tight_geometric (hHW : E.HasseBound)
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
  have hDKL := bivariate_poly_zeros_on_ExE_le E hHW G
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
theorem log_deriv_sz_paper_tight_geometric (hHW : E.HasseBound)
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
  have hCoreBound := log_deriv_sz_paper_core_tight_geometric E hHW D P B m hDeg hNV
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

/-- **All-zero density helper.** If `logDerivCheckFn` vanishes on every
defined non-vertical rational pair (the `hAllZero` hypothesis) and
`E.points.card` is large enough to dominate the DKL/Lang–Weil bound on
the zero set of the descended polynomial together with the bounds on
vertical and undefined pairs, then the descended polynomial
`geomPolyGFull E D gd (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (-m))`
vanishes on **every** pair `(A₀, A₁) ∈ E.points × E.points`.

Proof sketch: by contradiction; a non-zero witness gives a DKL/Lang–Weil
bound `≤ 18·(gd.support.card + k)·E.q` on the zero set. But under
`hAllZero` the zero set contains every defined non-vertical pair, whose
complement (vertical or undefined) is bounded linearly in `|E|` by
`card_vertical_pairs_le` and `logDerivCheckFn_undefined_set_bound_tight`.
The threshold `hELarge` rules this out. -/
private theorem geomPolyGFull_identically_zero_on_ExE (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hELarge :
      18 * (gd.support.card + k) * E.q +
          2 * E.points.card +
          (3 * D.degE + 9 * k + 71) * E.points.card
        < E.points.card * E.points.card) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (geomPolyGFull E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
          A₀ A₁ = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨A₀, A₁, hA₀, hA₁, hNZ⟩ := h
  -- Total-degree bound for the descended polynomial.
  have hTD := geomPolyGFull_total_degree_le_tight E D gd
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
  have hdM1 : gd.support.card + (k + 1) - 1 = gd.support.card + k := by omega
  have hTD' : total_degree_le E
      (geomPolyGFull E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
      (2 * (gd.support.card + k)) := by
    rwa [hdM1] at hTD
  -- DKL bound on the zero set, witnessed by `(A₀, A₁)`.
  have hLW := bivariate_poly_zeros_on_ExE_le E hHW
    (geomPolyGFull E D gd
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
    (2 * (gd.support.card + k)) hTD' ⟨A₀, A₁, hA₀, hA₁, hNZ⟩
  -- Defined non-vertical pairs are contained in the zero set under hAllZero.
  have hSdefSubZero :
      (E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          p.1.1 ≠ p.2.1 ∧ logDerivCheckFnDefined E D P B p.1 p.2) ⊆
      (E.points ×ˢ E.points).filter
        (fun p =>
          bivEval₂ (geomPolyGFull E D gd
              (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
            p.1 p.2 = 0) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hNV, hDef⟩ := hp
    have hCheck := hAllZero p.1 p.2 h1 h2 hNV hDef
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨h1, h2⟩,
      geomPolyGFull_zero_at_defined_pair E D gd P B m
        p.1 p.2 h1 h2 hNV hDef hCheck⟩
  -- Card bound on the defined non-vertical set via the DKL bound.
  have hSdefCard :
      ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          p.1.1 ≠ p.2.1 ∧ logDerivCheckFnDefined E D P B p.1 p.2)).card
        ≤ 18 * (gd.support.card + k) * E.q := by
    calc _ ≤ _ := Finset.card_le_card hSdefSubZero
      _ ≤ 9 * (2 * (gd.support.card + k)) * E.q := hLW
      _ = 18 * (gd.support.card + k) * E.q := by ring
  -- Cover E×E by (defined non-vert) ∪ vertical ∪ undefined.
  have hCover : (E.points ×ˢ E.points) ⊆
      (E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          p.1.1 ≠ p.2.1 ∧ logDerivCheckFnDefined E D P B p.1 p.2) ∪
      (E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          p.1.1 = p.2.1) ∪
      (E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ logDerivCheckFnDefined E D P B p.1 p.2) := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hVert : p.1.1 = p.2.1
    · left; right; exact ⟨hp, hVert⟩
    · by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
      · left; left; exact ⟨hp, hVert, hDef⟩
      · right; exact ⟨hp, hDef⟩
  have hVertCard :
      ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          p.1.1 = p.2.1)).card ≤ 2 * E.points.card :=
    card_vertical_pairs_le E
  have hUndefCard :
      ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card
        ≤ (3 * D.degE + 9 * k + 71) * E.points.card :=
    logDerivCheckFn_undefined_set_bound_tight E D P k B hDnz
  have hCardProd : (E.points ×ˢ E.points).card = E.points.card * E.points.card :=
    Finset.card_product _ _
  -- Combine into a single linear inequality and contradict hELarge.
  have hFinal : E.points.card * E.points.card ≤
      18 * (gd.support.card + k) * E.q +
        2 * E.points.card +
        (3 * D.degE + 9 * k + 71) * E.points.card := by
    calc E.points.card * E.points.card
        = (E.points ×ˢ E.points).card := hCardProd.symm
      _ ≤ _ := Finset.card_le_card hCover
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 18 * (gd.support.card + k) * E.q +
            2 * E.points.card +
            (3 * D.degE + 9 * k + 71) * E.points.card :=
          Nat.add_le_add (Nat.add_le_add hSdefCard hVertCard) hUndefCard
  exact absurd hFinal (Nat.not_le.mpr hELarge)

/-- **Sharp Hasse-Weil bound** in `ℕ`: `q ≤ n + 2 + Nat.sqrt(4(n+1))`.

Moved up from its original location so that the sharper density bridge
`hELarge_of_hLargeQ_main` below can use it.  -/
private theorem hasse_q_le_sharp_nat_of (hHW : E.HasseBound) :
    E.q ≤ E.points.card + 2 + Nat.sqrt (4 * (E.points.card + 1)) := by
  classical
  have hHW : ((E.numPoints : ℤ) - E.q - 1) ^ 2 ≤ 4 * E.q := hHW
  rw [E.hNumPoints] at hHW
  -- hHW: (((card + 1) : ℤ) - q - 1)^2 ≤ 4q.
  have hMcard : ((E.points.card : ℤ) - E.q)^2 ≤ 4 * (E.q : ℤ) := by
    have heq : ((E.points.card + 1 : ℕ) : ℤ) - E.q - 1
        = ((E.points.card : ℤ) - E.q) := by push_cast; ring
    rw [heq] at hHW; exact hHW
  by_cases hQ : E.q ≤ E.points.card + 2
  · -- q ≤ n + 2, so q ≤ n + 2 + sqrt(...) trivially.
    have hSqrtNonNeg : 0 ≤ Nat.sqrt (4 * (E.points.card + 1)) := Nat.zero_le _
    omega
  · push_neg at hQ
    -- q > n + 2, so q - n - 2 > 0 in ℕ.
    -- Derive (q - n - 2)^2 ≤ 4(n + 1) in ℕ.
    have hSqInt : ((E.q : ℤ) - E.points.card - 2)^2 ≤ 4 * ((E.points.card : ℤ) + 1) := by
      -- Identity: (q-n-2)² = (n-q)² + 4(n+1) - 4q.
      have h1 : ((E.q : ℤ) - E.points.card - 2)^2
          = ((E.points.card : ℤ) - E.q)^2 + 4 * ((E.points.card : ℤ) + 1) - 4 * E.q := by
        ring
      rw [h1]
      linarith
    -- Convert to ℕ.
    have hQ_le : E.points.card + 2 ≤ E.q := le_of_lt hQ
    have hSubInt : ((E.q - E.points.card - 2 : ℕ) : ℤ) = (E.q : ℤ) - E.points.card - 2 := by
      have : E.q - E.points.card ≥ 2 := by omega
      omega
    have hSqNat : (E.q - E.points.card - 2)^2 ≤ 4 * (E.points.card + 1) := by
      have hCastLhs : (((E.q - E.points.card - 2 : ℕ) : ℤ))^2
          = ((E.q : ℤ) - E.points.card - 2)^2 := by rw [hSubInt]
      have hCastRhs : ((4 * (E.points.card + 1) : ℕ) : ℤ)
          = 4 * ((E.points.card : ℤ) + 1) := by push_cast; ring
      have hZ : ((E.q - E.points.card - 2 : ℕ) : ℤ)^2
          ≤ ((4 * (E.points.card + 1) : ℕ) : ℤ) := by
        rw [hCastLhs, hCastRhs]; exact hSqInt
      exact_mod_cast hZ
    -- Apply Nat.le_sqrt.
    have hLeSqrt : E.q - E.points.card - 2 ≤ Nat.sqrt (4 * (E.points.card + 1)) := by
      rw [Nat.le_sqrt]; rw [show (E.q - E.points.card - 2) * (E.q - E.points.card - 2)
          = (E.q - E.points.card - 2)^2 from by ring]
      exact hSqNat
    omega

/-- **Sharper bridge**: same conclusion as `hELarge_of_hLargeQ` but driven
by the *main* `hLargeQ` threshold used by `geometric_residue_match`,
i.e. `n > 31·d + 31·k + 140` (stated in the form
`2·(5·(d+k+2)+3) + 21·(d+k+2) + 72 < n`).

The improvement comes from replacing the loose bound `q ≤ 2·n` with
the sharp form `q ≤ n + 2 + ⌊√(4(n+1))⌋` (`hasse_q_le_sharp_nat_of`,
from the `hHW` hypothesis), then a
squared-comparison `(4n - 36)² > (18s)²` (valid for `n ≥ 100`, hence
`n ≥ 141` here) to absorb the surd term into a linear bound. The
remaining accounting follows the same DKL + vertical-pairs +
undefined-set decomposition. -/
private theorem hELarge_of_hLargeQ_main (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) (k : ℕ)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72) :
    18 * (gd.support.card + k) * E.q +
        2 * E.points.card +
        (3 * D.degE + 9 * k + 71) * E.points.card
      < E.points.card * E.points.card := by
  classical
  set n := E.points.card with hn_def
  set d := D.degE with hd_def
  -- Reformulate hLargeQ in flat polynomial form.
  have hN_flat : n > 31 * d + 31 * k + 140 := by
    have h := hLargeQ
    have hEq : 2 * (5 * (d + k + 2) + 3) + 21 * (d + k + 2) + 72
             = 31 * d + 31 * k + 140 := by ring
    rw [hEq] at h; exact h
  have hSC : gd.support.card ≤ d := by
    calc gd.support.card
        = ∑ _ ∈ gd.support, 1 := by simp
      _ ≤ ∑ Q ∈ gd.support, gd.mult Q :=
          Finset.sum_le_sum (fun Q hQ => gd.mult_pos_on_support Q hQ)
      _ ≤ d := gd.accounting_le_degE
  have hN141 : n ≥ 141 := by omega
  have hN_pos : 0 < n := by omega
  -- Sharp Hasse bound: q ≤ n + 2 + s where s² ≤ 4(n+1).
  have hQbound : E.q ≤ n + 2 + Nat.sqrt (4 * (n + 1)) := hasse_q_le_sharp_nat_of E hHW
  set s := Nat.sqrt (4 * (n + 1)) with hs_def
  have hSqrtSq : s * s ≤ 4 * (n + 1) := Nat.sqrt_le _
  -- Key squared comparison: 4·n > 36 + 18·s.
  -- Proof: (4n - 36)² > (18s)² since (4n-36)² + 288n = 16n² + 1296,
  -- and 16n² > 1584n for n ≥ 100 ≤ 141, while (18s)² ≤ 1296(n+1).
  have h_4n_gt : 4 * n > 36 + 18 * s := by
    by_contra h_le
    push_neg at h_le
    have h_4n_ge : 36 ≤ 4 * n := by omega
    have h_18s_ge : 18 * s ≥ 4 * n - 36 := by omega
    have h_sq_ineq : (4 * n - 36) * (4 * n - 36) ≤ (18 * s) * (18 * s) :=
      Nat.mul_le_mul h_18s_ge h_18s_ge
    have h_18s_sq_upper : (18 * s) * (18 * s) ≤ 1296 * (n + 1) := by
      have h1 : (18 * s) * (18 * s) = 324 * (s * s) := by ring
      have h2 : 324 * (s * s) ≤ 324 * (4 * (n + 1)) :=
        Nat.mul_le_mul_left 324 hSqrtSq
      linarith
    -- (4n - 36)² + 288n = 16n² + 1296
    have h_expand : (4 * n - 36) * (4 * n - 36) + 288 * n
        = 16 * (n * n) + 1296 := by
      have h_eq : (4 * n - 36) + 36 = 4 * n := by omega
      have h_sq_eq : ((4 * n - 36) + 36) * ((4 * n - 36) + 36) = 16 * (n * n) := by
        rw [h_eq]; ring
      nlinarith [h_sq_eq]
    have h_4n_36_sq_le : (4 * n - 36) * (4 * n - 36) ≤ 1296 * (n + 1) :=
      le_trans h_sq_ineq h_18s_sq_upper
    -- So 16n² + 1296 ≤ 1296(n+1) + 288n = 1584n + 1296.
    have h_16n2_le : 16 * (n * n) ≤ 1584 * n := by linarith
    -- But for n ≥ 141, 16n² ≥ 2256n > 1584n.
    have h_16n2_ge : 16 * (n * n) ≥ 2256 * n := by
      have := Nat.mul_le_mul_right n hN141
      nlinarith
    omega
  -- T = gd.support.card + k ≤ d + k.
  have hT_le : 18 * (gd.support.card + k) ≤ 18 * (d + k) := by
    apply Nat.mul_le_mul_left; omega
  -- Bound LHS: 18·T·q + 2n + (3d+9k+71)·n
  --   ≤ 18·(d+k)·(n+2+s) + 2n + (3d+9k+71)·n
  --   = (21d+27k+73)·n + 36·(d+k) + 18·(d+k)·s.
  have hLHS_le :
      18 * (gd.support.card + k) * E.q + 2 * n
          + (3 * d + 9 * k + 71) * n
        ≤ (21 * d + 27 * k + 73) * n
            + 36 * (d + k) + 18 * (d + k) * s := by
    have h1 : 18 * (gd.support.card + k) * E.q
        ≤ 18 * (d + k) * (n + 2 + s) := by
      calc 18 * (gd.support.card + k) * E.q
          ≤ 18 * (d + k) * E.q := Nat.mul_le_mul_right _ hT_le
        _ ≤ 18 * (d + k) * (n + 2 + s) := Nat.mul_le_mul_left _ hQbound
    have h2 : 18 * (d + k) * (n + 2 + s) + 2 * n + (3 * d + 9 * k + 71) * n
            = (21 * d + 27 * k + 73) * n + 36 * (d + k) + 18 * (d + k) * s := by
      ring
    linarith
  -- Now show: (21d+27k+73)·n + 36·(d+k) + 18·(d+k)·s < n·n.
  -- Rewrite n·n - (21d+27k+73)·n = n·(n - 21d - 27k - 73).
  -- From hN_flat: n - 21d - 27k - 73 ≥ 10d + 4k + 68 (strict).
  have h_n_diff : n - (21 * d + 27 * k + 73) ≥ 10 * d + 4 * k + 68 := by omega
  have h_n_ge : n ≥ 21 * d + 27 * k + 73 := by omega
  -- n·(n - 21d - 27k - 73) ≥ n·(10d + 4k + 68) = 10dn + 4kn + 68n.
  have h_n_step : n * (n - (21 * d + 27 * k + 73)) ≥ n * (10 * d + 4 * k + 68) :=
    Nat.mul_le_mul_left n h_n_diff
  -- 10dn + 4kn + 68n > 36d + 36k + 18ds + 18ks.
  --   (10n - 18s - 36)·d + (4n - 18s - 36)·k + 68n > 0
  -- The first two coefficients are ≥ 0 (from h_4n_gt: 4n > 36 + 18s, hence 10n > 36 + 18s);
  -- the 68n term is > 0 (n ≥ 141), giving the strict inequality.
  have h_4n_18s_36 : 4 * n ≥ 18 * s + 36 := by omega
  have h_10n_18s_36 : 10 * n ≥ 18 * s + 36 := by
    have : 10 * n ≥ 4 * n := by omega
    omega
  have h_d_part : 10 * d * n ≥ 18 * d * s + 36 * d := by
    have hM : d * (10 * n) ≥ d * (18 * s + 36) := Nat.mul_le_mul_left d h_10n_18s_36
    nlinarith [hM]
  have h_k_part : 4 * k * n ≥ 18 * k * s + 36 * k := by
    have hM : k * (4 * n) ≥ k * (18 * s + 36) := Nat.mul_le_mul_left k h_4n_18s_36
    nlinarith [hM]
  have h_strict :
      n * (10 * d + 4 * k + 68) > 36 * (d + k) + 18 * (d + k) * s := by
    have h_expand_lhs : n * (10 * d + 4 * k + 68) = 10 * d * n + 4 * k * n + 68 * n := by
      ring
    have h_expand_rhs : 36 * (d + k) + 18 * (d + k) * s
                      = 36 * d + 36 * k + 18 * d * s + 18 * k * s := by ring
    rw [h_expand_lhs, h_expand_rhs]
    have h68 : 68 * n ≥ 1 := by omega
    omega
  -- Combine to conclude n*(n - (21d+27k+73)) > 36(d+k) + 18(d+k)·s.
  have h_combined :
      n * (n - (21 * d + 27 * k + 73)) > 36 * (d + k) + 18 * (d + k) * s :=
    lt_of_lt_of_le h_strict h_n_step
  -- Algebraic split: n·n = (21d+27k+73)·n + n·(n - 21d-27k-73).
  have h_n_split :
      n * n = (21 * d + 27 * k + 73) * n + n * (n - (21 * d + 27 * k + 73)) := by
    have h_eq : (21 * d + 27 * k + 73) + (n - (21 * d + 27 * k + 73)) = n := by omega
    calc n * n
        = n * ((21 * d + 27 * k + 73) + (n - (21 * d + 27 * k + 73))) := by rw [h_eq]
      _ = (21 * d + 27 * k + 73) * n + n * (n - (21 * d + 27 * k + 73)) := by ring
  -- Final assembly.
  have h_RHS_lt :
      (21 * d + 27 * k + 73) * n + 36 * (d + k) + 18 * (d + k) * s < n * n := by
    rw [h_n_split]; omega
  exact lt_of_le_of_lt hLHS_le h_RHS_lt

/-- **Convenience corollary**: combine `hELarge_of_hLargeQ` with the density
theorem to conclude vanishing on every pair `(A₀, A₁) ∈ E.points × E.points`
directly from the linear `hLargeQ` threshold. -/
private theorem geomPolyGFull_identically_zero_on_ExE_of_hLargeQ (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (geomPolyGFull E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
          A₀ A₁ = 0 :=
  geomPolyGFull_identically_zero_on_ExE E hHW D hDnz gd P B m hAllZero
    (hELarge_of_hLargeQ_main E hHW D gd k hLargeQ)

/-- Base-change the descended identity for `geomPolyGFull` back to the
geometric numerator identity required by the residue-uniqueness helper. -/
private theorem geomPolyGFullBar_eq_zero_of_geomPolyGFull_eq_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hGZero : geomPolyGFull E D gd R m = 0) :
    geomPolyGFullBar E D gd R m = 0 := by
  calc
    geomPolyGFullBar E D gd R m
        = baseChangeFourVar E (geomPolyGFull E D gd R m) :=
            (baseChange_geomPolyGFull E D gd R m).symm
    _ = baseChangeFourVar E 0 := congrArg (baseChangeFourVar E) hGZero
    _ = 0 := by simp [baseChangeFourVar]

/--
Experimental density-to-residue bridge.

The worker-2 density path supplies vanishing of the descended numerator on
all rational pairs in `E.points × E.points`. To feed the residue uniqueness
helper, the missing bridge is exactly the conversion from that finite-grid
vanishing statement to the descended polynomial identity. This theorem wires
the density output through that bridge and returns the required bar-level
identity.
-/
private theorem geomPolyGFullBar_eq_zero_of_hAllZero_density_with_identity_bridge (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hLargeDensity : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72)
    (hExEToPoly :
      (∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points →
        bivEval₂ (geomPolyGFull E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
          A₀ A₁ = 0) →
      geomPolyGFull E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) = 0) :
    geomPolyGFullBar E D gd
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) = 0 := by
  have hOnExE := geomPolyGFull_identically_zero_on_ExE_of_hLargeQ
    E hHW D hDnz gd P B m hAllZero hLargeDensity
  exact geomPolyGFullBar_eq_zero_of_geomPolyGFull_eq_zero E D gd
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
    (hExEToPoly hOnExE)

/--
Residue-rationality consequence of the all-zero density path, assuming only
the narrow finite-grid-to-polynomial-identity bridge exposed above.
-/
private theorem support_rational_of_hAllZero_density_with_identity_bridge (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (hDeg : D.degE < E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hB : ∀ j : Fin k, B j ∈ E.points)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hLargeDensity : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72)
    (hExEToPoly :
      (∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points →
        bivEval₂ (geomPolyGFull E D gd
          (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)))
          A₀ A₁ = 0) →
      geomPolyGFull E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) = 0) :
    gd_support_rational E D gd := by
  have hBarZero :
      geomPolyGFullBar E D gd
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j)) = 0 :=
    geomPolyGFullBar_eq_zero_of_hAllZero_density_with_identity_bridge
      E hHW D hDnz gd P B m hAllZero hLargeDensity hExEToPoly
  have hRpts :
      ∀ j : Fin (k + 1),
        ((Fin.cons (P.1, -P.2) B :
          Fin (k + 1) → ZMod E.q × ZMod E.q) j) ∈ E.points := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa using neg_y_mem_points E P.1 P.2 hP
    · intro j
      simpa using hB j
  exact support_rational_of_residues_vanish E D gd
    (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
    hDeg hRpts hBarZero

/--
Statement-level wrapper for the experimental density-to-residue integration.
The remaining open input is the finite-grid-to-polynomial-identity bridge for
the specific `geomPolyGFull` instance produced by the verifier message.
-/
private theorem gd_support_rational_of_hAllZero_via_density_bridge (hHW : E.HasseBound)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeDensity : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (gd : GeometricDivisorData E msg.toD)
    (hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (hExEToPoly :
      (∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points →
        bivEval₂ (geomPolyGFull E msg.toD gd
          (Fin.cons (stmt.target.1, -stmt.target.2) stmt.bases)
          (Fin.cons (-1) (fun j => -(msg.m (hkm ▸ j)))))
          A₀ A₁ = 0) →
      geomPolyGFull E msg.toD gd
        (Fin.cons (stmt.target.1, -stmt.target.2) stmt.bases)
        (Fin.cons (-1) (fun j => -(msg.m (hkm ▸ j)))) = 0) :
    gd_support_rational E msg.toD gd := by
  have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt hDeg hd
  exact support_rational_of_hAllZero_density_with_identity_bridge E hHW
    msg.toD hDegLt hDnz gd stmt.target hTargetOnE stmt.bases
    (fun i => msg.m (hkm ▸ i)) hBasesOnE hAllZero hLargeDensity hExEToPoly

/-- Under `gd_support_rational`, the rational image of `gd.support`
coincides with `zerosFinset E D`. Each `Q ∈ gd.support` rationalizes to
a unique rational zero of `D`, and conversely every rational zero lifts
to a unique support point. -/
private theorem gd_support_eq_zerosFinset_image
    (D : CoordRingElt E.q) (_hDnz : ¬ (D.a = 0 ∧ D.b = 0))
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
noncomputable def rationalMultAt
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

/-! ### Bridge: rational `ordAt` versus geometric `geomLocalOrder` -/

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
  -- Show natDegree r < natDegree (q^(k+1)) when r ≠ 0; if r = 0 use degree ⊥.
  have hr_deg : r.degree < (q ^ (k + 1)).degree := by
    have hq_ne_zero : q ≠ 0 := hq.ne_zero
    have hqk_natDeg : (q ^ k).natDegree = k * q.natDegree := hq.natDegree_pow k
    have hqk1_natDeg : (q ^ (k + 1)).natDegree = (k + 1) * q.natDegree := hq.natDegree_pow (k+1)
    have hqk1_deg : (q ^ (k + 1)).degree = ((k + 1) * q.natDegree : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hqp1.ne_zero, hqk1_natDeg]
    have hqk_deg : (q ^ k).degree = (k * q.natDegree : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hqp.ne_zero, hqk_natDeg]
    -- We bound: natDegree(q^k * mod1) ≤ k*natDeg q + (natDeg q - 1) < (k+1)*natDeg q.
    -- And natDegree(p %ₘ q^k) ≤ k*natDeg q - 1 < (k+1)*natDeg q.
    have h_mod_q_natDeg : ((p /ₘ q ^ k) %ₘ q).natDegree < q.natDegree :=
      Polynomial.natDegree_modByMonic_lt _ hq hq1
    have hk1_eq : (k + 1) * q.natDegree = k * q.natDegree + q.natDegree := by ring
    -- Bound 1: degree of q^k * mod1.
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
    -- Bound 2: degree of p %ₘ q^k.
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
  · -- D.a = 0 ⇒ D.b ≠ 0; (D.divLin β).a = 0; (D.divLin β).b ≠ 0.
    have hbz : D.b ≠ 0 := fun h => hDnz ⟨h_a, h⟩
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
    · -- Both nonzero. divLin keeps both nonzero.
      have h_da_div : (D.divLin β).a ≠ 0 := by
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
  -- LHS via divByMonic_pow_succ.
  -- RHS via divByMonic_pow_succ.
  -- They both equal p /ₘ (X - C β)^(n+1).
  -- LHS: do divByMonic by q first, then by q^n. We want (p /ₘ q) /ₘ q^n = p /ₘ q^(n+1).
  -- Use: (p /ₘ q^n) /ₘ q = p /ₘ q^(n+1) (divByMonic_pow_succ).
  -- And (p /ₘ q) /ₘ q^n = p /ₘ q^(n+1) requires the "other order" lemma.
  -- Strategy: induct on n.
  induction n with
  | zero => simp [Polynomial.divByMonic_one]
  | succ n IH =>
    -- LHS: (p /ₘ q) /ₘ q^(n+1) = ?.
    -- RHS: (p /ₘ q^(n+1)) /ₘ q = p /ₘ q^(n+2).
    -- By divByMonic_pow_succ: p /ₘ q^(n+1) /ₘ q = p /ₘ q^(n+2).
    -- IH: (p /ₘ q) /ₘ q^n = (p /ₘ q^n) /ₘ q.
    -- We want: (p /ₘ q) /ₘ q^(n+1) = p /ₘ q^(n+1) /ₘ q.
    -- (p /ₘ q) /ₘ q^(n+1) = ((p /ₘ q) /ₘ q^n) /ₘ q  [divByMonic_pow_succ]
    --                     = ((p /ₘ q^n) /ₘ q) /ₘ q  [IH]
    --                     = (p /ₘ q^n) /ₘ q^2       [divByMonic_pow_succ]
    --                     = p /ₘ q^(n+2)            [hmm, need iterated]
    -- OR more directly: use divByMonic_pow_succ on both sides reaching p /ₘ q^(n+2).
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
  -- Show (X - C β)^(2k) ∣ normPoly E D.
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
    · -- k = D.b.rootMultiplicity β.
      show (Polynomial.X - Polynomial.C β) ^ k ∣ D.b
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
  -- normPoly = D.a^2 - D.b^2 * curveX. (X - β)^(2k) divides both D.a^2 and D.b^2.
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
  -- 2 k_D ≤ m_D.
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

private theorem ordAt_nonTwoTorsion_aux_zero (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) :
    ordAt_nonTwoTorsion_aux E 0 D P = 0 := rfl

private theorem ordAt_nonTwoTorsion_aux_succ (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (n : ℕ) :
    ordAt_nonTwoTorsion_aux E (n + 1) D P =
      (if D.a = 0 ∧ D.b = 0 then 0
        else if D.eval P.1 P.2 ≠ 0 then 0
        else if D.eval P.1 (-P.2) ≠ 0 then
          Polynomial.rootMultiplicity P.1 (normPoly E D)
        else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P) := rfl

/-- Auxiliary: bridge for the fuel-form on non-2-torsion. By induction on
fuel. -/
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
      · -- Twin case: ordAt = 1 + ordAt(D.divLin); geomLocalOrder = 1 + geomLocalOrder(D.divLin).
        rw [if_neg (not_not.mpr hEvalNegP)]
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
      · -- Lone case: ordAt = m; geomLocalOrder = m too.
        push_neg at hEvalNegP
        rw [if_pos hEvalNegP]
        rw [geomLocalOrder_rationalLift_non_two_torsion E D P hP hY]
        have hk : commonRootMultRatGS E D P.1 = 0 :=
          commonRootMultRatGS_eq_zero_of_lone E D hY hEvalP hEvalNegP
        have hbr : branchRat E D P = 0 :=
          branchRat_eq_zero_of_lone E D hY hEvalP hEvalNegP
        simp only [hbr, if_true, hk, Nat.sub_zero]
    · -- D.eval P ≠ 0: both = 0.
      push_neg at hEvalP
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

/-- **The bridge theorem**: `ordAt` agrees with `geomLocalOrder` at a
rational lift, for any nonzero `D`, any rational point `P ∈ E.points`. -/
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

theorem ordAt_eq_rationalMultAt_of_gd_support_rational
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (_hRat : gd_support_rational E D gd) :
    ∀ P : ZMod E.q × ZMod E.q,
      ordAt E D P = rationalMultAt E D gd P := by
  intro P
  unfold rationalMultAt
  by_cases hP : P ∈ E.points ∧ D.eval P.1 P.2 = 0
  · rw [dif_pos hP]
    rw [gd.mult_eq_geomLocalOrder]
    exact ordAt_eq_geomLocalOrder_at_rationalLift E D hDnz P hP.1
  · rw [dif_neg hP]
    push_neg at hP
    by_cases hP' : P ∈ E.points
    · exact ordAt_pos_iff_zero E D hDnz P hP' |>.not.mpr (hP hP')
        |> Nat.eq_zero_of_not_pos
    · exact ordAt_eq_zero_offE E D hP'

theorem betaCanonical_eq_rationalMultAt_of_gd_support_rational
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (hRat : gd_support_rational E D gd) :
    ∀ P : ZMod E.q × ZMod E.q,
      betaCanonical E D P = rationalMultAt E D gd P := by
  intro P
  rw [betaCanonical_eq_betaTrue E D hDnz]
  exact ordAt_eq_rationalMultAt_of_gd_support_rational E D hDnz gd hRat P

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

/-- Base-change a rational evaluation zero of the descended geometric
numerator to a bar-level evaluation zero of `geomPolyGFullBar`. -/
private theorem geomPolyGFullBar_eval_zero_of_geomPolyGFull_eval_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hZero : bivEval₂ (geomPolyGFull E D gd R m) A₀ A₁ = 0) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
      (geomPolyGFullBar E D gd R m) = 0 := by
  have hLift := fqToBar_bivEval₂_eq_eval_baseChange E
    (geomPolyGFull E D gd R m) A₀ A₁
  rw [hZero, baseChange_geomPolyGFull E D gd R m] at hLift
  simpa [fqToBar] using hLift.symm

/-- Residue-divided identity from a direct bar-level evaluation zero and
explicit nonvanishing of every geometric and rational line factor. -/
private theorem geom_residue_sum_zero_of_eval_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hZero : MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
      (geomPolyGFullBar E D gd R m) = 0)
    (hLineQ : ∀ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) ≠ 0)
    (hLineR : ∀ j,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) ≠ 0) :
    (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹)
    + (∑ j : Fin M,
        fqToBar E (m j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E (R j)))⁻¹) = 0 := by
  classical
  have hProdQ_ne : (∏ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hLineQ
  have hProdR_ne : (∏ j : Fin M,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    exact hLineR j
  rw [geomPolyGFullBar_eval_eq_residue_clear E D gd R m A₀ A₁ hLineQ hLineR] at hZero
  rcases mul_eq_zero.mp hZero with hProds | hRes
  · rcases mul_eq_zero.mp hProds with hPQ | hPR
    · exact absurd hPQ hProdQ_ne
    · exact absurd hPR hProdR_ne
  · exact hRes

/-- Rational analogue of `lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff`:
on a non-vertical chord, the rational geometric line factor evaluates to
`-(A₁.1 − A₀.1) · (μ − zLambda lam P)`, embedded in `Fqbar`. -/
private theorem lineEvalNumAtFullBarOfFq_eval_eq_zLambda_diff
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E P)
      = -(fqToBar E (A₁.1 - A₀.1)) *
          (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
            - fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) P)) := by
  rw [lineEvalNumAtFullBarOfFq_eval_eq_lineThrough_mul E P A₀ A₁ hNV,
      L_eval_eq_zLambda_sub E A₀ A₁ P]
  have hSub : fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) P
        - zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
      = fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) P)
        - fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀) := by
    unfold fqToBar; rw [map_sub]
  rw [hSub]; ring

/--
**Partial-fraction form of the bar-level residue identity at a defined
non-vertical chord.** Under `hAllZero`, the residue-divided sum
re-expresses as a partial-fraction identity in
`μ := fqToBar (zLambda lam A₀)` over the geometric support and the
re-indexed rational `R = Fin.cons (P,-P) B`, with weights
`m' = Fin.cons (-1) (fun j => -m j)`:

  Σ_Q (mult Q) · (μ − zLambdaBar lam Q)⁻¹ +
  Σ_j fqToBar (m'_j) · (μ − fqToBar (zLambda lam R_j))⁻¹ = 0.

Direct corollary of `geom_residue_sum_zero_of_hAllZero` plus the
line-factor identities `lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff`
and `lineEvalNumAtFullBarOfFq_eval_eq_zLambda_diff`, together with
non-vanishing of `(A₁.1 − A₀.1)` in `Fqbar`.
-/
private theorem geom_residue_sum_zero_as_zLambda_pf
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
        (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          - zLambdaBar E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q)⁻¹)
    + (∑ j : Fin (k + 1),
        fqToBar E ((Fin.cons (-1) (fun j => -m j) : Fin (k + 1) → ZMod E.q) j) *
        (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          - fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2)
            ((Fin.cons (P.1, -P.2) B : Fin (k + 1) → ZMod E.q × ZMod E.q) j)))⁻¹)
      = 0 := by
  classical
  set R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B with hR_def
  set m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j) with hM'_def
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu_def
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  -- Starting bar-level residue identity.
  have hStart :=
    geom_residue_sum_zero_of_hAllZero E D gd P B m hAllZero A₀ A₁ hA₀ hA₁ hNV hDef
  -- Q-summand rewrite via the geometric line-factor identity.
  have hQ_rewrite : ∀ Q ∈ gd.support,
      ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹
      = -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹) := by
    intro Q _hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    simp only [neg_mul, inv_neg, mul_inv]
    ring
  -- R-summand rewrite via the rational line-factor identity.
  have hR_rewrite : ∀ j : Fin (k + 1),
      fqToBar E (m' j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E (R j)))⁻¹
      = -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m' j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹) := by
    intro j
    rw [lineEvalNumAtFullBarOfFq_eval_eq_zLambda_diff E (R j) A₀ A₁ hNV]
    simp only [neg_mul, inv_neg, mul_inv]
    ring
  -- Apply the rewrites to hStart.
  have hStart' :
      (∑ Q ∈ gd.support, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹))
      + (∑ j : Fin (k + 1), -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m' j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹)) = 0 := by
    rw [show (∑ Q ∈ gd.support, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹))
        = ∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBar E Q))⁻¹ from
        Finset.sum_congr rfl (fun Q hQ => (hQ_rewrite Q hQ).symm)]
    rw [show (∑ j : Fin (k + 1), -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m' j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹))
        = ∑ j : Fin (k + 1), fqToBar E (m' j) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBarOfFq E (R j)))⁻¹ from
        Finset.sum_congr rfl (fun j _ => (hR_rewrite j).symm)]
    exact hStart
  -- Pull out -(fqToBar Δx)⁻¹ and cancel.
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add] at hStart'
  have hInvNe : -(fqToBar E (A₁.1 - A₀.1))⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero hXBar)
  rcases mul_eq_zero.mp hStart' with h | h
  · exact absurd h hInvNe
  · exact h

/-- Partial-fraction form of the residue identity from direct polynomial
evaluation zero. This variant is used by the Frobenius-descent sampler:
definedness of `logDerivCheckFn` is not needed once density has already
given zero of the descended geometric numerator at every rational pair. -/
private theorem geom_residue_sum_zero_as_zLambda_pf_of_eval_zero
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hNV : A₀.1 ≠ A₁.1)
    (hZero : MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
      (geomPolyGFullBar E D gd R m) = 0)
    (hAvoidQ : ∀ Q ∈ gd.support,
      fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        - zLambdaBar E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q ≠ 0)
    (hAvoidR : ∀ j : Fin M,
      fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
        - fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (R j)) ≠ 0) :
    (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          - zLambdaBar E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) Q)⁻¹)
    + (∑ j : Fin M,
        fqToBar E (m j) *
        (fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) A₀)
          - fqToBar E (zLambda E (slopeOf A₀.1 A₀.2 A₁.1 A₁.2) (R j)))⁻¹)
      = 0 := by
  classical
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLam
  set μ := zLambda E lam A₀ with hMu_def
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hXBar : fqToBar E (A₁.1 - A₀.1) ≠ 0 :=
    (fqToBar_eq_zero_iff E _).not.mpr hX
  have hLineQ : ∀ Q ∈ gd.support,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q) ≠ 0 := by
    intro Q hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    exact mul_ne_zero (neg_ne_zero.mpr hXBar) (hAvoidQ Q hQ)
  have hLineR : ∀ j : Fin M,
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBarOfFq E (R j)) ≠ 0 := by
    intro j
    rw [lineEvalNumAtFullBarOfFq_eval_eq_zLambda_diff E (R j) A₀ A₁ hNV]
    exact mul_ne_zero (neg_ne_zero.mpr hXBar) (hAvoidR j)
  have hStart :=
    geom_residue_sum_zero_of_eval_zero E D gd R m A₀ A₁ hZero hLineQ hLineR
  have hQ_rewrite : ∀ Q ∈ gd.support,
      ((gd.mult Q : ℕ) : Fqbar E) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁) (lineEvalNumAtFullBar E Q))⁻¹
      = -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹) := by
    intro Q _hQ
    rw [lineEvalNumAtFullBar_eval_eq_zLambdaBar_diff E Q A₀ A₁ hNV]
    simp only [neg_mul, inv_neg, mul_inv]
    ring
  have hR_rewrite : ∀ j : Fin M,
      fqToBar E (m j) *
        (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
          (lineEvalNumAtFullBarOfFq E (R j)))⁻¹
      = -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹) := by
    intro j
    rw [lineEvalNumAtFullBarOfFq_eval_eq_zLambda_diff E (R j) A₀ A₁ hNV]
    simp only [neg_mul, inv_neg, mul_inv]
    ring
  have hStart' :
      (∑ Q ∈ gd.support, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹))
      + (∑ j : Fin M, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹)) = 0 := by
    rw [show (∑ Q ∈ gd.support, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (((gd.mult Q : ℕ) : Fqbar E) *
            (fqToBar E μ - zLambdaBar E lam Q)⁻¹))
        = ∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBar E Q))⁻¹ from
        Finset.sum_congr rfl (fun Q hQ => (hQ_rewrite Q hQ).symm)]
    rw [show (∑ j : Fin M, -(fqToBar E (A₁.1 - A₀.1))⁻¹ *
          (fqToBar E (m j) *
            (fqToBar E μ - fqToBar E (zLambda E lam (R j)))⁻¹))
        = ∑ j : Fin M, fqToBar E (m j) *
            (MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
              (lineEvalNumAtFullBarOfFq E (R j)))⁻¹ from
        Finset.sum_congr rfl (fun j _ => (hR_rewrite j).symm)]
    exact hStart
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add] at hStart'
  have hInvNe : -(fqToBar E (A₁.1 - A₀.1))⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero hXBar)
  rcases mul_eq_zero.mp hStart' with h | h
  · exact absurd h hInvNe
  · exact h

/-- Sampled partial-fraction identity at a good rational intercept, using
density to obtain polynomial vanishing and explicit pole avoidance to divide
the cleared numerator. -/
private theorem geom_pf_identity_at_good_intercept (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72)
    (lam μ : ZMod E.q)
    (hμ : μ ∈ goodIntercepts E lam)
    (hAvoidQ : ∀ Q ∈ gd.support,
      fqToBar E μ - zLambdaBar E lam Q ≠ 0)
    (hAvoidR : ∀ j : Fin (k + 1),
      fqToBar E μ - fqToBar E
        (zLambda E lam
          ((Fin.cons (P.1, -P.2) B :
            Fin (k + 1) → ZMod E.q × ZMod E.q) j)) ≠ 0) :
    (∑ Q ∈ gd.support, ((gd.mult Q : ℕ) : Fqbar E) *
        (fqToBar E μ - zLambdaBar E lam Q)⁻¹)
    + (∑ j : Fin (k + 1),
        fqToBar E
          ((Fin.cons (-1) (fun j => -m j) :
            Fin (k + 1) → ZMod E.q) j) *
        (fqToBar E μ - fqToBar E
          (zLambda E lam
            ((Fin.cons (P.1, -P.2) B :
              Fin (k + 1) → ZMod E.q × ZMod E.q) j)))⁻¹)
      = 0 := by
  classical
  simp only [goodIntercepts, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  obtain ⟨A₀, hA₀, A₁, hA₁, hne_A⟩ := Finset.one_lt_card.mp hμ
  simp only [pointsOnLine, Finset.mem_filter] at hA₀ hA₁
  have hNV : A₀.1 ≠ A₁.1 := by
    intro hx
    apply hne_A
    apply Prod.ext hx
    rw [hA₀.2, hA₁.2, hx]
  have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  have hslope : slopeOf A₀.1 A₀.2 A₁.1 A₁.2 = lam := by
    simp only [slopeOf]
    rw [hA₀.2, hA₁.2]
    have : lam * A₁.1 + μ - (lam * A₀.1 + μ) = lam * (A₁.1 - A₀.1) := by ring
    rw [this, mul_assoc, mul_inv_cancel₀ hxne, mul_one]
  have hμ_eq : zLambda E lam A₀ = μ := by
    simp only [zLambda]
    rw [hA₀.2]
    ring
  let R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B
  let m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j)
  have hRatZero :
      bivEval₂ (geomPolyGFull E D gd R m') A₀ A₁ = 0 :=
    geomPolyGFull_identically_zero_on_ExE_of_hLargeQ E hHW D hDnz gd P B m
      hAllZero hLargeQ A₀ A₁ hA₀.1 hA₁.1
  have hBarZero :
      MvPolynomial.eval (barBivEval₂Fun E A₀ A₁)
        (geomPolyGFullBar E D gd R m') = 0 :=
    geomPolyGFullBar_eval_zero_of_geomPolyGFull_eval_zero E D gd R m'
      A₀ A₁ hRatZero
  have hPF := geom_residue_sum_zero_as_zLambda_pf_of_eval_zero
    E D gd R m' A₀ A₁ hNV hBarZero
    (by
      intro Q hQ
      rw [hslope, hμ_eq]
      exact hAvoidQ Q hQ)
    (by
      intro j
      rw [hslope, hμ_eq]
      exact hAvoidR j)
  simpa [R, m', hslope, hμ_eq] using hPF

/-- A rational scalar-weighted summand of the bar-level residue identity
descends to `fqToBar` of a rational expression, when the line factor is
nonzero. -/
private theorem bar_residue_summand_descends_fq
    (P A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1)
    (c : ZMod E.q) (_hLine : (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 ≠ 0) :
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

/-- **polyG vanishes at every defined non-vertical rational pair** under
`hAllZero` + `gd_support_rational`, with `rationalMultAt`-derived
multiplicity coefficients on the zerosAt enumeration. -/
private theorem polyG_zero_of_hAllZero_and_hRat
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
    polyG E (zerosAt E D)
        (fun k' => (rationalMultAt E D gd (zerosAt E D k') : ZMod E.q))
        (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
        A₀ A₁ = 0 := by
  classical
  set L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2 with hL_def
  -- Step 1: use rational_residue_identity_zero_of_hAllZero.
  have hRatId := rational_residue_identity_zero_of_hAllZero E D hDnz gd hRat
    P B m hAllZero A₀ A₁ hA₀ hA₁ hNV hDef
  -- Step 2: extract chord-avoidance for all denominators (P-side and R-side).
  have hDenom : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0 := hDef
  have h_chord_avoid : ∀ P' ∈ zerosFinset E D, L.eval P'.1 P'.2 ≠ 0 :=
    chord_avoids_D_zeros_of_denom_defined D P B A₀ A₁ hA₀ hA₁ hNV hDenom
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  have h_negP_line : L.eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hDef)
  have h_B_lineProd : (Finset.univ : Finset (Fin k)).prod
        (fun j => L.eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hDef
  have h_B_line : ∀ j : Fin k, L.eval (B j).1 (B j).2 ≠ 0 := by
    intro j
    exact fun hj => h_B_lineProd (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  -- Step 3: reformulate hRatId using ellP form, after re-indexing the
  -- zerosFinset sum to a Fin-indexed sum.
  have hX : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hNV)
  -- ellP P A₀ A₁ = (A₁.1 - A₀.1) * L.eval P
  have hEllP : ∀ Q' : ZMod E.q × ZMod E.q,
      ellP E Q' A₀ A₁ = (A₁.1 - A₀.1) * L.eval Q'.1 Q'.2 := by
    intro Q'
    rw [ellP_eq_lineEval_mul E Q' A₀ A₁ hNV]
    ring
  -- Re-index Σ_P ∈ zerosFinset → Σ_k ∈ Fin (zerosCard).
  have hReIndex :
      (∑ P' ∈ zerosFinset E D, (rationalMultAt E D gd P' : ZMod E.q) *
            ((A₁.1 - A₀.1) * L.eval P'.1 P'.2)⁻¹)
        = ∑ k' : Fin (zerosCard E D),
            (rationalMultAt E D gd (zerosAt E D k') : ZMod E.q) *
              ((A₁.1 - A₀.1) * L.eval (zerosAt E D k').1 (zerosAt E D k').2)⁻¹ :=
    sum_zerosFinset_eq_sum_fin E D _
  rw [hReIndex] at hRatId
  -- Step 4: now multiply through by ∏_k ellP(zerosAt k) · ∏_j ellP(R_j).
  -- Use sum_div_iff_sum_mul_prod_erase on the combined sum form.
  -- Define the unified index: Sum (Q-side, R-side) and apply.
  set Q : Fin (zerosCard E D) → ZMod E.q × ZMod E.q := zerosAt E D with hQ_def
  set beta : Fin (zerosCard E D) → ZMod E.q :=
    fun k' => (rationalMultAt E D gd (Q k') : ZMod E.q) with hbeta_def
  set R : Fin (k + 1) → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B with hR_def
  set m' : Fin (k + 1) → ZMod E.q := Fin.cons (-1) (fun j => -m j) with hm'_def
  -- Establish that all ellP values are nonzero.
  have hQ_ellP : ∀ k', ellP E (Q k') A₀ A₁ ≠ 0 := by
    intro k'
    rw [hEllP]; apply mul_ne_zero hX
    have hQk_mem : zerosAt E D k' ∈ zerosFinset E D :=
      Finset.mem_filter.mpr ⟨zerosAt_mem_E E D k', zerosAt_eval_zero E D k'⟩
    exact h_chord_avoid (zerosAt E D k') hQk_mem
  have hR_ellP : ∀ j, ellP E (R j) A₀ A₁ ≠ 0 := by
    intro j; rw [hEllP]; apply mul_ne_zero hX
    refine Fin.cases ?_ ?_ j
    · show L.eval (R 0).1 (R 0).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_zero]; exact h_negP_line
    · intro i
      show L.eval (R i.succ).1 (R i.succ).2 ≠ 0
      rw [hR_def]; simp [Fin.cons_succ]; exact h_B_line i
  -- Restate hRatId using ellP form.
  have hRatId' :
      (∑ k' : Fin (zerosCard E D), beta k' * (ellP E (Q k') A₀ A₁)⁻¹) +
        (∑ j : Fin (k + 1), m' j * (ellP E (R j) A₀ A₁)⁻¹) = 0 := by
    convert hRatId using 2
    · apply Finset.sum_congr rfl; intro k' _
      congr 1; rw [hEllP]
    · apply Finset.sum_congr rfl; intro j _
      congr 1; rw [hEllP]
  -- Combine into a single sum over Fin (zerosCard E D) ⊕ Fin (k+1).
  -- Multiply the identity by ∏_k ellP(Q k) · ∏_j ellP(R j) to clear denominators.
  set bigProd : ZMod E.q := (∏ k', ellP E (Q k') A₀ A₁) * ∏ j, ellP E (R j) A₀ A₁
    with hBigProd_def
  have hBigProd_ne : bigProd ≠ 0 := by
    rw [hBigProd_def]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k' _ => hQ_ellP k'))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hR_ellP j))
  -- bigProd · 0 = 0
  have h_mul : bigProd *
      ((∑ k' : Fin (zerosCard E D), beta k' * (ellP E (Q k') A₀ A₁)⁻¹) +
        (∑ j : Fin (k + 1), m' j * (ellP E (R j) A₀ A₁)⁻¹)) = 0 := by
    rw [hRatId']; ring
  -- Per-summand: bigProd · (a/b) = a · (∏_{x≠b}) (when b ≠ 0).
  have hQ_summand : ∀ k',
      bigProd * (beta k' * (ellP E (Q k') A₀ A₁)⁻¹) =
        beta k' * (Finset.univ.erase k').prod
          (fun k'' => ellP E (Q k'') A₀ A₁) * ∏ j, ellP E (R j) A₀ A₁ := by
    intro k'
    have hk_mem : k' ∈ (Finset.univ : Finset (Fin (zerosCard E D))) :=
      Finset.mem_univ k'
    have hk_prod : (∏ k'' : Fin (zerosCard E D), ellP E (Q k'') A₀ A₁)
        = ellP E (Q k') A₀ A₁ * (Finset.univ.erase k').prod
            (fun k'' => ellP E (Q k'') A₀ A₁) :=
      (Finset.mul_prod_erase Finset.univ _ hk_mem).symm
    rw [hBigProd_def, hk_prod]
    have hInv : ellP E (Q k') A₀ A₁ * (ellP E (Q k') A₀ A₁)⁻¹ = 1 :=
      mul_inv_cancel₀ (hQ_ellP k')
    linear_combination
      ((Finset.univ.erase k').prod (fun k'' => ellP E (Q k'') A₀ A₁) *
        ∏ j, ellP E (R j) A₀ A₁) * (beta k') * hInv
  have hR_summand : ∀ j,
      bigProd * (m' j * (ellP E (R j) A₀ A₁)⁻¹) =
        m' j * (∏ k', ellP E (Q k') A₀ A₁) *
          (Finset.univ.erase j).prod (fun j'' => ellP E (R j'') A₀ A₁) := by
    intro j
    have hj_mem : j ∈ (Finset.univ : Finset (Fin (k + 1))) := Finset.mem_univ j
    have hj_prod : (∏ j'' : Fin (k + 1), ellP E (R j'') A₀ A₁)
        = ellP E (R j) A₀ A₁ * (Finset.univ.erase j).prod
            (fun j'' => ellP E (R j'') A₀ A₁) :=
      (Finset.mul_prod_erase Finset.univ _ hj_mem).symm
    rw [hBigProd_def, hj_prod]
    have hInv : ellP E (R j) A₀ A₁ * (ellP E (R j) A₀ A₁)⁻¹ = 1 :=
      mul_inv_cancel₀ (hR_ellP j)
    linear_combination
      ((∏ k', ellP E (Q k') A₀ A₁) *
        (Finset.univ.erase j).prod (fun j'' => ellP E (R j'') A₀ A₁)) *
        (m' j) * hInv
  -- Distribute and combine: bigProd · (Σ + Σ) = polyG.
  have h_distrib :
      bigProd *
        ((∑ k' : Fin (zerosCard E D), beta k' * (ellP E (Q k') A₀ A₁)⁻¹) +
          (∑ j : Fin (k + 1), m' j * (ellP E (R j) A₀ A₁)⁻¹)) =
      polyG E Q beta R m' A₀ A₁ := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k' _ => hQ_summand k')]
    rw [Finset.sum_congr rfl (fun j _ => hR_summand j)]
    rfl
  rw [h_distrib] at h_mul
  exact h_mul

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

/-- **polyG vanishes at every defined non-vertical rational pair under
hAllZero + hRat, with `multAt(betaCanonical)` coefficients** (using
existing `polyG_zero_at_defined`). -/
private theorem polyG_zero_at_defined_betaCanonical_of_hAllZero_and_hRat
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
    polyG E (zerosAt E D)
      (fun k' => ((multAt E (betaCanonical E D) D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B)
      (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0 := by
  classical
  have hGeom :=
    polyG_zero_of_hAllZero_and_hRat E D hDnz gd hRat P B m hAllZero
      A₀ A₁ hA₀ hA₁ hNV hDef
  have hβeq := betaCanonical_eq_rationalMultAt_of_gd_support_rational E D hDnz gd hRat
  simpa [multAt, hβeq] using hGeom

/-- **Layer A bridge**: raw `hAllZero` (on `stmt.bases`, `msg.m`) implies
the distinct-form `hAllZero` (on `baseAt`, `distinctM'_tail`). -/
private theorem hAllZero_baseAt_of_hAllZero_raw
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hAllZeroRaw : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target
        (baseAt E stmt msg hkm) A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target
        (baseImageCount E stmt msg hkm)
        (baseAt E stmt msg hkm)
        (distinctM'_tail E stmt msg hkm) A₀ A₁ = 0 := by
  intro A₀ A₁ hA₀ hA₁ hNV hDefDistinct
  -- Translate `defined`-distinct to `defined`-raw at `stmt.bases`.
  have hDefRaw : logDerivCheckFnDefined E msg.toD stmt.target
      stmt.bases A₀ A₁ := by
    unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDefDistinct ⊢
    intro hRawEqZero
    apply hDefDistinct
    set common := msg.toD.eval A₀.1 A₀.2 * msg.toD.eval A₁.1 A₁.2 *
      msg.toD.eval (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1)
        (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
          (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
            (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) *
      (3 * A₀.1 ^ 2 + E.curveA - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.2) *
      (3 * A₁.1 ^ 2 + E.curveA -
        2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) *
      (3 * (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) ^ 2 + E.curveA -
        2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
          (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
            (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
            (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1))) *
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2)
    change common * ∏ j : Fin stmt.k,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
        (stmt.bases j).1 (stmt.bases j).2 = 0 at hRawEqZero
    change common * ∏ i : Fin (baseImageCount E stmt msg hkm),
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval
        (baseAt E stmt msg hkm i).1 (baseAt E stmt msg hkm i).2 = 0
    rcases mul_eq_zero.mp hRawEqZero with hCommon | hProd
    · exact mul_eq_zero.mpr (Or.inl hCommon)
    · rw [Finset.prod_eq_zero_iff] at hProd
      obtain ⟨j, _, hj⟩ := hProd
      apply mul_eq_zero.mpr; right
      rw [Finset.prod_eq_zero_iff]
      refine ⟨baseIndexOf E stmt msg hkm (finCongr hkm j),
              Finset.mem_univ _, ?_⟩
      rw [baseAt_baseIndexOf]
      have hEq : extractorBases E stmt msg hkm (finCongr hkm j) = stmt.bases j := by
        unfold extractorBases
        congr 1
      rw [hEq]
      exact hj
  have hRaw := hAllZeroRaw A₀ A₁ hA₀ hA₁ hNV hDefRaw
  rw [logDerivCheckFn_eq_grouped] at hRaw
  exact hRaw

/-- **polyG vanishes at every defined non-vertical rational pair under
hAllZero + hRat with `distinctRCons` / `distinctMCons` and
`multAt(betaCanonical)` coefficients.** Combines Layer A scalar
invariance (`hAllZero_baseAt_of_hAllZero_raw`) with the cons-form
result (`polyG_zero_at_defined_betaCanonical_of_hAllZero_and_hRat`). -/
private theorem polyG_zero_at_defined_distinctRCons_betaCanonical_of_hAllZero_and_hRat
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (gd : GeometricDivisorData E msg.toD)
    (hRat : gd_support_rational E msg.toD gd)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
      logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E msg.toD stmt.target
      (baseAt E stmt msg hkm) A₀ A₁) :
    polyG E (zerosAt E msg.toD)
      (fun k' => ((multAt E (betaCanonical E msg.toD) msg.toD k' : ℕ) : ZMod E.q))
      (distinctRCons E stmt msg hkm) (distinctMCons E stmt msg hkm)
      A₀ A₁ = 0 := by
  have hAllZeroDistinct := hAllZero_baseAt_of_hAllZero_raw E stmt msg hkm hAllZero
  exact polyG_zero_at_defined_betaCanonical_of_hAllZero_and_hRat E msg.toD hDnz gd hRat
    stmt.target (baseAt E stmt msg hkm) (distinctM'_tail E stmt msg hkm)
    hAllZeroDistinct A₀ A₁ hA₀ hA₁ hNV hDef

/-- **Per-A₀ count of non-defined A₁ pairs.** For A₀ ∈ E.points outside
zerosFinset and the distinctR positions, the number of A₁ ∈ E.points
with `¬logDerivCheckFnDefined E D stmt.target baseAt A₀ A₁` is bounded
linearly in `D.degE + stmt.k`. Extracted from the internal proof in
`ExtractorBridge.lean`. -/
private theorem card_logDerivCheckFnDefined_complement_le
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + stmt.k + 2) + 3) +
        21 * (D.degE + stmt.k + 2) + 72)
    (A₀ : ZMod E.q × ZMod E.q) (hA₀ : A₀ ∈ E.points)
    (_hA₀nz : A₀ ∉ zerosFinset E D)
    (_hA₀nr : ∀ j : Fin (1 + baseImageCount E stmt msg hkm),
        distinctR E stmt msg hkm j ≠ A₀)
    (hA₀NotBad : A₀ ∉ badDenomA0 E D stmt.target
        (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)) :
    (E.points.filter (fun A₁ =>
        ¬logDerivCheckFnDefined E D stmt.target
          (baseAt E stmt msg hkm) A₀ A₁)).card
      ≤ 18 * D.degE + 10 * stmt.k + 112 := by
  classical
  let _ := hDnz
  set k₀ := baseImageCount E stmt msg hkm with hk₀_def
  set B₀ := baseAt E stmt msg hkm
  set P₀ := stmt.target
  have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
    calc baseImageCount E stmt msg hkm
        ≤ msg.k := by
          unfold baseImageCount baseImage
          exact (Finset.card_image_le).trans
            (by rw [Finset.card_univ, Fintype.card_fin])
      _ = stmt.k := hkm.symm
  by_cases hWit : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
      logDerivCheckFnDefined E D P₀ B₀ A₀ A₁
  · -- Witness exists: use denomScaledPoly + card_zeros_on_E_le.
    have hNZ := denomScaledPoly_modCurve_ne_zero E D P₀ k₀ B₀ A₀ hWit
    have hCardBound := card_zeros_on_E_le E
      (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) hNZ
    have hResBound := resultantX_denomScaledPoly_natDegree_le E D P₀ k₀ B₀ A₀
    have hFilterSubNV : E.points.filter (fun A₁ =>
          ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1)
        ⊆ E.points.filter (fun p =>
          bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0) := by
      intro A₁ hA₁
      simp only [Finset.mem_filter] at hA₁ ⊢
      refine ⟨hA₁.1, ?_⟩
      unfold logDerivCheckFnDefined at hA₁
      push_neg at hA₁
      rw [bivEval_denomScaledPoly_eq E D P₀ k₀ B₀ A₀ A₁ hA₁.2.2, hA₁.2.1, mul_zero]
    have hFilterSplit : E.points.filter (fun A₁ =>
          ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁)
        ⊆ E.points.filter (fun A₁ => A₁.1 = A₀.1) ∪
          E.points.filter (fun A₁ =>
            ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1) := by
      intro A₁ hA₁
      simp only [Finset.mem_filter, Finset.mem_union] at hA₁ ⊢
      by_cases h : A₀.1 = A₁.1
      · left; exact ⟨hA₁.1, h.symm⟩
      · right; exact ⟨hA₁.1, hA₁.2, h⟩
    calc (E.points.filter (fun A₁ =>
            ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁)).card
        ≤ _ := Finset.card_le_card hFilterSplit
      _ ≤ (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
          (E.points.filter (fun A₁ =>
            ¬logDerivCheckFnDefined E D P₀ B₀ A₀ A₁ ∧ A₀.1 ≠ A₁.1)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 + (E.points.filter (fun p =>
            bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0)).card :=
          Nat.add_le_add (card_points_with_fst_eq_le E A₀.1)
            (Finset.card_le_card hFilterSubNV)
      _ ≤ 2 + 2 * (resultantX E
            (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀)).natDegree :=
          Nat.add_le_add_left hCardBound 2
      _ ≤ 2 + 2 * (9 * D.degE + 5 * k₀ + 55) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 hResBound) 2
      _ ≤ 18 * D.degE + 10 * stmt.k + 112 := by
          have := hBI; omega
  · -- No defined witness: derive contradiction from hLargeQ.
    push_neg at hWit
    exfalso
    have hAllZeroBiv : ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
        bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) A₁ = 0 := by
      intro A₁ hA₁mem hNV
      rw [bivEval_denomScaledPoly_eq E D P₀ k₀ B₀ A₀ A₁ hNV]
      have hND := hWit A₁ hA₁mem hNV
      unfold logDerivCheckFnDefined at hND
      push_neg at hND
      rw [hND]; ring
    have hNZ : denomScaledPoly (E := E) D P₀ k₀ B₀ A₀ %ₘ curveEqPoly E ≠ 0 := by
      intro hZero
      apply hA₀NotBad
      rw [badDenomA0, Finset.mem_filter]
      exact ⟨hA₀, hZero⟩
    have hCardBound := card_zeros_on_E_le E
      (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) hNZ
    have hResBound := resultantX_denomScaledPoly_natDegree_le E D P₀ k₀ B₀ A₀
    have hNVsub : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)
        ⊆ E.points.filter (fun p =>
          bivEval (denomScaledPoly (E := E) D P₀ k₀ B₀ A₀) p = 0) := by
      intro A₁ hA₁
      simp only [Finset.mem_filter] at hA₁ ⊢
      exact ⟨hA₁.1, hAllZeroBiv A₁ hA₁.1 hA₁.2⟩
    have hNVcard : E.points.card - 2 ≤
        (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card := by
      have hCompl : (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card +
          (E.points.filter (fun A₁ => ¬A₁.1 = A₀.1)).card =
          E.points.card :=
        Finset.card_filter_add_card_filter_not (s := E.points)
          (p := fun A₁ => A₁.1 = A₀.1)
      have hVertCard := card_points_with_fst_eq_le E A₀.1
      have hEq : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1) =
          E.points.filter (fun A₁ => ¬A₁.1 = A₀.1) := by
        ext x; simp [ne_comm]
      rw [hEq]; omega
    have hUB : (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1)).card
        ≤ 2 * (9 * D.degE + 5 * k₀ + 55) :=
      le_trans (Finset.card_le_card hNVsub)
        (le_trans hCardBound (Nat.mul_le_mul_left 2 hResBound))
    have hSizeBound : E.points.card ≤ 2 * (9 * D.degE + 5 * k₀ + 55) + 2 := by omega
    have := hBI; omega

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
private theorem sigma_data_of_gd_support_rational (hHW : E.HasseBound)
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
  -- Apply sigma_matching_from_polyGFull_vanishing. Three sub-hypotheses needed:
  -- (1) multAt(betaCanonical) cast to ZMod E.q is non-zero pointwise.
  -- (2) polyGFull (with zerosAt, multAt(betaCanonical), distinctR, distinctM')
  --     vanishes on all of E × E.
  -- (3) Linear-threshold hypotheses (E.points.card vs d + M).
  -- (1) follows from betaCanonical_covers + sum_le_degE + hd.
  -- (2) is the substantial open piece: polyG vanishing extends from
  --     defined non-vert pairs to all E × E via density + bivariate density.
  -- (3) follows from hLargeQ.
  have hBetaNz : ∀ k : Fin (zerosCard E msg.toD),
      ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q) ≠ 0 := by
    haveI : NeZero E.q := ⟨E.hq_prime.ne_zero⟩
    intro k
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hDvd
    -- multAt(betaCanonical) k > 0 from coverage.
    have hPos : 0 < multAt E (betaCanonical E msg.toD) msg.toD k :=
      multAt_pos E (betaCanonical E msg.toD) msg.toD
        (betaCanonical_covers E msg.toD _hDnz) k
    -- multAt(betaCanonical) k < E.q from sum bound + degree bound.
    have hBetaSum := betaCanonical_sum_le_degE E msg.toD
    have hMultSum :=
      sum_multAt_eq_sum_βfun E (betaCanonical E msg.toD) msg.toD
        (betaCanonical_support E msg.toD)
    have hSingleLe : multAt E (betaCanonical E msg.toD) msg.toD k
        ≤ ∑ k' : Fin (zerosCard E msg.toD),
            multAt E (betaCanonical E msg.toD) msg.toD k' :=
      Finset.single_le_sum
        (f := fun k' => multAt E (betaCanonical E msg.toD) msg.toD k')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have hLt : multAt E (betaCanonical E msg.toD) msg.toD k < E.q :=
      lt_of_le_of_lt
        (hSingleLe.trans (hMultSum ▸ hBetaSum))
        (lt_of_le_of_lt _hDeg _hd)
    exact absurd (Nat.le_of_dvd hPos hDvd) (Nat.not_le.mpr hLt)
  have hELargeDkl : E.points.card * E.points.card - 2 * E.points.card >
        18 * (zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)) * E.q := by
    -- Setup bounds.
    have hZC : zerosCard E msg.toD ≤ msg.toD.degE := by
      have hβcov := betaCanonical_covers E msg.toD _hDnz
      have hβpos : ∀ k : Fin (zerosCard E msg.toD),
          1 ≤ multAt E (betaCanonical E msg.toD) msg.toD k :=
        fun k => multAt_pos E (betaCanonical E msg.toD) msg.toD hβcov k
      have hβsum := betaCanonical_sum_le_degE E msg.toD
      have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E msg.toD) msg.toD
        (betaCanonical_support E msg.toD)
      calc zerosCard E msg.toD
          = ∑ _ : Fin (zerosCard E msg.toD), 1 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E (betaCanonical E msg.toD) msg.toD k :=
            Finset.sum_le_sum (fun k _ => hβpos k)
        _ = ∑ P ∈ E.points, betaCanonical E msg.toD P := hβeq
        _ ≤ msg.toD.degE := hβsum
    have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
      calc baseImageCount E stmt msg hkm
          ≤ msg.k := by
            unfold baseImageCount baseImage
            exact (Finset.card_image_le).trans
              (by rw [Finset.card_univ, Fintype.card_fin])
        _ = stmt.k := hkm.symm
    set n := E.points.card with hn_def
    set T := zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm) with hT_def
    set M := msg.toD.degE + (1 + stmt.k) with hM_def
    have hT_le_M : T ≤ M := by
      rw [hT_def, hM_def]
      exact Nat.add_le_add hZC (Nat.add_le_add_left hBI _)
    have hM_pos : 1 ≤ M := by rw [hM_def]; omega
    -- hLargeQ flat: n > 31*(degE+k+2)+78 = 31*M + 109 (since M = degE+k+1).
    have hN_flat : n > 31 * M + 109 := by
      have h := _hLargeQ
      have hEq : 2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
              21 * (msg.toD.degE + stmt.k + 2) + 72
            = 31 * M + 109 := by rw [hM_def]; ring
      rw [hEq] at h
      exact h
    -- Sharp Hasse: q ≤ n + 2 + s with s² ≤ 4(n+1).
    have hQbound : E.q ≤ n + 2 + Nat.sqrt (4 * (n + 1)) := hasse_q_le_sharp_nat_of E hHW
    set s := Nat.sqrt (4 * (n + 1)) with hs_def
    have hSqrtSq : s * s ≤ 4 * (n + 1) := Nat.sqrt_le _
    -- Step 1: 13n > 18s (from squared bound 169n² > 324s² ≤ 1296(n+1)).
    have hN_141 : n ≥ 141 := by
      have h1 := hN_flat; have h2 := hM_pos; omega
    have h_169n2 : 169 * n * n > 1296 * (n + 1) := by
      nlinarith [hN_141, sq_nonneg n]
    have h_13n_18s : 13 * n > 18 * s := by
      have h_169n2' : 169 * n * n > 324 * (s * s) := by
        calc 169 * n * n > 1296 * (n + 1) := h_169n2
          _ = 324 * (4 * (n + 1)) := by ring
          _ ≥ 324 * (s * s) := Nat.mul_le_mul_left _ hSqrtSq
      have hSq : (13 * n) * (13 * n) > (18 * s) * (18 * s) := by
        have : (13 * n) * (13 * n) = 169 * n * n := by ring
        rw [this]
        have : (18 * s) * (18 * s) = 324 * (s * s) := by ring
        rw [this]
        exact h_169n2'
      -- From a*a > b*b in ℕ, derive a > b (contrapositive: a ≤ b → a*a ≤ b*b).
      by_contra h_le
      push_neg at h_le
      have : (13 * n) * (13 * n) ≤ (18 * s) * (18 * s) :=
        Nat.mul_le_mul h_le h_le
      omega
    -- Step 2: 107n > 36M.
    have h_107n_36M : 107 * n > 36 * M := by
      have h1 : 107 * n ≥ 107 * (31 * M + 110) := by
        have : n ≥ 31 * M + 110 := by omega
        exact Nat.mul_le_mul_left _ this
      have h2 : 107 * (31 * M + 110) = 3317 * M + 11770 := by ring
      have h3 : 3317 * M + 11770 > 36 * M := by omega
      linarith
    -- Combine: 13Mn + 107n > 18Ms + 36M.
    have h_combined : 13 * M * n + 107 * n > 18 * M * s + 36 * M := by
      have h1 : 13 * M * n ≥ 18 * M * s := by
        have h13_18 : M * (13 * n) ≥ M * (18 * s) :=
          Nat.mul_le_mul_left M (le_of_lt h_13n_18s)
        have heq1 : 13 * M * n = M * (13 * n) := by ring
        have heq2 : 18 * M * s = M * (18 * s) := by ring
        rw [heq1, heq2]; exact h13_18
      omega
    -- Goal: n*n - 2*n > 18*T*q.
    -- We have n*n - 2*n ≥ n*(n - 2 - 18*M) + 18*M*n = ... let me reformulate.
    -- n² - 2n = n(n-2). Want n(n-2) > 18*T*q.
    -- 18*T*q ≤ 18*M*q ≤ 18*M*(n + 2 + s) = 18Mn + 36M + 18Ms.
    -- Want n(n-2) > 18Mn + 36M + 18Ms.
    -- ⟺ n² - 2n - 18Mn - 36M > 18Ms.
    -- ⟺ n*(n - 18M - 2) - 36M > 18Ms.
    -- With n ≥ 31M + 110, n - 18M - 2 ≥ 13M + 108 ≥ 13M + 107.
    -- n*(13M+107) - 36M > 18Ms ⟺ 13Mn + 107n - 36M > 18Ms ⟺ 13Mn + 107n > 18Ms + 36M ✓.
    have h_n_minus : n - 18 * M - 2 ≥ 13 * M + 107 := by omega
    have h_lhs : n * (n - 18 * M - 2) ≥ n * (13 * M + 107) :=
      Nat.mul_le_mul_left _ h_n_minus
    have h_lhs2 : n * (13 * M + 107) = 13 * M * n + 107 * n := by ring
    have h_step : n * (n - 18 * M - 2) ≥ 13 * M * n + 107 * n := by
      rw [← h_lhs2]; exact h_lhs
    -- n*n = n*(n - 18M - 2) + n*(18M + 2) (since n ≥ 18M+2).
    have h_n_ge_18M2 : 18 * M + 2 ≤ n := by omega
    have h_n_split :
        n * (n - 18 * M - 2) + n * (18 * M + 2) = n * n := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have h_n_split' : n * (n - 18 * M - 2) = n * n - n * (18 * M + 2) := by omega
    -- 18*T*q ≤ 18*M*(n + 2 + s).
    have h_18Tq_le : 18 * T * E.q ≤ 18 * M * (n + 2 + s) := by
      calc 18 * T * E.q ≤ 18 * M * E.q :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT_le_M)
        _ ≤ 18 * M * (n + 2 + s) := Nat.mul_le_mul_left _ hQbound
    -- Want: n*n - 2*n > 18*T*q. Apply chain with sub: n*n - 2*n = n*(n-18M-2) + 18Mn.
    have h_n_expand : n * n - 2 * n = n * (n - 18 * M - 2) + 18 * M * n := by
      have h1 : n * (18 * M + 2) = 18 * M * n + 2 * n := by ring
      omega
    rw [h_n_expand]
    have h_18M_expand : 18 * M * (n + 2 + s) = 18 * M * n + 36 * M + 18 * M * s := by ring
    have h_chain : 18 * T * E.q ≤ 18 * M * n + 36 * M + 18 * M * s := by
      rw [← h_18M_expand]; exact h_18Tq_le
    -- Combine: 13Mn + 107n + 18Mn > 36M + 18Ms + 18Mn (since 13Mn + 107n > 36M + 18Ms).
    have h_combined' : 13 * M * n + 107 * n + 18 * M * n
        > 36 * M + 18 * M * s + 18 * M * n := by omega
    have h_step3 : n * (n - 18 * M - 2) + 18 * M * n
        ≥ 13 * M * n + 107 * n + 18 * M * n := by omega
    omega
  have hVanishing : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      bivEval₂ (polyGFull E (zerosAt E msg.toD)
        (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
        (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)) A₀ A₁ = 0 := by
    -- Step A: polyG = 0 at defined non-vertical pairs (distinct form), via
    -- polyG_zero_at_defined_distinctRCons_betaCanonical + finCongr to convert
    -- distinctRCons / distinctMCons to distinctR / distinctM'.
    have hAt_def_distinct :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          logDerivCheckFnDefined E msg.toD stmt.target
            (baseAt E stmt msg hkm) A₀ A₁ →
          polyG E (zerosAt E msg.toD)
            (fun k' => ((multAt E (betaCanonical E msg.toD) msg.toD k' : ℕ) : ZMod E.q))
            (distinctRCons E stmt msg hkm) (distinctMCons E stmt msg hkm)
            A₀ A₁ = 0 :=
      fun A₀ A₁ hA₀ hA₁ hNV hDef =>
        polyG_zero_at_defined_distinctRCons_betaCanonical_of_hAllZero_and_hRat E
          stmt msg hkm _hDnz gd _hRat _hAllZero A₀ A₁ hA₀ hA₁ hNV hDef
    -- Step B: convert distinctRCons / distinctMCons to distinctR / distinctM'
    -- via polyG_reindex (composes with finCongr).
    -- polyG_reindex says: polyG over R∘e = polyG over R, for any equiv e on Fin.
    -- distinctR = distinctRCons ∘ finCongr (Nat.add_comm 1 _).
    have hAt_def :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          logDerivCheckFnDefined E msg.toD stmt.target
            (baseAt E stmt msg hkm) A₀ A₁ →
          polyG E (zerosAt E msg.toD)
            (fun k' => ((multAt E (betaCanonical E msg.toD) msg.toD k' : ℕ) : ZMod E.q))
            (distinctR E stmt msg hkm) (distinctM' E stmt msg hkm)
            A₀ A₁ = 0 := by
      intro A₀ A₁ hA₀ hA₁ hNV hDef
      have h := hAt_def_distinct A₀ A₁ hA₀ hA₁ hNV hDef
      unfold distinctR distinctM'
      rw [polyG_reindex]
      exact h
    -- Step C: manual case split on A₀ being non-special vs special.
    -- For non-special A₀ (∉ zerosFinset, ∉ distinctR-image): per-A₀ density
    -- gives polyGPoly(A₀) ≡ 0 mod curveEqPoly via bivEval_zero_on_E_of_many_zeros.
    -- For special A₀: use polyG_swap_zero from non-special A₁ witnesses.
    set Q_fn : Fin (zerosCard E msg.toD) → ZMod E.q × ZMod E.q := zerosAt E msg.toD
      with hQ_fn_def
    set β_fn : Fin (zerosCard E msg.toD) → ZMod E.q :=
      fun k' => ((multAt E (betaCanonical E msg.toD) msg.toD k' : ℕ) : ZMod E.q)
      with hβ_fn_def
    set R_fn : Fin (1 + baseImageCount E stmt msg hkm) → ZMod E.q × ZMod E.q :=
      distinctR E stmt msg hkm with hR_fn_def
    set m_fn : Fin (1 + baseImageCount E stmt msg hkm) → ZMod E.q :=
      distinctM' E stmt msg hkm with hm_fn_def
    -- Bound: zerosCard ≤ degE, baseImageCount ≤ k.
    have hZC : zerosCard E msg.toD ≤ msg.toD.degE := by
      have hβcov := betaCanonical_covers E msg.toD _hDnz
      have hβpos : ∀ k : Fin (zerosCard E msg.toD),
          1 ≤ multAt E (betaCanonical E msg.toD) msg.toD k :=
        fun k => multAt_pos E (betaCanonical E msg.toD) msg.toD hβcov k
      have hβsum := betaCanonical_sum_le_degE E msg.toD
      have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E msg.toD) msg.toD
        (betaCanonical_support E msg.toD)
      calc zerosCard E msg.toD
          = ∑ _ : Fin (zerosCard E msg.toD), 1 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E (betaCanonical E msg.toD) msg.toD k :=
            Finset.sum_le_sum (fun k _ => hβpos k)
        _ = ∑ P ∈ E.points, betaCanonical E msg.toD P := hβeq
        _ ≤ msg.toD.degE := hβsum
    have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
      calc baseImageCount E stmt msg hkm
          ≤ msg.k := by
            unfold baseImageCount baseImage
            exact (Finset.card_image_le).trans
              (by rw [Finset.card_univ, Fintype.card_fin])
        _ = stmt.k := hkm.symm
    -- resultantX bound: ≤ 5*(d+K)+3 ≤ 5*(degE+1+k)+3 = 5*degE+5*k+8.
    have h_resultantX_le : ∀ A₀ : ZMod E.q × ZMod E.q,
        (resultantX E (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree
          ≤ 5 * msg.toD.degE + 5 * stmt.k + 8 := by
      intro A₀
      have h := resultantX_polyGPoly_natDegree_le E Q_fn β_fn R_fn m_fn A₀
      -- h: ≤ 5 * (zerosCard + (1 + baseImageCount)) + 3
      -- ≤ 5 * (degE + 1 + k) + 3 = 5*degE + 5*k + 8.
      have hSum : zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)
          ≤ msg.toD.degE + 1 + stmt.k := by omega
      omega
    -- The hLargeQ as the form needed by card_logDerivCheckFnDefined_complement_le.
    have hLargeQ_alt : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72 := _hLargeQ
    -- Per-A₀ non-defined count for non-special A₀ (also excluding badDenomA0).
    have h_card_nondef : ∀ A₀, A₀ ∈ E.points → A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₀) →
        A₀ ∉ badDenomA0 E msg.toD stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) →
        (E.points.filter (fun A₁ =>
            ¬logDerivCheckFnDefined E msg.toD stmt.target
              (baseAt E stmt msg hkm) A₀ A₁)).card
          ≤ 18 * msg.toD.degE + 10 * stmt.k + 112 :=
      fun A₀ hA₀ hnz hnr hnbad =>
        card_logDerivCheckFnDefined_complement_le E msg.toD _hDnz stmt msg hkm
          hLargeQ_alt A₀ hA₀ hnz hnr hnbad
    -- vertical exclusion: ≤ 2 same-x A₁'s.
    have h_vert : ∀ A₀ : ZMod E.q × ZMod E.q,
        (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card ≤ 2 :=
      fun A₀ => card_points_with_fst_eq_le E A₀.1
    -- Lower bound on # defined non-vert A₁'s for non-special A₀ (also non-badDenom).
    have h_card_def_lb : ∀ A₀, A₀ ∈ E.points → A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₀) →
        A₀ ∉ badDenomA0 E msg.toD stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) →
        (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1 ∧
            logDerivCheckFnDefined E msg.toD stmt.target
              (baseAt E stmt msg hkm) A₀ A₁)).card
          ≥ E.points.card - 2 - (18 * msg.toD.degE + 10 * stmt.k + 112) := by
      intro A₀ hA₀ hnz hnr hnbad
      have h_complement : E.points.filter
            (fun A₁ => ¬(A₀.1 ≠ A₁.1 ∧
              logDerivCheckFnDefined E msg.toD stmt.target
                (baseAt E stmt msg hkm) A₀ A₁))
          ⊆ E.points.filter (fun A₁ => A₁.1 = A₀.1) ∪
            E.points.filter (fun A₁ =>
              ¬logDerivCheckFnDefined E msg.toD stmt.target
                (baseAt E stmt msg hkm) A₀ A₁) := by
        intro A₁ hA₁
        simp only [Finset.mem_filter, Finset.mem_union, not_and_or, not_not] at hA₁ ⊢
        rcases hA₁ with ⟨hMem, h | h⟩
        · -- ¬(A₀.1 ≠ A₁.1) means A₀.1 = A₁.1
          left; exact ⟨hMem, h.symm⟩
        · right; exact ⟨hMem, h⟩
      have h_complement_card : (E.points.filter
            (fun A₁ => ¬(A₀.1 ≠ A₁.1 ∧
              logDerivCheckFnDefined E msg.toD stmt.target
                (baseAt E stmt msg hkm) A₀ A₁))).card
          ≤ 2 + (18 * msg.toD.degE + 10 * stmt.k + 112) := by
        calc _ ≤ _ := Finset.card_le_card h_complement
          _ ≤ _ + _ := Finset.card_union_le _ _
          _ ≤ 2 + (18 * msg.toD.degE + 10 * stmt.k + 112) :=
              Nat.add_le_add (h_vert A₀) (h_card_nondef A₀ hA₀ hnz hnr hnbad)
      have h_split := Finset.card_filter_add_card_filter_not (s := E.points)
        (p := fun A₁ => A₀.1 ≠ A₁.1 ∧
          logDerivCheckFnDefined E msg.toD stmt.target
            (baseAt E stmt msg hkm) A₀ A₁)
      omega
    -- For non-special non-badDenom A₀: polyGPoly(A₀) ≡ 0 mod curveEqPoly via density.
    have h_nonspec : ∀ A₀, A₀ ∈ E.points → A₀ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₀) →
        A₀ ∉ badDenomA0 E msg.toD stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) →
        ∀ A₁ ∈ E.points, polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₀ hA₀ hnz hnr hnbad A₁ hA₁
      have h_ge_def := h_card_def_lb A₀ hA₀ hnz hnr hnbad
      -- Sub: defined non-vert A₁'s ⊆ zeros of polyGPoly(A₀).
      have h_sub : E.points.filter (fun A₁' => A₀.1 ≠ A₁'.1 ∧
            logDerivCheckFnDefined E msg.toD stmt.target
              (baseAt E stmt msg hkm) A₀ A₁')
          ⊆ E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0) := by
        intro A₁' h
        simp only [Finset.mem_filter] at h ⊢
        refine ⟨h.1, ?_⟩
        rw [bivEval_polyGPoly]
        exact hAt_def A₀ A₁' hA₀ h.1 h.2.1 h.2.2
      have h_zeros_card : (E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          ≥ E.points.card - 2 - (18 * msg.toD.degE + 10 * stmt.k + 112) :=
        le_trans h_ge_def (Finset.card_le_card h_sub)
      -- Density: # zeros > 2 * resultantX.
      have h_resBd := h_resultantX_le A₀
      have h_many : (E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          > 2 * (resultantX E
              (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree := by
        have h := _hLargeQ
        omega
      have h_all := bivEval_zero_on_E_of_many_zeros E
        (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) h_many
      rw [← bivEval_polyGPoly]
      exact h_all A₁ hA₁
    -- For special A₀ via swap: get polyG = 0 from non-special non-badDenom A₁'s.
    have h_swap_zeros : ∀ A₀, A₀ ∈ E.points →
        ∀ A₁, A₁ ∈ E.points → A₁ ∉ zerosFinset E msg.toD →
        (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁) →
        A₁ ∉ badDenomA0 E msg.toD stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) →
        A₀.1 ≠ A₁.1 →
        polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₀ hA₀ A₁ hA₁ hA₁nz hA₁nr hA₁nbad _hNV
      exact polyG_swap_zero E Q_fn β_fn R_fn m_fn A₀ A₁
        (h_nonspec A₁ hA₁ hA₁nz hA₁nr hA₁nbad A₀ hA₀)
    -- Bound on |badDenomA0| (multiplicative form).
    have hBadCardMul :
        (badDenomA0 E msg.toD stmt.target
            (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card
          * (E.points.card - 2)
        ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
      have hBI := show baseImageCount E stmt msg hkm ≤ stmt.k from by
        unfold baseImageCount baseImage
        exact (Finset.card_image_le).trans
          (by rw [Finset.card_univ, Fintype.card_fin, hkm])
      have h := badDenomA0_card_mul_card_sub_two_le E msg.toD _hDnz stmt.target
        (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)
      calc _ ≤ _ := h
        _ ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card := by
            apply Nat.mul_le_mul_right; omega
    -- For special A₀ (in zerosFinset, R-image, or badDenomA0): enough zeros via swap.
    have h_spec : ∀ A₀, A₀ ∈ E.points →
        (A₀ ∈ zerosFinset E msg.toD ∨
          (∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₀) ∨
          A₀ ∈ badDenomA0 E msg.toD stmt.target
            (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)) →
        ∀ A₁ ∈ E.points, polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₀ hA₀ _hSpec A₁ hA₁
      -- # non-special non-badDenom A₁ with A₀.1 ≠ A₁.1.
      have h_sub : E.points.filter (fun A₁' =>
            A₁' ∉ zerosFinset E msg.toD ∧
            (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁') ∧
            A₁' ∉ badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) ∧
            A₀.1 ≠ A₁'.1)
          ⊆ E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0) := by
        intro A₁' h
        simp only [Finset.mem_filter] at h ⊢
        refine ⟨h.1, ?_⟩
        rw [bivEval_polyGPoly]
        exact h_swap_zeros A₀ hA₀ A₁' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      -- # complement of (non-special ∧ non-badDenom ∧ non-vert): bounded.
      have h_complement : E.points.filter
            (fun A₁' => ¬(A₁' ∉ zerosFinset E msg.toD ∧
              (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁') ∧
              A₁' ∉ badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) ∧
              A₀.1 ≠ A₁'.1))
          ⊆ E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD) ∪
            E.points.filter (fun A₁' =>
              ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁') ∪
            E.points.filter (fun A₁' =>
              A₁' ∈ badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)) ∪
            E.points.filter (fun A₁' => A₁'.1 = A₀.1) := by
        intro A₁' h
        simp only [Finset.mem_filter, Finset.mem_union, not_and_or, not_not, not_forall,
          Classical.not_not] at h ⊢
        rcases h with ⟨hMem, h | h | h | h⟩
        · left; left; left; exact ⟨hMem, h⟩
        · left; left; right
          refine ⟨hMem, ?_⟩
          obtain ⟨j, hj⟩ := h
          exact ⟨j, hj⟩
        · left; right; exact ⟨hMem, h⟩
        · right; exact ⟨hMem, h.symm⟩
      have h_zerosCard : (E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD)).card
          ≤ msg.toD.degE := by
        have h1 : E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD)
            ⊆ zerosFinset E msg.toD := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          exact hx.2
        exact (Finset.card_le_card h1).trans hZC
      have h_RimageCard : (E.points.filter (fun A₁' =>
            ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁')).card
          ≤ 1 + baseImageCount E stmt msg hkm := by
        have h1 : E.points.filter (fun A₁' =>
              ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁')
            ⊆ Finset.univ.image R_fn := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
          exact hx.2
        have h2 : (Finset.univ.image R_fn).card ≤ 1 + baseImageCount E stmt msg hkm := by
          refine Finset.card_image_le.trans ?_
          rw [Finset.card_univ, Fintype.card_fin]
        exact (Finset.card_le_card h1).trans h2
      have h_BadCardLe : (E.points.filter (fun A₁' =>
            A₁' ∈ badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm))).card
          ≤ (badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx
        exact hx.2
      have h_complement_card :
          (E.points.filter (fun A₁' => ¬(A₁' ∉ zerosFinset E msg.toD ∧
            (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁') ∧
            A₁' ∉ badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) ∧
            A₀.1 ≠ A₁'.1))).card
          ≤ msg.toD.degE + (1 + baseImageCount E stmt msg hkm) +
            (badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card + 2 := by
        have hCompL := Finset.card_le_card h_complement
        have hUL1 := Finset.card_union_le
            (E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD) ∪
             E.points.filter (fun A₁' =>
              ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁') ∪
             E.points.filter (fun A₁' =>
              A₁' ∈ badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)))
            (E.points.filter (fun A₁' => A₁'.1 = A₀.1))
        have hUL2 := Finset.card_union_le
            (E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD) ∪
             E.points.filter (fun A₁' =>
              ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁'))
            (E.points.filter (fun A₁' =>
              A₁' ∈ badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)))
        have hUL3 := Finset.card_union_le
            (E.points.filter (fun A₁' => A₁' ∈ zerosFinset E msg.toD))
            (E.points.filter (fun A₁' =>
              ∃ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j = A₁'))
        have hVert := h_vert A₀
        omega
      have h_split := Finset.card_filter_add_card_filter_not (s := E.points)
        (p := fun A₁' => A₁' ∉ zerosFinset E msg.toD ∧
          (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁') ∧
          A₁' ∉ badDenomA0 E msg.toD stmt.target
            (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) ∧
          A₀.1 ≠ A₁'.1)
      have h_card_def : (E.points.filter (fun A₁' =>
            A₁' ∉ zerosFinset E msg.toD ∧
            (∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₁') ∧
            A₁' ∉ badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) ∧
            A₀.1 ≠ A₁'.1)).card
          ≥ E.points.card - (msg.toD.degE + (1 + baseImageCount E stmt msg hkm)) -
              (badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card - 2 := by
        omega
      have h_zeros_ge :
          (E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          ≥ E.points.card - (msg.toD.degE + (1 + baseImageCount E stmt msg hkm)) -
              (badDenomA0 E msg.toD stmt.target
                (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card - 2 :=
        le_trans h_card_def (Finset.card_le_card h_sub)
      have h_resBd := h_resultantX_le A₀
      have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
        unfold baseImageCount baseImage
        exact (Finset.card_image_le).trans
          (by rw [Finset.card_univ, Fintype.card_fin, hkm])
      -- Linear bound: |badDenomA0| ≤ n - 11·degE - 11·stmt.k - 20.
      -- (Stated in terms of stmt.k via the relaxed version.)
      have hBadLinear :
          (badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)).card
            ≤ E.points.card - 11 * msg.toD.degE - 11 * stmt.k - 20 := by
        have hLargeQ_form : E.points.card ≥
            31 * msg.toD.degE + 31 * stmt.k + 141 := by
          have := _hLargeQ; omega
        exact badDenomA0_card_le_linear_relax E msg.toD _hDnz stmt.target
          (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm) stmt.k hBI
          hLargeQ_form
      have h_many : (E.points.filter (fun p =>
            bivEval (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) p = 0)).card
          > 2 * (resultantX E
              (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀)).natDegree := by
        have := _hLargeQ
        omega
      have h_all := bivEval_zero_on_E_of_many_zeros E
        (polyGPoly (E := E) Q_fn β_fn R_fn m_fn A₀) h_many
      rw [← bivEval_polyGPoly]
      exact h_all A₁ hA₁
    -- Combine: hAt_nonvert via case split (now four-way: zerosFinset / R-image /
    -- badDenomA0 / non-special non-badDenom).
    have hAt_nonvert :
        ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
          A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
          polyG E Q_fn β_fn R_fn m_fn A₀ A₁ = 0 := by
      intro A₀ A₁ hA₀ hA₁ _hNV
      by_cases hA₀nz : A₀ ∈ zerosFinset E msg.toD
      · exact h_spec A₀ hA₀ (Or.inl hA₀nz) A₁ hA₁
      · by_cases hA₀nr : ∀ j : Fin (1 + baseImageCount E stmt msg hkm), R_fn j ≠ A₀
        · by_cases hA₀nbad : A₀ ∈ badDenomA0 E msg.toD stmt.target
              (baseImageCount E stmt msg hkm) (baseAt E stmt msg hkm)
          · exact h_spec A₀ hA₀ (Or.inr (Or.inr hA₀nbad)) A₁ hA₁
          · exact h_nonspec A₀ hA₀ hA₀nz hA₀nr hA₀nbad A₁ hA₁
        · push_neg at hA₀nr
          exact h_spec A₀ hA₀ (Or.inr (Or.inl hA₀nr)) A₁ hA₁
    -- Step D: extend to all E × E via polyGFull_vanishes_on_ExE_of_polyG_zero.
    exact polyGFull_vanishes_on_ExE_of_polyG_zero E hHW _ _ _ _
      hAt_nonvert hELargeDkl
  have hELargeThr : E.points.card > 4 * (zerosCard E msg.toD +
        (1 + baseImageCount E stmt msg hkm)) + 2 := by
    -- zerosCard ≤ msg.toD.degE ≤ stmt.degBound, baseImageCount ≤ stmt.k.
    have hZC : zerosCard E msg.toD ≤ msg.toD.degE := by
      have hβcov := betaCanonical_covers E msg.toD _hDnz
      have hβpos : ∀ k : Fin (zerosCard E msg.toD),
          1 ≤ multAt E (betaCanonical E msg.toD) msg.toD k :=
        fun k => multAt_pos E (betaCanonical E msg.toD) msg.toD hβcov k
      have hβsum := betaCanonical_sum_le_degE E msg.toD
      have hβeq := sum_multAt_eq_sum_βfun E (betaCanonical E msg.toD) msg.toD
        (betaCanonical_support E msg.toD)
      calc zerosCard E msg.toD
          = ∑ _ : Fin (zerosCard E msg.toD), 1 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ k : Fin (zerosCard E msg.toD), multAt E (betaCanonical E msg.toD) msg.toD k :=
            Finset.sum_le_sum (fun k _ => hβpos k)
        _ = ∑ P ∈ E.points, betaCanonical E msg.toD P := hβeq
        _ ≤ msg.toD.degE := hβsum
    have hBI : baseImageCount E stmt msg hkm ≤ stmt.k := by
      calc baseImageCount E stmt msg hkm
          ≤ msg.k := by
            unfold baseImageCount baseImage
            exact (Finset.card_image_le).trans
              (by rw [Finset.card_univ, Fintype.card_fin])
        _ = stmt.k := hkm.symm
    have h1 : 4 * (zerosCard E msg.toD + (1 + baseImageCount E stmt msg hkm)) + 2
        ≤ 4 * (msg.toD.degE + (1 + stmt.k)) + 2 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add hZC (Nat.add_le_add_left hBI _)
    have h2 : 4 * (msg.toD.degE + (1 + stmt.k)) + 2
        ≤ 4 * (stmt.degBound + (1 + stmt.k)) + 2 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_right _hDeg _
    linarith [_hLargeQ]
  exact sigma_matching_from_polyGFull_vanishing E hHW
    (zerosAt E msg.toD)
    (fun k => ((multAt E (betaCanonical E msg.toD) msg.toD k : ℕ) : ZMod E.q))
    (distinctR E stmt msg hkm)
    (distinctM' E stmt msg hkm)
    (zerosAt_injective E msg.toD)
    (distinctR_injective E stmt msg hkm hNoNegP)
    hBetaNz
    (fun k => zerosAt_mem_E E msg.toD k)
    (fun j => distinctR_mem_points E stmt msg hkm _hTargetOnE _hBasesOnE j)
    hVanishing hELargeThr hELargeDkl

/--
Glue lemma packaging the final partial-fraction step of the Frobenius
descent branch.

Takes:
* slope-isolation `hSep` and non-rationality `hNonRat` (from
  `exists_slope_zLambdaBar_isolated_non_rational`),
* an enumeration `e : Fin n ≃ gd.support` with `e i₀ = Q`,
* an auxiliary `Fin k` family `R` of rational base points whose
  `zLambda` projections give the second pole family,
* a coefficient family `d` for the auxiliary poles,
* an evaluation finset `S` of size at least `n + k`, disjoint from
  both pole families, on which the partial-fraction sum vanishes.

Builds the abstract `α/β/c/d` data and invokes
`FrobDescentHelpers.isolated_coeff_zero_of_pf_sum` to conclude
`((gd.mult Q : ℕ) : Fqbar E) = 0`. The lemma is pure glue: the actual
sampling-set construction (cardinality / disjointness / vanish) is
left to the caller.
-/
private theorem frob_descent_isolate_mult_of_pf_sum
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (lam : ZMod E.q)
    (Q : GeomPoint E)
    (hSep : ∀ Q' ∈ gd.support, Q' ≠ Q →
      zLambdaBar E lam Q' ≠ zLambdaBar E lam Q)
    (hNonRat : (zLambdaBar E lam Q) ^ E.q ≠ zLambdaBar E lam Q)
    {n : ℕ} (e : Fin n ≃ {x // x ∈ gd.support})
    (i₀ : Fin n) (hi₀ : (e i₀).val = Q)
    {k : ℕ} (R : Fin k → ZMod E.q × ZMod E.q)
    (d : Fin k → Fqbar E)
    (S : Finset (Fqbar E))
    (hCard : n + k ≤ S.card)
    (hDisjointα : ∀ μ ∈ S, ∀ i : Fin n,
      μ ≠ zLambdaBar E lam (e i).val)
    (hDisjointβ : ∀ μ ∈ S, ∀ j : Fin k,
      μ ≠ fqToBar E (zLambda E lam (R j)))
    (hVanish : ∀ μ ∈ S,
      (∑ i : Fin n,
          ((gd.mult (e i).val : ℕ) : Fqbar E) *
            (μ - zLambdaBar E lam (e i).val)⁻¹) +
        (∑ j : Fin k,
            d j * (μ - fqToBar E (zLambda E lam (R j)))⁻¹) = 0) :
    ((gd.mult Q : ℕ) : Fqbar E) = 0 := by
  have hIsolatedα : ∀ j : Fin n, j ≠ i₀ →
      zLambdaBar E lam (e j).val ≠ zLambdaBar E lam (e i₀).val := by
    intro j hj
    rw [hi₀]
    refine hSep _ (e j).property (fun hEq => hj ?_)
    exact e.injective (Subtype.ext (hEq.trans hi₀.symm))
  have hIsolatedβ : ∀ j : Fin k,
      fqToBar E (zLambda E lam (R j)) ≠ zLambdaBar E lam (e i₀).val := by
    intro j hEq
    rw [hi₀] at hEq
    apply hNonRat
    have hβFix : (fqToBar E (zLambda E lam (R j))) ^ E.q =
        fqToBar E (zLambda E lam (R j)) := fqToBar_frob_fixed E _
    rw [hEq] at hβFix
    exact hβFix
  have key : ((gd.mult (e i₀).val : ℕ) : Fqbar E) = 0 :=
    FrobDescentHelpers.isolated_coeff_zero_of_pf_sum
      (α := fun i => zLambdaBar E lam (e i).val)
      (c := fun i => ((gd.mult (e i).val : ℕ) : Fqbar E))
      (β := fun j => fqToBar E (zLambda E lam (R j)))
      (d := d) i₀ hIsolatedα hIsolatedβ S hCard
      hDisjointα hDisjointβ hVanish
  rw [hi₀] at key
  exact key

/-- Reindex a support sum through an explicit `Fin` enumeration. -/
private theorem sum_support_eq_sum_fin
    {α : Type*} [AddCommMonoid α]
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {n : ℕ} (e : Fin n ≃ {x // x ∈ gd.support})
    (f : GeomPoint E → α) :
    (∑ i : Fin n, f (e i).val) = ∑ Q ∈ gd.support, f Q := by
  classical
  refine Finset.sum_bij
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (e i).val)
    ?_ ?_ ?_ ?_
  · intro i _
    exact (e i).property
  · intro i _ j _ hEq
    exact e.injective (Subtype.ext hEq)
  · intro Q hQ
    refine ⟨e.symm ⟨Q, hQ⟩, Finset.mem_univ _, ?_⟩
    simp
  · intro i _
    rfl

/-- Choose many rational intercepts avoiding all geometric support poles and
all auxiliary rational poles. -/
private theorem exists_goodIntercepts_avoiding_geom_and_rational_poles
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    {M : ℕ} (R : Fin M → ZMod E.q × ZMod E.q)
    (lam : ZMod E.q)
    (hGood : 2 * (gd.support.card + M) ≤ (goodIntercepts E lam).card) :
    ∃ S0 : Finset (ZMod E.q),
      S0 ⊆ goodIntercepts E lam ∧
      gd.support.card + M ≤ S0.card ∧
      (∀ μ ∈ S0, ∀ Q ∈ gd.support,
        fqToBar E μ ≠ zLambdaBar E lam Q) ∧
      (∀ μ ∈ S0, ∀ j : Fin M,
        μ ≠ zLambda E lam (R j)) := by
  classical
  set G := goodIntercepts E lam
  set badGeom : Finset (ZMod E.q) :=
    G.filter (fun μ => ∃ Q ∈ gd.support, fqToBar E μ = zLambdaBar E lam Q)
  set badRat : Finset (ZMod E.q) :=
    G.filter (fun μ => ∃ j : Fin M, μ = zLambda E lam (R j))
  set bad := badGeom ∪ badRat
  set S0 := G \ bad
  have hBadGeom_card : badGeom.card ≤ gd.support.card := by
    let f : {μ // μ ∈ badGeom} → {Q // Q ∈ gd.support} := fun μ =>
      ⟨Classical.choose (Finset.mem_filter.mp μ.property).2,
        (Classical.choose_spec (Finset.mem_filter.mp μ.property).2).1⟩
    have hf : Function.Injective f := by
      intro μ ν hEq
      apply Subtype.ext
      have hμeq :
          fqToBar E μ.val = zLambdaBar E lam (f μ).val :=
        (Classical.choose_spec (Finset.mem_filter.mp μ.property).2).2
      have hνeq :
          fqToBar E ν.val = zLambdaBar E lam (f ν).val :=
        (Classical.choose_spec (Finset.mem_filter.mp ν.property).2).2
      have hQ : (f μ).val = (f ν).val := congrArg Subtype.val hEq
      have hbar : fqToBar E μ.val = fqToBar E ν.val := by
        rw [hμeq, hνeq, hQ]
      exact fqToBar_injective E hbar
    have hcard := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe] using hcard
  have hBadRat_card : badRat.card ≤ M := by
    have hSub : badRat ⊆ (Finset.univ : Finset (Fin M)).image
        (fun j => zLambda E lam (R j)) := by
      intro μ hμ
      rcases (Finset.mem_filter.mp hμ).2 with ⟨j, hμj⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hμj.symm⟩
    calc badRat.card
        ≤ ((Finset.univ : Finset (Fin M)).image
            (fun j => zLambda E lam (R j))).card := Finset.card_le_card hSub
      _ ≤ M := by
        exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hBad_card : bad.card ≤ gd.support.card + M := by
    calc bad.card
        ≤ badGeom.card + badRat.card := Finset.card_union_le _ _
      _ ≤ gd.support.card + M := Nat.add_le_add hBadGeom_card hBadRat_card
  have hBad_sub : bad ⊆ G := by
    intro μ hμ
    rcases Finset.mem_union.mp hμ with hμ | hμ
    · exact (Finset.mem_filter.mp hμ).1
    · exact (Finset.mem_filter.mp hμ).1
  refine ⟨S0, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    exact (Finset.mem_sdiff.mp hμ).1
  · have hCard : S0.card = G.card - bad.card := by
      exact Finset.card_sdiff_of_subset hBad_sub
    rw [hCard]
    omega
  · intro μ hμ Q hQ hEq
    have hμG : μ ∈ G := (Finset.mem_sdiff.mp hμ).1
    have hμNotBad : μ ∉ bad := (Finset.mem_sdiff.mp hμ).2
    exact hμNotBad (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hμG, ⟨Q, hQ, hEq⟩⟩))
  · intro μ hμ j hEq
    have hμG : μ ∈ G := (Finset.mem_sdiff.mp hμ).1
    have hμNotBad : μ ∉ bad := (Finset.mem_sdiff.mp hμ).2
    exact hμNotBad (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hμG, ⟨j, hEq⟩⟩))

/-- Numeric threshold supplying enough rational samples for the Frobenius
partial-fraction descent. This is the remaining Hasse/valid-pairs arithmetic
obligation after the geometric and sampling plumbing is in place. -/
private theorem frob_sampling_validPairs_threshold (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D) (k : ℕ)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) +
        21 * (D.degE + k + 2) + 72) :
    6 * E.q * (2 * (gd.support.card + (k + 1)) + gd.support.card) + 1
      ≤ (validPairs E).card := by
  classical
  set n := E.points.card with hn_def
  set d := D.degE with hd_def
  set M := d + k + 1 with hM_def
  set s := gd.support.card with hs_def
  have hSC : s ≤ d := by
    rw [hs_def, hd_def]
    calc gd.support.card
        = ∑ _ ∈ gd.support, 1 := by simp
      _ ≤ ∑ Q ∈ gd.support, gd.mult Q :=
          Finset.sum_le_sum (fun Q hQ => gd.mult_pos_on_support Q hQ)
      _ ≤ D.degE := gd.accounting_le_degE
  have hM_pos : 0 < M := by
    rw [hM_def]
    omega
  have hN_flat : n ≥ 31 * M + 110 := by
    have h := hLargeQ
    have hEq : 2 * (5 * (D.degE + k + 2) + 3) +
            21 * (D.degE + k + 2) + 72
          = 31 * M + 109 := by
      rw [hM_def, hd_def]
      ring
    rw [hEq] at h
    omega
  have hN141 : n ≥ 141 := by
    have hM1 : 1 ≤ M := Nat.succ_le_of_lt hM_pos
    omega
  have hQbound : E.q ≤ n + 2 + Nat.sqrt (4 * (n + 1)) := by
    simpa [n] using hasse_q_le_sharp_nat_of E hHW
  set r := Nat.sqrt (4 * (n + 1)) with hr_def
  have hSqrtSq : r * r ≤ 4 * (n + 1) := Nat.sqrt_le _
  have h_169n2 : 169 * n * n > 1296 * (n + 1) := by
    nlinarith [hN141, sq_nonneg n]
  have h_13n_18r : 13 * n > 18 * r := by
    have h_169n2' : 169 * n * n > 324 * (r * r) := by
      calc 169 * n * n > 1296 * (n + 1) := h_169n2
        _ = 324 * (4 * (n + 1)) := by ring
        _ ≥ 324 * (r * r) := Nat.mul_le_mul_left _ hSqrtSq
    have hSq : (13 * n) * (13 * n) > (18 * r) * (18 * r) := by
      have h1 : (13 * n) * (13 * n) = 169 * n * n := by ring
      have h2 : (18 * r) * (18 * r) = 324 * (r * r) := by ring
      rw [h1, h2]
      exact h_169n2'
    by_contra hle
    push_neg at hle
    have : (13 * n) * (13 * n) ≤ (18 * r) * (18 * r) :=
      Nat.mul_le_mul hle hle
    omega
  have h_18Mr_lt_13Mn : 18 * M * r < 13 * M * n := by
    have h := (Nat.mul_lt_mul_left hM_pos).2 h_13n_18r
    have h1 : M * (18 * r) = 18 * M * r := by ring
    have h2 : M * (13 * n) = 13 * M * n := by ring
    rwa [h1, h2] at h
  have h_107n_36M : 107 * n > 36 * M := by
    have h1 : 107 * n ≥ 107 * (31 * M + 110) :=
      Nat.mul_le_mul_left _ hN_flat
    have h2 : 107 * (31 * M + 110) = 3317 * M + 11770 := by ring
    have h3 : 3317 * M + 11770 > 36 * M := by omega
    linarith
  have h_tail : 36 * M + 18 * M * r < (13 * M + 107) * n := by
    have hsum : 36 * M + 18 * M * r < 107 * n + 13 * M * n := by
      omega
    have hEq : 107 * n + 13 * M * n = (13 * M + 107) * n := by ring
    rwa [hEq] at hsum
  have hMain : 18 * M * (n + 2 + r) + 3 * n < n * n := by
    have hPre : 18 * M * (n + 2 + r) + 3 * n < (31 * M + 110) * n := by
      have hL : 18 * M * (n + 2 + r) + 3 * n =
          18 * M * n + 3 * n + (36 * M + 18 * M * r) := by ring
      have hR : (31 * M + 110) * n =
          18 * M * n + 3 * n + (13 * M + 107) * n := by ring
      rw [hL, hR]
      omega
    have hTop : (31 * M + 110) * n ≤ n * n := by
      exact Nat.mul_le_mul_right n hN_flat
    exact lt_of_lt_of_le hPre hTop
  have hQMain : 18 * M * E.q + 1 ≤ n * n - 3 * n := by
    have hq : 18 * M * E.q ≤ 18 * M * (n + 2 + r) :=
      Nat.mul_le_mul_left (18 * M) hQbound
    omega
  have hSampleCount :
      6 * E.q * (2 * (s + (k + 1)) + s) + 1 ≤ 18 * M * E.q + 1 := by
    have hT : 2 * (s + (k + 1)) + s ≤ 3 * M := by
      rw [hM_def]
      omega
    calc 6 * E.q * (2 * (s + (k + 1)) + s) + 1
        ≤ 6 * E.q * (3 * M) + 1 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left (6 * E.q) hT) 1
      _ = 18 * M * E.q + 1 := by ring
  have hValid := card_validPairs_lb E
  calc
    6 * E.q * (2 * (gd.support.card + (k + 1)) + gd.support.card) + 1
        = 6 * E.q * (2 * (s + (k + 1)) + s) + 1 := by rw [hs_def]
    _ ≤ 18 * M * E.q + 1 := hSampleCount
    _ ≤ n * n - 3 * n := hQMain
    _ ≤ (validPairs E).card := by
      simpa [n, ECSetup.numAffine] using hValid

/--
Frobenius descent core for the rational-support branch.

PROVIDED SOLUTION
Choose a slope `lam` with `exists_slope_zLambdaBar_isolated_non_rational`,
so the non-rational support point `Q` has a unique non-rational pole in the
single variable `mu = zLambdaBar E lam A₀`. Reparameterise the bar-level
residue identity from `hAllZero` as a partial-fraction sum in `mu`.
After removing poles and denominator failures, the `hLargeQ` hypothesis gives
enough rational evaluation points. Apply
`FrobDescentHelpers.partial_fraction_coeff_zero` and read off the coefficient
at the isolated pole, which is `((gd.mult Q : ℕ) : Fqbar E)`.
-/
private theorem frob_descent_mult_zero_of_not_fixed (hHW : E.HasseBound)
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (_hDeg : D.degE < E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E D P B A₀ A₁ →
      logDerivCheckFn E D P k B m A₀ A₁ = 0)
    (hLargeQ : E.points.card >
        2 * (5 * (D.degE + k + 2) + 3) + 21 * (D.degE + k + 2) + 72)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support)
    (hNotFixed : frobGeomPoint E Q ≠ Q) :
    ((gd.mult Q : ℕ) : Fqbar E) = 0 := by
  classical
  let M : ℕ := k + 1
  let R : Fin M → ZMod E.q × ZMod E.q := Fin.cons (P.1, -P.2) B
  let m' : Fin M → ZMod E.q := Fin.cons (-1) (fun j => -m j)
  let N : ℕ := 2 * (gd.support.card + M)
  have hQuant :
      6 * E.q * (N + gd.support.card) + 1 ≤ (validPairs E).card := by
    have h := frob_sampling_validPairs_threshold E hHW D gd k hLargeQ
    simpa [N, M, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  obtain ⟨lam, hSep, hNonRat, hGood⟩ :=
    exists_slope_zLambdaBar_isolated_non_rational_with_good_intercepts
      E D gd Q hQ hNotFixed N hQuant
  obtain ⟨S0, hS0Good, hS0Card, hS0AvoidQ, hS0AvoidR⟩ :=
    exists_goodIntercepts_avoiding_geom_and_rational_poles E D gd R lam
      (by simpa [N, M] using hGood)
  set S : Finset (Fqbar E) := S0.image (fqToBar E)
  have hS_card_eq : S.card = S0.card := by
    change (S0.image (fqToBar E)).card = S0.card
    exact Finset.card_image_of_injective (f := fqToBar E) S0 (fqToBar_injective E)
  set n : ℕ := gd.support.card
  set e : Fin n ≃ {x // x ∈ gd.support} := gd.support.equivFin.symm
  set i₀ : Fin n := e.symm ⟨Q, hQ⟩
  have hi₀ : (e i₀).val = Q := by
    simp [i₀, e]
  have hCard : n + M ≤ S.card := by
    rw [hS_card_eq]
    simpa [n, M] using hS0Card
  have hDisjointα : ∀ μ ∈ S, ∀ i : Fin n,
      μ ≠ zLambdaBar E lam (e i).val := by
    intro μ hμ i
    change μ ∈ S0.image (fqToBar E) at hμ
    rcases Finset.mem_image.mp hμ with ⟨μ0, hμ0, rfl⟩
    exact hS0AvoidQ μ0 hμ0 (e i).val (e i).property
  have hDisjointβ : ∀ μ ∈ S, ∀ j : Fin M,
      μ ≠ fqToBar E (zLambda E lam (R j)) := by
    intro μ hμ j hEq
    change μ ∈ S0.image (fqToBar E) at hμ
    rcases Finset.mem_image.mp hμ with ⟨μ0, hμ0, rfl⟩
    exact hS0AvoidR μ0 hμ0 j (fqToBar_injective E hEq)
  have hVanish : ∀ μ ∈ S,
      (∑ i : Fin n,
          ((gd.mult (e i).val : ℕ) : Fqbar E) *
            (μ - zLambdaBar E lam (e i).val)⁻¹) +
        (∑ j : Fin M,
            fqToBar E (m' j) *
            (μ - fqToBar E (zLambda E lam (R j)))⁻¹) = 0 := by
    intro μ hμ
    change μ ∈ S0.image (fqToBar E) at hμ
    rcases Finset.mem_image.mp hμ with ⟨μ0, hμ0, rfl⟩
    have hPF := geom_pf_identity_at_good_intercept E hHW D hDnz gd P B m
      hAllZero hLargeQ lam μ0 (hS0Good hμ0)
      (by
        intro Q' hQ'
        exact sub_ne_zero.mpr (hS0AvoidQ μ0 hμ0 Q' hQ'))
      (by
        intro j
        exact sub_ne_zero.mpr (fun hEq =>
          hS0AvoidR μ0 hμ0 j (fqToBar_injective E hEq)))
    rw [sum_support_eq_sum_fin E D gd e
      (fun Q' => ((gd.mult Q' : ℕ) : Fqbar E) *
        (fqToBar E μ0 - zLambdaBar E lam Q')⁻¹)]
    simpa [R, m', M] using hPF
  exact frob_descent_isolate_mult_of_pf_sum E D gd lam Q hSep hNonRat
    e i₀ hi₀ R (fun j => fqToBar E (m' j)) S hCard
    hDisjointα hDisjointβ hVanish

/-- **Rationality of the geometric support under `hAllZero`.** The all-zero
hypothesis on `logDerivCheckFn` over rational defined non-vertical pairs
forces every `Q ∈ gd.support` to have `F_q`-rational coordinates. -/
private theorem gd_support_rational_of_hAllZero (hHW : E.HasseBound)
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
    (_hDnz : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (gd : GeometricDivisorData E msg.toD)
    (_hAllZero :
      ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E msg.toD stmt.target stmt.bases A₀ A₁ →
        logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
          (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0) :
    gd_support_rational E msg.toD gd := by
  classical
  rw [gd_support_rational_iff_frob_fixed]
  intro Q hQ
  by_contra hNotFixed
  have hDegLt : msg.toD.degE < E.q := lt_of_le_of_lt _hDeg _hd
  have hMultNZ : ((gd.mult Q : ℕ) : Fqbar E) ≠ 0 :=
    gd_mult_fqbar_ne_zero E msg.toD gd hDegLt Q hQ
  exact absurd
    (frob_descent_mult_zero_of_not_fixed E hHW msg.toD gd hDegLt
      _hDnz stmt.target stmt.bases (fun i => msg.m (hkm ▸ i))
      _hAllZero _hLargeQ Q hQ hNotFixed)
    hMultNZ

private theorem geometric_residue_match (hHW : E.HasseBound)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
    gd_support_rational_of_hAllZero E hHW stmt hd msg hDeg hkm hSmooth hTargetOnE
      hBasesOnE hLargeQ hNoNegP hDnz gd hAllZero
  -- Step 2: splitsOnE follows from rational support.
  have hSplit : splitsOnE E msg.toD :=
    splitsOnE_of_gd_support_rational E msg.toD hDnz gd hRat
  -- Step 3: σ-matching from rational support + chord-sum identity.
  -- (No longer threads _hDenomNZ; the per-A₀ obstruction is absorbed via badDenomA0
  -- inside `sigma_data_of_gd_support_rational`.)
  have hσ := sigma_data_of_gd_support_rational E hHW stmt hd msg hDeg hkm hTargetOnE
    hBasesOnE hLargeQ hNoNegP hDnz gd hRat hAllZero
  exact ⟨hSplit, hσ⟩

/--
Geometric σ-matching theorem (used by
`extractor_of_logDerivCheck_all_zero_geometric_general`).

The proof is a thin wrapper around the residue-matching helper
`geometric_residue_match`; see that helper for the mathematical
content and `PROVIDED SOLUTION` outline.
-/
private theorem geometric_sigma_matching (hHW : E.HasseBound)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
  geometric_residue_match E hHW stmt hd hd2 msg hDeg hkm hSmooth
    hTargetOnE hBasesOnE hLargeQ hAdm hNoNegP hAllZero

set_option maxHeartbeats 800000 in
theorem extractor_of_logDerivCheck_all_zero_geometric_general (hHW : E.HasseBound)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
    geometric_sigma_matching E hHW stmt hd hd2 msg hDeg hkm hSmooth
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
theorem extractor_of_logDerivCheck_all_zero_geometric (hHW : E.HasseBound)
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q) (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q) (hDeg : msg.toD.degE ≤ stmt.degBound)
    (hkm : stmt.k = msg.k)
    (hSmooth : 4 * E.curveA ^ 3 + 27 * E.curveB ^ 2 ≠ 0)
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
  · exact extractor_of_logDerivCheck_all_zero_geometric_general E hHW stmt hd hd2
      msg hDeg hkm hSmooth hTargetOnE hBasesOnE hLargeQ hAdm hNegP hAllZero

end Divisor
