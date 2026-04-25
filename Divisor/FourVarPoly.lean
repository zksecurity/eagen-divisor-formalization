/-
  Divisor/FourVarPoly.lean — 4-variate polynomial framework

  Scaffolding for the Lang-Weil-on-E×E axiom
  (`Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`). Models a
  polynomial in `X₀, Y₀, X₁, Y₁` via `MvPolynomial (Fin 4) (ZMod q)`
  with variable assignment `0 = X₀, 1 = Y₀, 2 = X₁, 3 = Y₁`.

  Defines the ring, `bivEval₂`, basic evaluation lemmas, X-bi-degree
  predicate, and convenience accessors. Extended by
  `Divisor/ClearedFullPoly.lean` with the 4-variate cleared polynomial.
-/
import Divisor.DefsPre
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial

namespace Divisor

/-- 4-variate polynomial ring over `ZMod q`.

    Variable assignment:
    * `0 = X₀` (x-coordinate of first E-point)
    * `1 = Y₀` (y-coordinate of first E-point)
    * `2 = X₁` (x-coordinate of second E-point)
    * `3 = Y₁` (y-coordinate of second E-point) -/
abbrev FourVarPoly (q : ℕ) := MvPolynomial (Fin 4) (ZMod q)

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- 4-variate point-evaluation map. Given pair `(A₀, A₁)`, substitute
    `X 0 ↦ A₀.1, X 1 ↦ A₀.2, X 2 ↦ A₁.1, X 3 ↦ A₁.2`. -/
noncomputable def bivEval₂Fun
    (A₀ A₁ : ZMod q × ZMod q) : Fin 4 → ZMod q := fun i =>
  match i with
  | ⟨0, _⟩ => A₀.1
  | ⟨1, _⟩ => A₀.2
  | ⟨2, _⟩ => A₁.1
  | ⟨3, _⟩ => A₁.2

/-- Evaluate `f : FourVarPoly q` at a pair of plane points
    `(A₀, A₁) ∈ (ZMod q × ZMod q) × (ZMod q × ZMod q)`. -/
noncomputable def bivEval₂ (f : FourVarPoly q)
    (A₀ A₁ : ZMod q × ZMod q) : ZMod q :=
  MvPolynomial.eval (bivEval₂Fun A₀ A₁) f

@[simp] theorem bivEval₂_C (c : ZMod q) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (C c : FourVarPoly q) A₀ A₁ = c := by
  simp [bivEval₂]

@[simp] theorem bivEval₂_X₀ (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (X 0 : FourVarPoly q) A₀ A₁ = A₀.1 := by
  simp [bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_Y₀ (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (X 1 : FourVarPoly q) A₀ A₁ = A₀.2 := by
  simp [bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_X₁ (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (X 2 : FourVarPoly q) A₀ A₁ = A₁.1 := by
  simp [bivEval₂, bivEval₂Fun]

@[simp] theorem bivEval₂_Y₁ (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (X 3 : FourVarPoly q) A₀ A₁ = A₁.2 := by
  simp [bivEval₂, bivEval₂Fun]

theorem bivEval₂_add (f g : FourVarPoly q) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (f + g) A₀ A₁ = bivEval₂ f A₀ A₁ + bivEval₂ g A₀ A₁ := by
  simp [bivEval₂]

theorem bivEval₂_sub (f g : FourVarPoly q) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (f - g) A₀ A₁ = bivEval₂ f A₀ A₁ - bivEval₂ g A₀ A₁ := by
  simp [bivEval₂]

theorem bivEval₂_mul (f g : FourVarPoly q) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (f * g) A₀ A₁ = bivEval₂ f A₀ A₁ * bivEval₂ g A₀ A₁ := by
  simp [bivEval₂]

theorem bivEval₂_neg (f : FourVarPoly q) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (-f) A₀ A₁ = -bivEval₂ f A₀ A₁ := by
  simp [bivEval₂]

theorem bivEval₂_pow (f : FourVarPoly q) (n : ℕ) (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (f ^ n) A₀ A₁ = bivEval₂ f A₀ A₁ ^ n := by
  simp [bivEval₂]

theorem bivEval₂_sum {α : Type*} (s : Finset α) (f : α → FourVarPoly q)
    (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (∑ i ∈ s, f i) A₀ A₁ = ∑ i ∈ s, bivEval₂ (f i) A₀ A₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bivEval₂]
  | @insert _ _ h ih =>
      rw [Finset.sum_insert h, bivEval₂_add, Finset.sum_insert h, ih]

theorem bivEval₂_prod {α : Type*} (s : Finset α) (f : α → FourVarPoly q)
    (A₀ A₁ : ZMod q × ZMod q) :
    bivEval₂ (∏ i ∈ s, f i) A₀ A₁ = ∏ i ∈ s, bivEval₂ (f i) A₀ A₁ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bivEval₂]
  | @insert _ _ h ih =>
      rw [Finset.prod_insert h, bivEval₂_mul, Finset.prod_insert h, ih]

/-- The Weierstrass curve relation `Y₀² = X₀³ + A·X₀ + B` on the
    `A₀`-coordinates, as an `MvPolynomial (Fin 4)`. -/
noncomputable def curveEq₀ (E : ECSetup) : FourVarPoly E.q :=
  X 1 ^ 2 - (X 0 ^ 3 + C E.curveA * X 0 + C E.curveB)

/-- The Weierstrass curve relation `Y₁² = X₁³ + A·X₁ + B` on the
    `A₁`-coordinates, as an `MvPolynomial (Fin 4)`. -/
noncomputable def curveEq₁ (E : ECSetup) : FourVarPoly E.q :=
  X 3 ^ 2 - (X 2 ^ 3 + C E.curveA * X 2 + C E.curveB)

/-- X-bi-degree bound. `bi_x_degree_le E f dX dY` asserts that the
    degree of `f` in the `X₀` variable is at most `dX` and its degree
    in the `X₁` variable is at most `dY`.

    The Lang-Weil axiom uses this to bound the `F_q`-zero count on
    `E × E`: after reducing `f` modulo the curve relations to linearise
    each `Y_i`, these X-degrees determine the degree of the plane curve
    cut out on `E × E`, hence the SZ-count via Hasse-Weil on each fibre. -/
def bi_x_degree_le (_E : ECSetup) (f : FourVarPoly _E.q) (dX dY : ℕ) : Prop :=
  f.degreeOf 0 ≤ dX ∧ f.degreeOf 2 ≤ dY

theorem bi_x_degree_le.add
    {E : ECSetup} {f g : FourVarPoly E.q} {dX dY : ℕ}
    (hf : bi_x_degree_le E f dX dY) (hg : bi_x_degree_le E g dX dY) :
    bi_x_degree_le E (f + g) dX dY :=
  ⟨(MvPolynomial.degreeOf_add_le _ _ _).trans (max_le hf.1 hg.1),
   (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le hf.2 hg.2)⟩

theorem bi_x_degree_le.sub
    {E : ECSetup} {f g : FourVarPoly E.q} {dX dY : ℕ}
    (hf : bi_x_degree_le E f dX dY) (hg : bi_x_degree_le E g dX dY) :
    bi_x_degree_le E (f - g) dX dY := by
  refine ⟨?_, ?_⟩
  · have := MvPolynomial.degreeOf_sub_le (0 : Fin 4) f g
    exact this.trans (max_le hf.1 hg.1)
  · have := MvPolynomial.degreeOf_sub_le (2 : Fin 4) f g
    exact this.trans (max_le hf.2 hg.2)

theorem bi_x_degree_le.mul
    {E : ECSetup} {f g : FourVarPoly E.q} {dX dY dX' dY' : ℕ}
    (hf : bi_x_degree_le E f dX dY) (hg : bi_x_degree_le E g dX' dY') :
    bi_x_degree_le E (f * g) (dX + dX') (dY + dY') :=
  ⟨(MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add hf.1 hg.1),
   (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add hf.2 hg.2)⟩

theorem bi_x_degree_le.neg
    {E : ECSetup} {f : FourVarPoly E.q} {dX dY : ℕ}
    (hf : bi_x_degree_le E f dX dY) :
    bi_x_degree_le E (-f) dX dY := by
  refine ⟨?_, ?_⟩
  · simpa [degreeOf] using hf.1
  · simpa [degreeOf] using hf.2

theorem bi_x_degree_le.C
    {E : ECSetup} (c : ZMod E.q) :
    bi_x_degree_le E (C c : FourVarPoly E.q) 0 0 := by
  refine ⟨?_, ?_⟩ <;> simp [degreeOf_C]

theorem bi_x_degree_le.X₀
    {E : ECSetup} :
    bi_x_degree_le E (X 0 : FourVarPoly E.q) 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [degreeOf_X]; simp
  · rw [degreeOf_X]; simp

theorem bi_x_degree_le.Y₀
    {E : ECSetup} :
    bi_x_degree_le E (X 1 : FourVarPoly E.q) 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [degreeOf_X]; simp
  · rw [degreeOf_X]; simp

theorem bi_x_degree_le.X₁
    {E : ECSetup} :
    bi_x_degree_le E (X 2 : FourVarPoly E.q) 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [degreeOf_X]; simp
  · rw [degreeOf_X]; simp

theorem bi_x_degree_le.Y₁
    {E : ECSetup} :
    bi_x_degree_le E (X 3 : FourVarPoly E.q) 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [degreeOf_X]; simp
  · rw [degreeOf_X]; simp

theorem bi_x_degree_le.mono
    {E : ECSetup} {f : FourVarPoly E.q} {dX dY dX' dY' : ℕ}
    (hf : bi_x_degree_le E f dX dY)
    (hX : dX ≤ dX') (hY : dY ≤ dY') :
    bi_x_degree_le E f dX' dY' :=
  ⟨hf.1.trans hX, hf.2.trans hY⟩

theorem bi_x_degree_le.pow
    {E : ECSetup} {f : FourVarPoly E.q} {dX dY : ℕ}
    (hf : bi_x_degree_le E f dX dY) (n : ℕ) :
    bi_x_degree_le E (f ^ n) (n * dX) (n * dY) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩ <;> simp [degreeOf_C]
  | succ n ih =>
      have := bi_x_degree_le.mul (E := E) ih hf
      simpa [pow_succ, Nat.succ_mul] using this

theorem bi_x_degree_le.sum
    {E : ECSetup} {α : Type*} (s : Finset α) (f : α → FourVarPoly E.q)
    {dX dY : ℕ} (hf : ∀ i ∈ s, bi_x_degree_le E (f i) dX dY) :
    bi_x_degree_le E (∑ i ∈ s, f i) dX dY := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_⟩ <;> simp [degreeOf_C]
  | @insert _ _ h ih =>
      rw [Finset.sum_insert h]
      refine bi_x_degree_le.add (hf _ (Finset.mem_insert_self _ _))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem bi_x_degree_le.prod_fin
    {E : ECSetup} {k : ℕ} (f : Fin k → FourVarPoly E.q)
    {dX dY : ℕ} (hf : ∀ i, bi_x_degree_le E (f i) dX dY) :
    bi_x_degree_le E (∏ i : Fin k, f i) (k * dX) (k * dY) := by
  classical
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩ <;> simp [degreeOf_C]
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      have h0 := hf 0
      have hrest := ih (fun i => f i.succ) (fun i => hf i.succ)
      have hmul := bi_x_degree_le.mul (E := E) h0 hrest
      have hrw : (n + 1) * dX = dX + n * dX := by ring
      have hrw' : (n + 1) * dY = dY + n * dY := by ring
      rw [hrw, hrw']; exact hmul

/-- **Y-linearity predicate.** A 4-variate polynomial `f` is Y-linear
    when it has degree ≤ 1 in both `Y₀` (variable 1) and `Y₁` (variable 3).

    Structurally, Y-linear polynomials have the form
    `a(X₀,X₂)·Y₀·Y₁ + b(X₀,X₂)·Y₀ + c(X₀,X₂)·Y₁ + d(X₀,X₂)`.

    On the curve `E : Y² = X³ + AX + B`, Y-linearity means that for
    each `(X₀, X₂)` pair, the equation `f = 0` restricted to the
    curve has at most 1 solution in `(Y₀, Y₁)` (vs. 2 in general),
    saving a factor of 2 in the Lang-Weil zero-count bound. -/
def bi_y_linear (_E : ECSetup) (f : FourVarPoly _E.q) : Prop :=
  f.degreeOf 1 ≤ 1 ∧ f.degreeOf 3 ≤ 1

theorem bi_y_linear.of_degreeOf {E : ECSetup} {f : FourVarPoly E.q}
    (h1 : f.degreeOf 1 ≤ 1) (h3 : f.degreeOf 3 ≤ 1) :
    bi_y_linear E f :=
  ⟨h1, h3⟩

end Divisor
