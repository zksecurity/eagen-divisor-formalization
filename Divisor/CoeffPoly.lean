/-
  Divisor/CoeffPoly.lean

  Computable polynomial representation over `ZMod q`, used as the
  underlying value for the computable Eagen construction.  Mathlib's
  `Polynomial` API is in `noncomputable section`, so it cannot host
  `#eval`-style evaluation.

  `CoeffPoly q` wraps `List (ZMod q)` with index = degree (head =
  constant term).  Trailing zeros are tolerated; equality of
  representation is via `coeff` not list equality.

  Bridges to mathlib `Polynomial` are noncomputable theorems; the
  `CoeffPoly` operations themselves are plain `def`s.
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic

namespace Divisor

/-- A computable polynomial over `ZMod q`, stored as a coefficient
    list (index 0 = constant term). -/
structure CoeffPoly (q : ℕ) where
  coeffs : List (ZMod q)
  deriving Repr, DecidableEq

namespace CoeffPoly

variable {q : ℕ}

/-- Coefficient at index `n`; out-of-range coefficients are `0`. -/
def coeff (p : CoeffPoly q) (n : ℕ) : ZMod q :=
  p.coeffs[n]?.getD 0

/-- Length of the stored coefficient list (≥ natDegree + 1 in general). -/
def length (p : CoeffPoly q) : ℕ := p.coeffs.length

/-- The zero polynomial. -/
def zero : CoeffPoly q := ⟨[]⟩

instance : Zero (CoeffPoly q) := ⟨zero⟩

@[simp] theorem coeffs_zero : (0 : CoeffPoly q).coeffs = [] := rfl
@[simp] theorem coeff_zero (n : ℕ) : (0 : CoeffPoly q).coeff n = 0 := by
  show (([] : List (ZMod q))[n]?).getD 0 = 0
  simp

/-- The constant polynomial `c`. -/
def C (c : ZMod q) : CoeffPoly q := ⟨[c]⟩

@[simp] theorem coeff_C_zero (c : ZMod q) : (C c).coeff 0 = c := by
  unfold coeff C; rfl
@[simp] theorem coeff_C_succ (c : ZMod q) (n : ℕ) : (C c).coeff (n + 1) = 0 := by
  unfold coeff C; rfl

/-- The variable `X`. -/
def X : CoeffPoly q := ⟨[0, 1]⟩

@[simp] theorem coeff_X_zero : (X : CoeffPoly q).coeff 0 = 0 := by
  unfold coeff X; rfl
@[simp] theorem coeff_X_one : (X : CoeffPoly q).coeff 1 = 1 := by
  unfold coeff X; rfl
@[simp] theorem coeff_X_succ_succ (n : ℕ) : (X : CoeffPoly q).coeff (n + 2) = 0 := by
  unfold coeff X
  show (([0, 1] : List (ZMod q))[n + 2]?).getD 0 = 0
  simp

/-- Componentwise addition, padding the shorter list with zeros. -/
def add : CoeffPoly q → CoeffPoly q → CoeffPoly q
  | ⟨as⟩, ⟨bs⟩ => ⟨addList as bs⟩
where
  addList : List (ZMod q) → List (ZMod q) → List (ZMod q)
    | [], bs => bs
    | as, [] => as
    | a :: as', b :: bs' => (a + b) :: addList as' bs'

instance : Add (CoeffPoly q) := ⟨add⟩

/-- Pointwise negation. -/
def neg (p : CoeffPoly q) : CoeffPoly q := ⟨p.coeffs.map (-·)⟩

instance : Neg (CoeffPoly q) := ⟨neg⟩

instance : Sub (CoeffPoly q) := ⟨fun p q => p + (-q)⟩

/-- Scalar multiplication by a `ZMod q` value. -/
def smul (c : ZMod q) (p : CoeffPoly q) : CoeffPoly q :=
  ⟨p.coeffs.map (c * ·)⟩

instance : SMul (ZMod q) (CoeffPoly q) := ⟨smul⟩

/-- Polynomial multiplication via convolution. -/
def mul : CoeffPoly q → CoeffPoly q → CoeffPoly q
  | ⟨as⟩, ⟨bs⟩ => ⟨mulList as bs⟩
where
  mulList : List (ZMod q) → List (ZMod q) → List (ZMod q)
    | [], _ => []
    | _, [] => []
    | a :: as', bs =>
        add.addList (bs.map (a * ·)) (0 :: mulList as' bs)

instance : Mul (CoeffPoly q) := ⟨mul⟩

/-- The unit `1`. -/
def one : CoeffPoly q := ⟨[1]⟩

instance : One (CoeffPoly q) := ⟨one⟩

@[simp] theorem coeff_one_zero : (1 : CoeffPoly q).coeff 0 = 1 := by
  show (one : CoeffPoly q).coeff 0 = 1
  unfold coeff one; rfl

/-- Evaluation at a point, via Horner's method.  Folds from the
    leading coefficient downward: `result = result * x + coeff`. -/
def eval (p : CoeffPoly q) (x : ZMod q) : ZMod q :=
  p.coeffs.foldr (fun c acc => acc * x + c) 0

@[simp] theorem eval_zero (x : ZMod q) : (0 : CoeffPoly q).eval x = 0 := by
  unfold eval; simp [coeffs_zero]

@[simp] theorem eval_C (c : ZMod q) (x : ZMod q) : (C c).eval x = c := by
  unfold eval C; simp

@[simp] theorem eval_X (x : ZMod q) : (X : CoeffPoly q).eval x = x := by
  unfold eval X; simp

@[simp] theorem eval_one (x : ZMod q) : (1 : CoeffPoly q).eval x = 1 := by
  show (one : CoeffPoly q).eval x = 1
  unfold eval one; simp

/-- Synthetic division: returns the quotient `p / (X - C x₀)`.
    The (discarded) remainder is `p.eval x₀`.

    Closed-form: coefficient `n` of the quotient is
    `∑ j ∈ Icc (n+1) (length-1), x₀^(j - (n+1)) * p.coeff j`,
    matching mathlib's `Polynomial.coeff_divByMonic_X_sub_C`.

    Implementation: build the coefficient list directly via
    `List.range`, evaluating the closed-form sum at each index.
    Computable for `#eval`; bridges to mathlib become trivial. -/
def divXSubC (p : CoeffPoly q) (x₀ : ZMod q) : CoeffPoly q :=
  ⟨(List.range (p.coeffs.length - 1)).map fun n =>
    (Finset.Icc (n + 1) (p.coeffs.length - 1)).sum
      fun j => x₀ ^ (j - (n + 1)) * p.coeff j⟩

/-- Power. -/
def pow (p : CoeffPoly q) : ℕ → CoeffPoly q
  | 0 => 1
  | n + 1 => mul p (pow p n)

instance : HPow (CoeffPoly q) ℕ (CoeffPoly q) := ⟨pow⟩

/-! ## Bridges to mathlib `Polynomial`

These are noncomputable theorems used solely to relate the
computable `CoeffPoly` operations back to the existing
`Polynomial`-valued construction. -/

/-- Bridge: interpret a `CoeffPoly` as a mathlib `Polynomial`.  Sum
    of `monomial i (coeffs[i])` over `Finset.range p.coeffs.length`. -/
noncomputable def toPolynomial (p : CoeffPoly q) [Fact (Nat.Prime q)] :
    Polynomial (ZMod q) :=
  (Finset.range p.coeffs.length).sum
    (fun i => Polynomial.monomial i (p.coeff i))

variable [Fact (Nat.Prime q)]

/-- Coefficient of `toPolynomial p` agrees with `CoeffPoly.coeff`. -/
theorem toPolynomial_coeff (p : CoeffPoly q) (n : ℕ) :
    (toPolynomial p).coeff n = p.coeff n := by
  unfold toPolynomial
  rw [Polynomial.finset_sum_coeff]
  by_cases hn : n < p.coeffs.length
  · rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro i _ hin
      rw [Polynomial.coeff_monomial]
      exact if_neg hin
    · intro h; exact absurd (Finset.mem_range.mpr hn) h
  · push_neg at hn
    have hp : p.coeff n = 0 := by
      unfold coeff
      have := List.getElem?_eq_none (l := p.coeffs) (i := n) hn
      simp [this]
    rw [hp]
    apply Finset.sum_eq_zero
    intro i hi
    have hi_lt : i < p.coeffs.length := Finset.mem_range.mp hi
    rw [Polynomial.coeff_monomial]
    have hne : ¬ i = n := fun h => by
      rw [h] at hi_lt; exact absurd hi_lt hn.not_gt
    exact if_neg hne

/-- Evaluation bridge: `CoeffPoly.eval` matches `Polynomial.eval`. -/
theorem toPolynomial_eval (p : CoeffPoly q) (x : ZMod q) :
    (toPolynomial p).eval x = p.eval x := by
  unfold toPolynomial
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  -- Goal: ∑ i ∈ range length, coeff i * x^i = foldr ... 0 coeffs
  unfold CoeffPoly.eval
  -- Cast to the auxiliary statement for the underlying list, then
  -- prove by list induction.
  suffices h : ∀ (l : List (ZMod q)),
      (∑ i ∈ Finset.range l.length,
        ((⟨l⟩ : CoeffPoly q).coeff i) * x ^ i)
        = l.foldr (fun c acc => acc * x + c) 0 from h p.coeffs
  intro l
  induction l with
  | nil => simp
  | cons c cs ih =>
    -- (c :: cs).length = cs.length + 1 (defeq).
    show (∑ i ∈ Finset.range (cs.length + 1),
            (⟨c :: cs⟩ : CoeffPoly q).coeff i * x ^ i)
        = (cs.foldr (fun c acc => acc * x + c) 0) * x + c
    rw [Finset.sum_range_succ']
    have hcoeff0 : (⟨c :: cs⟩ : CoeffPoly q).coeff 0 = c := by
      show ((c :: cs : List (ZMod q))[0]?).getD 0 = c
      simp
    have hcoeffsucc : ∀ i, (⟨c :: cs⟩ : CoeffPoly q).coeff (i + 1)
        = (⟨cs⟩ : CoeffPoly q).coeff i := by
      intro i
      show ((c :: cs : List (ZMod q))[i + 1]?).getD 0
        = ((cs : List (ZMod q))[i]?).getD 0
      simp
    rw [hcoeff0, pow_zero, mul_one]
    have : (∑ i ∈ Finset.range cs.length,
              (⟨c :: cs⟩ : CoeffPoly q).coeff (i + 1) * x ^ (i + 1))
        = (∑ i ∈ Finset.range cs.length,
              (⟨cs⟩ : CoeffPoly q).coeff i * x ^ i) * x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeffsucc, pow_succ]
      ring
    rw [this, ih]

@[simp] theorem toPolynomial_zero : toPolynomial (0 : CoeffPoly q) = 0 := by
  unfold toPolynomial
  show (Finset.range (([] : List (ZMod q)).length)).sum _ = 0
  simp

@[simp] theorem toPolynomial_C (c : ZMod q) :
    toPolynomial (C c) = Polynomial.C c := by
  apply Polynomial.ext
  intro n
  rw [toPolynomial_coeff]
  match n with
  | 0 => simp
  | n + 1 => simp

@[simp] theorem toPolynomial_X :
    toPolynomial (X : CoeffPoly q) = Polynomial.X := by
  apply Polynomial.ext
  intro n
  rw [toPolynomial_coeff]
  match n with
  | 0 => simp [Polynomial.coeff_X]
  | 1 => simp [Polynomial.coeff_X]
  | n + 2 =>
    rw [coeff_X_succ_succ]
    rw [Polynomial.coeff_X]
    simp

/-! ### `add` bridge -/

/-- Coefficient of `add.addList`. -/
theorem coeff_addList (as bs : List (ZMod q)) (n : ℕ) :
    ((⟨add.addList as bs⟩ : CoeffPoly q).coeff n) =
      (⟨as⟩ : CoeffPoly q).coeff n + (⟨bs⟩ : CoeffPoly q).coeff n := by
  induction as generalizing bs n with
  | nil =>
    show (⟨add.addList [] bs⟩ : CoeffPoly q).coeff n
      = (⟨[]⟩ : CoeffPoly q).coeff n + (⟨bs⟩ : CoeffPoly q).coeff n
    show (((add.addList [] bs : List (ZMod q)))[n]?).getD 0
      = ((([] : List (ZMod q))[n]?).getD 0)
        + ((bs : List (ZMod q))[n]?).getD 0
    show ((bs : List (ZMod q))[n]?).getD 0
      = ((([] : List (ZMod q))[n]?).getD 0)
        + ((bs : List (ZMod q))[n]?).getD 0
    simp
  | cons a as' ih =>
    cases bs with
    | nil =>
      show (⟨add.addList (a :: as') []⟩ : CoeffPoly q).coeff n
        = (⟨a :: as'⟩ : CoeffPoly q).coeff n + (⟨[]⟩ : CoeffPoly q).coeff n
      show (((a :: as' : List (ZMod q)))[n]?).getD 0
        = ((a :: as' : List (ZMod q))[n]?).getD 0
          + ((([] : List (ZMod q))[n]?).getD 0)
      simp
    | cons b bs' =>
      cases n with
      | zero =>
        show (⟨add.addList (a :: as') (b :: bs')⟩ : CoeffPoly q).coeff 0
          = (⟨a :: as'⟩ : CoeffPoly q).coeff 0 + (⟨b :: bs'⟩ : CoeffPoly q).coeff 0
        show ((((a + b) :: add.addList as' bs' : List (ZMod q)))[0]?).getD 0
          = ((a :: as' : List (ZMod q))[0]?).getD 0
            + ((b :: bs' : List (ZMod q))[0]?).getD 0
        simp
      | succ k =>
        show (⟨add.addList (a :: as') (b :: bs')⟩ : CoeffPoly q).coeff (k + 1)
          = (⟨a :: as'⟩ : CoeffPoly q).coeff (k + 1)
            + (⟨b :: bs'⟩ : CoeffPoly q).coeff (k + 1)
        show ((((a + b) :: add.addList as' bs' : List (ZMod q)))[k + 1]?).getD 0
          = ((a :: as' : List (ZMod q))[k + 1]?).getD 0
            + ((b :: bs' : List (ZMod q))[k + 1]?).getD 0
        simp only [List.getElem?_cons_succ]
        exact ih bs' k

/-- Coefficient bridge for `add`. -/
@[simp] theorem coeff_add (p₁ p₂ : CoeffPoly q) (n : ℕ) :
    (p₁ + p₂).coeff n = p₁.coeff n + p₂.coeff n := by
  show (p₁.add p₂).coeff n = _
  obtain ⟨as⟩ := p₁
  obtain ⟨bs⟩ := p₂
  unfold add
  exact coeff_addList as bs n

theorem toPolynomial_add (p₁ p₂ : CoeffPoly q) :
    toPolynomial (p₁ + p₂) = toPolynomial p₁ + toPolynomial p₂ := by
  apply Polynomial.ext
  intro n
  rw [toPolynomial_coeff, Polynomial.coeff_add, toPolynomial_coeff,
      toPolynomial_coeff, coeff_add]

/-! ### `divXSubC` bridge

Synthetic division on `CoeffPoly` agrees with mathlib's
`Polynomial./ₘ (X − C x₀)`.  Since `divXSubC` is defined via the
closed-form coefficient sum that mathlib also produces
(`coeff_divByMonic_X_sub_C`), the bridge reduces to coefficient
equality plus a `length`-vs-`natDegree` argument. -/

/-- Coefficient formula for `divXSubC`. -/
theorem coeff_divXSubC (p : CoeffPoly q) (x₀ : ZMod q) (n : ℕ) :
    (p.divXSubC x₀).coeff n =
      if n < p.coeffs.length - 1 then
        (Finset.Icc (n + 1) (p.coeffs.length - 1)).sum
          fun j => x₀ ^ (j - (n + 1)) * p.coeff j
      else 0 := by
  show (((p.divXSubC x₀).coeffs)[n]?).getD 0 = _
  show (((List.range (p.coeffs.length - 1)).map
      (fun m => (Finset.Icc (m + 1) (p.coeffs.length - 1)).sum
        fun j => x₀ ^ (j - (m + 1)) * p.coeff j))[n]?).getD 0 = _
  by_cases hn : n < p.coeffs.length - 1
  · rw [if_pos hn, List.getElem?_map]
    have hlen : n < (List.range (p.coeffs.length - 1)).length := by
      rw [List.length_range]; exact hn
    rw [List.getElem?_eq_getElem hlen]
    simp [List.getElem_range]
  · push_neg at hn
    rw [if_neg hn.not_gt]
    have hlen : (List.range (p.coeffs.length - 1)).length ≤ n := by
      rw [List.length_range]; exact hn
    rw [List.getElem?_eq_none (l := (List.range (p.coeffs.length - 1)).map _)
      (i := n) (by rw [List.length_map]; exact hlen)]
    rfl

omit [Fact (Nat.Prime q)] in
/-- The `natDegree` of `toPolynomial p` is at most `p.coeffs.length - 1`. -/
theorem natDegree_toPolynomial_le (p : CoeffPoly q) [Fact (Nat.Prime q)] :
    (toPolynomial p).natDegree ≤ p.coeffs.length - 1 := by
  by_cases hL : p.coeffs.length = 0
  · have : p.coeffs = [] := List.length_eq_zero_iff.mp hL
    -- p = ⟨[]⟩ = 0 → natDegree = 0.
    have hp : p = 0 := by cases p; cases this; rfl
    rw [hp]; simp
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [toPolynomial_coeff]
    unfold coeff
    have : p.coeffs.length ≤ n := by omega
    have hnone := List.getElem?_eq_none (l := p.coeffs) (i := n) this
    simp [hnone]

/-- divXSubC bridge: matches mathlib's `/ₘ (X - C x₀)`. -/
theorem toPolynomial_divXSubC (p : CoeffPoly q) (x₀ : ZMod q) :
    toPolynomial (p.divXSubC x₀)
      = toPolynomial p /ₘ (Polynomial.X - Polynomial.C x₀) := by
  apply Polynomial.ext
  intro n
  rw [toPolynomial_coeff, Polynomial.coeff_divByMonic_X_sub_C,
      coeff_divXSubC]
  -- Both sides are sums of `x₀^(j - (n+1)) * p.coeff j` over a finite
  -- index range.  The CoeffPoly side caps at `p.coeffs.length - 1`;
  -- mathlib caps at `(toPolynomial p).natDegree`.  Differing trailing
  -- indices contribute zero since `p.coeff j = 0` outside the support.
  by_cases hn : n < p.coeffs.length - 1
  · rw [if_pos hn]
    -- Need: ∑ j ∈ Icc (n+1) (p.coeffs.length-1), ...
    --     = ∑ j ∈ Icc (n+1) (toPolynomial p).natDegree, x₀^... * (toPolynomial p).coeff j
    -- Replace coeff via toPolynomial_coeff and extend/shrink the range
    -- by noting out-of-support coeffs are 0.
    refine (Finset.sum_subset_zero_on_sdiff
      (s₁ := Finset.Icc (n + 1) (toPolynomial p).natDegree)
      (s₂ := Finset.Icc (n + 1) (p.coeffs.length - 1)) ?_ ?_ ?_).symm
    · -- Icc (n+1) natDeg ⊆ Icc (n+1) (length-1).
      intro j hj
      rw [Finset.mem_Icc] at *
      refine ⟨hj.1, ?_⟩
      exact hj.2.trans (natDegree_toPolynomial_le p)
    · -- On the difference, x₀^... * coeff = 0.
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hj
      have hcoeff : p.coeff j = 0 := by
        by_contra hne
        apply hj.2
        rw [Finset.mem_Icc]
        refine ⟨hj.1.1, ?_⟩
        -- p.coeff j ≠ 0 ⇒ j < length, so j ≤ length - 1.
        -- Bound j via natDegree(toPolynomial p).
        have hjlen : j < p.coeffs.length := by
          by_contra h
          push_neg at h
          have hnone := List.getElem?_eq_none (l := p.coeffs) (i := j) h
          unfold coeff at hne
          simp [hnone] at hne
        -- Actually we need j ≤ natDegree(toPolynomial p), not just j < length.
        -- toPolynomial_coeff says coeff_eq via Polynomial.
        have : (toPolynomial p).coeff j ≠ 0 := by
          rw [toPolynomial_coeff]; exact hne
        exact Polynomial.le_natDegree_of_ne_zero this
      rw [hcoeff, mul_zero]
    · intro j _
      rw [toPolynomial_coeff]
  · push_neg at hn
    rw [if_neg hn.not_gt]
    -- Need: 0 = ∑ j ∈ Icc (n+1) (toPolynomial p).natDegree, x₀^... * coeff j
    -- The Icc has natDeg ≤ p.coeffs.length - 1 ≤ n, so n+1 > natDeg, so Icc is empty.
    have hnd : (toPolynomial p).natDegree ≤ p.coeffs.length - 1 :=
      natDegree_toPolynomial_le p
    have hIcc : Finset.Icc (n + 1) (toPolynomial p).natDegree = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hIcc, Finset.sum_empty]

end CoeffPoly

end Divisor
