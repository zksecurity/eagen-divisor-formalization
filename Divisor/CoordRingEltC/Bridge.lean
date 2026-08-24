/-
  Divisor/CoordRingEltC/Bridge.lean

  Bridges from the computable `CoordRingEltC` layer to the existing
  `Polynomial`-valued `CoordRingElt`.  The forward direction
  (`toCoordRingElt`) is noncomputable, but it lets every operation
  on `CoordRingEltC` be related to its `CoordRingElt` counterpart.
-/
import Divisor.CoordRingEltC
import Divisor.IncrementalConstruction

open Polynomial

namespace Divisor

namespace CoordRingEltC

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Bridge: interpret a `CoordRingEltC` as a `CoordRingElt` via
    `CoeffPoly.toPolynomial` on both components. -/
noncomputable def toCoordRingElt (D : CoordRingEltC q) : CoordRingElt q :=
  ⟨D.a.toPolynomial, D.b.toPolynomial⟩

@[simp] theorem toCoordRingElt_a (D : CoordRingEltC q) :
    D.toCoordRingElt.a = D.a.toPolynomial := rfl

@[simp] theorem toCoordRingElt_b (D : CoordRingEltC q) :
    D.toCoordRingElt.b = D.b.toPolynomial := rfl

/-! ### `divLin` bridge -/

theorem divLin_toCoordRingElt (D : CoordRingEltC q) (x₀ : ZMod q) :
    (D.divLin x₀).toCoordRingElt = D.toCoordRingElt.divLin x₀ := by
  unfold CoordRingEltC.divLin CoordRingElt.divLin
  show (⟨(D.a.divXSubC x₀).toPolynomial, (D.b.divXSubC x₀).toPolynomial⟩ : CoordRingElt q)
    = ⟨D.a.toPolynomial /ₘ (Polynomial.X - Polynomial.C x₀),
        D.b.toPolynomial /ₘ (Polynomial.X - Polynomial.C x₀)⟩
  congr 1 <;> exact CoeffPoly.toPolynomial_divXSubC _ x₀

/-! ### `curveX` bridge -/

/-- `CoeffPoly` representation of `curveX E = X³ + A·X + B`. -/
def curveX_coeff (curveA curveB : ZMod q) : CoeffPoly q :=
  ⟨[curveB, curveA, 0, 1]⟩

/-- `toPolynomial` of `curveX_coeff` is `X^3 + C A * X + C B`. -/
theorem toPolynomial_curveX_coeff (curveA curveB : ZMod q) :
    (curveX_coeff curveA curveB).toPolynomial
      = Polynomial.X^3 + Polynomial.C curveA * Polynomial.X + Polynomial.C curveB := by
  apply Polynomial.ext
  intro n
  rw [CoeffPoly.toPolynomial_coeff]
  -- Compute both sides at each n.
  match n with
  | 0 =>
    show (curveX_coeff curveA curveB).coeff 0 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  | 1 =>
    show (curveX_coeff curveA curveB).coeff 1 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  | 2 =>
    show (curveX_coeff curveA curveB).coeff 2 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow]
  | 3 =>
    show (curveX_coeff curveA curveB).coeff 3 = _
    simp [curveX_coeff, CoeffPoly.coeff, Polynomial.coeff_X_pow]
  | k + 4 =>
    show (curveX_coeff curveA curveB).coeff (k + 4) = _
    have h_left : (curveX_coeff curveA curveB).coeff (k + 4) = 0 := by
      simp [curveX_coeff, CoeffPoly.coeff]
    rw [h_left]
    have h_X3 : (Polynomial.X^3 : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_X_pow]; simp
    have h_AX : (Polynomial.C curveA * Polynomial.X : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]
      simp
    have h_B : (Polynomial.C curveB : Polynomial (ZMod q)).coeff (k + 4) = 0 := by
      rw [Polynomial.coeff_C]; simp
    rw [Polynomial.coeff_add, Polynomial.coeff_add, h_X3, h_AX, h_B]
    ring

/-- `toPolynomial (curveX_coeff E.curveA E.curveB) = curveX E`. -/
theorem toPolynomial_curveX_coeff_eq_curveX (E : ECSetup) :
    (curveX_coeff E.curveA E.curveB).toPolynomial = curveX E := by
  rw [toPolynomial_curveX_coeff]
  rfl

/-! ### `mul` bridge -/

theorem mul_toCoordRingElt (E : ECSetup) (D₁ D₂ : CoordRingEltC E.q) :
    (CoordRingEltC.mul E.curveA E.curveB D₁ D₂).toCoordRingElt
      = mulCoordRingElt E D₁.toCoordRingElt D₂.toCoordRingElt := by
  unfold CoordRingEltC.mul mulCoordRingElt
  -- LHS: (⟨[curveB, curveA, 0, 1]⟩ : CoeffPoly).toPolynomial = curveX E.
  -- We restate the lhs using curveX_coeff so the curveX_coeff bridge fires.
  show (⟨D₁.a * D₂.a + D₁.b * D₂.b * curveX_coeff E.curveA E.curveB,
          D₁.a * D₂.b + D₂.a * D₁.b⟩ : CoordRingEltC E.q).toCoordRingElt
      = ⟨D₁.toCoordRingElt.a * D₂.toCoordRingElt.a
            + D₁.toCoordRingElt.b * D₂.toCoordRingElt.b * curveX E,
          D₁.toCoordRingElt.a * D₂.toCoordRingElt.b
            + D₂.toCoordRingElt.a * D₁.toCoordRingElt.b⟩
  unfold toCoordRingElt
  congr 1
  · rw [CoeffPoly.toPolynomial_add, CoeffPoly.toPolynomial_mul,
        CoeffPoly.toPolynomial_mul, CoeffPoly.toPolynomial_mul,
        toPolynomial_curveX_coeff_eq_curveX]
  · rw [CoeffPoly.toPolynomial_add, CoeffPoly.toPolynomial_mul,
        CoeffPoly.toPolynomial_mul]

/-! ### Helper bridges built from foundations -/

/-- `toPolynomial (X - C c) = X - C c` in mathlib. -/
theorem toPolynomial_X_sub_C (c : ZMod q) :
    (CoeffPoly.X - CoeffPoly.C c : CoeffPoly q).toPolynomial
      = Polynomial.X - Polynomial.C c := by
  rw [CoeffPoly.toPolynomial_sub, CoeffPoly.toPolynomial_X,
      CoeffPoly.toPolynomial_C]

/-- `toPolynomial (-(C λ) * X - C μ) = -(C λ) * X - C μ` in mathlib. -/
theorem toPolynomial_nonvertical_chord (lam mu : ZMod q) :
    (-(CoeffPoly.C lam) * CoeffPoly.X - CoeffPoly.C mu : CoeffPoly q).toPolynomial
      = -(Polynomial.C lam) * Polynomial.X - Polynomial.C mu := by
  rw [CoeffPoly.toPolynomial_sub, CoeffPoly.toPolynomial_mul,
      CoeffPoly.toPolynomial_neg, CoeffPoly.toPolynomial_C,
      CoeffPoly.toPolynomial_X, CoeffPoly.toPolynomial_C]

/-- `toPolynomial (1 : CoeffPoly q) = 1` in mathlib. -/
theorem toPolynomial_one :
    ((1 : CoeffPoly q) : CoeffPoly q).toPolynomial = (1 : Polynomial (ZMod q)) := by
  apply Polynomial.ext
  intro n
  rw [CoeffPoly.toPolynomial_coeff]
  match n with
  | 0 => simp [Polynomial.coeff_one]
  | k + 1 =>
    show (1 : CoeffPoly q).coeff (k + 1) = (1 : Polynomial (ZMod q)).coeff (k + 1)
    show (CoeffPoly.one : CoeffPoly q).coeff (k + 1) = _
    show (([1] : List (ZMod q))[k + 1]?).getD 0 = _
    rw [show ([1] : List (ZMod q))[k + 1]? = none from rfl]
    simp [Polynomial.coeff_one]

/-- `toPolynomial (-1 : CoeffPoly q) = -1` in mathlib. -/
theorem toPolynomial_neg_one :
    ((-1 : CoeffPoly q) : CoeffPoly q).toPolynomial = (-1 : Polynomial (ZMod q)) := by
  show ((-(1 : CoeffPoly q)) : CoeffPoly q).toPolynomial = -1
  rw [CoeffPoly.toPolynomial_neg, toPolynomial_one]

/-! ### `chord` bridge -/

private theorem chord_toCoordRingElt_aux_vertical
    (E : ECSetup) (x : ZMod E.q) :
    ((⟨CoeffPoly.X - CoeffPoly.C x, 0⟩ : CoordRingEltC E.q).toCoordRingElt
      : CoordRingElt E.q)
      = ⟨Polynomial.X - Polynomial.C x, 0⟩ := by
  unfold toCoordRingElt
  show (⟨(CoeffPoly.X - CoeffPoly.C x).toPolynomial,
        (0 : CoeffPoly E.q).toPolynomial⟩ : CoordRingElt E.q)
    = ⟨Polynomial.X - Polynomial.C x, 0⟩
  have h_a : (CoeffPoly.X - CoeffPoly.C x : CoeffPoly E.q).toPolynomial
    = Polynomial.X - Polynomial.C x := toPolynomial_X_sub_C x
  have h_b : (0 : CoeffPoly E.q).toPolynomial = 0 := CoeffPoly.toPolynomial_zero
  rw [h_a, h_b]

private theorem chord_toCoordRingElt_aux_nonvertical
    (E : ECSetup) (lam mu : ZMod E.q) :
    ((⟨-(CoeffPoly.C lam) * CoeffPoly.X - CoeffPoly.C mu, -1⟩
      : CoordRingEltC E.q).toCoordRingElt : CoordRingElt E.q)
      = ⟨-(Polynomial.C lam) * Polynomial.X - Polynomial.C mu, -1⟩ := by
  unfold toCoordRingElt
  have h_a : (-(CoeffPoly.C lam) * CoeffPoly.X - CoeffPoly.C mu : CoeffPoly E.q).toPolynomial
    = -(Polynomial.C lam) * Polynomial.X - Polynomial.C mu :=
    toPolynomial_nonvertical_chord lam mu
  have h_b : ((-1 : CoeffPoly E.q)).toPolynomial = (-1 : Polynomial (ZMod E.q)) :=
    toPolynomial_neg_one
  rw [h_a, h_b]

theorem chord_toCoordRingElt (E : ECSetup) (P Q : ZMod E.q × ZMod E.q) :
    (CoordRingEltC.chord E.curveA P Q).toCoordRingElt
      = chordCoordRingElt E P Q := by
  by_cases hxx : P.1 = Q.1
  · by_cases hyy : P.2 = Q.2
    · by_cases h2t : P.2 = 0
      · have lhs : CoordRingEltC.chord E.curveA P Q
            = ⟨CoeffPoly.X - CoeffPoly.C P.1, 0⟩ := by
          unfold CoordRingEltC.chord
          rw [if_pos hxx, if_pos hyy, if_pos h2t]
        have rhs : chordCoordRingElt E P Q
            = ⟨Polynomial.X - Polynomial.C P.1, 0⟩ := by
          unfold chordCoordRingElt
          rw [dif_pos hxx, dif_pos hyy, if_pos h2t]
        rw [lhs, rhs]
        exact chord_toCoordRingElt_aux_vertical E P.1
      · have lhs : CoordRingEltC.chord E.curveA P Q
            = ⟨-(CoeffPoly.C ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹))
                * CoeffPoly.X
                - CoeffPoly.C (P.2 - ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹) * P.1),
              -1⟩ := by
          unfold CoordRingEltC.chord
          rw [if_pos hxx, if_pos hyy, if_neg h2t]
        have rhs : chordCoordRingElt E P Q
            = ⟨-(Polynomial.C ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹))
                * Polynomial.X
                - Polynomial.C (P.2 - ((3 * P.1 ^ 2 + E.curveA) * (2 * P.2)⁻¹) * P.1),
              -1⟩ := by
          unfold chordCoordRingElt
          rw [dif_pos hxx, dif_pos hyy, if_neg h2t]
        rw [lhs, rhs]
        exact chord_toCoordRingElt_aux_nonvertical E _ _
    · have lhs : CoordRingEltC.chord E.curveA P Q
          = ⟨CoeffPoly.X - CoeffPoly.C P.1, 0⟩ := by
        unfold CoordRingEltC.chord
        rw [if_pos hxx, if_neg hyy]
      have rhs : chordCoordRingElt E P Q
          = ⟨Polynomial.X - Polynomial.C P.1, 0⟩ := by
        unfold chordCoordRingElt
        rw [dif_pos hxx, dif_neg hyy]
      rw [lhs, rhs]
      exact chord_toCoordRingElt_aux_vertical E P.1
  · have lhs : CoordRingEltC.chord E.curveA P Q
        = ⟨-(CoeffPoly.C ((Q.2 - P.2) * (Q.1 - P.1)⁻¹))
            * CoeffPoly.X
            - CoeffPoly.C (P.2 - ((Q.2 - P.2) * (Q.1 - P.1)⁻¹) * P.1),
          -1⟩ := by
      unfold CoordRingEltC.chord
      rw [if_neg hxx]
    have rhs : chordCoordRingElt E P Q
        = ⟨-(Polynomial.C ((Q.2 - P.2) * (Q.1 - P.1)⁻¹))
            * Polynomial.X
            - Polynomial.C (P.2 - ((Q.2 - P.2) * (Q.1 - P.1)⁻¹) * P.1),
          -1⟩ := by
      unfold chordCoordRingElt
      rw [dif_neg hxx]
    rw [lhs, rhs]
    exact chord_toCoordRingElt_aux_nonvertical E _ _

/-- `toPolynomial (one : CoeffPoly q) = 1` — re-exposed at this namespace
    for downstream use. -/
theorem toCoordRingElt_one (q : ℕ) [Fact (Nat.Prime q)] :
    ((⟨1, 0⟩ : CoordRingEltC q).toCoordRingElt : CoordRingElt q)
      = ⟨1, 0⟩ := by
  unfold toCoordRingElt
  have h_a : (1 : CoeffPoly q).toPolynomial = 1 := toPolynomial_one
  have h_b : (0 : CoeffPoly q).toPolynomial = 0 := CoeffPoly.toPolynomial_zero
  rw [show ((⟨1, 0⟩ : CoordRingEltC q).a = 1) from rfl,
      show ((⟨1, 0⟩ : CoordRingEltC q).b = 0) from rfl, h_a, h_b]

end CoordRingEltC

end Divisor
