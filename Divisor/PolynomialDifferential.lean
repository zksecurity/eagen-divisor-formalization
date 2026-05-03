/-
  Divisor/PolynomialDifferential.lean

  `Differential` instance for the polynomial ring `K[T]` over a field
  `K`, with the canonical formal derivative as the derivation.

  This is the bridge piece between mathlib's `Polynomial.derivative`
  (a function-level operation on `K[T]`) and `Differential.deriv`
  (a typeclass-level derivation). Future axiom-discharge work for
  `Polynomial.resultant_logDeriv_at_split_specialization_of_pos_natDegree`
  needs this bridge to apply the proved Galois theorem
  `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
  to the resultant setting.
-/
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.FieldTheory.Differential.Basic

namespace Polynomial

variable (K : Type*) [Field K]

/-- The canonical `Differential` instance on `K[T]`: the formal derivative
`Polynomial.derivative` as a derivation. -/
noncomputable instance instDifferentialPoly : Differential (Polynomial K) where
  deriv := (derivative' (R := K)).restrictScalars ℤ

/-- The canonical `Differential.deriv` on `K[T]` agrees with
`Polynomial.derivative`. -/
@[simp]
theorem deriv_eq_derivative (p : Polynomial K) :
    Differential.deriv p = derivative p := by
  rfl

end Polynomial
