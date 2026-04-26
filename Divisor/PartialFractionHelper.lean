/-
  Divisor/PFHelper.lean
  Partial fraction / sum-of-residues helper lemmas
-/
import Mathlib

open Polynomial Finset

/-- **Partial fraction identity (3 simple roots).** For three distinct
elements x₀, x₁, x₂ in a field K, any polynomial f of degree ≤ 1 satisfies
∑ᵢ f(xᵢ) / ∏_{j≠i} (xᵢ - xⱼ) = 0. -/
theorem pf_affine_sum_zero {K : Type*} [Field K]
    (x₀ x₁ x₂ c d : K)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    (c * x₀ + d) / ((x₀ - x₁) * (x₀ - x₂)) +
    (c * x₁ + d) / ((x₁ - x₀) * (x₁ - x₂)) +
    (c * x₂ + d) / ((x₂ - x₀) * (x₂ - x₁)) = 0 := by
  grind

/-- **Quadratic partial fraction.** For three distinct elements,
∑ᵢ xᵢ² / ∏_{j≠i} (xᵢ - xⱼ) = 1. -/
theorem pf_quadratic_sum_one {K : Type*} [Field K]
    (x₀ x₁ x₂ : K)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    x₀ ^ 2 / ((x₀ - x₁) * (x₀ - x₂)) +
    x₁ ^ 2 / ((x₁ - x₀) * (x₁ - x₂)) +
    x₂ ^ 2 / ((x₂ - x₀) * (x₂ - x₁)) = 1 := by
  grind +qlia

/-
**General partial fraction with 4-variable numerator.** For three distinct
elements and a numerator f(x) = a*x³ + b*x² + c*x + d, the Lagrange sum
∑ᵢ f(xᵢ)/∏_{j≠i}(xᵢ-xⱼ) equals a*(x₀+x₁+x₂) + b
(the coefficient of x² in f, adjusted by the leading term if deg = 3).
-/
theorem pf_cubic_sum {K : Type*} [Field K]
    (x₀ x₁ x₂ a b c d : K)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    (a * x₀^3 + b * x₀^2 + c * x₀ + d) / ((x₀ - x₁) * (x₀ - x₂)) +
    (a * x₁^3 + b * x₁^2 + c * x₁ + d) / ((x₁ - x₀) * (x₁ - x₂)) +
    (a * x₂^3 + b * x₂^2 + c * x₂ + d) / ((x₂ - x₀) * (x₂ - x₁))
    = a * (x₀ + x₁ + x₂) + b := by
  grind

/-! **Partial fractions: f/g sum at 3 roots with external denominator.**
For three distinct elements x₀, x₁, x₂ and f(x)/h(x) with deg(f) ≤ 1 and
h(xᵢ) ≠ 0:
∑ᵢ f(xᵢ) / (h(xᵢ) * ∏_{j≠i}(xᵢ-xⱼ))
= -∑_{roots α of h} f(α)/(h'(α) * chord_cubic(α))
(sum of all residues = 0 identity).

This is too complex to state abstractly; we'll use it pointwise instead.

**Key identity for the logDerivTerm decomposition**: on E with the chord
parametrization, the numerator of logDerivTerm decomposes as
φ(x) = 2y · D_chord'(x) - b(x) · chord_cubic'(x)
where D_chord(x) = a(x) - b(x)(λx+μ). -/