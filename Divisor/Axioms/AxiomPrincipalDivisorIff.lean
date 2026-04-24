/-
  Divisor/Axioms/AxiomPrincipalDivisorIff.lean

  Characterisation of principal divisors on E.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Corollary III.3.5, p. 63. See `axioms/principal_divisor_iff.md` +
  `axioms/snippets/silverman-cor-III.3.5-principal-divisor-081.png`.
-/
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Theorem 1: Principal Divisor Characterization
    (Silverman AEC III Corollary 3.5, p. 63)

A divisor `D = Σ n_P · (P)` on `E` is principal iff
  (1) `Σ n_P = 0` (degree zero), and
  (2) `Σ [n_P] · P = O` in the group law.

Silverman derives this from Prop 3.4(a,e) (p. 61-62, the divisor-
class isomorphism `σ : Pic⁰(E) ≅ E`). It characterises which formal
ℤ-linear combinations of points arise as the divisor `div(f)` of
some nonzero rational function `f ∈ F_q(E)^×`.
-/

/-- **Principal divisor characterization** (Silverman AEC III Cor 3.5,
    p. 63, restated).

    A finitely-supported coefficient function `coeffs : ECPoint E.q → ℤ`
    is the divisor of some nonzero rational function on `E` iff the
    degree and group-sum conditions hold.

    **Textbook statement (verbatim), Silverman AEC Corollary III.3.5, p.63:**

    > "Corollary 3.5. Let E be an elliptic curve and let
    > D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
    >    Σ_{P ∈ E} n_P = 0   and   Σ_{P ∈ E} [n_P] P = O.
    > (Note that the first sum is of integers, while the second is
    > addition on E.)"

    Silverman's statement is over `E(K̄)`; the Lean form restricts to
    `ECPoint E.q` (F_q-rational points). F_q-descent follows from
    Silverman's Remark 3.5.1 + Exercise 2.13b (GK̄/K-invariance of the
    Abel-Jacobi exact sequence). -/
axiom principal_divisor_iff
    (coeffs : ECPoint E.q → ℤ)
    (hFinSupp : Set.Finite (Function.support coeffs)) :
    IsPrincipal E coeffs ↔
      (∑ P ∈ hFinSupp.toFinset, coeffs P = 0) ∧
      (ECPoint.weightedSum E hFinSupp.toFinset
          (fun P => ECPoint.zsmul E (coeffs P) P) = 0)

end Divisor
