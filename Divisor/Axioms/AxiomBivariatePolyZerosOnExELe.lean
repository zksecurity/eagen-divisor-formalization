/-
  Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean

  Bound on the number of `F_q`-zeros of a 4-variate polynomial on
  `E × E`, used by `Divisor/ClearedFullPoly.lean` and downstream.

  Originally axiomatised under the DKL'14 Claim 7.2 + Hartshorne
  (Bezout) provenance; now proven as a *theorem* from
  `Divisor.hasse_weil` + Mathlib via the elementary fiber-counting
  route in `Divisor/BivariateZerosOnExE.lean` and
  `Divisor/CurveEvalZerosHelper.lean` (reduce mod `Y² = X³+AX+B` →
  `α(X) + β(X)·Y` → univariate norm-polynomial root count).

  Provenance retained for documentation:
  * Dvir, Kollar, Lovett, "Variety Evasive Sets",
    Comput. Complex. 23 (2014) — Claim 7.2, p. 10.
    PDF: `axioms/papers/DvirKollarLovett14.pdf`.
  * Hartshorne, *Algebraic Geometry*, GTM 52,
    Theorem I.7.7 (Bezout; cited textbook, not archived in this repo).
  * Ellenberg, Oberlin, Tao, "The Kakeya set and maximal
    conjectures for algebraic varieties over finite fields",
    Mathematika 56 (2010) — Lemma A.3, p. 23 (alternative).
    PDF: `axioms/papers/EllenbergOberlinTao10.pdf`.

  Full provenance at `axioms/bivariate_poly_zeros_on_ExE_le.md`.
-/
import Divisor.FourVarPoly
import Divisor.BivariateZerosOnExE

namespace Divisor

variable (E : ECSetup)

/-- **Bound on `|{(A₀, A₁) ∈ E × E : f(A₀, A₁) = 0}|`.**

    For a 4-variate polynomial `f ∈ F_q[X₀, Y₀, X₁, Y₁]` of total
    degree at most `D` that is **not identically zero on `E × E`**
    (witnessed by the existence of a point where it evaluates
    non-zero), the set of `F_q`-point pairs `(A₀, A₁) ∈ E × E` at
    which `f(A₀, A₁) = 0` has cardinality at most `9 · D · q`.

    **Status: proven.** This declaration was previously an `axiom`
    citing DKL'14 Claim 7.2 + Hartshorne I.7.7 (Bezout); it is now a
    `theorem` discharged by
    `Divisor.BivariateZerosOnExE.bivariate_poly_zeros_on_ExE_le_thm`.
    The only project-level axiom in its dependency chain is
    `Divisor.hasse_weil`.

    **Replaces an unsound prior axiom.** A previous form claimed
    `2·(dX + dY)·|E|` based only on bi-x-degree (`bi_x_degree_le`),
    which was Sage-falsified by counterexamples such as
    `f = Y₀ + Y₁` over `y² = x³ + 1` over `F_5` (axiom predicted 0,
    actual count is 5). The cause is that the X-bi-degree alone
    ignores the Y-degree contribution; total degree captures it. -/
theorem bivariate_poly_zeros_on_ExE_le
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q :=
  Divisor.BivariateZerosOnExE.bivariate_poly_zeros_on_ExE_le_thm E f D hDeg hNonzero

end Divisor
