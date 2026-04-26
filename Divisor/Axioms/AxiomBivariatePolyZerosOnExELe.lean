/-
  Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean

  Bound on the number of `F_q`-zeros of a 4-variate polynomial on
  `E × E`, used by `Divisor/ClearedFullPoly.lean` and downstream.

  Originally axiomatised under the DKL'14 Claim 7.2 + Hartshorne
  (Bezout) provenance; now proven as a *theorem* from
  `Divisor.hasse_weil` + Mathlib via the elementary fiber-counting
  route in `Divisor/Route1AttemptLW.lean` and
  `Divisor/CurveEvalZerosHelper.lean` (reduce mod `Y² = X³+AX+B` →
  `α(X) + β(X)·Y` → univariate Schwartz–Zippel).

  Provenance retained for documentation:
  * Dvir, Kollar, Lovett, "Variety Evasive Sets",
    Comput. Complex. 23 (2014) — Claim 7.2, p. 10.
    PDF: `axioms/papers/DvirKollarLovett14.pdf`.
  * Hartshorne, *Algebraic Geometry*, GTM 52,
    Theorem I.7.7 (Bezout). PDF: `axioms/papers/Hartshorne-AG.pdf`
    (cited textbook; standard citation).
  * Ellenberg, Oberlin, Tao, "The Kakeya set and maximal
    conjectures for algebraic varieties over finite fields",
    Mathematika 56 (2010) — Lemma A.3, p. 23 (alternative).
    PDF: `axioms/papers/EllenbergOberlinTao10.pdf`.
  * Lang & Weil, "Number of Points of Varieties in Finite Fields",
    Am. J. Math. 76 (1954), Theorem 1, p. 819.
    PDF: `axioms/papers/lang-weil-1954.pdf`.

  Full provenance at `axioms/bivariate_poly_zeros_on_ExE_le.md`.
-/
import Divisor.FourVarPoly
import Divisor.Route1AttemptLW

namespace Divisor

variable (E : ECSetup)

/-- **DKL'14 Claim 7.2 + Hartshorne (Bezout) corollary on `E × E`.**

    For a 4-variate polynomial `f ∈ F_q[X₀, Y₀, X₁, Y₁]` of total
    degree at most `D` that is **not identically zero on `E × E`**
    (witnessed by the existence of a point where it evaluates
    non-zero), the set of `F_q`-point pairs `(A₀, A₁) ∈ E × E` at
    which `f(A₀, A₁) = 0` has cardinality at most `9 · D · q`.

    **Primary reference (verbatim), DKL'14 Claim 7.2 (p. 10):**

    > Let V ∈ V_{n,d,k}. Then |V ∩ F^n| ≤ d · |F|^k.

    Here `V_{n,d,k}` denotes varieties in `F̄^n` of dimension `k` and
    degree `d` defined over `F`.

    **Primary reference (verbatim), Hartshorne I.7.7 (Bezout):**

    > Let Y, Z be distinct curves in P², having degrees d, e
    > respectively. Then `Y · Z = ∑_P i(Y, Z; P) = de`.

    The hypersurface-meets-surface generalisation in `P^N` follows by
    standard intersection theory (Hartshorne I.7).

    **Derivation chain.** Let `V := {f = 0} ∩ (E × E)`.
    1. `f` defines a hypersurface `H_f ⊂ A⁴` of degree `≤ D`.
    2. `E × E` ⊂ `P² × P²` is a surface (dimension 2) of degree `9`
       under the Segre embedding into `P⁸` (each `E ⊂ P²` has
       degree 3; product surface has degree `3·3 = 9`).
    3. By Bezout (Hartshorne I.7.7, hypersurface-meets-surface form),
       the intersection `V = H_f ∩ (E × E)` has dimension `≤ 1` and
       degree at most `9 · D`.
    4. By DKL'14 Claim 7.2 with `(n, d, k) = (8, 9D, 1)` (or by the
       elementary curve point-count of EOT'10 Lemma A.3),
       `|V(F_q)| ≤ 9·D·q`.

    **Alternative: EOT'10 Lemma A.3 (verbatim, p. 23):**

    > Let V ⊂ ℙ^N be a projective variety of dimension n and degree
    > d. Then |V(F)| ≤ d(|F|+1)^n.

    With `n = 1`, `d ≤ 9D`: `|V(F_q)| ≤ 9D·(q+1) ≤ 9D·q` for the
    sufficiently large `q ≥ 5` enforced by `ECSetup`.

    **Replaces an unsound prior axiom.** A previous form claimed
    `2·(dX + dY)·|E|` based only on bi-x-degree (`bi_x_degree_le`),
    which was Sage-falsified by counterexamples such as
    `f = Y₀ + Y₁` over `y² = x³ + 1` over `F_5` (axiom predicted 0,
    actual count is 5). The cause is that the X-bi-degree alone
    ignores the Y-degree contribution; total degree captures it.

    **Status: proven.** This declaration was previously an `axiom`;
    it is now a `theorem` discharged by
    `Divisor.Route1LW.bivariate_poly_zeros_on_ExE_le_thm_lw`. The
    only project-level axiom in its dependency chain is
    `Divisor.hasse_weil`. -/
theorem bivariate_poly_zeros_on_ExE_le
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q :=
  Divisor.Route1LW.bivariate_poly_zeros_on_ExE_le_thm_lw E f D hDeg hNonzero

end Divisor
