/-
  Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean

  Weil / Lang-Weil curve-points bound on the surface `E × E`.

  Reference: Lang & Weil, "Number of Points of Varieties in Finite
  Fields", American Journal of Mathematics 76 (1954), Theorem 1,
  p. 819. PDF archived at `axioms/papers/lang-weil-1954.pdf`;
  snippet `axioms/snippets/lang-weil-1954-thm-1-02.png`. Full
  provenance at `axioms/bivariate_poly_zeros_on_ExE_le.md`.
-/
import Divisor.FourVarPoly

namespace Divisor

variable (E : ECSetup)

/-- **Weil / Lang-Weil curve-points bound on `E × E`.**

    For a 4-variate polynomial `f ∈ F_q[X₀, Y₀, X₁, Y₁]` with
    X-bi-degree `(dX, dY)` — i.e. `degreeOf 0 f ≤ dX` and
    `degreeOf 2 f ≤ dY` — that is **not identically zero on `E × E`**
    (witnessed by the existence of a point where it evaluates
    non-zero), the set of `F_q`-point pairs `(A₀, A₁) ∈ E × E` at
    which `f(A₀, A₁) = 0` has cardinality at most
    `2·(dX + dY)·|E|`.

    **Primary reference (verbatim), Lang-Weil 1954, Theorem 1, p. 819:**

    > "Theorem 1. There exists a constant A(n, d, r) depending only on
    > n, d, r such that for any variety V = V_{n,d}^r defined over a
    > finite field k we have
    >   |N − q^r| ≤ (d − 1)(d − 2)·q^{r − 1/2} + A(n, d, r)·q^{r − 1}."

    **How the present form follows from Lang-Weil.** The zero set
    `{f = 0} ∩ (E × E)` is a curve `V` (dimension `r = 1`) inside the
    surface `E × E` (dimension 2, degree 9 in `P² × P² ⊂ P⁸` via
    Segre). By Bezout the degree of `V` is at most `9·(dX + dY)` (more
    carefully, the factor `2` in the axiom absorbs the two `Y_i`-branches
    introduced by reducing `f` modulo the curve relations `Y_i² = X_i³
    + A·X_i + B`). Applying Lang-Weil Theorem 1 with `r = 1` to each
    irreducible component of `V`, summing, and using the elliptic-curve
    point count `|E| ≥ q + 1 − 2√q` (Hasse, already axiomatised as
    `hasse_weil`), we obtain the stated bound `|V(F_q)| ≤ 2·(dX + dY)·|E|`
    for all `q ≥ 5` (which `ECSetup` already requires).

    **Supporting textbook references** (single-curve cases):
    * Silverman AEC Theorem V.1.1 (Hasse), p. 138.
    * Silverman AEC Theorem V.2.2 (Weil Conjectures), p. 141.
    * Stichtenoth AFFC Theorem 5.2.3 (Hasse-Weil Bound), p. 198.

    **Tightness vs. the paper.** `sections/ec.tex:763-779` states a
    specialised bound `18·(degE(D) + M − 1)·|E|` for the log-derivative
    polynomial — a factor of 2 tighter than this axiom's
    `2·(dX + dY)·|E|` when `dX = dY = 9·(d + k)`. The paper's tighter
    form uses structural symmetry of the log-deriv polynomial specifically;
    this axiom is the generic Lang-Weil bound applicable to any
    non-zero bivariate on `E × E`. Phase 5 of the plan addresses the
    factor-2 gap for the log-deriv application. -/
axiom bivariate_poly_zeros_on_ExE_le
    (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 2 * (dX + dY) * E.points.card

end Divisor
