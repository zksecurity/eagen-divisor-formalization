/-
  Divisor/Axioms.lean

  Classical results from algebraic geometry and number theory
  that are used in the probability bounds. These are well-established
  theorems whose proofs require infrastructure beyond current Mathlib.

  Only results from published textbooks / classical papers are axiomatized here.
  Results specific to Bassa's analysis are proved in the files where they appear.
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

/-- `IsPrincipal E coeffs` means the divisor `Σ coeffs(P) · (P)` on `E`
    arises as `div(f)` for some nonzero `f ∈ F_q(E)×`.

    Left opaque: the concrete definition would quantify over function-field
    elements (not formalized here). The characterization below pins it down
    to two concrete conditions on `coeffs`. -/
opaque IsPrincipal (E : ECSetup) (coeffs : ECPoint E.q → ℤ) : Prop

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

/-! ## Theorem 2: Principal Divisor of a Rational Function on E

    The **`CoordRingElt.has_principal_divisor`** statement (Silverman
    AEC III Cor 3.5, p. 63, specialised) used to live here as an
    axiom. It is now a theorem proved in
    `Divisor/HasPrincipalDivisor.lean` from the constructive multiplicity
    `betaConstructive` (see `Divisor/BetaConstructive.lean`) together
    with the narrow Abel-theorem axiom
    `CoordRingElt.divisor_group_sum_zero`, which captures the group-
    sum-zero direction of Cor 3.5 (derived in Silverman from
    Prop 3.4(a,e), p. 61-62). The pole-at-∞ identity
    `Σ β(P) = D.degE` (which would correspond to the degree-zero
    direction of Cor 3.5) is **not** recorded as an axiom — it fails
    when `normPoly E D` does not split over `F_q`; see
    `docs/divisor-degree-axiom-bug.md`. Only the unconditional bound
    `∑ β(P) ≤ D.degE` (proved directly from `betaConstructive`'s
    definition) is used downstream. -/

/-! ## Hasse-Weil Bound (Hasse 1936, Weil 1948)

|#E(F_q) - (q + 1)| ≤ 2·√q, equivalently (#E - q - 1)² ≤ 4q.

Citation: Silverman AEC Theorem V.1.1 (p.138), "Hasse". A fundamental
result in arithmetic geometry, proved by Hasse for elliptic curves
and generalized by Weil to higher genus curves.

**Integer-squared form.** Stated as `((numPoints - q - 1) : ℤ)² ≤ 4q`
because `2·Nat.sqrt q = 2·⌊√q⌋` is strictly smaller than `⌊2·√q⌋` in
general (e.g. at `q = 7`, `2·⌊√7⌋ = 4` while `⌊2·√7⌋ = 5`). The
squared form is the sharp integer statement and implies both
one-sided bounds when needed.

**Textbook statement (verbatim), Silverman AEC Theorem V.1.1, p.138:**

> "Theorem 1.1. (Hasse) Let E/F_q be an elliptic curve defined over a
> finite field. Then
>     |#E(F_q) − q − 1| ≤ 2√q."

Our `(·)² ≤ 4q` form is equivalent: `|x| ≤ 2√q  ↔  x² ≤ 4q` for `x ∈ ℤ`. -/
axiom hasse_weil :
  ((E.numPoints : ℤ) - E.q - 1)^2 ≤ 4 * E.q

/-! The specialized DKL / variety Schwartz-Zippel bound on E × E is
    stated in `Divisor/LogDeriv.lean` as
    `logDerivCheckFn_zero_set_bound`, because it references
    `logDerivCheckFn` which is defined there. It replaces the earlier
    generic `variety_sz_on_ExE` axiom whose `hBiDegree : True`
    side-condition was a soundness hole.
-/

end Divisor
