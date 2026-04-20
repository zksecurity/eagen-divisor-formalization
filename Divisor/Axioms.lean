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
    (Silverman, "Arithmetic of Elliptic Curves", Corollary 3.5)

A divisor `D = Σ n_P · (P)` on `E` is principal iff
  (1) `Σ n_P = 0` (degree zero), and
  (2) `Σ [n_P] · P = O` in the group law.

This is a foundational result in the theory of elliptic curves; it
characterizes which formal ℤ-linear combinations of points arise as the
divisor `div(f)` of some nonzero rational function `f ∈ F_q(E)×`.
-/

/-- `IsPrincipal E coeffs` means the divisor `Σ coeffs(P) · (P)` on `E`
    arises as `div(f)` for some nonzero `f ∈ F_q(E)×`.

    Left opaque: the concrete definition would quantify over function-field
    elements (not formalized here). The characterization below pins it down
    to two concrete conditions on `coeffs`. -/
opaque IsPrincipal (E : ECSetup) (coeffs : ECPoint E.q → ℤ) : Prop

/-- **Principal divisor characterization** (Silverman Cor 3.5, restated).

    A finitely-supported coefficient function `coeffs : ECPoint E.q → ℤ`
    is the divisor of some nonzero rational function on `E` iff the
    degree and group-sum conditions hold. -/
axiom principal_divisor_iff
    (coeffs : ECPoint E.q → ℤ)
    (hFinSupp : Set.Finite (Function.support coeffs)) :
    IsPrincipal E coeffs ↔
      (∑ P ∈ hFinSupp.toFinset, coeffs P = 0) ∧
      (ECPoint.weightedSum E hFinSupp.toFinset
          (fun P => ECPoint.zsmul E (coeffs P) P) = 0)

/-! ## Theorem 2: Principal Divisor of a Rational Function on E
    (Silverman, "Arithmetic of Elliptic Curves", Ch III, Prop 3.4 + Cor 3.5)

Every nonzero `D ∈ F_q(E)×` has a principal divisor supported on `D`'s
affine zeros with multiplicities summing to `D.degE`, together with
`-D.degE · (∞)`. Specialized to the coordinate-ring representation
`D = a(x) - b(x)·y` of a nonzero element of `F_q[E]` (i.e.,
`(a, b) ≠ (0, 0)`), this gives an integer multiplicity function `β` on
the affine points of `E` satisfying the principal-divisor conditions
(degree-zero + group-sum-zero) of `principal_divisor_iff`.
-/

/-- **Principal divisor of a nonzero `D ∈ F_q[E]`**
    (Silverman Ch III, Prop 3.4 + Cor 3.5).

    For a nonzero `D = a(x) - b(x)·y` (with `(a, b) ≠ (0, 0)`), the formal
    divisor `Σ β(P) · (P) − D.degE · (∞)` on `E` is principal, where `β`
    is the multiplicity of `D`'s affine zeros on `E`. The axiom packages
    this into:
    * `β`'s support is contained in `D`'s affine zeros on `E`.
    * `β`'s total weight equals `D.degE`.
    * The `β`-weighted group sum on `E.points` is `0`, which (after adding
      the `∞` term, contributing `0` via `zsmul·∞`) gives `principal_divisor_iff`'s
      group-sum-zero condition. -/
axiom CoordRingElt.has_principal_divisor
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) = D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) = 0

/-! ## Hasse-Weil Bound (Hasse 1936, Weil 1948)

|#E(F_q) - (q + 1)| <= 2 * sqrt(q)

A fundamental result in arithmetic geometry, proved by Hasse for
elliptic curves and generalized by Weil to higher genus curves.
-/
axiom hasse_weil_upper :
  E.numPoints ≤ E.q + 1 + 2 * Nat.sqrt E.q

axiom hasse_weil_lower :
  E.q + 1 - 2 * Nat.sqrt E.q ≤ E.numPoints

/-! The specialized DKL / variety Schwartz-Zippel bound on E × E is
    stated in `Divisor/LogDeriv.lean` as
    `logDerivCheckFn_zero_set_bound`, because it references
    `logDerivCheckFn` which is defined there. It replaces the earlier
    generic `variety_sz_on_ExE` axiom whose `hBiDegree : True`
    side-condition was a soundness hole.
-/

end Divisor
