/-
  Divisor/FourVarPoly.lean — 4-variate polynomial framework (minimal)

  Scaffolding for the Lang-Weil-on-E×E axiom
  (`Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`). Models a
  polynomial in `X₀, Y₀, X₁, Y₁` via `MvPolynomial (Fin 4) (ZMod q)`
  with variable assignment `0 = X₀, 1 = Y₀, 2 = X₁, 3 = Y₁`.

  The plan (`docs/bivariate-sz-paper-faithful.md`) will extend this
  file during Phases 2-4 with `clearedFullPoly` construction,
  evaluation lemmas, identity, and the bi-x-degree bound theorem.

  Representation note: the plan originally proposed nested
  `(ZMod q)[X][X][X][X]` layers. We switch to `MvPolynomial (Fin 4)`
  here because Mathlib provides `degreeOf` directly, giving a clean
  `bi_x_degree_le` definition without an ad-hoc recursion on layers.
-/
import Divisor.DefsPre
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

open MvPolynomial

namespace Divisor

/-- 4-variate polynomial ring over `ZMod q`.

    Variable assignment:
    * `0 = X₀` (x-coordinate of first E-point)
    * `1 = Y₀` (y-coordinate of first E-point)
    * `2 = X₁` (x-coordinate of second E-point)
    * `3 = Y₁` (y-coordinate of second E-point) -/
abbrev FourVarPoly (q : ℕ) := MvPolynomial (Fin 4) (ZMod q)

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- Evaluate `f : FourVarPoly q` at a pair of plane points
    `(A₀, A₁) ∈ (ZMod q × ZMod q) × (ZMod q × ZMod q)`. -/
noncomputable def bivEval₂ (f : FourVarPoly q)
    (A₀ A₁ : ZMod q × ZMod q) : ZMod q :=
  MvPolynomial.eval (fun i : Fin 4 =>
    match i with
    | ⟨0, _⟩ => A₀.1
    | ⟨1, _⟩ => A₀.2
    | ⟨2, _⟩ => A₁.1
    | ⟨3, _⟩ => A₁.2) f

/-- The Weierstrass curve relation `Y₀² = X₀³ + A·X₀ + B` on the
    `A₀`-coordinates, as an `MvPolynomial (Fin 4)`. -/
noncomputable def curveEq₀ (E : ECSetup) : FourVarPoly E.q :=
  X 1 ^ 2 - (X 0 ^ 3 + C E.curveA * X 0 + C E.curveB)

/-- The Weierstrass curve relation `Y₁² = X₁³ + A·X₁ + B` on the
    `A₁`-coordinates, as an `MvPolynomial (Fin 4)`. -/
noncomputable def curveEq₁ (E : ECSetup) : FourVarPoly E.q :=
  X 3 ^ 2 - (X 2 ^ 3 + C E.curveA * X 2 + C E.curveB)

/-- X-bi-degree bound. `bi_x_degree_le E f dX dY` asserts that the
    degree of `f` in the `X₀` variable is at most `dX` and its degree
    in the `X₁` variable is at most `dY`.

    The Lang-Weil axiom uses this to bound the `F_q`-zero count on
    `E × E`: after reducing `f` modulo the curve relations to linearise
    each `Y_i`, these X-degrees determine the degree of the plane curve
    cut out on `E × E`, hence the SZ-count via Hasse-Weil on each fibre. -/
def bi_x_degree_le (_E : ECSetup) (f : FourVarPoly _E.q) (dX dY : ℕ) : Prop :=
  f.degreeOf 0 ≤ dX ∧ f.degreeOf 2 ≤ dY

end Divisor
