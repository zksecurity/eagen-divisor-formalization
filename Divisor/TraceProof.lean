/-
  Divisor/TraceProof.lean

  Helper lemma for `polyG_zero_trace_formula` proof.
  Does NOT import ExtractorBridge to avoid circular dependency.
-/
import Divisor.PolyGTraceFormula
import Divisor.PolyGDensity
import Divisor.Soundness
import Divisor.DivisorPrincipal
import Divisor.Protocol

open Polynomial Finset Classical

namespace Divisor

variable {E : ECSetup}

/-- **polyG vanishes at a fully defined pair in Fin.cons form.**
    Parameterised over an arbitrary β_fun (the existential from
    `CoordRingElt.exists_divisor_multiplicity` / `has_principal_divisor`). -/
theorem polyG_zero_at_defined_fincons
    (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (hSplit : normPoly_splits_over_Fq E D)
    (hAccount : (∑ P ∈ E.points, β_fun P) =
                  (normPoly E D).natDegree)
    (P : ZMod E.q × ZMod E.q) {k : ℕ}
    (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points) (hNV : A₀.1 ≠ A₁.1)
    (hDef : logDerivCheckFnDefined E D P B A₀ A₁)
    (hQline : ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0)
    (hCheck : logDerivCheckFn E D P k B m A₀ A₁ = 0) :
    polyG E (zerosAt E D)
      (fun k' => ((multAt E β_fun D k' : ℕ) : ZMod E.q))
      (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) (fun j => -m j))
      A₀ A₁ = 0 := by
  -- Extract individual conditions from hDef
  unfold logDerivCheckFnDefined logDerivCheckFnDenom at hDef
  set lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2 with hLamDef
  set L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2 with hLDef
  set x₂ := lam ^ 2 - A₀.1 - A₁.1 with hx₂Def
  set y₂ := lam * x₂ + (A₀.2 - lam * A₀.1) with hy₂Def
  -- Factor out individual non-zero conditions from the product
  have hProdNZ := hDef
  have hBlineProd : (univ : Finset (Fin k)).prod (fun j => L.eval (B j).1 (B j).2) ≠ 0 :=
    right_ne_zero_of_mul hProdNZ
  have h7 : L.eval P.1 (-P.2) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have hLeftOf7 := left_ne_zero_of_mul (left_ne_zero_of_mul hProdNZ)
  have h6 : 3 * x₂ ^ 2 + E.curveA - 2 * lam * y₂ ≠ 0 :=
    right_ne_zero_of_mul hLeftOf7
  have hLeftOf6 := left_ne_zero_of_mul hLeftOf7
  have h5 : 3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf6
  have hLeftOf5 := left_ne_zero_of_mul hLeftOf6
  have h4 : 3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2 ≠ 0 :=
    right_ne_zero_of_mul hLeftOf5
  have hLeftOf4 := left_ne_zero_of_mul hLeftOf5
  have h3 : D.eval x₂ y₂ ≠ 0 := right_ne_zero_of_mul hLeftOf4
  have hLeftOf3 := left_ne_zero_of_mul hLeftOf4
  have h2 : D.eval A₁.1 A₁.2 ≠ 0 := right_ne_zero_of_mul hLeftOf3
  have h1 : D.eval A₀.1 A₀.2 ≠ 0 := left_ne_zero_of_mul hLeftOf3
  -- hDen for chord_sum_eq_residue_sum
  have hDen : ∀ pt : ZMod E.q × ZMod E.q,
      pt = A₀ ∨ pt = A₁ ∨ pt = (x₂, y₂)
      → 3 * pt.1 ^ 2 + E.curveA - 2 * lam * pt.2 ≠ 0 := by
    rintro pt (rfl | rfl | rfl) <;> assumption
  -- hBline
  have hBline : ∀ j : Fin k, L.eval (B j).1 (B j).2 ≠ 0 := by
    intro j hj; exact hBlineProd (prod_eq_zero (mem_univ j) hj)
  -- Apply the existing bridge theorem
  exact polyG_zero_at_defined E D hDnz β_fun hβsup hβcov hSplit hAccount
    P B m A₀ A₁ hA₀ hA₁ hNV h1 h2 h3 hQline hDen h7 hBline hCheck

end Divisor
