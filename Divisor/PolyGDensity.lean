/-
  Divisor/PolyGDensity.lean

  Density argument for `polyG` vanishing on `E × E`.

  Main theorem (`polyG_zero_on_nonvertical_of_defined`):
  if `polyG` vanishes on all non-vertical pairs satisfying a predicate
  `defined`, and if the defined non-vertical subset is dense enough
  (i.e., for each fixed `A₀`, the number of defined non-vertical `A₁`
  exceeds `2 · (resultantX E (polyGPoly A₀)).natDegree`), then `polyG`
  vanishes on ALL non-vertical pairs of `E × E`.

  The proof uses the polynomial form `polyGPoly` from `PolyGBridge.lean`
  and the zero-count bound `card_zeros_on_E_le` from
  `CubicIntersection.lean`.
-/
import Divisor.PolyGBridge

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Core density lemma for bivariate polynomials on E -/

/-- If the zero set of a bivariate polynomial `f` on `E.points` exceeds
    `2 · (resultantX E f).natDegree`, then `f %ₘ curveEqPoly E = 0`
    and hence `bivEval f` vanishes on all of `E.points`. -/
theorem bivEval_zero_on_E_of_many_zeros
    (f : (ZMod E.q)[X][X])
    (hCard : (E.points.filter (fun p => bivEval f p = 0)).card
             > 2 * (resultantX E f).natDegree) :
    ∀ p ∈ E.points, bivEval f p = 0 := by
  suffices h : f %ₘ curveEqPoly E = 0 by
    intro p hp
    rw [bivEval_eq_modByMonic_on_E E f hp, h]
    unfold bivEval; simp
  by_contra hNZ
  have hBound := card_zeros_on_E_le E f hNZ
  omega

/-! ## Resultant degree bound for `polyGPoly` -/

/-- The resultant of `polyGPoly` has natDegree ≤ `5 · (d + K) + 3`. -/
theorem resultantX_polyGPoly_natDegree_le
    {d K : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin K → ZMod E.q × ZMod E.q) (m : Fin K → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (polyGPoly (E := E) Q β R m A₀)).natDegree
      ≤ 5 * (d + K) + 3 := by
  have hN : (polyGPoly (E := E) Q β R m A₀).natDegree ≤ 2 * ((d + K) / 2) + 1 := by
    have := polyGPoly_natDegree_le E Q β R m A₀
    omega
  have hM := InnerDegLe_polyGPoly E Q β R m A₀
  have hRes := resultantX_natDegree_le_of_InnerDegLe (E := E)
    (polyGPoly (E := E) Q β R m A₀) (d + K) ((d + K) / 2) hM hN
  omega

/-! ## Main density theorem for `polyG` -/

/-- **Density argument for `polyG`.**

    If `polyG` vanishes on all non-vertical pairs `(A₀, A₁)` satisfying
    a predicate `defined`, and if for each `A₀ ∈ E.points` the set of
    defined non-vertical `A₁`'s exceeds
    `2 · (resultantX E (polyGPoly A₀)).natDegree`,
    then `polyG` vanishes on ALL non-vertical pairs of `E × E`.

    The "defined" predicate is abstract: in practice it captures the
    condition that the slope-denominators (line-evaluation denominators)
    are all nonzero, but the theorem works for any predicate satisfying
    the density condition. -/
theorem polyG_zero_on_nonvertical_of_defined
    {d K : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin K → ZMod E.q × ZMod E.q) (m : Fin K → ZMod E.q)
    (defined : (ZMod E.q × ZMod E.q) → (ZMod E.q × ZMod E.q) → Prop)
    (hDefined : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      defined A₀ A₁ →
      polyG E Q β R m A₀ A₁ = 0)
    (hDense : ∀ A₀ ∈ E.points,
      (E.points.filter (fun A₁ => A₀.1 ≠ A₁.1 ∧ defined A₀ A₁)).card
        > 2 * (resultantX E (polyGPoly (E := E) Q β R m A₀)).natDegree) :
    ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      polyG E Q β R m A₀ A₁ = 0 := by
  intro A₀ A₁ hA₀ hA₁ _hNV
  -- Step 1: the zero set of polyG(A₀, ·) on E.points is large.
  have hSub : E.points.filter (fun A₁ => A₀.1 ≠ A₁.1 ∧ defined A₀ A₁)
              ⊆ E.points.filter (fun A₁ => polyG E Q β R m A₀ A₁ = 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hDefined A₀ x hA₀ hx.1 hx.2.1 hx.2.2⟩
  have hMany : (E.points.filter (fun A₁ => polyG E Q β R m A₀ A₁ = 0)).card
               > 2 * (resultantX E (polyGPoly (E := E) Q β R m A₀)).natDegree :=
    lt_of_lt_of_le (hDense A₀ hA₀) (Finset.card_le_card hSub)
  -- Step 2: rewrite in terms of bivEval and apply density lemma.
  have hBivSub : E.points.filter (fun A₁ => polyG E Q β R m A₀ A₁ = 0)
                 ⊆ E.points.filter (fun p => bivEval (polyGPoly (E := E) Q β R m A₀) p = 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by rw [bivEval_polyGPoly]; exact hx.2⟩
  have hBivMany : (E.points.filter
      (fun p => bivEval (polyGPoly (E := E) Q β R m A₀) p = 0)).card
      > 2 * (resultantX E (polyGPoly (E := E) Q β R m A₀)).natDegree :=
    lt_of_lt_of_le hMany (Finset.card_le_card hBivSub)
  have hAllZero := bivEval_zero_on_E_of_many_zeros E
    (polyGPoly (E := E) Q β R m A₀) hBivMany
  rw [← bivEval_polyGPoly E Q β R m A₀ A₁]
  exact hAllZero A₁ hA₁

end Divisor
