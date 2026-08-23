/-
  Divisor/SlopeChoice.lean

  Project-level slope choice for the Frobenius descent argument.
-/
import Divisor.CoeffDescent
import Divisor.FrobDescentHelpers
import Divisor.PolyGSlopeProjection
import Mathlib

open Finset Classical

namespace Divisor

variable (E : ECSetup)

private theorem geomPoint_eq_of_xy (Q₁ Q₂ : GeomPoint E)
    (hx : Q₁.x = Q₂.x) (hy : Q₁.y = Q₂.y) : Q₁ = Q₂ := by
  rcases Q₁ with ⟨_, _, _⟩
  rcases Q₂ with ⟨_, _, _⟩
  simp at hx hy
  subst hx
  subst hy
  rfl

private theorem sub_pow_char_fqbar (a b : Fqbar E) :
    (a - b) ^ E.q = a ^ E.q - b ^ E.q := by
  haveI : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩
  exact @sub_pow_char (Fqbar E) _ a b E.q ⟨E.hq_prime⟩ _

/-- Frobenius commutes with the projected coordinate `zLambdaBar`. -/
theorem zLambdaBar_frob
    (Q : GeomPoint E) (lam : ZMod E.q) :
    (zLambdaBar E lam Q) ^ E.q = zLambdaBar E lam (frobGeomPoint E Q) := by
  simp only [zLambdaBar, frobGeomPoint]
  rw [sub_pow_char_fqbar]
  congr 1
  rw [mul_pow, fqToBar_frob_fixed]

/--
For a non-Frobenius-fixed geometric support point `Q`, choose a base-field
slope whose projection isolates `Q` among `gd.support` and is itself not
Frobenius-fixed.
-/
theorem exists_slope_zLambdaBar_isolated_non_rational
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (hCardBound : gd.support.card < E.q)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support)
    (hNotFixed : frobGeomPoint E Q ≠ Q) :
    ∃ lam : ZMod E.q,
      (∀ Q' ∈ gd.support, Q' ≠ Q →
        zLambdaBar E lam Q' ≠ zLambdaBar E lam Q) ∧
      (zLambdaBar E lam Q) ^ E.q ≠ zLambdaBar E lam Q := by
  haveI : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩
  set n := gd.support.card
  set e : Fin n ≃ { x // x ∈ gd.support } := gd.support.equivFin.symm
  set xf : Fin n → Fqbar E := fun i => (e i).val.x
  set yf : Fin n → Fqbar E := fun i => (e i).val.y
  set i₀ : Fin n := e.symm ⟨Q, hQ⟩
  have hi₀_val : (e i₀).val = Q := by
    simp [i₀, e]
  have hDistinct : ∀ j : Fin n, j ≠ i₀ → (xf j ≠ xf i₀ ∨ yf j ≠ yf i₀) := by
    intro j hj
    simp only [xf, yf]
    by_contra h
    push_neg at h
    have hPtEq : (e j).val = (e i₀).val :=
      geomPoint_eq_of_xy E _ _ h.1 h.2
    exact hj (e.injective (Subtype.ext hPtEq))
  have hNF : (xf i₀) ^ E.q ≠ xf i₀ ∨ (yf i₀) ^ E.q ≠ yf i₀ := by
    simp only [xf, yf, hi₀_val]
    by_contra h
    push_neg at h
    exact hNotFixed (geomPoint_eq_of_xy E _ _ h.1 h.2)
  obtain ⟨lam, hSep, hFrob⟩ :=
    FrobDescentHelpers.exists_good_slope_abstract
      (K := Fqbar E) (p := E.q) xf yf i₀ hDistinct hNF hCardBound
  refine ⟨lam, ?_, ?_⟩
  · intro Q' hQ' hne
    set j := e.symm ⟨Q', hQ'⟩
    have hj_ne : j ≠ i₀ := by
      intro h
      apply hne
      have := congr_arg (fun i => (e i).val) h
      simp [j, i₀, e] at this
      exact this
    have hj_val : (e j).val = Q' := by
      simp [j, e]
    have := hSep j hj_ne
    simp only [xf, yf, hj_val, hi₀_val, zLambdaBar, fqToBar] at this ⊢
    exact this
  · intro hFix
    apply hFrob
    simp only [xf, yf, hi₀_val]
    show (Q.y - (algebraMap (ZMod E.q) (Fqbar E)) lam * Q.x) ^ E.q =
          Q.y - (algebraMap (ZMod E.q) (Fqbar E)) lam * Q.x
    have : (zLambdaBar E lam Q) ^ E.q = zLambdaBar E lam Q := hFix
    simp only [zLambdaBar, fqToBar] at this
    exact this

/-- Finite-bad-slope form of `exists_slope_zLambdaBar_isolated_non_rational`.

All rational slopes that either fail to isolate `Q` in the geometric support
or make `zLambdaBar lam Q` Frobenius-fixed are contained in a finset of size
at most `gd.support.card`. -/
theorem exists_bad_slope_set_zLambdaBar_isolated_non_rational
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support)
    (hNotFixed : frobGeomPoint E Q ≠ Q) :
    ∃ bad : Finset (ZMod E.q), bad.card ≤ gd.support.card ∧
      ∀ lam : ZMod E.q, lam ∉ bad →
        (∀ Q' ∈ gd.support, Q' ≠ Q →
          zLambdaBar E lam Q' ≠ zLambdaBar E lam Q) ∧
        (zLambdaBar E lam Q) ^ E.q ≠ zLambdaBar E lam Q := by
  haveI : Fact (Nat.Prime E.q) := ⟨E.hq_prime⟩
  set n := gd.support.card
  set e : Fin n ≃ { x // x ∈ gd.support } := gd.support.equivFin.symm
  set xf : Fin n → Fqbar E := fun i => (e i).val.x
  set yf : Fin n → Fqbar E := fun i => (e i).val.y
  set i₀ : Fin n := e.symm ⟨Q, hQ⟩
  have hi₀_val : (e i₀).val = Q := by
    simp [i₀, e]
  have hDistinct : ∀ j : Fin n, j ≠ i₀ → (xf j ≠ xf i₀ ∨ yf j ≠ yf i₀) := by
    intro j hj
    simp only [xf, yf]
    by_contra h
    push_neg at h
    have hPtEq : (e j).val = (e i₀).val :=
      geomPoint_eq_of_xy E _ _ h.1 h.2
    exact hj (e.injective (Subtype.ext hPtEq))
  have hNF : (xf i₀) ^ E.q ≠ xf i₀ ∨ (yf i₀) ^ E.q ≠ yf i₀ := by
    simp only [xf, yf, hi₀_val]
    by_contra h
    push_neg at h
    exact hNotFixed (geomPoint_eq_of_xy E _ _ h.1 h.2)
  obtain ⟨bad, hbad_card, hbad⟩ :=
    FrobDescentHelpers.exists_bad_slope_set_abstract
      (K := Fqbar E) (p := E.q) xf yf i₀ hDistinct hNF
  refine ⟨bad, by simpa [n] using hbad_card, ?_⟩
  intro lam hlam
  obtain ⟨hSep, hNonRat⟩ := hbad lam hlam
  constructor
  · intro Q' hQ' hne
    set j := e.symm ⟨Q', hQ'⟩
    have hj_ne : j ≠ i₀ := by
      intro h
      apply hne
      have := congr_arg (fun i => (e i).val) h
      simp [j, i₀, e] at this
      exact this
    have hj_val : (e j).val = Q' := by
      simp [j, e]
    have := hSep j hj_ne
    simp only [xf, yf, hj_val, hi₀_val, zLambdaBar, fqToBar] at this ⊢
    exact this
  · intro hFix
    apply hNonRat
    simp only [xf, yf, hi₀_val]
    show (Q.y - (algebraMap (ZMod E.q) (Fqbar E)) lam * Q.x) ^ E.q =
          Q.y - (algebraMap (ZMod E.q) (Fqbar E)) lam * Q.x
    have : (zLambdaBar E lam Q) ^ E.q = zLambdaBar E lam Q := hFix
    simp only [zLambdaBar, fqToBar] at this
    exact this

/-- Combined slope choice for Frobenius descent: choose a rational slope that
isolates a non-rational geometric support point and has many rational chord
intercepts available for partial-fraction sampling. -/
theorem exists_slope_zLambdaBar_isolated_non_rational_with_good_intercepts
    (D : CoordRingElt E.q) (gd : GeometricDivisorData E D)
    (Q : GeomPoint E) (hQ : Q ∈ gd.support)
    (hNotFixed : frobGeomPoint E Q ≠ Q)
    (N : ℕ)
    (hQuant : 6 * E.q * (N + gd.support.card) + 1 ≤ (validPairs E).card) :
    ∃ lam : ZMod E.q,
      (∀ Q' ∈ gd.support, Q' ≠ Q →
        zLambdaBar E lam Q' ≠ zLambdaBar E lam Q) ∧
      (zLambdaBar E lam Q) ^ E.q ≠ zLambdaBar E lam Q ∧
      N ≤ (goodIntercepts E lam).card := by
  obtain ⟨bad, hbad_card, hbad⟩ :=
    exists_bad_slope_set_zLambdaBar_isolated_non_rational E D gd Q hQ hNotFixed
  have hQuantBad : 6 * E.q * (N + bad.card) + 1 ≤ (validPairs E).card := by
    refine (Nat.add_le_add_right ?_ 1).trans hQuant
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_left hbad_card N
  obtain ⟨lam, hlam_bad, hGood⟩ :=
    exists_good_lambda_avoiding_bad E bad N hQuantBad
  obtain ⟨hSep, hNonRat⟩ := hbad lam hlam_bad
  exact ⟨lam, hSep, hNonRat, hGood⟩

end Divisor
