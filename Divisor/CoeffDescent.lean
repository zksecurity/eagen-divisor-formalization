/-
  Divisor/CoeffDescent.lean

  Generic helper lemmas for finite-field coefficient descent.
-/
import Divisor.GeomLocalOrder
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

open Finset Classical MvPolynomial

namespace Divisor

variable (E : ECSetup)

/-! ## MvPolynomial descent from coefficient range -/

/-- An `MvPolynomial` over `S` is in the range of `MvPolynomial.map f` if every
coefficient lies in the range of `f`. -/
theorem mvpoly_in_range_of_coeffs_in_range
    {R S : Type*} {σ : Type*} [DecidableEq σ] [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ S)
    (hcoeff : ∀ d : σ →₀ ℕ, ∃ r : R, f r = MvPolynomial.coeff d p) :
    ∃ q : MvPolynomial σ R, MvPolynomial.map f q = p := by
  use ∑ d ∈ p.support, MvPolynomial.monomial d (Classical.choose (hcoeff d))
  rw [map_sum]
  simp_rw [MvPolynomial.map_monomial]
  conv_rhs => rw [MvPolynomial.as_sum p]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact Classical.choose_spec (hcoeff d)

/-! ## Finite-field fixed-point descent -/

/-- `fqToBar` is Frobenius-fixed. -/
theorem fqToBar_frob_fixed (a : ZMod E.q) :
    (fqToBar E a) ^ E.q = fqToBar E a := by
  simp [fqToBar, ← map_pow, ZMod.pow_card]

/--
In the algebraic closure of `ZMod q`, every element fixed by the
`q`-power Frobenius lies in the image of the canonical embedding.
-/
theorem fqbar_fixed_by_frob_in_range
    (c : Fqbar E) (hc : c ^ E.q = c) :
    ∃ a : ZMod E.q, algebraMap (ZMod E.q) (Fqbar E) a = c := by
  set p := (Polynomial.X ^ E.q - Polynomial.X : Polynomial (Fqbar E)) with hp_def
  have hq2 : 2 ≤ E.q := Nat.Prime.two_le E.hq_prime
  have hp_ne : p ≠ 0 := by
    intro h
    have h1 : p.natDegree = E.q := by
      simp only [hp_def]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow E.q
      · simp [Polynomial.natDegree_X]
        omega
    simp [h] at h1
    omega
  have hc_root : c ∈ p.roots := by
    rw [Polynomial.mem_roots hp_ne]
    simp [Polynomial.IsRoot, hp_def, hc]
  have him : ∀ a : ZMod E.q, algebraMap (ZMod E.q) (Fqbar E) a ∈ p.roots := by
    intro a
    rw [Polynomial.mem_roots hp_ne]
    simp [Polynomial.IsRoot, hp_def, ← map_pow, ZMod.pow_card]
  have hcard : p.roots.card ≤ E.q := by
    have h1 : p.natDegree = E.q := by
      simp only [hp_def]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow E.q
      · simp [Polynomial.natDegree_X]
        omega
    have h2 := Polynomial.card_roots hp_ne
    rw [Polynomial.degree_eq_natDegree hp_ne, h1, Nat.cast_le] at h2
    exact h2
  have hinj : Function.Injective (algebraMap (ZMod E.q) (Fqbar E)) :=
    RingHom.injective _
  let S := Finset.image (algebraMap (ZMod E.q) (Fqbar E)) Finset.univ
  have hS_card : S.card = E.q := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
  have hS_sub : S ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Multiset.mem_toFinset.mpr (him a)
  have hroots_card : p.roots.toFinset.card ≤ E.q :=
    (Multiset.toFinset_card_le p.roots).trans hcard
  have hS_eq : S = p.roots.toFinset := by
    rwa [Finset.subset_iff_eq_of_card_le (by omega)] at hS_sub
  have hc_mem : c ∈ S := by
    rw [hS_eq]
    exact Multiset.mem_toFinset.mpr hc_root
  rw [Finset.mem_image] at hc_mem
  obtain ⟨a, _, ha⟩ := hc_mem
  exact ⟨a, ha⟩

/-! ## Frobenius action setup -/

/-- The `q`-power Frobenius endomorphism on `Fqbar E`. -/
noncomputable def frobEnd : Fqbar E →+* Fqbar E :=
  frobenius (Fqbar E) E.q

@[simp]
theorem frobEnd_apply (x : Fqbar E) : frobEnd E x = x ^ E.q := by
  simp [frobEnd, frobenius_def]

/-- The Frobenius-on-coefficients map for four-variable polynomials. -/
noncomputable def frobMvPoly : FourVarPolyBar E →+* FourVarPolyBar E :=
  MvPolynomial.map (frobEnd E)

theorem frobMvPoly_coeff (p : FourVarPolyBar E) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (frobMvPoly E p) = (MvPolynomial.coeff d p) ^ E.q := by
  simp [frobMvPoly, MvPolynomial.coeff_map, frobEnd_apply]

/-- If `frobMvPoly E p = p`, then every coefficient of `p` descends to `ZMod E.q`. -/
theorem coeffs_descend_of_frob_fixed
    (p : FourVarPolyBar E)
    (hfix : frobMvPoly E p = p) :
    ∀ d : Fin 4 →₀ ℕ,
      ∃ a : ZMod E.q, algebraMap (ZMod E.q) (Fqbar E) a = MvPolynomial.coeff d p := by
  intro d
  apply fqbar_fixed_by_frob_in_range
  have := congr_arg (fun f => MvPolynomial.coeff d f) hfix
  simp [frobMvPoly_coeff] at this
  exact this

/-! ## Basic Frobenius-on-MvPolynomial identities -/

@[simp]
theorem frobMvPoly_X (i : Fin 4) :
    frobMvPoly E (MvPolynomial.X i : FourVarPolyBar E) = MvPolynomial.X i := by
  simp [frobMvPoly, MvPolynomial.map_X]

@[simp]
theorem frobMvPoly_C (c : Fqbar E) :
    frobMvPoly E (MvPolynomial.C c : FourVarPolyBar E) = MvPolynomial.C (c ^ E.q) := by
  simp [frobMvPoly, MvPolynomial.map_C, frobEnd_apply]

theorem frobMvPoly_C_fqToBar (a : ZMod E.q) :
    frobMvPoly E (MvPolynomial.C (fqToBar E a) : FourVarPolyBar E) =
      MvPolynomial.C (fqToBar E a) := by
  rw [frobMvPoly_C]
  congr 1
  exact fqToBar_frob_fixed E a

theorem frobMvPoly_C_natCast (n : ℕ) :
    frobMvPoly E (MvPolynomial.C ((n : ℕ) : Fqbar E) : FourVarPolyBar E) =
      MvPolynomial.C ((n : ℕ) : Fqbar E) := by
  rw [frobMvPoly_C]
  congr 1
  rw [← map_natCast (algebraMap (ZMod E.q) (Fqbar E)) n, ← map_pow,
    ZMod.pow_card, map_natCast]

/-! ## Frobenius on geometric points -/

/-- Apply Frobenius to a geometric point. -/
noncomputable def frobGeomPoint (Q : GeomPoint E) : GeomPoint E where
  x := Q.x ^ E.q
  y := Q.y ^ E.q
  onCurve := by
    have hQ := Q.onCurve
    have h1 : (frobenius (Fqbar E) E.q) (Q.y ^ 2) =
        (frobenius (Fqbar E) E.q)
          (Q.x ^ 3 + fqToBar E E.curveA * Q.x + fqToBar E E.curveB) := congr_arg _ hQ
    simp only [map_pow, map_add, map_mul, frobenius_def, fqToBar_frob_fixed] at h1
    exact h1

end Divisor
