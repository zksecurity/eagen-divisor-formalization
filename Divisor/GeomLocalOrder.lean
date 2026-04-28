/-
  Divisor/GeomLocalOrder.lean

  Local-order API for geometric zeros over `F_qbar`.

  The geometric `polyG` soundness path needs true local multiplicities,
  not just finite support. This file isolates that obligation: the hard
  theorem is the construction of a local-order package on a fixed
  geometric zero support. Once that package exists, assembling
  `GeometricDivisorData` is routine and proved below.
-/
import Divisor.GeomBase
import Divisor.BetaConstructive
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## Explicit geometric local-order candidate -/

/-- The `a(x)` part of `D = a(x) - b(x)y`, base-changed to `F_qbar`. -/
noncomputable def geomAPoly (D : CoordRingElt E.q) : Polynomial (Fqbar E) :=
  Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) D.a

/-- The `b(x)` part of `D = a(x) - b(x)y`, base-changed to `F_qbar`. -/
noncomputable def geomBPoly (D : CoordRingElt E.q) : Polynomial (Fqbar E) :=
  Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) D.b

/--
Common `x = α` vanishing order of the two coefficient polynomials.

The zero-polynomial cases matter: if one coefficient is identically zero,
the common factor should be the full order of the other coefficient, not
`0`.
-/
noncomputable def commonRootMultiplicity
    (a b : Polynomial (Fqbar E)) (α : Fqbar E) : ℕ :=
  if a = 0 then b.rootMultiplicity α
  else if b = 0 then a.rootMultiplicity α
  else min (a.rootMultiplicity α) (b.rootMultiplicity α)

theorem commonRootMultiplicity_le_left
    (a b : Polynomial (Fqbar E)) (α : Fqbar E) (ha : a ≠ 0) :
    commonRootMultiplicity E a b α ≤ a.rootMultiplicity α := by
  unfold commonRootMultiplicity
  rw [if_neg ha]
  by_cases hb : b = 0
  · rw [if_pos hb]
  · rw [if_neg hb]
    exact min_le_left _ _

theorem commonRootMultiplicity_le_right
    (a b : Polynomial (Fqbar E)) (α : Fqbar E) (hb : b ≠ 0) :
    commonRootMultiplicity E a b α ≤ b.rootMultiplicity α := by
  unfold commonRootMultiplicity
  by_cases ha : a = 0
  · rw [if_pos ha]
  · rw [if_neg ha, if_neg hb]
    exact min_le_right _ _

/-- `a` is divisible by the common root factor. -/
theorem commonRootFactor_dvd_left
    (a b : Polynomial (Fqbar E)) (α : Fqbar E) :
    (X - C α) ^ commonRootMultiplicity E a b α ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · exact dvd_trans
      (pow_dvd_pow _ (commonRootMultiplicity_le_left E a b α ha))
      (pow_rootMultiplicity_dvd a α)

/-- `b` is divisible by the common root factor. -/
theorem commonRootFactor_dvd_right
    (a b : Polynomial (Fqbar E)) (α : Fqbar E) :
    (X - C α) ^ commonRootMultiplicity E a b α ∣ b := by
  by_cases hb : b = 0
  · rw [hb]
    exact dvd_zero _
  · exact dvd_trans
      (pow_dvd_pow _ (commonRootMultiplicity_le_right E a b α hb))
      (pow_rootMultiplicity_dvd b α)

/-- The quotient of `a` after removing its common `x = α` factor with `b`. -/
noncomputable def geomATilde (D : CoordRingElt E.q) (α : Fqbar E) :
    Polynomial (Fqbar E) :=
  geomAPoly E D /ₘ
    ((X - C α) ^ commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α)

/-- The quotient of `b` after removing its common `x = α` factor with `a`. -/
noncomputable def geomBTilde (D : CoordRingElt E.q) (α : Fqbar E) :
    Polynomial (Fqbar E) :=
  geomBPoly E D /ₘ
    ((X - C α) ^ commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α)

/--
Candidate true local order of `D` at a geometric affine point.

For ramified fibers (`y = 0`) the single affine point receives the full
root multiplicity of the norm. On a two-point fiber, remove the common
coefficient factor first; the residual sheet selected by
`a_tilde(α) - b_tilde(α)y = 0` receives the remaining norm multiplicity,
while its conjugate receives the common factor.
-/
noncomputable def geomLocalOrder (D : CoordRingElt E.q) (Q : GeomPoint E) : ℕ :=
  let m := (normPolyBar E D).rootMultiplicity Q.x
  if Q.y = 0 then
    m
  else
    let k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x
    if (geomATilde E D Q.x).eval Q.x - (geomBTilde E D Q.x).eval Q.x * Q.y = 0 then
      m - k
    else
      k

/-! ## Local multiplicity interface -/

/--
`n` is the geometric local zero multiplicity of `D` at `Q`.

Mathematically this is `ord_Q(D)` in the completed local ring of the
smooth base-changed curve. The inequality against `rootMultiplicity`
records the easy projection bound; exact fiber accounting is stated
separately in `GeomLocalOrderOnSupport`.
-/
def IsGeometricZeroMultiplicity (D : CoordRingElt E.q) (Q : GeomPoint E)
    (n : ℕ) : Prop :=
  D.geomEval E Q = 0 ∧
  0 < n ∧
  n ≤ (normPolyBar E D).rootMultiplicity Q.x

/--
Finite geometric zero divisor of a nonzero `CoordRingElt`.

The support is over `F_qbar`, not `E(F_q)`. Multiplicities are true local
orders. `fiber_accounting` is the central local-algebra identity:
the sum of local orders over an affine x-fiber equals the root
multiplicity of the norm polynomial at that x-coordinate.
-/
structure GeometricDivisorData (D : CoordRingElt E.q) where
  support : Finset (GeomPoint E)
  mult : GeomPoint E → ℕ
  support_eval_zero : ∀ Q ∈ support, D.geomEval E Q = 0
  eval_zero_mem_support : ∀ Q, D.geomEval E Q = 0 → Q ∈ support
  multiplicity_spec :
    ∀ Q ∈ support, IsGeometricZeroMultiplicity E D Q (mult Q)
  mult_pos_on_support : ∀ Q ∈ support, 0 < mult Q
  mult_zero_off_support : ∀ Q, Q ∉ support → mult Q = 0
  accounting_le_degE : (∑ Q ∈ support, mult Q) ≤ D.degE
  fiber_accounting :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), mult Q)
        = (normPolyBar E D).rootMultiplicity α
  frobenius_stable :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧ mult Q' = mult Q

/--
Core exact local orders on a fixed finite geometric zero support.

This package intentionally contains the fiber-accounting and Frobenius
laws, not just pointwise positivity. A support-only assignment such as
`ord Q = 1` can satisfy the projection bound below, but it is not the
geometric local order and would make the later fiber theorem false.
-/
structure GeomLocalOrderCore
    (D : CoordRingElt E.q) (support : Finset (GeomPoint E)) where
  ord : GeomPoint E → ℕ
  ord_pos_on_support : ∀ Q ∈ support, 0 < ord Q
  ord_zero_off_support : ∀ Q, Q ∉ support → ord Q = 0
  multiplicity_spec :
    ∀ Q ∈ support, IsGeometricZeroMultiplicity E D Q (ord Q)
  fiber_accounting :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), ord Q)
        = (normPolyBar E D).rootMultiplicity α
  frobenius_stable :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧ ord Q' = ord Q

/--
True local orders on a fixed finite geometric zero support.

This is the precise hard proof object needed to replace the old
`splitsOnE`-based rational multiplicity model. The intended construction
defines `ord Q` by a uniformizer expansion in the completed local ring:

* if `Q.y ≠ 0`, use `x - Q.x` as uniformizer;
* if `Q.y = 0`, use `y` as uniformizer.

The fiber-accounting field is the key theorem:
`Σ_{Q.x = α} ord_Q(D) = rootMultiplicity α (normPolyBar E D)`.
-/
structure GeomLocalOrderOnSupport
    (D : CoordRingElt E.q) (support : Finset (GeomPoint E)) where
  ord : GeomPoint E → ℕ
  ord_pos_on_support : ∀ Q ∈ support, 0 < ord Q
  ord_zero_off_support : ∀ Q, Q ∉ support → ord Q = 0
  multiplicity_spec :
    ∀ Q ∈ support, IsGeometricZeroMultiplicity E D Q (ord Q)
  accounting_le_degE : (∑ Q ∈ support, ord Q) ≤ D.degE
  fiber_accounting :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), ord Q)
        = (normPolyBar E D).rootMultiplicity α
  frobenius_stable :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧ ord Q' = ord Q

/-! ## Helper lemmas for the explicit local-order proofs -/

/-- The base-changed norm polynomial is nonzero when `D` is nonzero. -/
theorem normPolyBar_ne_zero (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) :
    normPolyBar E D ≠ 0 := by
  exact Polynomial.map_ne_zero (normPoly_ne_zero E D hDnz)

/-- Root multiplicity of `normPolyBar` at `Q.x` is positive when `geomEval = 0`. -/
theorem rootMultiplicity_normPolyBar_pos_of_geomEval_zero
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (Q : GeomPoint E) (hQ : D.geomEval E Q = 0) :
    0 < (normPolyBar E D).rootMultiplicity Q.x := by
  rw [rootMultiplicity_pos (normPolyBar_ne_zero E D hDnz)]
  exact normPolyBar_eval_zero_of_geomEval_zero E D Q hQ

/-- `geomEval` equals the evaluation of `a(x) - b(x)y` after base change. -/
theorem geomEval_eq_geomAPoly_sub_geomBPoly_mul_y
    (D : CoordRingElt E.q) (Q : GeomPoint E) :
    D.geomEval E Q =
      (geomAPoly E D).eval Q.x - (geomBPoly E D).eval Q.x * Q.y := by
  unfold CoordRingElt.geomEval geomAPoly geomBPoly
  simp [eval_map]

/-- When the common factor is trivial, the residual branch condition is `geomEval`. -/
theorem geomATilde_sub_geomBTilde_eq_geomEval_when_k_zero
    (D : CoordRingElt E.q) (Q : GeomPoint E)
    (hk : commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x = 0) :
    (geomATilde E D Q.x).eval Q.x - (geomBTilde E D Q.x).eval Q.x * Q.y
      = D.geomEval E Q := by
  unfold geomATilde geomBTilde
  rw [hk]
  simp [geomEval_eq_geomAPoly_sub_geomBPoly_mul_y]

/-- If `Q` is not a zero and `Q.y ≠ 0`, the common root factor at `Q.x` is trivial. -/
theorem commonRootMultiplicity_eq_zero_of_geomEval_ne_zero
    (D : CoordRingElt E.q)
    (Q : GeomPoint E) (_hy : Q.y ≠ 0) (hQ : D.geomEval E Q ≠ 0) :
    commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x = 0 := by
  contrapose! hQ
  simp_all +decide [commonRootMultiplicity]
  rw [geomEval_eq_geomAPoly_sub_geomBPoly_mul_y]
  aesop

/--
The norm polynomial is divisible by the square of the common coefficient
factor at `α`.
-/
theorem normPolyBar_dvd_pow_twice_commonRootMultiplicity
    (D : CoordRingElt E.q) (α : Fqbar E) :
    let k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α
    (X - C α) ^ (2 * k) ∣ normPolyBar E D := by
  set k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α
  have h_div_a : (X - C α) ^ k ∣ geomAPoly E D :=
    commonRootFactor_dvd_left E (geomAPoly E D) (geomBPoly E D) α
  have h_div_b : (X - C α) ^ k ∣ geomBPoly E D :=
    commonRootFactor_dvd_right E (geomAPoly E D) (geomBPoly E D) α
  convert mul_dvd_mul h_div_a h_div_a |> fun h =>
    h.sub
      (dvd_mul_of_dvd_left
        (mul_dvd_mul h_div_b h_div_b)
        (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (Polynomial.X ^ 3 + Polynomial.C E.curveA * Polynomial.X +
            Polynomial.C E.curveB))) using 1; ring_nf
  convert congr_arg
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))) (normPoly_eq E D) using 1;
    norm_num [normPolyBar]; ring_nf
  unfold curveX
  norm_num [geomAPoly, geomBPoly]
  ring_nf

/-- The norm root multiplicity is at least twice the common coefficient order. -/
theorem rootMultiplicity_normPolyBar_ge_twice_common
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (α : Fqbar E) :
    let k := commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α
    2 * k ≤ (normPolyBar E D).rootMultiplicity α := by
  convert Polynomial.le_rootMultiplicity_iff _ |>.2
    (normPolyBar_dvd_pow_twice_commonRootMultiplicity E D α) using 1
  exact normPolyBar_ne_zero E D hDnz

/-- In the ramified case `Q.y = 0`, norm vanishing is equivalent to `geomEval = 0`. -/
theorem normPolyBar_eval_eq_zero_iff_geomEval_zero_of_y_eq_zero
    (D : CoordRingElt E.q) (Q : GeomPoint E) (hy : Q.y = 0) :
    (normPolyBar E D).eval Q.x = 0 ↔ D.geomEval E Q = 0 := by
  have h_normPoly_def :
      normPolyBar E D =
        (geomAPoly E D)^2 -
          (geomBPoly E D)^2 *
            (Polynomial.X^3 + Polynomial.C (fqToBar E E.curveA) * Polynomial.X +
              Polynomial.C (fqToBar E E.curveB)) := by
    have h_normPoly_def :
        normPoly E D =
          D.a^2 - D.b^2 *
            (Polynomial.X^3 + Polynomial.C E.curveA * Polynomial.X +
              Polynomial.C E.curveB) := by
      convert normPoly_eq E D
    unfold normPolyBar geomAPoly geomBPoly
    simp +decide [h_normPoly_def]
    exact Or.inl rfl
  rw [h_normPoly_def, geomEval_eq_geomAPoly_sub_geomBPoly_mul_y]
  simp +decide [hy, sub_eq_iff_eq_add]
  rw [← Q.onCurve, hy, zero_pow two_ne_zero]
  aesop

/-! ## Proof targets for the explicit local-order candidate -/

/--
The explicit local-order candidate is positive at every geometric zero.

PROVIDED SOLUTION
Use `normPolyBar_eval_zero_of_geomEval_zero` to show `Q.x` is a root of
`normPolyBar E D`, hence the norm root multiplicity is positive. In the
ramified case `Q.y = 0`, `geomLocalOrder` is that full multiplicity.
In the two-sheet case, factor the common `x = Q.x` order from `a` and
`b`; the residual sheet predicate decides which point gets the residual
`m - k` and which gets `k`. The zero condition excludes the impossible
case where the selected positive component is zero.
-/
theorem geomLocalOrder_pos_of_geomEval_zero
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (Q : GeomPoint E) (hQ : D.geomEval E Q = 0) :
    0 < geomLocalOrder E D Q := by
  unfold geomLocalOrder
  have h_root_pos : 0 < rootMultiplicity Q.x (normPolyBar E D) :=
    rootMultiplicity_normPolyBar_pos_of_geomEval_zero E D hDnz Q hQ
  by_cases hy : Q.y = 0 <;> simp_all +decide
  split_ifs
  · refine' Nat.sub_pos_of_lt _
    have h_common :
        2 * commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x
          ≤ rootMultiplicity Q.x (normPolyBar E D) := by
      apply rootMultiplicity_normPolyBar_ge_twice_common
      aesop
    linarith [
      show 0 < rootMultiplicity Q.x (normPolyBar E D) from
        Nat.pos_of_ne_zero (by aesop)]
  · contrapose! hQ
    rw [← geomATilde_sub_geomBTilde_eq_geomEval_when_k_zero]
    · aesop
    · aesop

/--
The explicit local-order candidate vanishes away from the geometric zero
set.

PROVIDED SOLUTION
Unfold `geomLocalOrder`. If `Q.y = 0`, a positive norm multiplicity
would make `D.geomEval E Q = 0` by the norm identity at a ramified
fiber. If `Q.y ≠ 0`, a positive common factor or residual sheet factor
forces `a(Q.x) - b(Q.x)Q.y = 0`, contradicting the hypothesis.
-/
theorem geomLocalOrder_eq_zero_of_geomEval_ne_zero
    (D : CoordRingElt E.q) (_hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (Q : GeomPoint E) (hQ : D.geomEval E Q ≠ 0) :
    geomLocalOrder E D Q = 0 := by
  by_cases hy : Q.y = 0 <;> simp_all +decide [geomLocalOrder]
  · exact fun h => False.elim <| hQ <| by
      simpa [hy] using
        normPolyBar_eval_eq_zero_iff_geomEval_zero_of_y_eq_zero E D Q hy |>.1 h
  · grind +suggestions

/--
The explicit local-order candidate satisfies the pointwise multiplicity
predicate.

PROVIDED SOLUTION
Combine `geomLocalOrder_pos_of_geomEval_zero` with the projection bound
`geomLocalOrder ≤ rootMultiplicity Q.x (normPolyBar E D)`. The bound is
immediate in the ramified case and follows in the two-sheet case from
the common-factor decomposition of `normPolyBar E D`.
-/
theorem geomLocalOrder_multiplicity_spec
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (Q : GeomPoint E) (hQ : D.geomEval E Q = 0) :
    IsGeometricZeroMultiplicity E D Q (geomLocalOrder E D Q) := by
  refine' ⟨hQ, geomLocalOrder_pos_of_geomEval_zero E D hDnz Q hQ, _⟩
  unfold geomLocalOrder
  by_cases hy : Q.y = 0 <;> simp +decide [hy]
  split_ifs
  · exact Nat.sub_le _ _
  · exact Nat.le_of_lt_succ (by
      linarith [rootMultiplicity_normPolyBar_ge_twice_common E D hDnz Q.x])

/--
Fiber accounting for the explicit local-order candidate.

PROVIDED SOLUTION
For each `α`, the affine fiber of the short Weierstrass model has at
most two geometric points. If there is no geometric zero above `α`, both
sides are zero. If there is one zero, it is the ramified or single-sheet
case and receives the full norm root multiplicity. If there are two
zeros, they are conjugate sheets; after factoring the common coefficient
order `k`, one sheet receives `k` and the other receives `m - k`, so the
sum is `m = rootMultiplicity α (normPolyBar E D)`.
-/
theorem geomLocalOrder_fiber_accounting
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), geomLocalOrder E D Q)
        = (normPolyBar E D).rootMultiplicity α := by
  sorry

/-! ## Frobenius helpers -/

/-- Frobenius fixes the image of the base field in the algebraic closure. -/
private lemma frob_alg_eq (c : ZMod E.q) :
    (algebraMap (ZMod E.q) (Fqbar E) c) ^ E.q =
      algebraMap (ZMod E.q) (Fqbar E) c := by
  rw [← map_pow, ZMod.pow_card]

/-- Evaluating a base-changed polynomial at `α^q` gives the `q`-th power
of its evaluation at `α`. -/
private theorem eval₂_pow_q (g : Polynomial (ZMod E.q)) (α : Fqbar E) :
    g.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) (α ^ E.q) =
    (g.eval₂ (algebraMap (ZMod E.q) (Fqbar E)) α) ^ E.q := by
  simp only [← eval_map]
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.map_add, eval_add]
    rw [hp, hq, add_pow_char _ _ E.q]
  | monomial n c =>
    simp only [Polynomial.map_monomial, eval_monomial]
    rw [mul_pow, ← map_pow, ZMod.pow_card]
    congr 1
    rw [← pow_mul, mul_comm, pow_mul]

/-- Evaluating a mapped polynomial at `α^q` gives the `q`-th power of evaluation at `α`. -/
private theorem eval_map_pow_q (g : Polynomial (ZMod E.q)) (α : Fqbar E) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).eval (α ^ E.q) =
    ((Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).eval α) ^ E.q := by
  simp only [eval_map]
  exact eval₂_pow_q E g α

/-- Frobenius on coefficients fixes a polynomial base-changed from `F_q`. -/
private theorem map_frob_eq_self (g : Polynomial (ZMod E.q)) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g) =
    Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g := by
  rw [Polynomial.map_map]
  congr 1
  ext c
  show (frobeniusEquiv (Fqbar E) E.q) (algebraMap (ZMod E.q) (Fqbar E) c) = _
  rw [frobeniusEquiv_def, frob_alg_eq E c]

/-- Evaluating `map σ h` at `σ(α)` equals `σ(h.eval α)`. -/
private lemma map_frob_eval (h : Polynomial (Fqbar E)) (α : Fqbar E) :
    (Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom h).eval
      ((frobeniusEquiv (Fqbar E) E.q) α) =
    (frobeniusEquiv (Fqbar E) E.q) (h.eval α) := by
  set σ := frobeniusEquiv (Fqbar E) E.q
  rw [eval_map]
  have key := hom_eval₂ h (RingHom.id (Fqbar E)) σ.toRingHom α
  simp at key
  exact key.symm

/-- Frobenius sends `(X - C α)^k` to `(X - C (α^q))^k`. -/
private lemma map_frob_X_sub_C_pow (α : Fqbar E) (k : ℕ) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom ((X - C α) ^ k) =
    (X - C (α ^ E.q)) ^ k := by
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 1

/-- Root multiplicity of a base-changed polynomial is Frobenius-invariant. -/
private theorem rootMultiplicity_map_pow_q
    (g : Polynomial (ZMod E.q)) (α : Fqbar E) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).rootMultiplicity (α ^ E.q) =
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).rootMultiplicity α := by
  by_cases hg : g = 0
  · subst hg
    simp [Polynomial.map_zero, rootMultiplicity_zero]
  · set f := Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g
    set σ := frobeniusEquiv (Fqbar E) E.q
    have hf : f ≠ 0 := Polynomial.map_ne_zero hg
    have h_map_σ : Polynomial.map σ.toRingHom f = f := map_frob_eq_self E g
    have h_map_σ_inv : Polynomial.map σ.symm.toRingHom f = f := by
      rw [show f = Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g from rfl,
        Polynomial.map_map]
      congr 1
      ext c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      have hfix :
          σ (algebraMap (ZMod E.q) (Fqbar E) c) =
            algebraMap (ZMod E.q) (Fqbar E) c := by
        rw [frobeniusEquiv_def, frob_alg_eq E c]
      exact σ.symm_apply_eq.mpr hfix.symm
    have hσα : σ α = α ^ E.q := frobeniusEquiv_def _ _ _
    have hσ_inv : σ.symm (α ^ E.q) = α := by
      rw [← hσα, σ.symm_apply_apply]
    apply le_antisymm
    · calc
        f.rootMultiplicity (α ^ E.q)
            ≤ (Polynomial.map σ.symm.toRingHom f).rootMultiplicity (σ.symm (α ^ E.q)) :=
              Polynomial.le_rootMultiplicity_map (by rw [h_map_σ_inv]; exact hf) _
        _ = f.rootMultiplicity α := by rw [h_map_σ_inv, hσ_inv]
    · calc
        f.rootMultiplicity α
            ≤ (Polynomial.map σ.toRingHom f).rootMultiplicity (σ α) :=
              Polynomial.le_rootMultiplicity_map (by rw [h_map_σ]; exact hf) _
        _ = f.rootMultiplicity (α ^ E.q) := by rw [h_map_σ, hσα]

/-- Root multiplicity of a nonzero base-changed polynomial is Frobenius-invariant. -/
private theorem rootMultiplicity_pow_q
    (g : Polynomial (ZMod E.q)) (_hg : g ≠ 0) (α : Fqbar E) :
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).rootMultiplicity (α ^ E.q) =
    (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E)) g).rootMultiplicity α :=
  rootMultiplicity_map_pow_q E g α

/-- The curve equation is preserved by Frobenius. -/
private theorem onCurve_pow_q (x y : Fqbar E)
    (h : y ^ 2 = x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB) :
    (y ^ E.q) ^ 2 = (x ^ E.q) ^ 3 + fqToBar E E.curveA * (x ^ E.q) +
      fqToBar E E.curveB := by
  rw [← pow_mul, show E.q * 2 = 2 * E.q from by ring, pow_mul, h]
  rw [show x ^ 3 + fqToBar E E.curveA * x + fqToBar E E.curveB =
      x ^ 3 + (fqToBar E E.curveA * x + fqToBar E E.curveB) from by ring]
  rw [add_pow_char _ _ E.q, add_pow_char _ _ E.q, mul_pow]
  rw [← pow_mul, show 3 * E.q = E.q * 3 from by ring, pow_mul]
  unfold fqToBar
  rw [← map_pow, ZMod.pow_card, ← map_pow, ZMod.pow_card]
  ring

/-- Geometric evaluation at the Frobenius image is zero when the original is. -/
private theorem geomEval_zero_pow_q (D : CoordRingElt E.q) (Q : GeomPoint E)
    (hQ : D.geomEval E Q = 0) :
    D.geomEval E ⟨Q.x ^ E.q, Q.y ^ E.q, onCurve_pow_q E Q.x Q.y Q.onCurve⟩ = 0 := by
  unfold CoordRingElt.geomEval at *
  simp only at *
  rw [eval₂_pow_q E D.a Q.x, eval₂_pow_q E D.b Q.x, ← mul_pow,
    ← sub_pow_char, hQ, zero_pow (Nat.Prime.pos E.hq_prime).ne']

/-- The common root multiplicity is preserved by Frobenius. -/
private theorem commonRootMultiplicity_pow_q (D : CoordRingElt E.q)
    (_hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (α : Fqbar E) :
    commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) (α ^ E.q) =
    commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α := by
  unfold commonRootMultiplicity geomAPoly geomBPoly
  split_ifs <;> simp_all [rootMultiplicity_map_pow_q E]

/-- Frobenius fixes `geomAPoly`. -/
private lemma map_frob_geomAPoly (D : CoordRingElt E.q) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom (geomAPoly E D) =
      geomAPoly E D := by
  unfold geomAPoly
  exact map_frob_eq_self E D.a

/-- Frobenius fixes `geomBPoly`. -/
private lemma map_frob_geomBPoly (D : CoordRingElt E.q) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom (geomBPoly E D) =
      geomBPoly E D := by
  unfold geomBPoly
  exact map_frob_eq_self E D.b

/-- `map σ` commutes with `/ₘ` for the common root factor in `geomAPoly`. -/
private lemma geomATilde_frob (D : CoordRingElt E.q)
    (_hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (α : Fqbar E) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom (geomATilde E D α) =
    geomATilde E D (α ^ E.q) := by
  show Polynomial.map _ (geomAPoly E D /ₘ _) = geomAPoly E D /ₘ _
  have hm :
      ((X - C α) ^
        commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α).Monic :=
    (monic_X_sub_C α).pow _
  rw [Polynomial.map_divByMonic _ hm, map_frob_geomAPoly E D,
    map_frob_X_sub_C_pow E α, commonRootMultiplicity_pow_q E D _hDnz α]

/-- `map σ` commutes with `/ₘ` for the common root factor in `geomBPoly`. -/
private lemma geomBTilde_frob (D : CoordRingElt E.q)
    (_hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (α : Fqbar E) :
    Polynomial.map (frobeniusEquiv (Fqbar E) E.q).toRingHom (geomBTilde E D α) =
    geomBTilde E D (α ^ E.q) := by
  show Polynomial.map _ (geomBPoly E D /ₘ _) = geomBPoly E D /ₘ _
  have hm :
      ((X - C α) ^
        commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) α).Monic :=
    (monic_X_sub_C α).pow _
  rw [Polynomial.map_divByMonic _ hm, map_frob_geomBPoly E D,
    map_frob_X_sub_C_pow E α, commonRootMultiplicity_pow_q E D _hDnz α]

/-- The residual branch condition at the Frobenius image is the `q`-th power
of the original branch condition. -/
private theorem branch_value_pow_q (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (Q : GeomPoint E) :
    (geomATilde E D (Q.x ^ E.q)).eval (Q.x ^ E.q) -
      (geomBTilde E D (Q.x ^ E.q)).eval (Q.x ^ E.q) * (Q.y ^ E.q) =
    ((geomATilde E D Q.x).eval Q.x -
      (geomBTilde E D Q.x).eval Q.x * Q.y) ^ E.q := by
  set σ := frobeniusEquiv (Fqbar E) E.q
  rw [← geomATilde_frob E D hDnz Q.x, ← geomBTilde_frob E D hDnz Q.x]
  rw [show Q.x ^ E.q = σ Q.x from (frobeniusEquiv_def _ _ _).symm]
  rw [map_frob_eval E (geomATilde E D Q.x) Q.x]
  rw [map_frob_eval E (geomBTilde E D Q.x) Q.x]
  rw [show Q.y ^ E.q = σ Q.y from (frobeniusEquiv_def _ _ _).symm]
  rw [← σ.map_mul, ← σ.map_sub]
  rw [show σ _ = _ ^ E.q from frobeniusEquiv_def _ _ _]

/-- The explicit local-order candidate is Frobenius-invariant. -/
private theorem geomLocalOrder_eq_frob (D : CoordRingElt E.q)
    (hDnz : ¬ (D.a = 0 ∧ D.b = 0)) (Q : GeomPoint E)
    (_hQ : D.geomEval E Q = 0) :
    geomLocalOrder E D ⟨Q.x ^ E.q, Q.y ^ E.q, onCurve_pow_q E Q.x Q.y Q.onCurve⟩ =
    geomLocalOrder E D Q := by
  unfold geomLocalOrder
  simp only
  have hm : (normPolyBar E D).rootMultiplicity (Q.x ^ E.q) =
      (normPolyBar E D).rootMultiplicity Q.x := by
    unfold normPolyBar
    exact rootMultiplicity_map_pow_q E (normPoly E D) Q.x
  rw [hm]
  by_cases hy : Q.y = 0
  · have hy' : Q.y ^ E.q = 0 := by
      rw [hy, zero_pow (Nat.Prime.pos E.hq_prime).ne']
    rw [if_pos hy', if_pos hy]
  · have hy' : Q.y ^ E.q ≠ 0 := pow_ne_zero _ hy
    simp only [hy, hy', ite_false]
    have hk :
        commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) (Q.x ^ E.q) =
          commonRootMultiplicity E (geomAPoly E D) (geomBPoly E D) Q.x :=
      commonRootMultiplicity_pow_q E D hDnz Q.x
    rw [hk]
    have hbranch := branch_value_pow_q E D hDnz Q
    rw [hbranch]
    simp only [pow_eq_zero_iff (Nat.Prime.pos E.hq_prime).ne']

/--
Frobenius stability for the explicit local-order candidate.

PROVIDED SOLUTION
Map `Q` to `(Q.x^q, Q.y^q)`. Frobenius preserves the base-changed curve
equation and `D.geomEval = 0` because `D` has coefficients in `F_q`.
It preserves root multiplicities of base-changed polynomials and the
common-factor decomposition defining `geomLocalOrder`, so the local
order is unchanged.
-/
theorem geomLocalOrder_frobenius_stable
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧
          geomLocalOrder E D Q' = geomLocalOrder E D Q := by
  intro Q hQ
  have hQzero := hSupportZero Q hQ
  set Q' : GeomPoint E := ⟨Q.x ^ E.q, Q.y ^ E.q, onCurve_pow_q E Q.x Q.y Q.onCurve⟩
  have hQ'zero : D.geomEval E Q' = 0 := geomEval_zero_pow_q E D Q hQzero
  have hQ'mem : Q' ∈ support := hZeroSupport Q' hQ'zero
  exact ⟨Q', hQ'mem, rfl, rfl, geomLocalOrder_eq_frob E D hDnz Q hQzero⟩

/--
Existence of core local orders on a fixed finite geometric zero support.

PROVIDED SOLUTION
Base-change the affine coordinate ring of `E` to `F_qbar`. At each
smooth affine point in `support`, define `ord Q` as the vanishing order
of `D = a - b*y` in the completed local ring. Use the standard
uniformizer computation on a short Weierstrass curve:

* for `Q.y ≠ 0`, `x - Q.x` is a uniformizer;
* for `Q.y = 0`, `y` is a uniformizer and `x - Q.x` has order two.

The support, positivity, projection-bound, fiber-accounting, and
Frobenius-stability fields follow from the definition of local order,
the identity `N(D) = (a - b*y)(a + b*y)`, and Frobenius invariance of
`D`'s base-field coefficients.
-/
theorem exists_geomLocalOrderCore
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∃ _core : GeomLocalOrderCore E D support, True := by
  refine ⟨{
    ord := geomLocalOrder E D
    ord_pos_on_support := fun Q hQ =>
      geomLocalOrder_pos_of_geomEval_zero E D hDnz Q (hSupportZero Q hQ)
    ord_zero_off_support := fun Q hQ =>
      geomLocalOrder_eq_zero_of_geomEval_ne_zero E D hDnz Q
        (fun hZero => hQ (hZeroSupport Q hZero))
    multiplicity_spec := fun Q hQ =>
      geomLocalOrder_multiplicity_spec E D hDnz Q (hSupportZero Q hQ)
    fiber_accounting :=
      geomLocalOrder_fiber_accounting E D hDnz support hSupportZero hZeroSupport
    frobenius_stable :=
      geomLocalOrder_frobenius_stable E D hDnz support hSupportZero hZeroSupport
  }, trivial⟩

/--
Degree accounting for geometric local orders.

PROVIDED SOLUTION
Sum the fiber-accounting identity over all roots of `normPolyBar E D`.
The total root multiplicity over `F_qbar` is bounded by the natDegree of
the base-changed norm polynomial, and `natDegree (normPoly E D) ≤ D.degE`.
-/
theorem geomLocalOrderCore_accounting_le_degE
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (_hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support)
    (core : GeomLocalOrderCore E D support) :
    (∑ Q ∈ support, core.ord Q) ≤ D.degE := by
  have hsum :
      (∑ Q ∈ support, core.ord Q)
        = ∑ α ∈ (normPolyBar E D).roots.toFinset,
            (normPolyBar E D).rootMultiplicity α := by
    have hfiber :
        (∑ Q ∈ support, core.ord Q)
          = ∑ α ∈ (normPolyBar E D).roots.toFinset,
              ∑ Q ∈ support.filter (fun Q => Q.x = α), core.ord Q := by
      rw [← Finset.sum_biUnion]
      · congr with Q
        simp +decide
        intro hQ
        exact ⟨
          Polynomial.map_ne_zero (normPoly_ne_zero E D hDnz),
          normPolyBar_eval_zero_of_geomEval_zero E D Q (hSupportZero Q hQ)⟩
      · intro x _hx y _hy hxy
        exact Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy (by aesop)
    exact hfiber.trans (Finset.sum_congr rfl fun α _hα => core.fiber_accounting α)
  rw [hsum]
  have hcard :
      (normPolyBar E D).roots.card ≤ (normPoly E D).natDegree := by
    exact le_trans (Polynomial.card_roots' _) (by erw [Polynomial.natDegree_map])
  convert hcard.trans (normPoly_natDegree_le E D) using 1
  rw [← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun α _hα => by rw [Polynomial.count_roots]

/--
Fiber accounting for geometric local orders.

PROVIDED SOLUTION
For each `α`, factor the norm as
`N(D) = (a - b*y)(a + b*y)` in the completed semilocal ring over the
fiber `x = α`. The order of the norm at `α` is the sum of the local
orders of `a - b*y` over the affine points above `α`; this includes the
2-torsion case where the two sheets coalesce and `y` is the uniformizer.
-/
theorem geomLocalOrderCore_fiber_accounting
    (D : CoordRingElt E.q)
    (support : Finset (GeomPoint E))
    (core : GeomLocalOrderCore E D support) :
    ∀ α : Fqbar E,
      (∑ Q ∈ support.filter (fun Q => Q.x = α), core.ord Q)
        = (normPolyBar E D).rootMultiplicity α := by
  exact core.fiber_accounting

/--
Frobenius stability for geometric local orders.

PROVIDED SOLUTION
Frobenius sends `(x, y)` to `(x^q, y^q)`, preserves the base-changed
curve equation, and preserves `D.geomEval = 0` because `D` has
`F_q`-coefficients. It identifies the completed local rings at `Q` and
`Frob(Q)`, carrying a uniformizer to a unit times a uniformizer, so local
orders are preserved.
-/
theorem geomLocalOrderCore_frobenius_stable
    (D : CoordRingElt E.q)
    (support : Finset (GeomPoint E))
    (core : GeomLocalOrderCore E D support) :
    ∀ Q ∈ support,
      ∃ Q' ∈ support,
        Q'.x = Q.x ^ E.q ∧ Q'.y = Q.y ^ E.q ∧ core.ord Q' = core.ord Q := by
  exact core.frobenius_stable

/--
Existence of true local orders on a fixed finite geometric zero support.

This theorem only assembles the pointwise, accounting, fiber, and
Frobenius pieces above.
-/
theorem exists_geomLocalOrderOnSupport
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∃ _lo : GeomLocalOrderOnSupport E D support, True := by
  classical
  obtain ⟨core, _⟩ :=
    exists_geomLocalOrderCore E D hDnz support hSupportZero hZeroSupport
  refine ⟨{
    ord := core.ord
    ord_pos_on_support := core.ord_pos_on_support
    ord_zero_off_support := core.ord_zero_off_support
    multiplicity_spec := core.multiplicity_spec
    accounting_le_degE :=
      geomLocalOrderCore_accounting_le_degE E D hDnz support hSupportZero hZeroSupport core
    fiber_accounting := core.fiber_accounting
    frobenius_stable := core.frobenius_stable
  }, trivial⟩

/--
Assembly of geometric divisor data from the local-order package.

This theorem is intentionally just plumbing: all local algebra is isolated
in `exists_geomLocalOrderOnSupport`.
-/
theorem exists_geometricDivisorData_of_support
    (D : CoordRingElt E.q) (hDnz : ¬ (D.a = 0 ∧ D.b = 0))
    (support : Finset (GeomPoint E))
    (hSupportZero : ∀ Q ∈ support, D.geomEval E Q = 0)
    (hZeroSupport : ∀ Q, D.geomEval E Q = 0 → Q ∈ support) :
    ∃ gd : GeometricDivisorData E D, gd.support = support := by
  classical
  obtain ⟨lo, _⟩ :=
    exists_geomLocalOrderOnSupport E D hDnz support hSupportZero hZeroSupport
  refine ⟨{
    support := support
    mult := lo.ord
    support_eval_zero := hSupportZero
    eval_zero_mem_support := hZeroSupport
    multiplicity_spec := lo.multiplicity_spec
    mult_pos_on_support := lo.ord_pos_on_support
    mult_zero_off_support := lo.ord_zero_off_support
    accounting_le_degE := lo.accounting_le_degE
    fiber_accounting := lo.fiber_accounting
    frobenius_stable := lo.frobenius_stable
  }, rfl⟩

end Divisor
