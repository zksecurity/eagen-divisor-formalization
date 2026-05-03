/-
  Divisor/ChordFiberWeightedDegree.lean

  Weighted-Sylvester degree bounds for the chord-fiber product.

  Goal: a coordinate-native proof of the natDegree inequality

      (chord_fiber_product_concrete E lam D).natDegree ≤ (normPoly E D).natDegree

  for any D with `¬ (D.a = 0 ∧ D.b = 0)`, *without* coprime
  hypothesis. This is the gcd-1 base case (and more) of stub 2a in
  `Divisor/Sketch/ChordFiberProductConcrete.lean`.

  Strategy (codex-suggested, weight-based Sylvester):

  Assign weights `wt(x) = 2`, `wt(Z) = 3` to the bivariate ring
  `(ZMod E.q)[Z][x]`. Define the per-coefficient weight bounds:

  **Lemma A** (chord-cubic weight bound):
      ∀ k ≤ 3, 3 · ((chordCubicBiv E lam).coeff k).natDegree + 2k ≤ 6.

  **Lemma B** (DLineBiv weight bound):
      ∀ k, 3 · ((DLineBiv E lam D).coeff k).natDegree + 2k
            ≤ (normPoly E D).natDegree
      (equivalent under `¬ (D.a = 0 ∧ D.b = 0)`).

  Then: in the Sylvester determinant `Σ_σ sgn(σ) · ∏_j entry_j`,
  each summand is a product of m=3 g-coefficients (from g = DLineBiv,
  the chord-cubic columns) and n = deg DLineBiv f-coefficients (from
  f = chordCubicBiv, the DLine columns), where the indices satisfy
  Σ I_l + Σ J_l = m·n. Multiplying the weight bounds:

      3 · Σ deg_Z(f.coeff I_l) + 2 · Σ I_l ≤ 6n
      3 · Σ deg_Z(g.coeff J_l) + 2 · Σ J_l ≤ m · w   (w = (normPoly).natDegree)

  Adding and using Σ I + Σ J = m·n = 3n:

      3 · deg_Z(product) + 2 · 3n ≤ 6n + 3 · w
      3 · deg_Z(product) ≤ 3 · w
      deg_Z(product) ≤ w.

  Hence `deg_Z(det) ≤ w = (normPoly).natDegree`, which is the
  required bound on `chord_fiber_product_concrete`.

  This file lays the groundwork: per-coefficient weight bounds
  (Lemmas A, B). The main determinant analysis is the substantive
  remaining work; the per-coefficient bounds here are mechanical
  coefficient computations.
-/
import Divisor.ChordFiberProductConcrete

open Polynomial

namespace Divisor

variable (E : ECSetup)

/-! ## Per-coefficient weight bounds

These lemmas convert the structural form of `chordCubicBiv` and
`DLineBiv` into weight inequalities that the Sylvester determinant
analysis consumes. -/

/-- **Lemma A**: weight bound for `chordCubicBiv` coefficients.

For `f = chordCubicBiv E lam ∈ (ZMod E.q)[Z][x]` (where outer `x` is
the curve x-coordinate, inner `Z` is the chord intercept variable),

    3 · (f.coeff k).natDegree + 2 · k ≤ 6   for k ≤ 3.

The four coefficients are:
- `f.coeff 3 = 1` (from `X^3`), natDegree 0.
- `f.coeff 2 = -C(λ²)` (constant in inner `Z`), natDegree 0.
- `f.coeff 1 = C(A) - 2λ · Z` (linear in inner `Z`), natDegree ≤ 1.
- `f.coeff 0 = C(B) - Z²` (quadratic in inner `Z`), natDegree ≤ 2.

Verifications:
- k=3: 3·0 + 6 = 6 ≤ 6 ✓
- k=2: 3·0 + 4 = 4 ≤ 6 ✓
- k=1: 3·1 + 2 = 5 ≤ 6 ✓
- k=0: 3·2 + 0 = 6 ≤ 6 ✓ -/
theorem chordCubicBiv_coeff_natDegree_weighted_bound
    (lam : ZMod E.q) (k : ℕ) (hk : k ≤ 3) :
    3 * ((chordCubicBiv E lam).coeff k).natDegree + 2 * k ≤ 6 := by
  classical
  -- Case-split on k ∈ {0, 1, 2, 3}.
  interval_cases k
  · -- k = 0: coeff 0 = C(B) - Z²; natDegree ≤ 2.
    have hcoeff : (chordCubicBiv E lam).coeff 0
        = Polynomial.C E.curveB - Polynomial.X ^ 2 := by
      unfold chordCubicBiv
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
                 Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
                 Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [hcoeff]
    have hbound : (Polynomial.C E.curveB - Polynomial.X ^ 2 :
        Polynomial (ZMod E.q)).natDegree ≤ 2 := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C _).le.trans (by omega)
      · exact (Polynomial.natDegree_X_pow_le 2)
    omega
  · -- k = 1: coeff 1 = C(A) - C(2λ) · X; natDegree ≤ 1.
    have hcoeff : (chordCubicBiv E lam).coeff 1
        = Polynomial.C E.curveA - Polynomial.C (2 * lam) * Polynomial.X := by
      unfold chordCubicBiv
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
                 Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
                 Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_mul_X]
      norm_num
    rw [hcoeff]
    have hbound :
        (Polynomial.C E.curveA - Polynomial.C (2 * lam) * Polynomial.X :
            Polynomial (ZMod E.q)).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C _).le.trans (by omega)
      · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        exact Polynomial.natDegree_X_le
    omega
  · -- k = 2: coeff 2 = -C(λ²); natDegree 0.
    have hcoeff : (chordCubicBiv E lam).coeff 2
        = -Polynomial.C (lam ^ 2) := by
      unfold chordCubicBiv
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
                 Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
                 Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [hcoeff]
    have hbound : (-Polynomial.C (lam ^ 2) :
        Polynomial (ZMod E.q)).natDegree = 0 := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_C]
    omega
  · -- k = 3: coeff 3 = 1; natDegree 0.
    have hcoeff : (chordCubicBiv E lam).coeff 3 = 1 := by
      unfold chordCubicBiv
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
                 Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
                 Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [hcoeff]
    have hbound : (1 : Polynomial (ZMod E.q)).natDegree = 0 := Polynomial.natDegree_one
    omega

/-! ### DLineBiv coefficient structure

The DLineBiv coefficient at outer-X index `k` lives in the inner ring
`(ZMod E.q)[Z]` and has the explicit form

    DLineBiv.coeff k = (D.a.coeff k - λ · D.b.coeff(k-1)) − D.b.coeff(k) · Z

(treating `D.b.coeff(-1) = 0`). In particular, its natDegree as an
inner polynomial is at most 1, and is 0 whenever `D.b.coeff k = 0`. -/

/-- **Bound on natDegree of `DLineBiv.coeff k`.**

The DLineBiv coefficient at outer x^k is a polynomial in inner Z of
natDegree ≤ 1, with the leading-Z coefficient determined by
`D.b.coeff k`. Specifically, when `D.b.coeff k ≠ 0`, the natDegree is
exactly 1; otherwise it is at most 0. -/
private lemma DLineBiv_coeff_natDegree_le_one
    (lam : ZMod E.q) (D : CoordRingElt E.q) (k : ℕ) :
    ((DLineBiv E lam D).coeff k).natDegree ≤ 1 := by
  classical
  -- Helper: a sum of polynomials with each term of natDegree ≤ 1 has natDegree ≤ 1.
  have hsum_le : ∀ s : Finset (ℕ × ℕ), ∀ f : ℕ × ℕ → Polynomial (ZMod E.q),
      (∀ p ∈ s, (f p).natDegree ≤ 1) →
      (∑ p ∈ s, f p).natDegree ≤ 1 := by
    intro s f hbnd
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.sum_insert hpt]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact hbnd p (Finset.mem_insert_self _ _)
        · exact ih (fun q hq => hbnd q (Finset.mem_insert_of_mem hq))
  -- DLineBiv.coeff k = (D.a.map C).coeff k - (D.b.map C * (C(Cλ)X + CX)).coeff k.
  have hsplit :
      ((DLineBiv E lam D).coeff k).natDegree
        ≤ max ((D.a.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])).coeff k).natDegree
              ((D.b.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
                  * (Polynomial.C (Polynomial.C lam) * Polynomial.X
                      + Polynomial.C Polynomial.X)).coeff k).natDegree := by
    show (((D.a.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
          - (D.b.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
              * ((Polynomial.C (Polynomial.C lam) * Polynomial.X)
                  + Polynomial.C Polynomial.X)).coeff k).natDegree ≤ _
    rw [Polynomial.coeff_sub]
    exact Polynomial.natDegree_sub_le _ _
  refine hsplit.trans (max_le ?_ ?_)
  · -- (D.a.map C).coeff k = C(D.a.coeff k), natDegree = 0 ≤ 1.
    rw [Polynomial.coeff_map]
    exact (Polynomial.natDegree_C _).le.trans (by omega)
  · -- (D.b.map C * Q).coeff k = sum_{i+j=k} (D.b.map C).coeff i * Q.coeff j.
    -- Each Q.coeff j has natDegree ≤ 1; (D.b.map C).coeff i = C(D.b.coeff i) is a
    -- constant, so each summand has natDegree ≤ 1.
    rw [Polynomial.coeff_mul]
    refine hsum_le _ _ ?_
    rintro ⟨i, j⟩ _
    refine Polynomial.natDegree_mul_le.trans ?_
    -- (D.b.map C).coeff i = C(D.b.coeff i): natDegree = 0.
    rw [Polynomial.coeff_map, Polynomial.natDegree_C, zero_add]
    -- Q.coeff j has natDegree ≤ 1.
    show ((Polynomial.C (Polynomial.C lam) * Polynomial.X
            + Polynomial.C Polynomial.X).coeff j).natDegree ≤ 1
    rw [Polynomial.coeff_add]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · -- (C(Cλ) · X).coeff j = (Cλ if j = 1 else 0). natDegree = 0.
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X]
      split_ifs
      · rw [mul_one]; exact (Polynomial.natDegree_C _).le.trans (by omega)
      · rw [mul_zero]; simp
    · -- (C X).coeff j = (X if j = 0 else 0). natDegree ≤ 1.
      rw [Polynomial.coeff_C]
      split_ifs
      · exact Polynomial.natDegree_X_le
      · simp

end Divisor
