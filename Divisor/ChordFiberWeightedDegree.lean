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

/-- **Sharper structural bound on `DLineBiv.coeff k` when `D.b.coeff k = 0`.**

When `D.b.coeff k = 0`, the leading-Z term in `DLineBiv.coeff k`
vanishes and the natDegree is at most 0 (i.e. the coefficient is a
constant in `Z`). This is the case-split that the weight inequality
needs to be tight in the `k > deg D.b` direction.

TODO: prove via direct coefficient-of-coefficient analysis. The key
identity is

    (DLineBiv).coeff k = C(D.a.coeff k - λ · D.b.coeff(k-1))
                            - C(D.b.coeff k) · Z

(with `D.b.coeff(-1) = 0`), so when `D.b.coeff k = 0` only the
constant `C(D.a.coeff k - λ · D.b.coeff(k-1))` remains, of natDegree 0. -/
private lemma DLineBiv_coeff_natDegree_le_zero_of_b_coeff_zero
    (lam : ZMod E.q) (D : CoordRingElt E.q) (k : ℕ)
    (hbz : D.b.coeff k = 0) :
    ((DLineBiv E lam D).coeff k).natDegree ≤ 0 := by
  classical
  -- Strategy: combine `natDegree ≤ 1` with `coeff 1 = 0` to get `natDegree ≤ 0`.
  -- The inner-X coefficient at degree 1 of (DLineBiv).coeff k is exactly
  -- `-D.b.coeff k`, which vanishes by hypothesis.
  have hdeg_le_one := DLineBiv_coeff_natDegree_le_one E lam D k
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro N hN
  -- Either N = 1 or N ≥ 2. For N ≥ 2, use natDegree ≤ 1.
  rcases (Nat.lt_or_ge 1 N) with hN2 | hN1
  · -- N ≥ 2: by natDegree ≤ 1, coeff N = 0.
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hdeg_le_one hN2)
  · -- N = 1: compute (DLineBiv.coeff k).coeff 1 = -D.b.coeff k.
    have hN1' : N = 1 := by omega
    subst hN1'
    -- Compute the coefficient.
    show (((D.a.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
          - (D.b.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
              * (Polynomial.C (Polynomial.C lam) * Polynomial.X
                  + Polynomial.C Polynomial.X))).coeff k).coeff 1 = 0
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
    -- (D.a.map C).coeff k = C(D.a.coeff k); .coeff 1 = 0.
    rw [Polynomial.coeff_map, Polynomial.coeff_C_succ]
    rw [zero_sub, neg_eq_zero]
    -- Need: ((D.b.map C * Q).coeff k).coeff 1 = D.b.coeff k.
    rw [Polynomial.coeff_mul]
    rw [Polynomial.finset_sum_coeff]
    -- Sum over (i, j) ∈ antidiagonal k of (D.b.map C).coeff i .coeff (1 - 0) ·
    --   Q.coeff j .coeff 0 + similar
    -- The only nonzero contribution is (i, j) = (k, 0): (D.b.map C).coeff k = C(D.b.coeff k),
    -- .coeff 0 = D.b.coeff k. Q.coeff 0 = X, .coeff 1 = 1. So term = D.b.coeff k · 1.
    -- For (i, j) = (k-1, 1): (D.b.map C).coeff (k-1) = C(D.b.coeff (k-1)). Q.coeff 1 = Cλ.
    -- coeff 1 of (C(D.b.coeff(k-1)) · Cλ) = C(D.b.coeff(k-1) · λ).coeff 1 = 0.
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hsum : i + j = k := Finset.mem_antidiagonal.mp hij
    rw [Polynomial.coeff_mul]
    -- C(D.b.coeff i).coeff l = D.b.coeff i if l = 0 else 0.
    rw [Polynomial.coeff_map]
    -- The term at l: (C(D.b.coeff i)).coeff l · (Q.coeff j).coeff (1-l).
    rw [Finset.sum_eq_single ⟨0, 1⟩]
    · -- Main term: (C(D.b.coeff i)).coeff 0 · (Q.coeff j).coeff 1 = D.b.coeff i · (Q.coeff j).coeff 1.
      rw [Polynomial.coeff_C_zero]
      -- Compute (Q.coeff j).coeff 1.
      have hqcoeff_succ :
          ((Polynomial.C (Polynomial.C lam) * Polynomial.X
              + Polynomial.C (Polynomial.X : Polynomial (ZMod E.q))).coeff j).coeff 1
            = if j = 0 then 1 else 0 := by
        rw [Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
        split_ifs with hj1 hj0 hj1' hj0' <;>
          simp_all [Polynomial.coeff_X, Polynomial.coeff_C]
      rw [hqcoeff_succ]
      split_ifs with hj0
      · -- j = 0, so i = k. Term = D.b.coeff k · 1 = D.b.coeff k = 0 by hbz.
        subst hj0
        have hi : i = k := by simpa using hsum
        subst hi
        rw [hbz, mul_one]
      · -- j ≠ 0. Term = D.b.coeff i · 0 = 0.
        rw [mul_zero]
    · intro b hbmem hbne
      -- For b ≠ (0, 1): C(D.b.coeff i) only has nonzero coeff at index 0.
      rcases Finset.mem_antidiagonal.mp hbmem with hb_sum
      have hb1 : b.1 ≠ 0 := by
        rintro h0
        apply hbne
        ext
        · exact h0
        · omega
      rw [Polynomial.coeff_C, if_neg hb1, zero_mul]
    · intro hne
      -- (0, 1) ∈ antidiagonal 1 always.
      exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hne

/-! ### Auxiliary normPoly natDegree bounds

The weighted-Sylvester analysis needs lower bounds on `(normPoly).natDegree`
in terms of `D.a.natDegree` and `D.b.natDegree`. The key observation:
`normPoly = D.a^2 - D.b^2 · curveX` with `curveX.natDegree = 3`, so the
two summands have natDegrees of different parities (`2·a.natDeg` even,
`2·b.natDeg + 3` odd) and cannot cancel. -/

/-- **`(normPoly).natDegree ≥ 2·D.b.natDegree + 3`** when `D.b ≠ 0`. -/
private lemma normPoly_natDegree_ge_b_curveX
    (D : CoordRingElt E.q) (hb : D.b ≠ 0) :
    2 * D.b.natDegree + 3 ≤ (normPoly E D).natDegree := by
  classical
  -- normPoly = D.a² - D.b² · curveX.
  rw [normPoly_eq]
  have hbsq_ne : D.b ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hcurveX_natDeg : (curveX E).natDegree = 3 := by
    refine le_antisymm (curveX_natDegree_le_three E) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    show (curveX E).coeff 3 ≠ 0
    unfold curveX
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
  have hcurveX_ne : (curveX E) ≠ 0 := by
    intro h
    have := hcurveX_natDeg
    rw [h, Polynomial.natDegree_zero] at this
    omega
  have hprod_natDeg : (D.b ^ 2 * curveX E).natDegree = 2 * D.b.natDegree + 3 := by
    rw [Polynomial.natDegree_mul hbsq_ne hcurveX_ne, hcurveX_natDeg,
        Polynomial.natDegree_pow]
  have hprod_lead :
      (D.b ^ 2 * curveX E).coeff (2 * D.b.natDegree + 3) ≠ 0 := by
    rw [show 2 * D.b.natDegree + 3 = (D.b ^ 2 * curveX E).natDegree from hprod_natDeg.symm]
    rw [← Polynomial.leadingCoeff]
    exact (Polynomial.leadingCoeff_ne_zero).mpr (mul_ne_zero hbsq_ne hcurveX_ne)
  -- Case-split on whether D.a² dominates the index 2·D.b.natDegree + 3.
  by_cases hdeg : 2 * D.a.natDegree < 2 * D.b.natDegree + 3
  · -- D.a².natDegree < target index, so D.a².coeff at index = 0.
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [Polynomial.coeff_sub]
    have hDa_sq_natDeg : (D.a ^ 2).natDegree = 2 * D.a.natDegree :=
      Polynomial.natDegree_pow _ _
    have hDa_zero : (D.a ^ 2).coeff (2 * D.b.natDegree + 3) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hDa_sq_natDeg]; exact hdeg
    rw [hDa_zero, zero_sub, neg_ne_zero]
    exact hprod_lead
  · -- 2·D.a.natDegree ≥ 2·D.b.natDegree + 3. Then D.a ≠ 0 (from hb-related parity).
    push_neg at hdeg
    -- We must have D.a ≠ 0, since otherwise 2·D.a.natDegree = 0 and target ≥ 3.
    have ha : D.a ≠ 0 := by
      intro ha0
      rw [ha0, Polynomial.natDegree_zero, mul_zero] at hdeg
      omega
    -- By parity (LHS even, RHS odd): 2·D.a.natDegree ≥ 2·D.b.natDegree + 4.
    have hparity : 2 * D.a.natDegree ≥ 2 * D.b.natDegree + 4 := by
      rcases Nat.even_or_odd (2 * D.a.natDegree) with hev | hod
      · omega
      · have : Even (2 * D.a.natDegree) := ⟨_, two_mul _⟩
        exact absurd this (Nat.not_even_iff_odd.mpr hod)
    -- Show normPoly.natDegree ≥ 2·D.a.natDegree (D.a² wins at this index).
    have hDa_sq_natDeg : (D.a ^ 2).natDegree = 2 * D.a.natDegree :=
      Polynomial.natDegree_pow _ _
    have hDa_sq_lead :
        (D.a ^ 2).coeff (2 * D.a.natDegree) = D.a.leadingCoeff ^ 2 := by
      rw [show 2 * D.a.natDegree = (D.a ^ 2).natDegree from hDa_sq_natDeg.symm,
          ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_pow]
    have hDa_sq_lead_ne : (D.a.leadingCoeff : ZMod E.q) ^ 2 ≠ 0 :=
      pow_ne_zero _ ((Polynomial.leadingCoeff_ne_zero).mpr ha)
    have hprod_zero :
        (D.b ^ 2 * curveX E).coeff (2 * D.a.natDegree) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hprod_natDeg]; omega
    have hDa_le : 2 * D.a.natDegree ≤ (D.a ^ 2 - D.b ^ 2 * curveX E).natDegree := by
      refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [Polynomial.coeff_sub, hDa_sq_lead, hprod_zero, sub_zero]
      exact hDa_sq_lead_ne
    omega

/-- **`(normPoly).natDegree ≥ 2·D.a.natDegree`** when `D.a ≠ 0`.
Analogous to `normPoly_natDegree_ge_b_curveX` but for the
`D.a^2` summand. -/
private lemma normPoly_natDegree_ge_a_sq
    (D : CoordRingElt E.q) (ha : D.a ≠ 0) :
    2 * D.a.natDegree ≤ (normPoly E D).natDegree := by
  classical
  rw [normPoly_eq]
  have hcurveX_natDeg : (curveX E).natDegree = 3 := by
    refine le_antisymm (curveX_natDegree_le_three E) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    show (curveX E).coeff 3 ≠ 0
    unfold curveX
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
  have hDa_sq_natDeg : (D.a ^ 2).natDegree = 2 * D.a.natDegree :=
    Polynomial.natDegree_pow _ _
  have hDa_sq_lead :
      (D.a ^ 2).coeff (2 * D.a.natDegree) = D.a.leadingCoeff ^ 2 := by
    rw [show 2 * D.a.natDegree = (D.a ^ 2).natDegree from hDa_sq_natDeg.symm,
        ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_pow]
  have hDa_sq_lead_ne : (D.a.leadingCoeff : ZMod E.q) ^ 2 ≠ 0 :=
    pow_ne_zero _ ((Polynomial.leadingCoeff_ne_zero).mpr ha)
  -- Case-split on whether D.b² · curveX dominates the target index 2·D.a.natDegree.
  by_cases hb : D.b = 0
  · rw [hb]
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
               zero_mul, sub_zero]
    rw [hDa_sq_natDeg]
  · have hcurveX_ne : (curveX E) ≠ 0 := by
      intro h
      have := hcurveX_natDeg
      rw [h, Polynomial.natDegree_zero] at this
      omega
    have hbsq_ne : D.b ^ 2 ≠ 0 := pow_ne_zero _ hb
    have hprod_natDeg : (D.b ^ 2 * curveX E).natDegree = 2 * D.b.natDegree + 3 := by
      rw [Polynomial.natDegree_mul hbsq_ne hcurveX_ne, hcurveX_natDeg,
          Polynomial.natDegree_pow]
    by_cases hdeg : 2 * D.b.natDegree + 3 < 2 * D.a.natDegree
    · -- D.a² dominates: use (normPoly).coeff(2·D.a.natDegree) ≠ 0.
      refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [Polynomial.coeff_sub, hDa_sq_lead]
      have hprod_zero :
          (D.b ^ 2 * curveX E).coeff (2 * D.a.natDegree) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hprod_natDeg]; exact hdeg
      rw [hprod_zero, sub_zero]
      exact hDa_sq_lead_ne
    · -- D.b² · curveX dominates: 2·D.b.natDegree + 3 ≥ 2·D.a.natDegree, by parity ≥ +1.
      push_neg at hdeg
      -- (D.b² · curveX).natDegree ≥ 2·D.a.natDegree.
      have hprod_lead :
          (D.b ^ 2 * curveX E).coeff (2 * D.b.natDegree + 3) ≠ 0 := by
        rw [show 2 * D.b.natDegree + 3 = (D.b ^ 2 * curveX E).natDegree from
              hprod_natDeg.symm]
        rw [← Polynomial.leadingCoeff]
        exact (Polynomial.leadingCoeff_ne_zero).mpr (mul_ne_zero hbsq_ne hcurveX_ne)
      -- Note 2·D.b.natDegree + 3 ≠ 2·D.a.natDegree by parity (odd vs even).
      have hparity : 2 * D.b.natDegree + 3 ≠ 2 * D.a.natDegree := by
        rcases Nat.even_or_odd (2 * D.a.natDegree) with hev | hod
        · -- 2·D.a.natDegree even, 2·D.b.natDegree + 3 odd.
          intro heq
          have : Even (2 * D.b.natDegree + 3) := heq.symm ▸ hev
          have : Odd (2 * D.b.natDegree + 3) := ⟨D.b.natDegree + 1, by ring⟩
          omega
        · have : Even (2 * D.a.natDegree) := ⟨_, two_mul _⟩
          exact absurd this (Nat.not_even_iff_odd.mpr hod)
      have : 2 * D.b.natDegree + 3 ≥ 2 * D.a.natDegree + 1 := by omega
      -- (D.a^2 - D.b^2 · curveX).natDegree ≥ 2·D.b.natDegree + 3 ≥ 2·D.a.natDegree + 1.
      have hge : 2 * D.b.natDegree + 3 ≤ (D.a^2 - D.b^2 * curveX E).natDegree := by
        refine Polynomial.le_natDegree_of_ne_zero ?_
        rw [Polynomial.coeff_sub]
        have hDa_zero :
            (D.a ^ 2).coeff (2 * D.b.natDegree + 3) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [hDa_sq_natDeg]; omega
        rw [hDa_zero, zero_sub, neg_ne_zero]
        exact hprod_lead
      omega

/-- **`DLineBiv.natDegree ≤ max(D.a.natDegree, D.b.natDegree + 1)`.** -/
private lemma DLineBiv_natDegree_le
    (lam : ZMod E.q) (D : CoordRingElt E.q) :
    (DLineBiv E lam D).natDegree ≤ max D.a.natDegree (D.b.natDegree + 1) := by
  classical
  -- DLineBiv = D.a.map C - D.b.map C * Q with Q = C(C λ) X + C X.
  show ((D.a.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]))
        - D.b.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])
            * (Polynomial.C (Polynomial.C lam) * Polynomial.X
                + Polynomial.C Polynomial.X)).natDegree ≤ _
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · -- D.a.map C: natDegree ≤ D.a.natDegree.
    refine Polynomial.natDegree_map_le.trans ?_
    omega
  · refine Polynomial.natDegree_mul_le.trans ?_
    have hQ : (Polynomial.C (Polynomial.C lam) * Polynomial.X
                + Polynomial.C (Polynomial.X : Polynomial (ZMod E.q))).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        exact Polynomial.natDegree_X_le
      · exact (Polynomial.natDegree_C _).le.trans (by omega)
    have hbmap : (D.b.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X])).natDegree
                  ≤ D.b.natDegree := Polynomial.natDegree_map_le
    omega

/-- **Lemma B: DLineBiv per-coefficient weight bound.**

For `k ≤ (DLineBiv E lam D).natDegree`,

    3 · ((DLineBiv E lam D).coeff k).natDegree + 2 · k ≤ (normPoly E D).natDegree.

This is the G-row weight bound feeding into the Sylvester determinant
analysis, completing the per-coefficient ingredient list for the
weighted-Sylvester proof of the natDegree bound

    (chord_fiber_product_concrete E lam D).natDegree ≤ (normPoly E D).natDegree. -/
private lemma DLineBiv_coeff_natDegree_weighted_bound
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (k : ℕ) (hk : k ≤ (DLineBiv E lam D).natDegree) :
    3 * ((DLineBiv E lam D).coeff k).natDegree + 2 * k
      ≤ (normPoly E D).natDegree := by
  classical
  by_cases hbz : D.b.coeff k = 0
  · -- D.b.coeff k = 0: natDegree(coeff) ≤ 0.
    have hcoeff_le := DLineBiv_coeff_natDegree_le_zero_of_b_coeff_zero E lam D k hbz
    -- Need: 0·3 + 2k ≤ (normPoly).natDegree, i.e., 2k ≤ (normPoly).natDegree.
    -- Use DLineBiv.natDegree bound: k ≤ max(D.a.natDegree, D.b.natDegree + 1).
    have hk_max : k ≤ max D.a.natDegree (D.b.natDegree + 1) :=
      hk.trans (DLineBiv_natDegree_le E lam D)
    -- Case: D.a ≠ 0 ∨ D.b ≠ 0.
    rcases not_and_or.mp hD with hane | hbne
    · -- D.a ≠ 0: use 2·D.a.natDegree ≤ (normPoly).natDegree.
      have hbnd_a := normPoly_natDegree_ge_a_sq E D hane
      by_cases hb : D.b = 0
      · -- D.b = 0: DLineBiv = D.a.map C, natDegree = D.a.natDegree (sharp).
        have hdline_eq : DLineBiv E lam D
            = D.a.map (Polynomial.C : ZMod E.q →+* (ZMod E.q)[X]) := by
          show D.a.map _ - D.b.map _ * _ = _
          rw [hb]; simp
        have hk_a : k ≤ D.a.natDegree := by
          have : (DLineBiv E lam D).natDegree ≤ D.a.natDegree := by
            rw [hdline_eq]; exact Polynomial.natDegree_map_le
          omega
        omega
      · -- D.b ≠ 0: also have b-bound.
        have hbnd_b := normPoly_natDegree_ge_b_curveX E D hb
        omega
    · -- D.b ≠ 0: use 2·D.b.natDegree + 3 ≤ (normPoly).natDegree.
      have hbnd_b := normPoly_natDegree_ge_b_curveX E D hbne
      by_cases ha : D.a = 0
      · -- D.a = 0: D.a.natDegree = 0. From hk_max: k ≤ max(0, D.b.natDegree + 1) = D.b.natDegree + 1.
        rw [ha] at hk_max
        simp at hk_max
        omega
      · -- D.a ≠ 0: also have a-bound.
        have hbnd_a := normPoly_natDegree_ge_a_sq E D ha
        omega
  · -- D.b.coeff k ≠ 0: natDegree(coeff) ≤ 1, k ≤ D.b.natDegree.
    have hcoeff_le := DLineBiv_coeff_natDegree_le_one E lam D k
    have hk_le : k ≤ D.b.natDegree :=
      Polynomial.le_natDegree_of_ne_zero hbz
    have hb : D.b ≠ 0 := by
      intro hb0
      apply hbz
      rw [hb0, Polynomial.coeff_zero]
    have hbnd_b := normPoly_natDegree_ge_b_curveX E D hb
    omega

/-! ## Main theorem (target): the natDegree inequality

The weighted-Sylvester result: for any `D` with `¬ (D.a = 0 ∧ D.b = 0)`,

    (chord_fiber_product_concrete E lam D).natDegree ≤ (normPoly E D).natDegree.

Proof outline:

Let `f = chordCubicBiv E lam`, `g = DLineBiv E lam D`, `m = 3`,
`n = g.natDegree`, `w = (normPoly E D).natDegree`. We have:

* `chord_fiber_product = Polynomial.resultant f g m n
                       = (Polynomial.sylvester f g m n).det`.
* From `Matrix.det_apply`: `det = Σ σ : Equiv.Perm, sgn σ · ∏ i, M[σ i, i]`.
* For each permutation σ, the product `∏_i M[σ i, i]` is a product of
  `m + n` entries, each either an f-coeff or g-coeff (or zero).
* By Lemma A (chordCubicBiv) and Lemma B (DLineBiv), each entry has
  weighted natDegree bounded:
  - f-entries (at the `n` f-columns, with index `i - j_f`):
    `3·natDeg(f.coeff(i-j_f)) + 2·(i-j_f) ≤ 6`.
  - g-entries (at the `m` g-columns, with index `i - j_g`):
    `3·natDeg(g.coeff(i-j_g)) + 2·(i-j_g) ≤ w`.
* Summing the weighted inequalities over all `m + n` columns:
  `3·Σ_j natDeg(M[σ j, j]) + 2·Σ_j (σ j - j_offset) ≤ 6n + 3w`.
* `Σ_j (σ j - j_offset) = m·n = 3n` (standard Sylvester fact).
* So `3·Σ natDeg ≤ 6n + 3w − 2·3n = 3w`, hence `Σ natDeg ≤ w`.
* By `Polynomial.natDegree_prod_le`: `natDeg(prod) ≤ Σ natDeg ≤ w`.
* By `Polynomial.natDegree_sum_le_of_forall_le` over permutations:
  `natDeg(det) ≤ w`.

The Sylvester sum-bound is the substantive remaining work: a
`Matrix.det_apply`-style expansion that tracks the index sum
`Σ_j (σ j - j_offset) = m·n` and applies the per-column weight bounds. -/

/-! ### Sylvester column offsets and index-sum identity

Combinatorial helpers for the determinant analysis. -/

/-- The column offset for the Sylvester matrix `sylvester f g m n`:
- For `j` in the first `m` columns (g-columns), `off j = j.val`.
- For `j` in the last `n` columns (f-columns), `off j = j.val - m`.
This corresponds to the shift `j₁` used in the matrix definition. -/
private noncomputable def sylvesterOff (m n : ℕ) (j : Fin (m + n)) : ℕ :=
  j.addCases (motive := fun _ => ℕ) (fun j₁ : Fin m => j₁.val) (fun j₁ : Fin n => j₁.val)

/-- **Sum of Sylvester column offsets** equals `m(m-1)/2 + n(n-1)/2`. -/
private lemma sum_sylvesterOff_eq
    (m n : ℕ) :
    (∑ j : Fin (m + n), sylvesterOff m n j)
      = m * (m - 1) / 2 + n * (n - 1) / 2 := by
  classical
  rw [Fintype.sum_equiv finSumFinEquiv.symm
        (sylvesterOff m n)
        (fun j => sylvesterOff m n (finSumFinEquiv j))
        (fun x => by simp)]
  rw [Fintype.sum_sum_type]
  congr 1
  · have h1 : ∀ j₁ : Fin m,
        sylvesterOff m n (finSumFinEquiv (Sum.inl j₁)) = j₁.val := by
      intro j₁
      simp [sylvesterOff, finSumFinEquiv, Fin.addCases]
    rw [show (∑ j₁ : Fin m, sylvesterOff m n (finSumFinEquiv (Sum.inl j₁)))
          = ∑ j₁ : Fin m, j₁.val from
          Finset.sum_congr rfl (fun j₁ _ => h1 j₁)]
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id]
  · have h2 : ∀ j₁ : Fin n,
        sylvesterOff m n (finSumFinEquiv (Sum.inr j₁)) = j₁.val := by
      intro j₁
      simp [sylvesterOff, finSumFinEquiv, Fin.addCases]
    rw [show (∑ j₁ : Fin n, sylvesterOff m n (finSumFinEquiv (Sum.inr j₁)))
          = ∑ j₁ : Fin n, j₁.val from
          Finset.sum_congr rfl (fun j₁ _ => h2 j₁)]
    rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id]

/-- **Sum of (σ j).val over a permutation** equals `(m+n)(m+n-1)/2`. -/
private lemma sum_perm_val
    {m n : ℕ} (σ : Equiv.Perm (Fin (m + n))) :
    (∑ j : Fin (m + n), (σ j).val) = (m + n) * (m + n - 1) / 2 := by
  classical
  rw [Equiv.sum_comp σ (fun j : Fin (m + n) => j.val)]
  rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id]

/-- **Index sum identity for Sylvester**: `Σ_j ((σ j).val - sylvesterOff j) = m * n`,
provided each `(σ j).val ≥ sylvesterOff j` (so the σ-image lands within
the row range of each column). -/
private lemma sum_sylvester_idx_eq
    {m n : ℕ} (σ : Equiv.Perm (Fin (m + n)))
    (h : ∀ j, sylvesterOff m n j ≤ (σ j).val) :
    (∑ j : Fin (m + n), ((σ j).val - sylvesterOff m n j)) = m * n := by
  classical
  -- We show: (Σ idx) + (Σ off) = Σ (σ j).val, which gives Σ idx = Σ σ - Σ off.
  -- Using Nat.sub_add_cancel pointwise.
  have hadd : (∑ j : Fin (m + n), ((σ j).val - sylvesterOff m n j))
              + (∑ j : Fin (m + n), sylvesterOff m n j)
            = (∑ j : Fin (m + n), (σ j).val) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact Nat.sub_add_cancel (h j)
  rw [sum_perm_val σ, sum_sylvesterOff_eq] at hadd
  -- hadd: (Σ idx) + (m(m-1)/2 + n(n-1)/2) = (m+n)(m+n-1)/2.
  -- Need: Σ idx = m*n.
  have h_m : Even (m * (m - 1)) := Nat.even_mul_pred_self m
  have h_n : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  have h_mn_full : Even ((m + n) * (m + n - 1)) := Nat.even_mul_pred_self (m + n)
  obtain ⟨a, ha⟩ := h_m
  obtain ⟨b, hb⟩ := h_n
  obtain ⟨c, hc⟩ := h_mn_full
  -- Show: (m+n)(m+n-1) = m(m-1) + n(n-1) + 2mn (over ℕ).
  have hkey : (m + n) * (m + n - 1) = m * (m - 1) + n * (n - 1) + 2 * m * n := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hm, hn]
      · simp [hm]
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · -- Both positive: lift to ℤ for clean ring arithmetic.
        zify [Nat.sub_le, hm, hn, Nat.add_sub_cancel,
              show 1 ≤ m + n from by omega]
        ring
  rw [ha, hb, hc] at hkey hadd
  have h_div_a : (a + a) / 2 = a := by omega
  have h_div_b : (b + b) / 2 = b := by omega
  have h_div_c : (c + c) / 2 = c := by omega
  rw [h_div_a, h_div_b, h_div_c] at hadd
  -- hadd: Σ idx + (a + b) = c.
  -- hkey: c + c = (a + a) + (b + b) + 2 * m * n.
  -- ⇒ c = a + b + m*n.
  -- ⇒ Σ idx = m * n.
  have hc_eq : c = a + b + m * n := by linarith
  linarith

/-! ### Per-permutation product bound

For each permutation σ of the Sylvester matrix index set, the product
`∏ j, M[σ j, j]` has natDegree ≤ w (the normPoly natDegree). Combined
with `Matrix.det_apply` and `natDegree_sum_le_of_forall_le`, this
gives the determinant natDegree bound. -/

/-- **Per-permutation product bound** for the chord/DLine Sylvester matrix.

For any permutation σ of `Fin (3 + DLineBiv.natDegree)`,

    (∏ j, M[σ j, j]).natDegree ≤ (normPoly).natDegree

where M is the Sylvester matrix of `chordCubicBiv` and `DLineBiv`.

The proof case-splits on whether some entry vanishes (in which case the
product is zero) or all entries are nonzero (the weighted-Sylvester
sum-bound applies). -/
private lemma sylvester_chord_DLine_perm_prod_natDegree_le
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (σ : Equiv.Perm (Fin ((chordCubicBiv E lam).natDegree
                              + (DLineBiv E lam D).natDegree))) :
    (∏ i, Polynomial.sylvester (chordCubicBiv E lam) (DLineBiv E lam D)
            (chordCubicBiv E lam).natDegree (DLineBiv E lam D).natDegree
            (σ i) i).natDegree
      ≤ (normPoly E D).natDegree := by
  classical
  -- Case 1: some entry is zero ⇒ product = 0.
  by_cases hzero : ∃ j,
      Polynomial.sylvester (chordCubicBiv E lam) (DLineBiv E lam D)
        (chordCubicBiv E lam).natDegree (DLineBiv E lam D).natDegree (σ j) j = 0
  · obtain ⟨j₀, hj₀⟩ := hzero
    have hprodzero :
        (∏ i, Polynomial.sylvester (chordCubicBiv E lam) (DLineBiv E lam D)
              (chordCubicBiv E lam).natDegree (DLineBiv E lam D).natDegree (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) hj₀
    rw [hprodzero, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · -- Case 2: all entries nonzero. Apply weighted-Sylvester sum-bound.
    push_neg at hzero
    -- Step 1: support — each (σ j).val is in the row range.
    have hsupp : ∀ j : Fin ((chordCubicBiv E lam).natDegree
                              + (DLineBiv E lam D).natDegree),
        sylvesterOff (chordCubicBiv E lam).natDegree
          (DLineBiv E lam D).natDegree j ≤ (σ j).val := by
      intro j
      have hne := hzero j
      -- Decompose j via addCases: j is castAdd of some j₁ : Fin m, or natAdd of j₁ : Fin n.
      obtain ⟨j₁, rfl⟩ | ⟨j₁, rfl⟩ :
          (∃ j₁ : Fin (chordCubicBiv E lam).natDegree,
              j = Fin.castAdd (DLineBiv E lam D).natDegree j₁) ∨
          (∃ j₁ : Fin (DLineBiv E lam D).natDegree,
              j = Fin.natAdd (chordCubicBiv E lam).natDegree j₁) := by
        rcases Nat.lt_or_ge j.val (chordCubicBiv E lam).natDegree with hjm | hjm
        · left
          refine ⟨⟨j.val, hjm⟩, ?_⟩
          ext; rfl
        · right
          have hjm_le : (chordCubicBiv E lam).natDegree ≤ j.val := hjm
          refine ⟨⟨j.val - (chordCubicBiv E lam).natDegree, ?_⟩, ?_⟩
          · have := j.isLt
            omega
          · ext; simp [Fin.natAdd]; omega
      · -- j is castAdd j₁ (g-col case).
        unfold sylvesterOff
        rw [Fin.addCases_left]
        unfold Polynomial.sylvester at hne
        rw [Matrix.of_apply, Fin.addCases_left] at hne
        by_contra hlt
        push_neg at hlt
        have hnotin :
            ¬ (σ (Fin.castAdd _ j₁)).val ∈
              Set.Icc j₁.val (j₁.val + (DLineBiv E lam D).natDegree) := by
          simp only [Set.mem_Icc, not_and_or]
          left; omega
        rw [if_neg hnotin] at hne
        exact hne rfl
      · -- j is natAdd j₁ (f-col case).
        unfold sylvesterOff
        rw [Fin.addCases_right]
        unfold Polynomial.sylvester at hne
        rw [Matrix.of_apply, Fin.addCases_right] at hne
        by_contra hlt
        push_neg at hlt
        have hnotin :
            ¬ (σ (Fin.natAdd _ j₁)).val ∈
              Set.Icc j₁.val (j₁.val + (chordCubicBiv E lam).natDegree) := by
          simp only [Set.mem_Icc, not_and_or]
          left; omega
        rw [if_neg hnotin] at hne
        exact hne rfl
    -- TODO: combine with weighted bounds (Lemmas A, B) and index-sum identity.
    sorry

theorem chord_fiber_product_concrete_natDegree_le_normPoly_natDegree
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (chord_fiber_product_concrete E lam D).natDegree
      ≤ (normPoly E D).natDegree := by
  classical
  -- chord_fiber_product = (sylvester chordCubicBiv DLineBiv 3 n).det.
  unfold chord_fiber_product_concrete
  rw [Polynomial.resultant, Matrix.det_apply]
  -- Goal: (Σ σ : Perm, sgn σ • ∏ i, M (σ i) i).natDegree ≤ ...
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro σ _
  -- Extract sgn σ as ±1, so it doesn't affect natDegree.
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · -- sgn = 1.
    rw [hsign]
    simp only [one_smul]
    exact sylvester_chord_DLine_perm_prod_natDegree_le E lam D hD σ
  · -- sgn = -1.
    rw [hsign]
    simp only [Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    exact sylvester_chord_DLine_perm_prod_natDegree_le E lam D hD σ

end Divisor
