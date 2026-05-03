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

/-- **Lemma B (target): DLineBiv per-coefficient weight bound.**

For `k ≤ (DLineBiv E lam D).natDegree`,

    3 · ((DLineBiv E lam D).coeff k).natDegree + 2 · k ≤ (normPoly E D).natDegree.

This is the G-row weight bound feeding into the Sylvester determinant
analysis, completing the per-coefficient ingredient list for the
weighted-Sylvester proof of the natDegree bound

    (chord_fiber_product_concrete E lam D).natDegree ≤ (normPoly E D).natDegree. -/
private lemma DLineBiv_coeff_natDegree_weighted_bound
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (k : ℕ) (_hk : k ≤ (DLineBiv E lam D).natDegree) :
    3 * ((DLineBiv E lam D).coeff k).natDegree + 2 * k
      ≤ (normPoly E D).natDegree :=
  sorry

end Divisor
