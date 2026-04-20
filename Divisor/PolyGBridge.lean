/-
  Divisor/PolyGBridge.lean

  Polynomial form of `polyG` (T4 extractor bridge infrastructure).

  `polyG E Q β R m A₀ A₁` is a scalar-valued function on `E × E`
  (see `Divisor/LogDeriv.lean`). In T4's extractor soundness
  argument, we need `polyG` to vanish on non-vertical pairs of
  `E × E`; in polynomial-form we'd derive this from
  `polyGPoly A₀ %ₘ curveEqPoly = 0`, via the identity
  `bivEval (polyGPoly Q β R m A₀) A₁ = polyG E Q β R m A₀ A₁`.

  This file is part of the axiom-elimination programme: phase D1
  of the plan (`logDerivCheckFn ≡ 0 ⇒ polyG ≡ 0` bridge). It
  introduces the polynomial form and its evaluation identity; the
  bridge from `clearedFiberPoly` to `polyGPoly` (the paper-level
  residue identity) is future work.
-/
import Divisor.ClearedPolyForm
import Divisor.PolyFibK

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Polynomial form of `polyG` at fixed `A₀`

    Using `lineEvalNumAt A₀ P = (P.2 - A₀.2)·lamDen - (P.1 - A₀.1)·lamNum`
    in place of `ellP E P A₀ A₁`, `polyGPoly` is an element of
    `(ZMod E.q)[X][X]` whose `bivEval` at `A₁` reproduces `polyG`.
-/

/-- Polynomial form of `polyG` (at fixed `A₀`). -/
noncomputable def polyGPoly
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  (∑ k : Fin d, embedScalar (E := E) (β k) *
    (∏ k' ∈ Finset.univ.erase k, lineEvalNumAt (E := E) A₀ (Q k')) *
    (∏ j : Fin M, lineEvalNumAt (E := E) A₀ (R j)))
  + (∑ j : Fin M, embedScalar (E := E) (m j) *
    (∏ k : Fin d, lineEvalNumAt (E := E) A₀ (Q k)) *
    (∏ j' ∈ Finset.univ.erase j, lineEvalNumAt (E := E) A₀ (R j')))

/-- `bivEval (polyGPoly Q β R m A₀) A₁ = polyG E Q β R m A₀ A₁`. -/
theorem bivEval_polyGPoly
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) :
    bivEval (polyGPoly (E := E) Q β R m A₀) A₁ =
      polyG E Q β R m A₀ A₁ := by
  unfold polyGPoly polyG
  rw [bivEval_add, bivEval_finset_sum, bivEval_finset_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [bivEval_mul, bivEval_mul, bivEval_finset_prod, bivEval_finset_prod,
        bivEval_embedScalar]
    have h1 : ∀ k' ∈ Finset.univ.erase k,
        bivEval (lineEvalNumAt (E := E) A₀ (Q k')) A₁ = ellP E (Q k') A₀ A₁ :=
      fun k' _ => bivEval_lineEvalNumAt_eq_ellP E A₀ (Q k') A₁
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin M)),
        bivEval (lineEvalNumAt (E := E) A₀ (R j)) A₁ = ellP E (R j) A₀ A₁ :=
      fun j _ => bivEval_lineEvalNumAt_eq_ellP E A₀ (R j) A₁
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
  · apply Finset.sum_congr rfl
    intro j _
    rw [bivEval_mul, bivEval_mul, bivEval_finset_prod, bivEval_finset_prod,
        bivEval_embedScalar]
    have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d)),
        bivEval (lineEvalNumAt (E := E) A₀ (Q k)) A₁ = ellP E (Q k) A₀ A₁ :=
      fun k _ => bivEval_lineEvalNumAt_eq_ellP E A₀ (Q k) A₁
    have h2 : ∀ j' ∈ Finset.univ.erase j,
        bivEval (lineEvalNumAt (E := E) A₀ (R j')) A₁ = ellP E (R j') A₀ A₁ :=
      fun j' _ => bivEval_lineEvalNumAt_eq_ellP E A₀ (R j') A₁
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]

/-! ## Outer natDegree bound

    `lineEvalNumAt` has outer natDegree ≤ 1 (already proved in
    `ClearedPolyForm.lean`), so its product over `d+M` or `d+M-1`
    factors gives a combined outer natDegree ≤ `d+M`.
-/

/-- `polyGPoly` has outer natDegree ≤ `d + M`. -/
theorem polyGPoly_natDegree_le {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (polyGPoly (E := E) Q β R m A₀).natDegree ≤ d + M := by
  unfold polyGPoly
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · -- First sum: each term has natDegree ≤ (d - 1) + M ≤ d + M.
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro k _
    have hQerase :
        (∏ k' ∈ Finset.univ.erase k,
           lineEvalNumAt (E := E) A₀ (Q k')).natDegree
          ≤ (Finset.univ.erase k).card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun k' _ =>
        lineEvalNumAt_natDegree_le E A₀ (Q k'))).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hRall :
        (∏ j : Fin M, lineEvalNumAt (E := E) A₀ (R j)).natDegree
          ≤ (Finset.univ : Finset (Fin M)).card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun j _ =>
        lineEvalNumAt_natDegree_le E A₀ (R j))).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    refine Polynomial.natDegree_mul_le.trans ?_
    refine (Nat.add_le_add (Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (by rw [embedScalar_natDegree_le]) hQerase)) hRall).trans ?_
    rw [Nat.zero_add, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
    omega
  · -- Second sum: each term has natDegree ≤ d + (M - 1) ≤ d + M.
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro j _
    have hQall :
        (∏ k : Fin d, lineEvalNumAt (E := E) A₀ (Q k)).natDegree
          ≤ (Finset.univ : Finset (Fin d)).card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun k _ =>
        lineEvalNumAt_natDegree_le E A₀ (Q k))).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hRerase :
        (∏ j' ∈ Finset.univ.erase j,
           lineEvalNumAt (E := E) A₀ (R j')).natDegree
          ≤ (Finset.univ.erase j).card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (fun j' _ =>
        lineEvalNumAt_natDegree_le E A₀ (R j'))).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    refine Polynomial.natDegree_mul_le.trans ?_
    refine (Nat.add_le_add (Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (by rw [embedScalar_natDegree_le]) hQall)) hRerase).trans ?_
    rw [Nat.zero_add, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
    omega

/-! ## Inner natDegree bound -/

/-- `polyGPoly` inner natDegree ≤ `d + M`. -/
theorem InnerDegLe_polyGPoly {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (β : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (polyGPoly (E := E) Q β R m A₀) (d + M) := by
  unfold polyGPoly
  have hFirst : InnerDegLe (E := E)
      (∑ k : Fin d, embedScalar (E := E) (β k) *
        (∏ k' ∈ Finset.univ.erase k, lineEvalNumAt (E := E) A₀ (Q k')) *
        (∏ j : Fin M, lineEvalNumAt (E := E) A₀ (R j))) (d + M) := by
    refine InnerDegLe.sum (Finset.univ : Finset (Fin d)) _ (d + M) ?_
    intro k _
    have hβterm : InnerDegLe (E := E) (embedScalar (E := E) (β k) *
        ∏ k' ∈ Finset.univ.erase k, lineEvalNumAt (E := E) A₀ (Q k')) (d - 1) := by
      have hprod : InnerDegLe (E := E)
          (∏ k' ∈ Finset.univ.erase k, lineEvalNumAt (E := E) A₀ (Q k'))
          (d - 1) := by
        refine (InnerDegLe.prod (Finset.univ.erase k) _ (fun _ => 1) (fun k' _ =>
          InnerDegLe_lineEvalNumAt A₀ (Q k'))).weaken ?_
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_one,
            Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin]
      exact ((InnerDegLe_embedScalar _).mul hprod).weaken (by omega)
    have hRall : InnerDegLe (E := E) (∏ j : Fin M,
        lineEvalNumAt (E := E) A₀ (R j)) M := by
      refine (InnerDegLe.prod (Finset.univ : Finset (Fin M)) _ (fun _ => 1)
        (fun j _ => InnerDegLe_lineEvalNumAt A₀ (R j))).weaken ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_univ,
          Fintype.card_fin]
    exact (hβterm.mul hRall).weaken (by omega)
  have hSecond : InnerDegLe (E := E)
      (∑ j : Fin M, embedScalar (E := E) (m j) *
        (∏ k : Fin d, lineEvalNumAt (E := E) A₀ (Q k)) *
        (∏ j' ∈ Finset.univ.erase j, lineEvalNumAt (E := E) A₀ (R j'))) (d + M) := by
    refine InnerDegLe.sum (Finset.univ : Finset (Fin M)) _ (d + M) ?_
    intro j _
    have hmterm : InnerDegLe (E := E) (embedScalar (E := E) (m j) *
        ∏ k : Fin d, lineEvalNumAt (E := E) A₀ (Q k)) d := by
      have hprod : InnerDegLe (E := E) (∏ k : Fin d,
          lineEvalNumAt (E := E) A₀ (Q k)) d := by
        refine (InnerDegLe.prod (Finset.univ : Finset (Fin d)) _ (fun _ => 1)
          (fun k _ => InnerDegLe_lineEvalNumAt A₀ (Q k))).weaken ?_
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_univ,
            Fintype.card_fin]
      exact ((InnerDegLe_embedScalar _).mul hprod).weaken (by omega)
    have hRerase : InnerDegLe (E := E) (∏ j' ∈ Finset.univ.erase j,
        lineEvalNumAt (E := E) A₀ (R j')) (M - 1) := by
      refine (InnerDegLe.prod (Finset.univ.erase j) _ (fun _ => 1)
        (fun j' _ => InnerDegLe_lineEvalNumAt A₀ (R j'))).weaken ?_
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_one,
          Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
    exact (hmterm.mul hRerase).weaken (by omega)
  exact (hFirst.add hSecond).weaken (by simp)

end Divisor
