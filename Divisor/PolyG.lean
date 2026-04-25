/-
  Divisor/PolyG.lean — paper §5 polynomial G + total-degree lemmas.

  Reuses `polyGFull` (defined in `Divisor/ClearedFullPoly.lean`),
  which exactly matches paper §5's G:

    G := ∑_k β_k · ∏_{k'≠k} ℓ_{Q_{k'}} · ∏_j ℓ_{R_j}
       + ∑_j m_j · ∏_k ℓ_{Q_k} · ∏_{j'≠j} ℓ_{R_{j'}}

  This file adds the `total_degree_le` bounds required for the
  corrected `bivariate_poly_zeros_on_ExE_le` axiom (DKL+Bezout).
-/
import Divisor.ClearedFullPoly

namespace Divisor

open MvPolynomial

variable (E : ECSetup)

/-! ### Step B3 — `lineEvalNumAtFull` total-degree

  `lineEvalNumAtFull E P = (y(P) − Y₀)(X₁ − X₀) − (x(P) − X₀)(Y₁ − Y₀)`.
  Each parenthesised factor has total degree ≤ 1 (a constant minus an
  `X i`); each product has total degree ≤ 2; the subtraction preserves
  the bound. Hence `total_degree_le E (lineEvalNumAtFull E P) 2`. -/
theorem lineEvalNumAtFull_total_degree_le (P : ZMod E.q × ZMod E.q) :
    total_degree_le E (lineEvalNumAtFull E P) 2 := by
  unfold lineEvalNumAtFull
  refine total_degree_le.sub ?_ ?_
  · -- (embedScalar pt.2 - varA₀y) * lamDenFull
    have h1 : total_degree_le E (embedScalarFull E P.2 - varA₀y E) 1 := by
      unfold embedScalarFull varA₀y
      exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
        (total_degree_le.X _)
    have h2 : total_degree_le E (lamDenFull E) 1 := by
      unfold lamDenFull varA₁x varA₀x
      exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)
    exact total_degree_le.mul h1 h2
  · -- (embedScalar pt.1 - varA₀x) * lamNumFull
    have h1 : total_degree_le E (embedScalarFull E P.1 - varA₀x E) 1 := by
      unfold embedScalarFull varA₀x
      exact total_degree_le.sub ((total_degree_le.C _).mono (Nat.zero_le _))
        (total_degree_le.X _)
    have h2 : total_degree_le E (lamNumFull E) 1 := by
      unfold lamNumFull varA₁y varA₀y
      exact total_degree_le.sub (total_degree_le.X _) (total_degree_le.X _)
    exact total_degree_le.mul h1 h2

/-! ### Step B4 — `polyGFull` total-degree (paper §5)

  Each summand of `polyGFull` is a product of:
  * one constant (β_k or m_j) — total degree 0,
  * `(d-1)` factors of `lineEvalNumAtFull E (Q k')` — each degree 2,
  * `M` factors of `lineEvalNumAtFull E (R j)` — each degree 2.
  (Or symmetrically: `d` Q-factors and `(M-1)` R-factors.)

  Total per summand: `2·(d - 1 + M) = 2·(d + M - 1)`. Sum over `d + M`
  summands preserves the bound. Hence `polyGFull` has total degree at
  most `2·(d + M - 1)`.

  We state the bound as `2·(d + M)` (the looser, more-convenient form
  with `+M` instead of `+M-1`); the tighter `2·(d + M - 1)` form is
  available by setting `M ↦ M+1` if needed.  This avoids the
  natural-number subtraction issue when `d = 0` or `M = 0`. -/
theorem polyGFull_total_degree_le
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q) :
    total_degree_le E (polyGFull E Q beta R m) (2 * (d + M)) := by
  classical
  unfold polyGFull
  refine total_degree_le.add ?_ ?_
  · -- ∑_k β_k · ∏_{k'≠k} ℓ_{Q k'} · ∏_j ℓ_{R j}
    refine total_degree_le.sum _ _ ?_
    intro k _
    have hβ : total_degree_le E (MvPolynomial.C (beta k) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    -- ∏_{k'∈univ.erase k} ℓ_{Q k'} : product of (d-1) factors of degree 2
    have hQErase : total_degree_le E
        (∏ k' ∈ (Finset.univ (α := Fin d)).erase k, lineEvalNumAtFull E (Q k'))
        (((Finset.univ (α := Fin d)).erase k).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k' _
      exact lineEvalNumAtFull_total_degree_le E (Q k')
    -- ∏_{j∈univ} ℓ_{R j} : product of M factors of degree 2
    have hR : total_degree_le E
        (∏ j : Fin M, lineEvalNumAtFull E (R j))
        ((Finset.univ (α := Fin M)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j _
      exact lineEvalNumAtFull_total_degree_le E (R j)
    have hMul := total_degree_le.mul (total_degree_le.mul hβ hQErase) hR
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin d)).erase k).card ≤ d := by
      have := Finset.card_erase_le (s := (Finset.univ (α := Fin d))) (a := k)
      simpa using this
    have hMC : (Finset.univ (α := Fin M)).card = M := by simp
    rw [hMC]
    set ce := ((Finset.univ (α := Fin d)).erase k).card with hce
    have hCE : ce * 2 ≤ d * 2 := Nat.mul_le_mul_right 2 hEC
    omega
  · -- ∑_j m_j · ∏_k ℓ_{Q k} · ∏_{j'≠j} ℓ_{R j'}
    refine total_degree_le.sum _ _ ?_
    intro j _
    have hm : total_degree_le E (MvPolynomial.C (m j) : FourVarPoly E.q) 0 :=
      total_degree_le.C _
    have hQ : total_degree_le E
        (∏ k : Fin d, lineEvalNumAtFull E (Q k))
        ((Finset.univ (α := Fin d)).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro k _
      exact lineEvalNumAtFull_total_degree_le E (Q k)
    have hRErase : total_degree_le E
        (∏ j' ∈ (Finset.univ (α := Fin M)).erase j, lineEvalNumAtFull E (R j'))
        (((Finset.univ (α := Fin M)).erase j).card * 2) := by
      refine total_degree_le.prod_const _ _ ?_
      intro j' _
      exact lineEvalNumAtFull_total_degree_le E (R j')
    have hMul := total_degree_le.mul (total_degree_le.mul hm hQ) hRErase
    refine hMul.mono ?_
    have hEC : ((Finset.univ (α := Fin M)).erase j).card ≤ M := by
      have := Finset.card_erase_le (s := (Finset.univ (α := Fin M))) (a := j)
      simpa using this
    have hDC : (Finset.univ (α := Fin d)).card = d := by simp
    rw [hDC]
    set ce := ((Finset.univ (α := Fin M)).erase j).card with hce
    have hCE : ce * 2 ≤ M * 2 := Nat.mul_le_mul_right 2 hEC
    omega

end Divisor
