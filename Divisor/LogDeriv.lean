/-
  Divisor/LogDeriv.lean

  Corollary 1 (Schwartz-Zippel for the Log-Derivative Check).

  Proof structure (following the paper):

  1. By Lemma 6 (norm decomposition), f(Q₀,Q₁) equals the log-derivative
     of N(D) evaluated at (L_Q=0) minus the RHS sum.

  2. N(D) = lc(D)^3 * prod_k (z - z(Q_k))^{beta_k} in F_q(z), so
     L(N(D)) = sum_k beta_k / (z - z(Q_k)).

  3. Evaluating at z = mu and noting mu - z(P) = -L_Q(P):
     f = 0 iff sum_k beta_k/L_Q(Q_k) + sum_j m_j/L_Q(R_j) = 0.

  4. Define ell_P := (y(P)-Y0)(X1-X0) - (x(P)-X0)(Y1-Y0),
     which satisfies ell_P = L_Q(P) * (X1-X0).
     Clearing denominators: f = 0 iff G = 0 where
       G = sum_k beta_k * prod_{k'!=k} ell_{Q_{k'}} * prod_j ell_{R_j}
         + sum_j m_j * prod_k ell_{Q_k} * prod_{j'!=j} ell_{R_{j'}}

  5. deg(G) <= 2*(d+M-1) where d = #{distinct zeros of D}.
     Since d <= degE(D), deg(G) <= 2*(degE(D)+M-1).

  6. If f not identically zero on E x E, then G not identically zero.
     E x E has degree 9 in P^4 (complete intersection of two cubics).
     By Bezout: {G=0} cap (E x E) is a curve of degree <= 2*deg(G)*9/2 = 9*deg(G).
     By variety bound (DKL): #zeros <= 18*(degE(D)+M-1) * q.

  7. Probability bound: Pr[f=0] <= 18*(degE(D)+M-1)*q / (#E-1)(#E-3).
-/
import Divisor.Defs
import Divisor.Axioms
import Divisor.BassaMonic

open Finset Classical

namespace Divisor

variable (E : ECSetup)

/-! ## The linear form ell_P on E x E -/

/-- ell_P(X0,Y0,X1,Y1) = (y(P)-Y0)(X1-X0) - (x(P)-X0)(Y1-Y0)
    Satisfies ell_P = L_Q(P) * (X1-X0) where L_Q is the line
    through (X0,Y0) and (X1,Y1). -/
def ellP (P : ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (P.2 - A₀.2) * (A₁.1 - A₀.1) - (P.1 - A₀.1) * (A₁.2 - A₀.2)

/-- ell_P = L_Q(P) * (X1 - X0) -/
theorem ellP_eq_lineEval_mul (P A₀ A₁ : ZMod E.q × ZMod E.q)
    (hx : A₀.1 ≠ A₁.1) :
    ellP E P A₀ A₁ =
    (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval P.1 P.2 * (A₁.1 - A₀.1) := by
  simp only [ellP, lineThrough, Line.eval, slopeOf]
  have hxne : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp
  ring

/-- ell_P = linearFormL (used in BassaMonic) -/
theorem ellP_eq_linearFormL (P A₀ A₁ : ZMod E.q × ZMod E.q) :
    ellP E P A₀ A₁ = linearFormL E A₀ A₁ P := by
  simp only [ellP, linearFormL]

/-! ## The denominator-cleared polynomial G

G(A₀,A₁) = sum_k beta_k * prod_{k'!=k} ell_{Q_k'} * prod_j ell_{R_j}
          + sum_j m_j * prod_k ell_{Q_k} * prod_{j'!=j} ell_{R_{j'}}

G = 0 iff f = 0 on the valid challenge space (X1!=X0, all ell != 0).
-/

/-- The denominator-cleared polynomial G.
    Parameters: zeros Q with multiplicities beta, target points R with
    coefficients m. -/
noncomputable def polyG
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  -- First sum: sum_k beta_k * prod_{k'!=k} ell_{Q_k'} * prod_j ell_{R_j}
  (Finset.univ.sum (fun k =>
    beta k *
    ((Finset.univ.erase k).prod (fun k' => ellP E (Q k') A₀ A₁)) *
    (Finset.univ.prod (fun j => ellP E (R j) A₀ A₁)))) +
  -- Second sum: sum_j m_j * prod_k ell_{Q_k} * prod_{j'!=j} ell_{R_{j'}}
  (Finset.univ.sum (fun j =>
    m j *
    (Finset.univ.prod (fun k => ellP E (Q k) A₀ A₁)) *
    ((Finset.univ.erase j).prod (fun j' => ellP E (R j') A₀ A₁))))

/-! ## Denominator-clearing (algebraic)

The core algebraic step in paper `cor:log-derivative`'s proof:
`Σ c_i / p_i = 0` is equivalent to `Σ c_i · Π_{j≠i} p_j = 0`, under the
assumption that every `p_i ≠ 0`. Applied in the soundness argument to
clear the denominators `L(Q_k)` and `L(R_j)` in the log-derivative
identity, turning the identity into a polynomial equation that can be
bounded via variety SZ. -/

theorem sum_div_iff_sum_mul_prod_erase {α : Type*} [DecidableEq α]
    {K : Type*} [Field K] (s : Finset α) (p c : α → K)
    (hNonzero : ∀ i ∈ s, p i ≠ 0) :
    (∑ i ∈ s, c i / p i) = 0 ↔
    (∑ i ∈ s, c i * ∏ j ∈ s.erase i, p j) = 0 := by
  have hProd : ∏ i ∈ s, p i ≠ 0 := Finset.prod_ne_zero_iff.mpr hNonzero
  have hEq : (∑ i ∈ s, c i * ∏ j ∈ s.erase i, p j)
           = (∏ i ∈ s, p i) * ∑ i ∈ s, c i / p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_prod_erase s p hi]
    have hpi : p i ≠ 0 := hNonzero i hi
    field_simp
    ring
  constructor
  · intro h
    rw [hEq, h, mul_zero]
  · intro h
    rw [hEq] at h
    exact (mul_eq_zero.mp h).resolve_left hProd

/-! ## Concrete evaluation functions -/

/-- Paper-faithful log-derivative `(dD/dz)/D` on `E` w.r.t. `z = y − λx`.

    Chain rule: `dD/dz = (∂D/∂x)·(dx/dz) + (∂D/∂y)·(dy/dz)` with
    `∂D/∂x = a'(x) − b'(x)·y`, `∂D/∂y = −b(x)`,
    `dx/dz = 2y/(3x²+A − 2λy)`, `dy/dz = (3x²+A)/(3x²+A − 2λy)`
    (from the chord parametrisation and `2y·dy = (3x²+A)·dx`).

    Corresponds to Lemma `lem:log-deriv-norm` of `sections/ec.tex:557-579`. -/
noncomputable def logDerivTerm
    (D : CoordRingElt E.q) (curveA : ZMod E.q) (lam : ZMod E.q)
    (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let num_x := D.a.derivative.eval pt.1 - D.b.derivative.eval pt.1 * pt.2
  let num_y := -D.b.eval pt.1
  let den := D.eval pt.1 pt.2
  let dxdz_num := 2 * pt.2
  let dydz_num := 3 * pt.1 ^ 2 + curveA
  let dxdz_den := 3 * pt.1 ^ 2 + curveA - 2 * lam * pt.2
  (num_x * dxdz_num + num_y * dydz_num) * (den * dxdz_den)⁻¹

/-- The log-derivative check function f(A₀,A₁) -/
noncomputable def logDerivCheckFn
    (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  let L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2
  let x₂ := lam ^ 2 - A₀.1 - A₁.1
  let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
  let A₂ := (x₂, y₂)
  let lhs := logDerivTerm E D E.curveA lam A₀ +
             logDerivTerm E D E.curveA lam A₁ +
             logDerivTerm E D E.curveA lam A₂
  let negP := (P.1, -P.2)
  let rhs := -(L.eval negP.1 negP.2)⁻¹ +
    (Finset.univ (α := Fin k)).sum (fun j => -(m j) * (L.eval (B j).1 (B j).2)⁻¹)
  lhs - rhs

/-! ## Denominator-cleared form of `logDerivCheckFn` (Step 8')

    The `logDerivCheckFn` definition uses several inverses — one in each
    `logDerivTerm` (the factor `(D.eval · (3x² + A - 2λy))⁻¹`) and one
    per evaluation point in the `-1/L(·)` RHS sum. To bound its zero
    set via a `polynomial_zeros_on_cubic`-style argument we work with
    the *denominator-cleared* product
    `logDerivCheckFnCleared := logDerivCheckFn · denom`,
    which vanishes iff `logDerivCheckFn` vanishes on the valid-challenge
    subspace (`denom ≠ 0`). -/

/-- Product of all denominators appearing in `logDerivCheckFn`. -/
noncomputable def logDerivCheckFnDenom
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
  let L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2
  let x₂ := lam ^ 2 - A₀.1 - A₁.1
  let y₂ := lam * x₂ + (A₀.2 - lam * A₀.1)
  D.eval A₀.1 A₀.2 * D.eval A₁.1 A₁.2 * D.eval x₂ y₂ *
  (3 * A₀.1 ^ 2 + E.curveA - 2 * lam * A₀.2) *
  (3 * A₁.1 ^ 2 + E.curveA - 2 * lam * A₁.2) *
  (3 * x₂ ^ 2 + E.curveA - 2 * lam * y₂) *
  L.eval P.1 (-P.2) *
  (Finset.univ : Finset (Fin k)).prod (fun j => L.eval (B j).1 (B j).2)

/-- The denominator-cleared log-derivative check. Defined as the product
    of `logDerivCheckFn` with all its denominators; equals zero iff
    `logDerivCheckFn = 0` on the valid-challenge subspace. -/
noncomputable def logDerivCheckFnCleared
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  logDerivCheckFn E D P k B m A₀ A₁ * logDerivCheckFnDenom E D P B A₀ A₁

/-- **Denominator-clearing equivalence.** On the valid-challenge
    subspace (where all denominators are nonzero), `logDerivCheckFn = 0`
    iff `logDerivCheckFnCleared = 0`. This is the field arithmetic
    step; no algebraic-geometry content. -/
theorem logDerivCheckFn_eq_zero_iff_cleared
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hDenom : logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0) :
    logDerivCheckFn E D P k B m A₀ A₁ = 0 ↔
    logDerivCheckFnCleared E D P k B m A₀ A₁ = 0 := by
  unfold logDerivCheckFnCleared
  constructor
  · intro h; rw [h, zero_mul]
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact h1
    · exact absurd h2 hDenom

/-! ## Corollary 1: the probability bound -/

/-- The "NotEq" bad set: pairs `(A₀, A₁) ∈ validPairs` for which the
    verifier's log-derivative check vanishes. -/
noncomputable def badChallengesNotEq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (validPairs E).filter (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)

/-! The mechanized variety bound is derived in
    `Divisor/ClearedPolyForm.lean` from two narrow axioms
    (`logDerivCheckFn_fiber_count_bound`, `logDerivCheckFn_badA₀_bound`)
    plus the `fiber_argument` infrastructure. `log_deriv_sz` below
    lifts the resulting bound from `E.points ×ˢ E.points` to `validPairs E`. -/

/-! ## Non-vanishing criterion

The non-vanishing criterion `log_deriv_nonvanishing_criterion` — if
`polyG ≡ 0` on `F_q × F_q` with sufficient `q`, then `β_k + m_{σ(k)} = 0`
and unmatched `m_j = 0` — is mechanized as a theorem in
`Divisor/PolyFibK.lean` via the partial-fraction + slope-distribution
infrastructure there (Phase A of the axiom elimination plan).
-/

end Divisor
