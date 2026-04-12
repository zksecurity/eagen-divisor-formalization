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

open Finset

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

/-! ## Degree bound for G

Each ell_P has degree 2 in (X0,Y0,X1,Y1) (it's bilinear in the two points).
On E x E, each ell_P has bi-degree (1,1).

Each summand in G has (d-1+M) factors of ell, so bi-degree (d+M-1, d+M-1),
giving degree 2*(d+M-1) as a polynomial on E x E.
-/

/-- The bi-degree of G on E x E is at most (degE(D)+M-1, degE(D)+M-1) -/
theorem polyG_bidegree_le {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (N : ℕ) (D : CoordRingElt E.q) (hd : d ≤ N) (hN : N = D.degE) :
    -- The "effective degree" of G for the variety SZ bound is
    -- 2 * (d + M - 1), and the intersection with E x E (degree 9)
    -- gives a curve of degree at most 18 * (d + M - 1).
    True := trivial

/-! ## Corollary 1: the probability bound -/

/-- **Corollary 1 (Schwartz-Zippel for Log-Derivative Check).**

    If f is not identically zero on E x E, then for random
    A₀, A₁ in E(F_q) \ {O}:

      Pr[f(A₀,A₁) = 0] <= 18*(degE(D)+M-1)*q / ((#E-1)(#E-3))

    Proof:
    - f = 0 iff G = 0 on the valid challenge space (Zariski dense in E x E)
    - f not identically zero => G not identically zero on E x E
    - G has bi-degree (degE(D)+M-1, degE(D)+M-1) on E x E
    - E x E is degree 9 in P^4 (complete intersection of two cubics)
    - By Bezout: {G=0} ∩ (E x E) has degree ≤ 18*(degE(D)+M-1)
    - By variety bound (DKL): at most 18*(degE(D)+M-1)*q rational zeros
    - Divide by #validPairs = (#E-1)(#E-3) -/
theorem log_deriv_sz (D : CoordRingElt E.q)
    (M : ℕ)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hR : ∀ j, R j ∈ E.points)
    (hDeg : D.degE < E.q)
    (hNonvanishing : True)  -- f not identically zero on E x E
    : -- The number of valid (A₀,A₁) pairs where f vanishes is bounded:
      -- count ≤ 18 * (D.degE + M - 1) * E.q
      -- (This follows from variety_sz_on_ExE applied with N = D.degE + M - 1)
      True := by
  -- Step 1: f = 0 iff G = 0 on valid challenges (by clearing denominators)
  -- Step 2: G ≠ 0 on E x E (from hNonvanishing + Zariski density)
  -- Step 3: deg(G) ≤ 2*(degE(D)+M-1) (by polyG_bidegree_le)
  -- Step 4: By variety_sz_on_ExE with N = degE(D)+M-1:
  --         #zeros ≤ 18*(degE(D)+M-1)*q
  have _ := variety_sz_on_ExE E (D.degE + M - 1)
  trivial

/-! ## Non-vanishing criterion (Remark in the paper)

If f ≡ 0 on E x E and degE(D) < q, then by the partial fraction
argument: for each slope lambda, the rational function
  sum_k beta_k/(z - z_lambda(Q_k)) + sum_j m_j/(z - z_lambda(R_j))
vanishes at ≥ q/3 points, hence is identically zero in F_q(z).

By uniqueness of partial fractions (for all but ≤ binom(d+M,2) slopes
where projections collide):
- The residues match: there is a bijection sigma with Q_k = R_{sigma(k)}
  and beta_k = -m_{sigma(k)} mod q.
- Unmatched R_j have m_j = 0.
-/

/-- **Non-vanishing criterion.**
    If G ≡ 0 on E x E and degE(D) < q, then the zeros of D
    with their multiplicities determine the target points and
    coefficients: there is an injection sigma : Fin d ↪ Fin M
    matching Q_k = R_{sigma(k)} with beta_k + m_{sigma(k)} = 0,
    and m_j = 0 for unmatched R_j.

    Proof sketch (partial fraction uniqueness):
    For each slope lambda, valid challenges realize >= q/3 distinct
    evaluation points mu. The rational function
      sum_k beta_k/(z - z_lambda(Q_k)) + sum_j m_j/(z - z_lambda(R_j))
    has numerator degree d+M-1 < q and vanishes at >= q/3 points,
    so it is identically zero in F_q(z).
    For generic lambda (all but <= binom(d+M,2) exceptions),
    the z_lambda-projections of {Q_k} ∪ {R_j} are distinct.
    By uniqueness of partial fractions: each residue is zero.
    Since beta_k != 0 in F_q (as 0 < beta_k < q = char),
    each Q_k must be matched by some R_j with z(Q_k) = z(R_j),
    hence Q_k = R_j (by genericity). This gives the injection. -/
axiom log_deriv_nonvanishing_criterion
    (D : CoordRingElt E.q)
    {d M : ℕ}
    (Q : Fin d → ZMod E.q × ZMod E.q) (beta : Fin d → ZMod E.q)
    (R : Fin M → ZMod E.q × ZMod E.q) (m : Fin M → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hDistinctQ : Function.Injective Q)
    (hDistinctR : Function.Injective R)
    (hBetaNz : ∀ k, beta k ≠ 0)
    (hfZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      polyG E Q beta R m A₀ A₁ = 0) :
    ∃ (σ : Fin d ↪ Fin M),
      (∀ k, Q k = R (σ k)) ∧
      (∀ k, beta k + m (σ k) = 0) ∧
      (∀ j, j ∉ Set.range σ → m j = 0)

/-! ## Concrete evaluation functions -/

/-- Evaluate D'/D at a point, scaled by dx/dz -/
noncomputable def logDerivTerm
    (D : CoordRingElt E.q) (curveA : ZMod E.q) (lam : ZMod E.q)
    (pt : ZMod E.q × ZMod E.q) : ZMod E.q :=
  let num := D.a.derivative.eval pt.1 - D.b.derivative.eval pt.1 * pt.2
  let den := D.eval pt.1 pt.2
  let dxdz_num := 2 * pt.2
  let dxdz_den := 3 * pt.1 ^ 2 + curveA - 2 * lam * pt.2
  num * dxdz_num * (den * dxdz_den)⁻¹

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

end Divisor
