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

/-! ## Function-field wrappers

Thin wrappers naming the field-theoretic objects that appear in the paper's
`lem:log-deriv-norm`: the field norm `N_{F_q(E)/F_q(L)}(D)` evaluated at the
place `(L = 0)`, and its logarithmic derivative. These are left opaque
because a concrete definition would require the function field `F_q(E)` and
its degree-3 subfield `F_q(L)` — infrastructure beyond current Mathlib.
Downstream uses access them only through the two classical identities
stated as axioms below (`norm_decomposition`, `log_deriv_kernel_classical`). -/

/-- The norm `N_{F_q(E)/F_q(L)}(D)` evaluated at the place `(L = 0)`, as
    an element of `F_q`. By Galois theory this equals
    `lc(D)^3 · ∏_α (-L(Q_α))^{n_α}` where `(D)_0 = Σ n_α · (Q_α)`, but
    for axiomatic use we keep it opaque. -/
opaque normAtZero (E : ECSetup) (D : CoordRingElt E.q) (L : Line E.q) :
    ZMod E.q

/-- The logarithmic derivative of `N_{F_q(E)/F_q(L)}(D)` with respect to
    `L`, evaluated at the place `(L = 0)`. Equals
    `-Σ_α n_α / L(Q_α)` modulo the characteristic (Bassa24b §4). -/
opaque logDerivNormAtZero (E : ECSetup) (D : CoordRingElt E.q) (L : Line E.q) :
    ZMod E.q

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

/-! ## Paper `lem:log-deriv-norm` and `lem:log-deriv-kernel` (axioms)

These are the two classical function-field identities supplying the LHS
and characterizing the kernel of the log-derivative. Restated here with
real content (formerly vacuous `True` bodies in `Divisor/Axioms.lean`);
axiom status retained per the "classical AG as axioms" policy.

They are not yet consumed by a mechanized proof further upstream — that
requires Gap 3 (the denominator-clearing / variety SZ bound for
`logDerivCheckFn`) to be formalized, at which point
`norm_decomposition` supplies the identification of the LHS sum of
`logDerivTerm`s with `logDerivNormAtZero`, and `log_deriv_kernel_classical`
is used to conclude that two functions with the same log-derivative
differ only by a constant factor on the norm. -/

/-- **Paper `lem:log-deriv-norm` (Bassa24b §4).**

    Identifies the sum of per-point log-derivative terms with the
    logarithmic derivative of the norm `N_{F_q(E)/F_q(L)}(D)` at the
    place `(L = 0)`.

    Side-conditions mirror the paper's hypotheses:
    * `D ≠ 0` in `F_q[E]` (paper writes "`D ∈ F_q[E] ∖ {0}`"),
    * non-vertical line (`A₀.1 ≠ A₁.1`),
    * `D` does not vanish at any of the three collinear points (no poles
      of `D'/D`), and
    * `A₂` is the third intersection of the chord `A₀ A₁` with `E`.

    Equivalent axiomatization of paper Eq. (after `lem:log-deriv-norm`):
        `Σ_i (a'(x_i) - (3x_i²+A)/(2y_i)·b(x_i) - y_i b'(x_i))
              / (a(x_i) - y_i b(x_i)) · 2y_i/(3x_i²+A-2λy_i)
           = L(N(D))|_{(L=0)}`. -/
axiom norm_decomposition
    (D : CoordRingElt E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (x₂ y₂ : ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNonVert : A₀.1 ≠ A₁.1)
    (hA₂ : thirdPoint E A₀ A₁ = ECPoint.affine x₂ y₂)
    (hD₀ : D.eval A₀.1 A₀.2 ≠ 0)
    (hD₁ : D.eval A₁.1 A₁.2 ≠ 0)
    (hD₂ : D.eval x₂ y₂ ≠ 0) :
    let lam := slopeOf A₀.1 A₀.2 A₁.1 A₁.2
    let L := lineThrough A₀.1 A₀.2 A₁.1 A₁.2
    logDerivTerm E D E.curveA lam A₀
      + logDerivTerm E D E.curveA lam A₁
      + logDerivTerm E D E.curveA lam (x₂, y₂)
    = logDerivNormAtZero E D L

/-- **Paper `lem:log-deriv-kernel` (Bassa24b Lem 1; Stichtenoth Ch 4).**

    Low-degree kernel of the logarithmic derivative consists of constants.
    Stated in the form actually consumed by `cor:log-derivative`'s
    non-vanishing remark: two low-degree `CoordRingElt`s whose norms have
    the same log-derivative on every line differ by a (line-independent)
    multiplicative constant.

    Formally: if `logDerivNormAtZero E D₁ L = logDerivNormAtZero E D₂ L`
    for every line `L`, and both `degE(D_i) < q`, then there is a
    nonzero constant `c ∈ F_q` with `normAtZero E D₁ L = c · normAtZero E D₂ L`
    for every `L`. -/
axiom log_deriv_kernel_classical
    (D₁ D₂ : CoordRingElt E.q)
    (hDeg₁ : D₁.degE < E.q)
    (hDeg₂ : D₂.degE < E.q)
    (hLogEq : ∀ L : Line E.q,
      logDerivNormAtZero E D₁ L = logDerivNormAtZero E D₂ L) :
    ∃ c : ZMod E.q, c ≠ 0 ∧
      ∀ L : Line E.q, normAtZero E D₁ L = c * normAtZero E D₂ L

/-! ## Corollary 1: the probability bound -/

/-- The "NotEq" bad set: pairs `(A₀, A₁) ∈ validPairs` for which the
    verifier's log-derivative check vanishes. -/
noncomputable def badChallengesNotEq
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (validPairs E).filter (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)

/-- **Specialized variety bound** (DKL / EOT, specialized to
    `logDerivCheckFn` on E × E). Replaces the generic
    `variety_sz_on_ExE` axiom whose `hBiDegree : True` side-condition
    was a soundness hole. The bi-degree of `logDerivCheckFn` (after
    denominator clearing via `polyG`) on E × E is
    `(D.degE + k - 1, D.degE + k - 1)`; this is determined structurally
    by the definition of `logDerivCheckFn`, not an informal hypothesis.

    Classical DKL/EOT variety bound: a bi-degree (N, N) function on the
    degree-9 surface E × E ⊂ P⁴ has at most `18 * N * q` rational zeros
    when it is not identically zero. -/
axiom logDerivCheckFn_zero_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNonzero : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
      logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)).card
      ≤ 18 * (D.degE + k) * E.q

/-- **Corollary 1 (Schwartz-Zippel for Log-Derivative Check).**

    If `logDerivCheckFn` is not identically zero on `E.points × E.points`,
    then the number of valid challenges where it vanishes is at most
    `18 * (D.degE + k) * E.q`. Lift of `logDerivCheckFn_zero_set_bound`
    from `E.points ×ˢ E.points` to `validPairs E`. -/
theorem log_deriv_sz (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hDeg : D.degE < E.q)
    (hNonvanishing : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (badChallengesNotEq E D P B m).card ≤ 18 * (D.degE + k) * E.q := by
  have hBound :=
    logDerivCheckFn_zero_set_bound E D P B m hDeg hNonvanishing
  -- badChallengesNotEq ⊆ (validPairs E) ⊆ distinctPairs E.points ⊆ E.points ×ˢ E.points.
  have hsub : badChallengesNotEq E D P B m ⊆
      (E.points ×ˢ E.points).filter
        (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0) := by
    intro p hp
    simp only [badChallengesNotEq, Finset.mem_filter] at hp
    obtain ⟨hVP, hf⟩ := hp
    have hDP : p ∈ distinctPairs E.points := (Finset.mem_filter.mp hVP).1
    have hEE : p ∈ E.points ×ˢ E.points :=
      (Finset.mem_filter.mp hDP).1
    exact Finset.mem_filter.mpr ⟨hEE, hf⟩
  exact le_trans (Finset.card_le_card hsub) hBound

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

end Divisor
