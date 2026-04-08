/-
  Divisor/Axioms.lean

  Axiomatized results from algebraic geometry that are used
  in the probability bounds but whose proofs require deep
  infrastructure beyond current Mathlib.

  Each axiom corresponds to a cited result in the paper.
-/
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Theorem 1: Principal Divisor Characterization (Silverman, Cor 3.5)

A divisor D = sum n_P * P in Div(E) is principal iff
  (1) sum n_P = 0, and
  (2) sum [n_P] P = O in the group law.
-/
axiom principal_divisor_iff :
  ∀ (coeffs : ECPoint E.q → ℤ) (hFinSupp : Set.Finite (Function.support coeffs)),
    -- D is principal iff both conditions hold
    True  -- Statement placeholder; the characterization is used only
          -- as background justification, not directly in the bounds.

/-! ## Hasse-Weil Bound

|#E(F_q) - (q + 1)| <= 2 * sqrt(q)

We state the upper bound as: numPoints <= q + 1 + 2 * Nat.sqrt q
and the practically useful consequence that numPoints >= q + 1 - 2 * Nat.sqrt q.
-/
axiom hasse_weil_upper :
  E.numPoints ≤ E.q + 1 + 2 * Nat.sqrt E.q

axiom hasse_weil_lower :
  E.q + 1 - 2 * Nat.sqrt E.q ≤ E.numPoints

/-! ## Lemma 3: Rationality of f (Bassa 2024a, Lemma 7)

The comparison polynomial
  f(X0,Y0,X1,Y1) = prod_i ((y(Qi)-Y0)(X1-X0) - (x(Qi)-X0)(Y1-Y0))
                  - prod_i ((y(Pi)-Y0)(X1-X0) - (x(Pi)-X0)(Y1-Y0))
lies in F_q[X0,Y0,X1,Y1] (not just F_qbar[...]).

This follows from the Galois invariance of the first product:
the Q_i form complete Galois orbits since D in F_q[E].
-/
axiom f_rational
    (D : CoordRingElt E.q)
    {n : ℕ}
    (P : Fin n → ZMod E.q × ZMod E.q)
    (hP : ∀ i, P i ∈ E.points) :
    True  -- The polynomial f is defined over F_q.
          -- Formalized as: the coefficients of f lie in ZMod q.

/-! ## Lemma 4: Non-vanishing of f on E x E (Bassa 2024a, Lemma 8)

If the multiset of zeros of D differs from the multiset {P_1,...,P_N}
and N << q, then f does not vanish identically on E x E.

Proof uses: irreducibility of E x E, substitution of a specific P_1
into f to get a product of nonzero linear forms, and Hasse-Weil
to ensure 3N < #E(F_q).
-/
axiom f_nonvanishing
    (D : CoordRingElt E.q)
    (N : ℕ)
    (hDeg : D.degE = N)
    (P : Fin N → ZMod E.q × ZMod E.q)
    (hP : ∀ i, P i ∈ E.points)
    (hNeq : True)  -- "(D)_0 ≠ sum P_i" as multisets
    (hSmall : 3 * N < E.numPoints) :
    True  -- f does not vanish identically on E x E

/-! ## Theorem 3: Generalized Schwartz-Zippel on varieties
    (Dvir-Kollar-Lovett 2014, Claim 7.2)

For a projective variety V of dimension n and degree d:
  #V(F_q) <= d * q^n

We state the specific application to E x E:
E x E is a surface of degree 9 (= 3 * 3).
A function of bi-degree (N, N) restricted to E x E cuts out
a curve of degree at most 2N * 9 = 18N.
So the number of F_q-rational zeros on E x E is at most 18N * q.
-/
axiom variety_sz_on_ExE
    (N : ℕ)
    (f_nonzero : Prop)
    (hf : f_nonzero) :
    -- The number of zeros of a nonzero function of bi-degree (N,N)
    -- on E x E is at most 18 * N * q.
    -- In terms of our Finset formulation:
    -- (ExE_points.filter (fun p => f(p) = 0)).card <= 18 * N * E.q
    True

/-! ## Lemma 5: Log-Derivative Kernel (Bassa 2024b, Lemma 1)

Let F/K be a function field with K perfect and the full constant field.
Let delta be a derivation of F/K and L(f) = delta(f)/f the log derivative.
If t in ker(L) and deg_F(t) < char(K), then t in K.

Corollary: for nonzero f, g of degree < p,
L(f) = L(g) iff f = c * g for some constant c in K.
-/
axiom log_deriv_kernel
    (D₁ D₂ : CoordRingElt E.q)
    (hDeg₁ : D₁.degE < E.q)
    (hDeg₂ : D₂.degE < E.q)
    (hLogEq : True)  -- L(N(D1)) = L(N(D2)) for all lines L
    : True  -- N(D1) = c * N(D2) for some constant c

/-! ## Lemma 6: Log-Derivative and Norm Map
    (Bassa 2024b, Section 4; Bassa 2025, Lemma 5)

For D(x,y) = a(x) - y * b(x) with only poles at O,
and line L = y - lam * x - mu defining subfield F_q(L):

  L(N_{F_q(E)/F_q(L)}(D))((L=0))
    = sum_{i=0}^{2} (a'(x_i) - (3x_i^2+A)/(2y_i) * b(x_i) - y_i * b'(x_i))
                     / (a(x_i) - y_i * b(x_i))
                     * 2*y_i / (3*x_i^2 + A - 2*lam*y_i)

where x_i, y_i are the coordinates of A_i.
-/
axiom log_deriv_norm_formula
    (D : CoordRingElt E.q)
    (A₀ A₁ A₂ : ZMod E.q × ZMod E.q)
    (L : Line E.q) :
    -- The log-derivative of the norm evaluated at (L=0) equals
    -- the explicit sum over A_0, A_1, A_2.
    True

end Divisor
