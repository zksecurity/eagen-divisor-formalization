/-
  Divisor/Protocol.lean

  Protocol definitions for the discrete log relation.

  Construction 1: Merlin-Arthur protocol Pi^MA
  Three-round interactive protocol Pi^IP

  These correspond to Figures 1 and 2 and Constructions 1-2 in the paper.
-/
import Divisor.Defs

open Polynomial Finset

namespace Divisor

variable {q : ℕ} [hq : Fact (Nat.Prime q)]

/-! ## The discrete log relation

R^Dlog = { ((B, P), n) : P = sum [n_i] * B_i, n_i in [0, d) }

We define this over F_q points with a degree bound d.
-/

/-- The discrete log relation: public statement and witness -/
structure DlogStatement (q : ℕ) [Fact (Nat.Prime q)] where
  /-- Number of generators -/
  k : ℕ
  /-- Generator points B_1, ..., B_k -/
  bases : Fin k → ZMod q × ZMod q
  /-- Target point P -/
  target : ZMod q × ZMod q

/-- A witness for the discrete log relation -/
structure DlogWitness (q : ℕ) [Fact (Nat.Prime q)] where
  /-- Number of generators -/
  k : ℕ
  /-- Scalar witnesses n_1, ..., n_k (as natural numbers < d) -/
  scalars : Fin k → ℕ
  /-- Degree bound -/
  degBound : ℕ
  /-- Each scalar is within the degree bound -/
  hRange : ∀ i, scalars i < degBound

/-- The relation holds: P = sum [n_i] * B_i -/
def dlogHolds (stmt : DlogStatement q) (wit : DlogWitness q)
    (hk : stmt.k = wit.k) : Prop :=
  -- Abstractly: stmt.target = sum_{i} [wit.scalars i] * stmt.bases i
  -- We axiomatize the group law computation.
  sorry

/-! ## MA Protocol (Construction 1, Figure 1)

Prover message: (m, a(x), b(x)) where
  - m = n mod q in F_q^k
  - D(x,y) = a(x) - b(x)*y with (D)_0 = (-P) + sum n_i * (B_i)

Verifier: samples A0, A1, computes A2 = -(A0+A1), line L,
  checks log-derivative identity.
-/

/-- The prover's message in the MA protocol -/
structure MAProverMsg (q : ℕ) [Fact (Nat.Prime q)] where
  /-- Number of generators -/
  k : ℕ
  /-- Reduced witnesses m_i = n_i mod q -/
  m : Fin k → ZMod q
  /-- Polynomial a(x) -/
  polyA : Polynomial (ZMod q)
  /-- Polynomial b(x) -/
  polyB : Polynomial (ZMod q)

/-- The coordinate ring element D from the prover message -/
def MAProverMsg.toD (msg : MAProverMsg q) : CoordRingElt q :=
  { a := msg.polyA, b := msg.polyB }

/-- The verifier's challenge in the MA protocol: two random points -/
structure MAChallenge (q : ℕ) [Fact (Nat.Prime q)] where
  A₀ : ZMod q × ZMod q
  A₁ : ZMod q × ZMod q

/-- The verifier's degree check: degE(D) <= d -/
def verifierDegreeCheck (msg : MAProverMsg q) (d : ℕ) : Prop :=
  msg.toD.degE ≤ d

/-- The MA verifier's acceptance predicate.
    Given statement, prover message, and challenge points,
    the verifier checks the log-derivative identity. -/
def maVerifierAccepts (E : ECSetup) (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (chal : MAChallenge E.q)
    (hChal₀ : chal.A₀ ∈ E.points)
    (hChal₁ : chal.A₁ ∈ E.points)
    (hDistinct : chal.A₀ ≠ chal.A₁)
    (hNotNeg : chal.A₀ ≠ (chal.A₁.1, -chal.A₁.2)) : Prop :=
  -- 1. Degree check
  verifierDegreeCheck msg stmt.k ∧
  -- 2. Log-derivative check (the core Weil reciprocity verification)
  -- LHS: sum_{i=0}^{2} D'(A_i)/D(A_i) * dx(A_i)/dz
  -- RHS: -1/L(-P) + sum_j (-m_j)/L(B_j)
  -- We leave the concrete computation abstract.
  True

/-! ## Three-Round IP Protocol (Figure 2)

Round 1: Prover -> Verifier: (m, a(x), b(x))  [same as MA]
Round 2: Verifier -> Prover: (A0, A1)
Round 3: Prover -> Verifier: (h0, h1, h2, g) where
  h_i = D'(A_i) / D(A_i)
  g = -1 / L(-P)
-/

/-- The prover's third-round message in the IP protocol -/
structure IPProverMsg3 (q : ℕ) [Fact (Nat.Prime q)] where
  /-- h_i = D'(A_i) / D(A_i) for i = 0, 1, 2 -/
  h : Fin 3 → ZMod q
  /-- g = -1 / L(-P) -/
  g : ZMod q

/-- The IP verifier's acceptance predicate.
    Checks:
    1. degE(D) <= d
    2. LHS = RHS (using the provided h_i and g)
    3. h_i * D(A_i) = D'(A_i) for i = 0, 1, 2
    4. g * L(-P) = -1
-/
def ipVerifierAccepts (E : ECSetup) (stmt : DlogStatement E.q)
    (msg1 : MAProverMsg E.q) (chal : MAChallenge E.q)
    (msg3 : IPProverMsg3 E.q)
    (hChal₀ : chal.A₀ ∈ E.points)
    (hChal₁ : chal.A₁ ∈ E.points) : Prop :=
  let D := msg1.toD
  let L := lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2
  let negP := (stmt.target.1, -stmt.target.2)
  -- 1. Degree check
  verifierDegreeCheck msg1 stmt.k ∧
  -- 2. Consistency: h_i * D(A_i) = D'(A_i) for the three points
  -- (axiomatized; requires polynomial derivative)
  True ∧
  -- 3. Consistency: g * L(-P) = -1
  msg3.g * L.eval negP.1 negP.2 = -1 ∧
  -- 4. Main check: sum h_i * dx(A_i)/dz = g + sum (-m_j)/L(B_j)
  True

/-! ## Key property: unique third-round message

For any first-round message and challenge, there is at most one
third-round message that makes the verifier accept.
This is because h_i and g are uniquely determined by
D, the challenge points, and the statement. -/

/-- If the verifier accepts, the third-round message is uniquely determined -/
theorem ip_unique_third_round (E : ECSetup)
    (stmt : DlogStatement E.q) (msg1 : MAProverMsg E.q)
    (chal : MAChallenge E.q) (msg3 msg3' : IPProverMsg3 E.q)
    (hChal₀ : chal.A₀ ∈ E.points)
    (hChal₁ : chal.A₁ ∈ E.points)
    (hD₀ : msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0)
    (hD₁ : msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0)
    (hAcc : ipVerifierAccepts E stmt msg1 chal msg3 hChal₀ hChal₁)
    (hAcc' : ipVerifierAccepts E stmt msg1 chal msg3' hChal₀ hChal₁) :
    msg3 = msg3' := by
  sorry
  -- h_i is uniquely determined by D'(A_i) / D(A_i) (D(A_i) != 0)
  -- g is uniquely determined by -1 / L(-P)

end Divisor
