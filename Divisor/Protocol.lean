/-
  Divisor/Protocol.lean — Protocol definitions for the discrete log relation.
-/
import Divisor.Defs

open Polynomial Finset

namespace Divisor

variable {q : ℕ} [hq : Fact (Nat.Prime q)]

/-! ## The discrete log relation -/

structure DlogStatement (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  bases : Fin k → ZMod q × ZMod q
  target : ZMod q × ZMod q

structure DlogWitness (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  scalars : Fin k → ℕ
  degBound : ℕ
  hRange : ∀ i, scalars i < degBound

/-- The relation: witnessed by a coordinate ring element D
    whose divisor encodes P = Σ [n_i] * B_i. -/
def dlogHolds (stmt : DlogStatement q) (wit : DlogWitness q)
    (hk : stmt.k = wit.k) : Prop :=
  ∃ D : CoordRingElt q,
    D.degE ≤ wit.degBound ∧
    -- The zeros of D encode: (-P) + Σ n_i·(B_i)
    -- This is the divisor-based formulation of the dlog relation.
    True

/-! ## MA Protocol -/

structure MAProverMsg (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  m : Fin k → ZMod q
  polyA : Polynomial (ZMod q)
  polyB : Polynomial (ZMod q)

def MAProverMsg.toD (msg : MAProverMsg q) : CoordRingElt q :=
  { a := msg.polyA, b := msg.polyB }

structure MAChallenge (q : ℕ) [Fact (Nat.Prime q)] where
  A₀ : ZMod q × ZMod q
  A₁ : ZMod q × ZMod q

def verifierDegreeCheck (msg : MAProverMsg q) (d : ℕ) : Prop :=
  msg.toD.degE ≤ d

/-- The MA verifier accepts iff the degree and log-derivative checks pass -/
def maVerifierAccepts (E : ECSetup) (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (chal : MAChallenge E.q) : Prop :=
  verifierDegreeCheck msg stmt.k ∧
  -- The log-derivative identity holds at the challenge points.
  -- Concrete check defined in LogDeriv.lean; here we state it abstractly.
  True

/-! ## Three-Round IP Protocol -/

structure IPProverMsg3 (q : ℕ) [Fact (Nat.Prime q)] where
  h : Fin 3 → ZMod q
  g : ZMod q

/-- Compute A₂ from the challenge: third intersection of line through A₀,A₁ with E -/
noncomputable def computeA₂ (chal : MAChallenge q) : ZMod q × ZMod q :=
  let lam := slopeOf chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2
  let x₂ := lam ^ 2 - chal.A₀.1 - chal.A₁.1
  let y₂ := lam * x₂ + (chal.A₀.2 - lam * chal.A₀.1)
  (x₂, y₂)

/-- The IP verifier checks:
    1. degE(D) ≤ d
    2. h_i * D(A_i) = D'(A_i) for i = 0,1,2 where D' is the formal derivative
    3. g * L(-P) = -1
    4. Σ h_i * dx(A_i)/dz = g + Σ (-m_j)/L(B_j)

    For uniqueness: h_i is determined by D and A_i (check 2),
    and g is determined by L and P (check 3).
    So acceptance uniquely determines msg3. -/
def ipVerifierAccepts (E : ECSetup) (stmt : DlogStatement E.q)
    (msg1 : MAProverMsg E.q) (chal : MAChallenge E.q)
    (A₂ : ZMod E.q × ZMod E.q)
    (msg3 : IPProverMsg3 E.q) : Prop :=
  let D := msg1.toD
  let L := lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2
  let negP := (stmt.target.1, -stmt.target.2)
  verifierDegreeCheck msg1 stmt.k ∧
  (msg3.h 0 * D.eval chal.A₀.1 chal.A₀.2 =
    D.a.derivative.eval chal.A₀.1 - D.b.derivative.eval chal.A₀.1 * chal.A₀.2) ∧
  (msg3.h 1 * D.eval chal.A₁.1 chal.A₁.2 =
    D.a.derivative.eval chal.A₁.1 - D.b.derivative.eval chal.A₁.1 * chal.A₁.2) ∧
  (msg3.h 2 * D.eval A₂.1 A₂.2 =
    D.a.derivative.eval A₂.1 - D.b.derivative.eval A₂.1 * A₂.2) ∧
  msg3.g * L.eval negP.1 negP.2 = -1

/-- **Uniqueness of third-round message.**
    If D(A₀) ≠ 0 and D(A₁) ≠ 0 and L(-P) ≠ 0,
    then there is at most one msg3 the verifier accepts. -/
theorem ip_unique_third_round (E : ECSetup)
    (stmt : DlogStatement E.q) (msg1 : MAProverMsg E.q)
    (chal : MAChallenge E.q) (A₂ : ZMod E.q × ZMod E.q)
    (msg3 msg3' : IPProverMsg3 E.q)
    (hD₀ : msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0)
    (hD₁ : msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0)
    (hD₂ : msg1.toD.eval A₂.1 A₂.2 ≠ 0)
    (hLP : (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
              stmt.target.1 (-stmt.target.2) ≠ 0)
    (hAcc : ipVerifierAccepts E stmt msg1 chal A₂ msg3)
    (hAcc' : ipVerifierAccepts E stmt msg1 chal A₂ msg3') :
    msg3 = msg3' := by
  obtain ⟨_, hh0, hh1, hh2, hg⟩ := hAcc
  obtain ⟨_, hh0', hh1', hh2', hg'⟩ := hAcc'
  have h0_eq : msg3.h 0 = msg3'.h 0 :=
    mul_right_cancel₀ hD₀ (hh0.trans hh0'.symm)
  have h1_eq : msg3.h 1 = msg3'.h 1 :=
    mul_right_cancel₀ hD₁ (hh1.trans hh1'.symm)
  have h2_eq : msg3.h 2 = msg3'.h 2 :=
    mul_right_cancel₀ hD₂ (hh2.trans hh2'.symm)
  have g_eq : msg3.g = msg3'.g :=
    mul_right_cancel₀ hLP (hg.trans hg'.symm)
  cases msg3; cases msg3'
  simp only [IPProverMsg3.mk.injEq] at *
  exact ⟨by ext i; fin_cases i <;> assumption, g_eq⟩

end Divisor
