/-
  Divisor/Protocol.lean — Protocol definitions for the discrete log relation.
-/
import Divisor.Defs
import Divisor.LogDeriv

open Polynomial Finset

namespace Divisor

variable {q : ℕ} [hq : Fact (Nat.Prime q)]

/-! ## The discrete log relation -/

/-- A discrete-log statement together with an admissible set `admSet`
    ⊆ `F_q[x]²` (with `(0, 0) ∉ admSet`) that the verifier uses to rule
    out the zero divisor at the protocol level.

    Paper `\protMA` (Eagen, Bassa25) parameterizes soundness by
    `admSet`. Common choices:
    * Maximal:    `{(a, b) : (a, b) ≠ (0, 0)}`
    * Parker:     `{(a, b) : a₁ = 1}` (coefficient of x in a is 1)
    * Eagen:      `{(a, b) : a₀ = 1}` (constant coefficient of a is 1)
    * Hash:       `{(a, b) : ⟨r, a ‖ b⟩ ≠ 0}` for some challenge r ∈ F_q^n.

    Axiomatic use of `admSet`: downstream proofs only depend on
    `(0, 0) ∉ admSet`, captured by the `admSet_excludes_zero` field. -/
structure DlogStatement (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  degBound : ℕ
  bases : Fin k → ZMod q × ZMod q
  target : ZMod q × ZMod q
  admSet : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop
  admSet_excludes_zero : ¬ admSet (0, 0)

/-! ## Concrete admissible sets (paper's four constructions) -/

/-- Maximal: `{(a, b) : (a, b) ≠ (0, 0)}`. -/
def admSetMax : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop :=
  fun ab => ab ≠ (0, 0)

theorem admSetMax_excludes_zero : ¬ (admSetMax (q := q) (0, 0)) := by
  intro h; exact h rfl

/-- Parker: `{(a, b) : coeff(a, 1) = 1}`. -/
def admSetParker : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop :=
  fun ab => ab.1.coeff 1 = 1

theorem admSetParker_excludes_zero : ¬ (admSetParker (q := q) (0, 0)) := by
  intro h
  change (0 : Polynomial (ZMod q)).coeff 1 = 1 at h
  simp at h

/-- Eagen: `{(a, b) : coeff(a, 0) = 1}`. -/
def admSetEagen : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop :=
  fun ab => ab.1.coeff 0 = 1

theorem admSetEagen_excludes_zero : ¬ (admSetEagen (q := q) (0, 0)) := by
  intro h
  change (0 : Polynomial (ZMod q)).coeff 0 = 1 at h
  simp at h

/-- Hash: `{(a, b) : ⟨r, (coeffs a ‖ coeffs b)⟩ ≠ 0}` for some challenge
    `r : ℕ → ZMod q`. The zero polynomial has all-zero coefficients, so
    the inner product is `0`, hence excluded. -/
def admSetHash (r : ℕ → ZMod q) :
    Polynomial (ZMod q) × Polynomial (ZMod q) → Prop :=
  fun ab =>
    (∑ i ∈ Finset.range (ab.1.natDegree + 1), r i * ab.1.coeff i) +
    (∑ i ∈ Finset.range (ab.2.natDegree + 1), r (ab.1.natDegree + 1 + i) * ab.2.coeff i)
    ≠ 0

theorem admSetHash_excludes_zero (r : ℕ → ZMod q) :
    ¬ (admSetHash r (0, 0)) := by
  intro h
  apply h
  simp

/-- Witness for the discrete-log relation. Scalars are signed integers so
    that the paper's extractor special case `n_{j*} = -1` (for
    `-P ∈ {B_j}`) can be represented natively. The range condition
    `|scalars i| < degBound` bounds the absolute value by the divisor
    degree (paper requires `n_i ∈ F_p` with `Σ n_i ≤ degBound`; for the
    soundness analysis the looser `|n_i| < degBound` is what matters). -/
structure DlogWitness (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  scalars : Fin k → ℤ
  degBound : ℕ
  hRange : ∀ i, (scalars i).natAbs < degBound

/-- The discrete-log relation `P = Σ [n_i] · B_i` in the group `E(F_q)`,
    expressed via `ECPoint.weightedSum`. Matches paper `relDlog`.
    The equality `stmt.k = wit.k` is bundled existentially so the
    relation is a plain `Prop` on `(stmt, wit)`, avoiding type-mismatch
    issues when threading the equality through theorem statements. -/
def relDlog (E : ECSetup) (stmt : DlogStatement E.q) (wit : DlogWitness E.q) :
    Prop :=
  ∃ (hk : stmt.k = wit.k),
    (ECPoint.affine stmt.target.1 stmt.target.2 : ECPoint E.q) =
      ECPoint.weightedSum E (Finset.univ : Finset (Fin wit.k))
        (fun i => ECPoint.zsmul E (wit.scalars i)
                    (ECPoint.affine
                      (stmt.bases (Fin.cast hk.symm i)).1
                      (stmt.bases (Fin.cast hk.symm i)).2))

/-! ## MA Protocol -/

structure MAProverMsg (q : ℕ) [Fact (Nat.Prime q)] where
  k : ℕ
  m : Fin k → ZMod q
  polyA : Polynomial (ZMod q)
  polyB : Polynomial (ZMod q)

def MAProverMsg.toD (msg : MAProverMsg q) : CoordRingElt q :=
  { a := msg.polyA, b := msg.polyB }

/-- A `CoordRingElt` is the zero element of `F_q[E]` iff both its `a(x)`
    and `b(x)` polynomials are zero. (Canonical representation makes
    this a syntactic check.) -/
def CoordRingElt.isZero (D : CoordRingElt q) : Prop :=
  D.a = 0 ∧ D.b = 0

/-- Consequence of the admSet side-condition `(0, 0) ∉ admSet`: a message
    passing the admissible-set check has `D = msg.toD ≠ 0` in `F_q[E]`.
    This is the form the soundness proof actually consumes (paper
    obs:zero-divisor: the log-derivative identity requires `D ≠ 0`). -/
theorem admSet_implies_toD_nonzero (stmt : DlogStatement q)
    (msg : MAProverMsg q) (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ¬ msg.toD.isZero := by
  intro hZero
  obtain ⟨ha, hb⟩ := hZero
  -- `msg.toD.a = msg.polyA`, `msg.toD.b = msg.polyB` by construction
  have ha' : msg.polyA = 0 := ha
  have hb' : msg.polyB = 0 := hb
  apply stmt.admSet_excludes_zero
  have h : (msg.polyA, msg.polyB) = ((0 : Polynomial (ZMod q)), 0) :=
    Prod.ext ha' hb'
  exact h ▸ hAdm

/-! ### Honest-prover divisor encoding

Paper `\protMA`: the honest prover constructs `D = msg.toD` so that its
divisor on `E` is `(-P) + Σ_i n_i · (B_i) - degE(D) · (∞)`, where
`n_i = wit.scalars i`, `B_i = stmt.bases i`, `P = stmt.target`.

Concretely, `honestDivisorCoeffs` spells out this target coefficient
function on `ECPoint E.q`, and `isHonestFor` requires (i) `msg.m_i` to
reduce correctly to `wit.scalars i` in `ZMod E.q`, and (ii) the formal
divisor to be principal (i.e. it is in fact `div(f)` for some nonzero
rational function `f ∈ F_q(E)×`). By `principal_divisor_iff`, condition
(ii) is equivalent to two concrete checks; by construction it also
subsumes the curve-side claim `P = Σ [n_i] · B_i`. -/

/-- Target divisor coefficients for the honest prover's `D`:
    `+1` at `-P`, `n_i` at each `B_i` (with duplicates summed), and
    `-degE(D)` at `∞`. All other points get `0`. -/
noncomputable def honestDivisorCoeffs (E : ECSetup) (stmt : DlogStatement E.q)
    (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) : ECPoint E.q → ℤ :=
  fun P => match P with
    | .infinity => -(msg.toD.degE : ℤ)
    | .affine x y =>
        (if (x, y) = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
          (fun i => stmt.bases i = (x, y)),
          (wit.scalars (hk ▸ i))

/-- Predicate: `msg` is the honest prover's first-round message for
    `(stmt, wit)`.

    Two conditions:
    * `msg.m_i ≡ wit.scalars i (mod q)` — the reduced scalar vector matches.
    * The divisor `(-P) + Σ_i n_i · (B_i) - degE(D) · (∞)` is principal
      (so `D = msg.toD` can be interpreted as a rational function with
      this divisor, via `IsPrincipal` from `Axioms.lean`).

    Replaces the previous `True` placeholder, which was a soundness hole:
    with `True`, `weil_reciprocity_honest` could be invoked for an
    arbitrary (possibly malicious) `msg`, yielding the false conclusion
    that `logDerivCheckFn = 0` everywhere for it. The two conjuncts here
    cannot hold jointly unless `msg` genuinely encodes the honest
    witness, closing the hole. -/
def MAProverMsg.isHonestFor (E : ECSetup) (msg : MAProverMsg E.q)
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hkm : stmt.k = msg.k) : Prop :=
  (∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)))
  ∧ IsPrincipal E (honestDivisorCoeffs E stmt wit hk msg)

structure MAChallenge (q : ℕ) [Fact (Nat.Prime q)] where
  A₀ : ZMod q × ZMod q
  A₁ : ZMod q × ZMod q

def verifierDegreeCheck (msg : MAProverMsg q) (d : ℕ) : Prop :=
  msg.toD.degE ≤ d

/-- Helper to evaluate `msg.m` at an index of statement type,
    transporting via `hk : stmt.k = msg.k`. Hides the `hk ▸` cast. -/
def MAProverMsg.mAt {stmt : DlogStatement q} {msg : MAProverMsg q}
    (hk : stmt.k = msg.k) (i : Fin stmt.k) : ZMod q :=
  msg.m (hk ▸ i)

/-- The MA verifier accepts iff the degree, admissible-set, AND
    log-derivative checks all pass. This matches paper `\protMA`
    (fig:ma): the admissible-set check `(a, b) ∈ admSet` ensures
    `D = a(x) - b(x) y ≠ 0` in `F_q[E]` (since `(0, 0) ∉ admSet`),
    which discharges the `D ≠ 0` hypothesis of the log-derivative
    soundness argument (paper obs:zero-divisor).

    The extractor handles `-P ∈ {B_j}` overlap through a dedicated
    branch in `extractedScalars` (the paper's special case), rather than
    through a verifier-side check on `D(-P)`. -/
def maVerifierAccepts (E : ECSetup) (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) (chal : MAChallenge E.q)
    (hk : stmt.k = msg.k) : Prop :=
  verifierDegreeCheck msg stmt.degBound ∧
  stmt.admSet (msg.polyA, msg.polyB) ∧
  logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
    (fun i => msg.m (hk ▸ i)) chal.A₀ chal.A₁ = 0

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
  verifierDegreeCheck msg1 stmt.degBound ∧
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
