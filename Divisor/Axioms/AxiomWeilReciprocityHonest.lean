/-
  Divisor/Axioms/AxiomWeilReciprocityHonest.lean

  Completeness form of Weil reciprocity: for the honest prover's
  divisor, `logDerivCheckFn` vanishes off the bad set.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Exercise II.2.11, p. 39 (the Weil reciprocity law as such);
  Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.),
  Corollary 4.3.3 (Residue Theorem), p. 171 (the theorem it descends
  from). See `axioms/weil_reciprocity_honest.md`.
-/
import Divisor.Defs
import Divisor.SupportDisjoint
import Divisor.Protocol
import Divisor.LogDeriv

namespace Divisor

variable (E : ECSetup)

/-- **Weil reciprocity axiom** (classical; Silverman AEC Exercise II.2.11,
    p.39).

    If `msg` is the honest first-round message for `(stmt, wit)` — i.e.
    `msg.toD`'s divisor of zeros on `E` is `(-P) + Σ n_i · (B_i)` as
    encoded by `MAProverMsg.isHonestFor` — then the log-derivative
    identity `logDerivCheckFn` vanishes at every challenge whose
    `{A₀, A₁, A₂}` is disjoint from `supp((D)_0)` (equivalently:
    `(A₀, A₁) ∉ badChallengesCompleteness E msg.toD`).

    This is Weil reciprocity applied to the principal divisor of the
    rational function `D / L^m` where `L` is the chord line through
    the on-curve points `A₀, A₁, A₂`: the log-derivative identity is obtained from the
    fact that a principal divisor has zero sum of residues on `E`, so
    summing residues over the divisor of zeros yields the stated
    identity whenever the evaluation points avoid the support of that
    divisor.

    **Textbook statement (verbatim), Silverman AEC Exercise II.2.11, p.39:**

    > "2.11. Let C be a smooth curve and let f, g ∈ K̄(C)* be functions
    > such that div(f) and div(g) have disjoint support. (See Exercise
    > 2.10.) Prove Weil's reciprocity law
    >     f(div(g)) = g(div(f))
    > using the following two steps:
    > (a) Verify Weil's reciprocity law directly for C = P¹.
    > (b) Now prove it for arbitrary C by using the map g : C → P¹ to
    >     reduce to (a)."

    (Exercise 2.10 defines `f(D) = ∏_P f(P)^{n_P}` for D = Σ n_P (P)
    when div(f) and D have disjoint supports.)

    **Related theorem (Residue Theorem), Stichtenoth Cor 4.3.3, p.171:**

    > "Corollary 4.3.3 (Residue Theorem). Let F/K be an algebraic
    > function field over an algebraically closed field, and let
    > ω ∈ Δ_F be a differential of F/K. Then res_P(ω) = 0 for almost
    > all places P ∈ IP_F, and Σ_{P ∈ IP_F} res_P(ω) = 0."

    Weil reciprocity is the direct corollary of the Residue Theorem
    applied to `f · dg/g` and `g · df/f`. -/
axiom weil_reciprocity_honest
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0

end Divisor
