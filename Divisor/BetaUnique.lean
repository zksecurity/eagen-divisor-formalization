/-
  Divisor/BetaUnique.lean

  Investigation of uniqueness for principal-divisor decompositions
  `β_fun : ZMod E.q × ZMod E.q → ℕ` satisfying Silverman AEC III
  Cor 3.5-style conditions (support, coverage, sum-bound, group-sum-zero).

  ## Main finding: pointwise uniqueness DOES NOT hold.

  ### Counterexample

  * **Curve:** E: y² = x³ − x over F₁₇  (q = 17, curveA = −1, curveB = 0).
  * **Point:** P = (4, 3) ∈ E(F₁₇), with −P = (4, 14).
    Verification: 3² = 9 = 4³ − 4 (mod 17). ✓
  * **Order of P:** ord(P) = 4.
    • 2P: tangent slope λ = (3·16−1)/(2·3) = 47/6 = 13·3 = 5 (mod 17).
      μ = 3−5·4 = 0. x₂ = 25−8 = 0. y₂ = 0. So 2P = (0, 0).
    • (0, 0) is a 2-torsion point (y = 0), so 4P = 2·(2P) = O. ✓
    • 2P ≠ O, so ord(P) = 4 exactly.
  * **Divisor element:** D = (a, b) with a(X) = (X − 4)³, b = 0.
    D.eval(x, y) = (x − 4)³.  D.degE = max(2·3, 3+2·0) = 6.
  * **normPoly:** N(D) = a² = (X − 4)⁶.
    rootMultiplicity(4, N(D)) = 6.
  * **betaConstructive:** Both sheets P = (4, 3) and −P = (4, 14) are
    D-zeros (since D depends only on x). Twin case: y ≠ 0 and
    D.eval(4, −3) = 0. So β(P) = β(−P) = 6/2 = 3.
    Sum = 6 ≤ 6 = D.degE. ✓
    Group sum: 3·P + 3·(−P) = 3·(P + (−P)) = 3·O = O. ✓
  * **Alternative β_fun:** β_fun(P) = 5, β_fun(−P) = 1, else 0.
    • Support: {P, −P} ⊆ E.points ∩ D⁻¹(0). ✓
    • Coverage: β_fun(P) = 5 ≠ 0, β_fun(−P) = 1 ≠ 0. ✓
    • Sum: 5 + 1 = 6 ≤ 6 = D.degE. ✓
    • Group sum: 5·P + 1·(−P) = 5P − P = 4P = O. ✓
      (since ord(P) = 4).
  * **Conclusion:** β_fun(P) = 5 ≠ 3 = betaConstructive(P).
    Both satisfy all four conditions, so pointwise uniqueness fails.

  ### Mechanism

  Over a finite field, the elliptic-curve group E(F_q) is finite, so
  every point is torsion. When a pair of twin-sheet zeros P, −P has the
  property that P has torsion order n dividing some 2t ≤ m (where
  m = rootMultiplicity of their shared x-coordinate in normPoly),
  one can redistribute t units of multiplicity from one sheet to the
  other: β(P) = m/2 + t, β(−P) = m/2 − t. The sum is unchanged (= m),
  and the group-sum change 2t·P = O vanishes because n | 2t. The
  coverage condition is preserved whenever m/2 − t ≥ 1.

  ### Consequences for `polyG_zero_trace_formula`

  The axiom `polyG_zero_trace_formula` (in `ExtractorBridge.lean`)
  quantifies over *arbitrary* β_fun satisfying the four conditions.
  Since pointwise uniqueness fails, the polyG-vanishing for an
  arbitrary β_fun CANNOT be reduced to the betaConstructive case
  via a uniqueness argument: the ZMod E.q-casts of the multiplicities
  genuinely differ (5 ≠ 3 in ZMod 17), and polyG is linear in those
  casts.

  The correct proof of `polyG_zero_trace_formula` must appeal to the
  function-field trace-of-log-derivative identity (Lang *Algebra*
  §VI.5 + Stichtenoth §III.1–5 + Silverman ATAEC III §1) applied
  to each valid β_fun independently. This is the content the axiom
  captures; no uniqueness shortcut exists.

  ### Weaker true statements

  We prove two weaker statements that ARE true:

  1. **Support agreement** (`support_iff_of_principal_conditions`):
     any valid β_fun is nonzero at exactly the same points as
     betaConstructive — the zero locus of D on E.

  2. **Group-sum agreement** (`group_sum_eq_of_principal_conditions`):
     any valid β_fun has the same weighted group sum as
     betaConstructive (namely zero). This expresses the fact
     that both represent principal divisors with the same underlying
     rational function D up to the sign of the pole at ∞.

  Neither statement suffices to bridge `polyG_zero_trace_formula`
  from the betaConstructive case to the general case, because polyG
  depends on the *individual* multiplicity values (mod q), not just
  their support or group sum.
-/
import Divisor.BetaConstructive
import Divisor.DivisorPrincipal
import Divisor.Axioms.AxiomCoordRingEltDivisorGroupSumZero

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Weaker true statement 1: Support agreement

    Any β_fun satisfying the support and coverage conditions has the
    same support as `betaConstructive E D`. -/

/-- Two valid multiplicity functions are nonzero at exactly the same
    points: the affine zeros of `D` on `E`. -/
theorem support_iff_of_principal_conditions
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0) :
    ∀ P, β_fun P ≠ 0 ↔ betaConstructive E D P ≠ 0 := by
  intro P
  constructor
  · intro hβ
    obtain ⟨hPE, hPZ⟩ := hβsup P hβ
    exact betaConstructive_covers E D hD P hPE hPZ
  · intro hBC
    obtain ⟨hPE, hPZ⟩ := betaConstructive_support E D P hBC
    exact hβcov P hPE hPZ

/-! ## Weaker true statement 2: Group-sum agreement

    Both β_fun and betaConstructive yield vanishing weighted group
    sums (both represent the affine part of the same principal
    divisor class). -/

/-- The weighted group sum of any valid β_fun equals that of
    betaConstructive (both are zero). Requires the splitting hypothesis
    so that `betaConstructive_group_sum_zero` matches Silverman AEC III
    Cor 3.5 exactly. -/
theorem group_sum_eq_of_principal_conditions
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβgroup : ECPoint.weightedSum E E.points
                 (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine P.1 P.2)) = 0) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine P.1 P.2)) =
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) := by
  rw [hβgroup, betaConstructive_group_sum_zero E D hD hSplit]

/-! ## Sum-bound agreement

    Both β_fun and betaConstructive have sums bounded by D.degE.
    This is an immediate consequence of their respective hypotheses. -/

/-- Both valid multiplicity functions have ∑ β ≤ D.degE. -/
theorem sum_le_degE_of_principal_conditions
    (D : CoordRingElt E.q)
    (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ D.degE) :
    (∑ P ∈ E.points, β_fun P) ≤ D.degE ∧
    (∑ P ∈ E.points, betaConstructive E D P) ≤ D.degE :=
  ⟨hβsum, betaConstructive_sum_le_degE E D⟩

/-! ## The original pointwise uniqueness statement is FALSE.

    The theorem

    ```
    multAt E β_fun D k = multAt E (betaConstructive E D) D k
    ```

    does not hold for all valid β_fun. See the counterexample at the
    top of this file (E: y² = x³ − x over F₁₇, D = (x−4)³,
    β_fun(4,3) = 5 vs betaConstructive(4,3) = 3).

    The commented-out statement below records what was requested;
    it is left commented because it is false:
-/

-- /-- **FALSE** — see counterexample above.
-- theorem multAt_eq_multAt_betaConstructive_of_principal_conditions
--     (E : ECSetup) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
--     (β_fun : ZMod E.q × ZMod E.q → ℕ)
--     (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
--     (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
--     (hβsum : (∑ P ∈ E.points, β_fun P) ≤ D.degE)
--     (hβgroup : ECPoint.weightedSum E E.points
--                  (fun P => ECPoint.nsmul E (β_fun P) (ECPoint.affine P.1 P.2)) = 0) :
--     ∀ k : Fin (zerosCard E D),
--       multAt E β_fun D k = multAt E (betaConstructive E D) D k
-- -/

/-! ## Path forward for `polyG_zero_trace_formula`

    The axiom `polyG_zero_trace_formula` (ExtractorBridge.lean)
    quantifies over arbitrary β_fun. Since pointwise uniqueness
    fails, eliminating that axiom requires the full function-field
    trace-of-log-derivative argument:

    1. For any nonzero D ∈ F_q[E] and any principal-divisor
       decomposition β_fun, the residue identity (`\ref{lem:log-derivative}` /
       `chord_sum_eq_residue_sum`) holds with β_fun's
       multiplicities — not just betaConstructive's. This follows
       from the fact that div(D) = Σ β(P)·(P) − deg·(∞) is the
       SAME divisor regardless of which valid β_fun is used to
       compute it (Silverman AEC III Cor 3.5 uniqueness of div(f)
       for f), combined with the residue theorem for differentials
       on E (Stichtenoth §III.5).

    2. The polyG = 0 conclusion then follows from combining the
       generalized residue identity with logDerivCheckFn = 0, as
       in `polyG_zero_of_Lemma6_and_logDerivCheck_zero`.

    Note: while the *multiplicity values* β_fun(P) are not unique
    (counterexample above), the formal divisor div(D) ∈ Div(E) IS
    unique (it is determined by D as a rational function on E).
    The non-uniqueness arises because multiple ℕ-valued functions
    can represent the same formal divisor's affine part when the
    pole order at ∞ is not pinned to exactly D.degE (only bounded
    by ≤ D.degE). In the classical setting where ∑ β = D.degE
    exactly, the decomposition IS unique; the non-uniqueness is
    an artifact of the weakened sum-bound condition. -/

end Divisor
