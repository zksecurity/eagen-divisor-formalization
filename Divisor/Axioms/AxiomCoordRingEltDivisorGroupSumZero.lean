/-
  Divisor/Axioms/AxiomCoordRingEltDivisorGroupSumZero.lean

  Narrow Abel's theorem form: β-weighted group-sum of D's zeros is O,
  under the splitting hypothesis.

  Reference: Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
  Corollary III.3.5, p. 63 (the ⇒ direction, specialised to F_q-rational
  divisors under splitting). See `axioms/coordringelt_divisor_group_sum_zero.md`.
-/
import Divisor.Defs
import Divisor.BetaConstructive

namespace Divisor

variable (E : ECSetup)

/-- **Abel's theorem on E for `D`'s divisor, split form** (Silverman
    AEC III Corollary 3.5, p.63, group-sum-zero direction — derived in
    Silverman from Prop 3.4(a,e)).

    Under the splitting hypothesis `normPoly_splits_over_Fq E D`, every
    geometric zero of `D` on `E` is F_q-rational, so the F_q-sum
    matches the full `Σ [n_P] P` of Cor 3.5. The `β`-weighted group
    sum over `E`'s affine points then vanishes: the divisor of the
    nonzero rational function `D = a(x) − b(x)·y` has group-sum zero,
    and the `∞` contribution is `-D.degE · (∞) = 0`.

    **Textbook statement (verbatim), Silverman AEC Corollary III.3.5, p.63:**

    > "Corollary 3.5. Let E be an elliptic curve and let
    > D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
    >    Σ_{P ∈ E} n_P = 0   and   Σ_{P ∈ E} [n_P] P = O.
    > (Note that the first sum is of integers, while the second is
    > addition on E.)"

    This axiom uses the `(⇒)` direction of Cor 3.5 (principal ⇒ group-sum-zero),
    specialised to `D = a(x) − b(x)·y ∈ F_q[E]^×` whose geometric divisor
    is F_q-supported under the splitting hypothesis. -/
axiom CoordRingElt.divisor_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0

/-- Direct restatement of the group-sum axiom as a convenience theorem
    under the chosen `β = betaConstructive E D` representative. Requires
    the splitting hypothesis to match Silverman AEC III Cor 3.5 exactly. -/
theorem betaConstructive_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0 :=
  CoordRingElt.divisor_group_sum_zero E D hD hSplit

end Divisor
