/-
  Divisor/NormVanish.lean

  Theorem 2 (Norm Vanishing): Bassa 2024a, Theorem 6.

  If D vanishes at Q_1,...,Q_N and P != Q_i, then for random
  A0, A1 defining a line L:

    Pr[N_{F_q(E)/F_q(L)}(D)(L(P)) = 0] <= 2*N / (#E(F_q) - 1)

  Proof: The norm vanishes iff L(P) = L(Q_i) for some i,
  which forces the slope lam = (y(P)-y(Q_i))/(x(P)-x(Q_i)).
  At most N such slopes; each has probability <= 2/(#E-1)
  by Lemma 1. Union bound gives 2N/(#E-1).
-/
import Divisor.Defs
import Divisor.SlopeDist

namespace Divisor

variable (E : ECSetup)

/-! ## Norm vanishing condition

N_{F_q(E)/F_q(L)}(D)(L(P)) = 0 iff L(P) = L(Q_i) for some zero Q_i of D.
This is equivalent to: there exists i such that
  y(P) - lam * x(P) = y(Q_i) - lam * x(Q_i)
i.e. lam = (y(P) - y(Q_i)) / (x(P) - x(Q_i))  when x(P) != x(Q_i).
When x(P) = x(Q_i), since P != Q_i we must have y(P) != y(Q_i),
so no lam satisfies the equation.
-/

/-- The set of "bad slopes" for P relative to the zeros Q_i of D:
    slopes lam such that L(P) = L(Q_i) for some zero Q_i. -/
def badSlopes (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    Finset (ZMod E.q) :=
  ((zeros D E.points).filter (fun Q => Q.1 ≠ P.1)).image
    (fun Q => slopeOf P.1 P.2 Q.1 Q.2)

/-- There are at most N bad slopes (one per zero with x(Q) != x(P)) -/
theorem card_badSlopes_le (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N) :
    (badSlopes E D P).card ≤ N := by
  unfold badSlopes
  calc (((zeros D E.points).filter (fun Q => Q.1 ≠ P.1)).image
          (fun Q => slopeOf P.1 P.2 Q.1 Q.2)).card
      ≤ ((zeros D E.points).filter (fun Q => Q.1 ≠ P.1)).card := Finset.card_image_le
    _ ≤ (zeros D E.points).card := Finset.card_filter_le _ _
    _ ≤ N := hN

/-- The set of pairs (A0, A1) where the norm vanishes at L(P) -/
def normVanishPairs (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (distinctPairs E.points).filter (fun pair =>
    pair.1.1 ≠ pair.2.1 ∧
    ∃ lam ∈ badSlopes E D P,
      slopeOf pair.1.1 pair.1.2 pair.2.1 pair.2.2 = lam)

/-! ## Main result: Theorem 2 -/

/-- **Theorem 2 (Norm Vanishing).**
    The number of pairs (A0, A1) where the norm of D
    vanishes at L(P) is at most 2 * N * numAffine.

    Since there are numAffine * (numAffine - 1) ordered pairs,
    Pr[norm vanishes] <= 2*N*numAffine / (numAffine*(numAffine-1))
                       = 2*N / (numAffine - 1)
                       = 2*N / (#E(F_q) - 2). -/
theorem norm_vanishing (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N)
    (hP : P ∈ E.points)
    (hPnotZero : P ∉ zeros D E.points) :
    (normVanishPairs E D P).card ≤ 2 * N * E.numAffine := by
  sorry
  -- Proof:
  -- normVanishPairs is a subset of the union over lam in badSlopes
  -- of pairsWithSlope lam.
  -- By slope_distribution, each pairsWithSlope has card <= 2 * numAffine.
  -- By card_badSlopes_le, there are at most N bad slopes.
  -- By union bound: total <= N * (2 * numAffine) = 2 * N * numAffine.

end Divisor
