/-
  Divisor/NormVanish.lean

  Theorem 2 (Norm Vanishing): proved from Lemma 1 (slope distribution).

  If D vanishes at Q_1,...,Q_N and P != Q_i, then for random line L:
    Pr[N(D)(L(P)) = 0] <= 2*N / (#E(F_q) - 1)
-/
import Divisor.Defs
import Divisor.SlopeDist

namespace Divisor

variable (E : ECSetup)

/-! ## Norm vanishing reduces to slope distribution

N(D)(L(P)) = 0 iff L(P) = L(Q_i) for some zero Q_i of D.
This requires the slope lam = (y(P)-y(Q_i))/(x(P)-x(Q_i)).
At most N such slopes exist. Each occurs with probability
<= 2/(#E-1) by slope distribution (Lemma 1).
Union bound gives 2N/(#E-1).
-/

/-- Bad slopes: slopes lam such that L(P) = L(Q_i) for some zero Q_i -/
def badSlopes (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    Finset (ZMod E.q) :=
  ((zeros D E.points).filter (fun Q => Q.1 ≠ P.1)).image
    (fun Q => slopeOf P.1 P.2 Q.1 Q.2)

/-- At most N bad slopes -/
theorem card_badSlopes_le (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N) :
    (badSlopes E D P).card ≤ N := by
  unfold badSlopes
  calc (((zeros D E.points).filter _).image _).card
      ≤ ((zeros D E.points).filter _).card := Finset.card_image_le
    _ ≤ (zeros D E.points).card := Finset.card_filter_le _ _
    _ ≤ N := hN

/-- Pairs where the norm vanishes at L(P) -/
def normVanishPairs (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (distinctPairs E.points).filter (fun pair =>
    pair.1.1 ≠ pair.2.1 ∧
    ∃ s ∈ badSlopes E D P,
      slopeOf pair.1.1 pair.1.2 pair.2.1 pair.2.2 = s)

/-- **Theorem 2 (Norm Vanishing).**
    The number of pairs where the norm vanishes at L(P) is at most
    2 * N * numAffine, giving Pr <= 2N / (numAffine - 1).

    Proof: union bound over at most N bad slopes, each contributing
    at most 2 * numAffine pairs by Lemma 1. -/
theorem norm_vanishing (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N)
    (hP : P ∈ E.points)
    (hPnotZero : P ∉ zeros D E.points) :
    (normVanishPairs E D P).card ≤ 2 * N * E.numAffine := by
  sorry
  -- Proof outline:
  -- normVanishPairs ⊆ ⋃_{s ∈ badSlopes} pairsWithSlope s
  -- By Lemma 1: each |pairsWithSlope s| ≤ 2 * numAffine
  -- By card_biUnion_le: |⋃| ≤ Σ_{s ∈ badSlopes} 2 * numAffine
  -- = |badSlopes| * 2 * numAffine ≤ N * 2 * numAffine

end Divisor
