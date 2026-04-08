/-
  Divisor/SlopeDist.lean

  Lemma 1 (Slope Distribution): Bassa 2025, Lemma 4.

  For a given slope lam in F_q, the number of ordered pairs
  (A0, A1) of distinct affine points on E such that the line
  through them has slope lam is at most 2 * (#E(F_q) - 1).

  Equivalently: Pr[slope(A0,A1) = lam] <= 2 / (#E(F_q) - 1).

  Proof: classify lines of slope lam by how they meet E.
  A cubic meets a line in at most 3 points (counted with multiplicity).
  Each rational point on E lies on exactly one line of slope lam.
  A line with k distinct rational points contributes k*(k-1) ordered pairs.
  Since k <= 3, we have k*(k-1) <= 2*k, so the total number of
  ordered pairs is at most 2 * (number of rational points on all such lines)
  = 2 * (numAffine).
-/
import Divisor.Defs

namespace Divisor

variable (E : ECSetup)

/-! ## Lines of a given slope -/

/-- The set of affine points with a given x-coordinate -/
def pointsWithX (x : ZMod E.q) : Finset (ZMod E.q × ZMod E.q) :=
  E.points.filter (fun p => p.1 = x)

/-- A line of slope lam partitions E(F_q) \ {O}: each affine point
    lies on exactly one line y = lam * x + c for a unique c. -/
def interceptOf (lam : ZMod E.q) (p : ZMod E.q × ZMod E.q) : ZMod E.q :=
  p.2 - lam * p.1

/-- Points on the line y = lam * x + c -/
def pointsOnLine (lam c : ZMod E.q) : Finset (ZMod E.q × ZMod E.q) :=
  E.points.filter (fun p => p.2 = lam * p.1 + c)

/-- Each line of slope lam meets E in at most 3 affine rational points.
    (A line and a cubic intersect in at most 3 points by Bezout.) -/
axiom line_meets_cubic_le_three (lam c : ZMod E.q) :
  (pointsOnLine E lam c).card ≤ 3

/-- Ordered pairs of distinct points on a single line -/
def orderedPairsOnLine (lam c : ZMod E.q) : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  distinctPairs (pointsOnLine E lam c)

/-- Key inequality: for k <= 3, k * (k - 1) <= 2 * k -/
theorem ordered_pairs_le_twice (k : ℕ) (hk : k ≤ 3) : k * (k - 1) ≤ 2 * k := by
  interval_cases k <;> omega

/-- The number of ordered pairs on a line with at most 3 points
    is at most twice the number of points on that line. -/
theorem card_orderedPairsOnLine_le (lam c : ZMod E.q) :
    (orderedPairsOnLine E lam c).card ≤ 2 * (pointsOnLine E lam c).card := by
  sorry

/-- The set of ordered pairs with a given slope lam -/
def pairsWithSlope (lam : ZMod E.q) :
    Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (distinctPairs E.points).filter (fun p =>
    p.1.1 ≠ p.2.1 ∧ slopeOf p.1.1 p.1.2 p.2.1 p.2.2 = lam)

/-- Each affine point lies on exactly one line of slope lam,
    so the total number of rational incidences is at most numAffine. -/
theorem total_points_on_lines_le (lam : ZMod E.q) :
    (E.points.biUnion (fun p =>
      ({interceptOf E lam p} : Finset (ZMod E.q)).image
        (fun c => (pointsOnLine E lam c).card))).sum id ≤ E.numAffine := by
  sorry

/-! ## Main result: Lemma 1 -/

/-- **Lemma 1 (Slope Distribution).**
    For a given slope lam, the number of ordered pairs (A0, A1)
    of distinct affine points on E with that slope is at most
    2 * numAffine.

    Since there are numAffine * (numAffine - 1) total ordered pairs
    of distinct affine points, this gives:
      Pr[slope = lam] <= 2 * numAffine / (numAffine * (numAffine - 1))
                       = 2 / (numAffine - 1)
                       = 2 / (#E(F_q) - 2)
    The paper's bound 2 / (#E(F_q) - 1) follows since numAffine = #E - 1. -/
theorem slope_distribution (lam : ZMod E.q) :
    (pairsWithSlope E lam).card ≤ 2 * E.numAffine := by
  sorry
  -- Proof sketch:
  -- 1. Partition pairsWithSlope by the intercept c = y0 - lam*x0.
  -- 2. Pairs with intercept c are exactly orderedPairsOnLine lam c.
  -- 3. By card_orderedPairsOnLine_le, each contributes <= 2 * (pointsOnLine lam c).card.
  -- 4. Sum over all c: sum of (pointsOnLine lam c).card = numAffine
  --    (each affine point on exactly one line of slope lam).
  -- 5. Total <= 2 * numAffine.

end Divisor
