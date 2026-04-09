/-
  Divisor/NormVanish.lean — Theorem 2 (Norm Vanishing)
-/
import Divisor.Defs
import Divisor.SlopeDist

open Finset

namespace Divisor

variable (E : ECSetup)

/-- Bad slopes: slopes where L(P) = L(Q_i) for some zero Q_i -/
def badSlopes (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    Finset (ZMod E.q) :=
  ((zeros D E.points).filter (fun Q => Q.1 ≠ P.1)).image
    (fun Q => slopeOf P.1 P.2 Q.1 Q.2)

theorem card_badSlopes_le (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N) :
    (badSlopes E D P).card ≤ N := by
  calc (badSlopes E D P).card
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
    |normVanishPairs| ≤ 2 * N * numAffine.

    Proof: normVanishPairs ⊆ ⋃_{s ∈ badSlopes} pairsWithSlope s.
    By Lemma 1 each has ≤ 2*numAffine elements.
    By card_biUnion_le and card_badSlopes_le. -/
theorem norm_vanishing (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (N : ℕ) (hN : (zeros D E.points).card ≤ N)
    (hP : P ∈ E.points)
    (hPnotZero : P ∉ zeros D E.points) :
    (normVanishPairs E D P).card ≤ 2 * N * E.numAffine := by
  -- normVanishPairs ⊆ ⋃_{s ∈ badSlopes} pairsWithSlope s
  have hsub : normVanishPairs E D P ⊆
      (badSlopes E D P).biUnion (fun s => pairsWithSlope E s) := by
    intro p hp
    simp only [normVanishPairs, Finset.mem_filter, Finset.mem_biUnion] at hp ⊢
    obtain ⟨hdist, hx, s, hs, hslope⟩ := hp
    exact ⟨s, hs, Finset.mem_filter.mpr ⟨hdist, hx, hslope⟩⟩
  calc (normVanishPairs E D P).card
      ≤ ((badSlopes E D P).biUnion (fun s => pairsWithSlope E s)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s ∈ badSlopes E D P, (pairsWithSlope E s).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ s ∈ badSlopes E D P, (2 * E.numAffine) :=
        Finset.sum_le_sum (fun s _ => slope_distribution E s)
    _ = (badSlopes E D P).card * (2 * E.numAffine) := by
        simp [Finset.sum_const]
    _ ≤ N * (2 * E.numAffine) := by
        apply Nat.mul_le_mul_right
        exact card_badSlopes_le E D P N hN
    _ = 2 * N * E.numAffine := by ring

end Divisor
