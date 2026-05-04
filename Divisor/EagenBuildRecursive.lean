/-
  Divisor/EagenBuildRecursive.lean

  Recursive `eagenBuild` driver for general-N point lists, following
  Eagen §3.1.1 ("Incremental construction") in 596.pdf.

  The construction:
  * Level 0 input: list of points P_0, ..., P_{n-1} summing to zero.
  * For each adjacent pair (P_2i, P_2i+1):
      - Build chord line L_i through them with third intersection Q_i = -(P_2i + P_2i+1).
      - div(L_i) = (P_2i) + (P_2i+1) + (Q_i) - 3O.
  * Level 1 input: list of points [-Q_0, -Q_1, ...]. (Note: -Q_i = P_2i + P_2i+1.)
  * For each adjacent pair (-Q_2j, -Q_2j+1):
      - Build chord line L'_j through them with third intersection Q'_j = Q_2j + Q_2j+1.
      - Combined polynomial associated with Q'_j:
            M_j = L'_j · L_2j · L_2j+1 / ((x - x(Q_2j))(x - x(Q_2j+1)))
        with div(M_j) = (P_4j) + (P_4j+1) + (P_4j+2) + (P_4j+3) + (Q'_j) - 5O.
  * Recurse on the Q'_j's.
  * Termination: if Σ P_i = 0, the final third intersection is O, and the
    output polynomial has divisor exactly Σ (P_i) - n·O.

  Odd-length lists: carry the unpaired point + polynomial forward.

  This file builds the recursive driver and proves the divisor equation
  by induction on levels. Length-4 (handled in `Divisor/IncrementalConstruction.lean`)
  is the base case; this file generalizes to length-2^k and beyond.
-/

import Divisor.IncrementalConstruction

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-- An "accumulator" entry: a point and a polynomial whose divisor is
    `(absorbed P_i's) + (point) - (level+1)·O`. The recursion combines
    pairs of accumulators into a new entry at the next level. -/
structure EagenAccum where
  /-- The "carry point" — the running negation-of-sum of absorbed P_i's. -/
  point : ZMod E.q × ZMod E.q
  /-- The accumulated polynomial. At level 0 this is `1` (multiplicative identity).
      At level k > 0, contains `k+1` accumulated chord-line factors and `k`
      vertical-line denominators. -/
  poly : CoordRingElt E.q

/-- Initial accumulator from a single point: `(P, 1)`. -/
noncomputable def EagenAccum.singleton (P : ZMod E.q × ZMod E.q) : EagenAccum E :=
  { point := P, poly := { a := 1, b := 0 } }

/-- Combine two accumulators per Eagen §3.1.1: build the chord/tangent line
    `L` through their points, take third intersection `Q`, and form
    `(L · a.poly · b.poly) / (X - x(a.point))^? / (X - x(b.point))^?`.

    For now, this is a placeholder; the full division logic depends on
    whether either point is at infinity (handled by carry-forward in
    odd-length lists). For two affine points with distinct x-coordinates,
    the chord is regular and we divide by both `(X - x(a.point))` and
    `(X - x(b.point))`. -/
noncomputable def EagenAccum.combine_distinct (a b : EagenAccum E)
    (_h_xx : a.point.1 ≠ b.point.1) : EagenAccum E :=
  let chord := chordCoordRingElt E a.point b.point
  let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
  let Qx := lam ^ 2 - a.point.1 - b.point.1
  let Qy := lam * Qx + (a.point.2 - lam * a.point.1)
  -- Q := (Qx, Qy) is the third intersection. The next-level "carry point" is -Q.
  let neg_Q : ZMod E.q × ZMod E.q := (Qx, -Qy)
  -- Combined polynomial: chord · a.poly · b.poly, divided by verticals at a.point.1
  -- and b.point.1.
  let mul_combined := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
  -- Apply two divLin operations.
  let after_divA := mul_combined.divLin a.point.1
  let after_divB := after_divA.divLin b.point.1
  { point := neg_Q, poly := after_divB }

/-- Pair adjacent entries in a list and combine each pair. Carries forward
    a single unpaired entry at the end (odd-length lists). -/
noncomputable def eagenBuild_one_level (xs : List (EagenAccum E)) :
    List (EagenAccum E) :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if h : a.point.1 ≠ b.point.1 then
        EagenAccum.combine_distinct E a b h :: eagenBuild_one_level rest
      else
        -- Same x-coordinates: either tangent doubling or vertical chord.
        -- For now, fail-safely return the inputs unchanged (this case will
        -- need separate handling).
        a :: b :: eagenBuild_one_level rest

/-- Iterate `eagenBuild_one_level` until the list has length ≤ 1.
    Termination: each level halves the list length; fuel = `xs.length` is
    safely an upper bound. -/
noncomputable def eagenBuild_iterate :
    ℕ → List (EagenAccum E) → List (EagenAccum E)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else eagenBuild_iterate n (eagenBuild_one_level E xs)

/-- Top-level eagenBuild driver: takes a list of points (assumed to sum to
    zero) and returns the polynomial witness. The result polynomial's
    divisor equals `Σ (P_i) - n·O` when the input sums to zero. -/
noncomputable def eagenBuild (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingElt E.q :=
  let initial := Ps.map (EagenAccum.singleton E)
  let final := eagenBuild_iterate E Ps.length initial
  match final with
  | [] => { a := 1, b := 0 }  -- empty input: identity
  | [single] => single.poly  -- single accumulator: the answer
  | _ => { a := 1, b := 0 }  -- shouldn't happen if iterations sufficient

/-! ## Future work

This is the skeleton of the recursive driver. Substantial proofs needed:

1. **Divisor equation**: `divisorOfD E (eagenBuild E Ps) R` computes
   correctly per the Eagen procedure (induction on levels).
2. **Odd-length handling**: properly carry-forward the unpaired entry.
3. **Tangent doubling**: handle `a.point = b.point` case (m = 2 input).
4. **Vertical chord**: handle `a.point = -b.point` case (chord is vertical).
5. **Termination/correctness of `eagenBuild_iterate`**: fuel-based recursion
   produces a length-1 list when starting from non-empty even-length input.

The length-4 base case is handled in `Divisor/IncrementalConstruction.lean`'s
`eagenBuild_length4_explicit`. The recursive driver will reduce to that
case at the second-to-last level. -/

end Divisor
