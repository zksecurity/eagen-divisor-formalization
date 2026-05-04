/-
  Divisor/EagenBuildRecursive.lean

  Recursive `eagenBuild` driver for general-N point lists, following
  Eagen §3.1.1 ("Incremental construction") in 596.pdf.

  ## The construction (for sum-zero list `Ps`)

  **Level 0**: pair adjacent inputs `(P_2i, P_2i+1)`, build chord line
  `L_i` through them with third intersection `Q_i = -(P_2i + P_2i+1)`.
  Each such pair produces a level-1 entry `(-Q_i, L_i)` — point is
  `-Q_i = P_2i + P_2i+1` (group sum), polynomial is the chord line.

  **Level k → k+1** (k ≥ 1): given level-k entries `(a_pt, a_poly)` and
  `(b_pt, b_poly)` (where the points are `-Q_*` from previous level),
  build chord line `L'` through `a_pt, b_pt` with third intersection
  `Q'`. The level-(k+1) entry is `(-Q', M)` where:

      M = (L' · a_poly · b_poly) / ((X - x(a_pt)) · (X - x(b_pt)))

  Both `(X - x(a_pt))` and `(X - x(b_pt))` divide cleanly because the
  numerator vanishes at both `±a_pt.1` (since `L'` vanishes at `a_pt`
  and `a_poly` vanishes at `-(a_pt) = Q_{prev}`) and similarly for
  `b_pt`.

  **Termination**: when the input list is sum-zero, the final third
  intersection at the top level is `O` (infinity). The output polynomial
  has divisor exactly `Σ(P_i) - n·O`.

  **Odd lengths**: carry the unpaired entry forward to the next level.

  ## Status

  This file holds the skeleton + design. The length-4 base case is in
  `Divisor/IncrementalConstruction.lean` (proved equivalent to the
  paper's level-1 simplification under sum-zero). Generalization to
  any-N requires:

  1. Carry-forward logic for odd lengths.
  2. Division correctness proof (verticals factor cleanly).
  3. Divisor equation by induction on levels.
  4. Tangent doubling / vertical-chord branches at each level.
-/

import Divisor.IncrementalConstruction

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-- An "accumulator" entry at level k > 0: a point (= -Q from prior
    level chord = group-sum of absorbed P's at this level) and the
    accumulated polynomial whose divisor incorporates the absorbed P's
    plus the third intersection. -/
structure EagenAccum where
  point : ZMod E.q × ZMod E.q
  poly : CoordRingElt E.q

/-! ## Level-0 step: build chord lines from input points

For a list of input points `[P_0, P_1, ..., P_{n-1}]`, pair them up and
build chord lines. Each pair `(P_2i, P_2i+1)` produces a level-1 entry
`(-Q_i, L_i)`.

Odd-length input: the last (unpaired) point becomes a level-1 entry
`(P_{n-1}, 1)` carrying just the point with identity polynomial. -/

/-- Build a level-1 accumulator from two distinct affine points.
    The chord through `P, Q` has third intersection `-(P+Q)`; the new
    accumulator is `(-(P+Q), chord)`. -/
noncomputable def EagenAccum.fromChordPair_distinct
    (P Q : ZMod E.q × ZMod E.q) (_h_xx : P.1 ≠ Q.1) : EagenAccum E :=
  let chord := chordCoordRingElt E P Q
  let lam := slopeOf P.1 P.2 Q.1 Q.2
  let Qx := lam ^ 2 - P.1 - Q.1
  let Qy := lam * Qx + (P.2 - lam * P.1)
  -- Third intersection is (Qx, Qy). The "next-level input" is its negation.
  { point := (Qx, -Qy), poly := chord }

/-- Process the initial input list, pairing adjacent points and building
    chord lines. Returns the level-1 accumulator list. Odd input lengths
    carry the last point forward as `(P_last, 1)`. -/
noncomputable def eagenBuild_level0 (Ps : List (ZMod E.q × ZMod E.q)) :
    List (EagenAccum E) :=
  match Ps with
  | [] => []
  | [P] => [{ point := P, poly := { a := 1, b := 0 } }]
  | P :: Q :: rest =>
      if h : P.1 ≠ Q.1 then
        EagenAccum.fromChordPair_distinct E P Q h :: eagenBuild_level0 rest
      else
        -- Tangent doubling or vertical chord: handled separately.
        -- For now, fail-safely return a placeholder.
        { point := P, poly := { a := 1, b := 0 } } :: eagenBuild_level0 rest

/-! ## Level-(k+1) step (k ≥ 1): combine two level-k accumulators

Combine `(a_pt, a_poly)` and `(b_pt, b_poly)` per the paper formula:
    `new_poly = chord(a_pt, b_pt) · a_poly · b_poly / divLin(a_pt.1) / divLin(b_pt.1)`. -/

noncomputable def EagenAccum.combine_higher_distinct
    (a b : EagenAccum E) (_h_xx : a.point.1 ≠ b.point.1) : EagenAccum E :=
  let chord := chordCoordRingElt E a.point b.point
  let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
  let Qx := lam ^ 2 - a.point.1 - b.point.1
  let Qy := lam * Qx + (a.point.2 - lam * a.point.1)
  let mul_with_chord := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
  let after_div_a := mul_with_chord.divLin a.point.1
  let after_div_b := after_div_a.divLin b.point.1
  { point := (Qx, -Qy), poly := after_div_b }

/-- Combine two accumulators when their points are negatives of each
    other (`a.point = -b.point`, so `a.point.1 = b.point.1`). The chord
    through `(P, -P)` is the vertical line `(X - x(P))`. Their group sum
    is `0` (the identity = ∞), so the level-(k+1) "third intersection"
    is also `O`.

    Polynomial: `(X - x(a.point)) · a.poly · b.poly / (X - x(a.point))^2
                = a.poly · b.poly / (X - x(a.point))`. -/
noncomputable def EagenAccum.combine_higher_vertical
    (a b : EagenAccum E)
    (_h_xx : a.point.1 = b.point.1) (_h_yy : a.point.2 = -b.point.2) :
    EagenAccum E :=
  -- Combined = a.poly · b.poly / (X - x(a.point)).
  let mul_ab := mulCoordRingElt E a.poly b.poly
  let combined := mul_ab.divLin a.point.1
  -- "New point" is the identity (= O). Encode as the affine pair (a.point.1, 0)
  -- as a sentinel; in the divisor equation, the actual contribution is at ∞.
  -- Since the recursion should terminate here for sum-zero inputs, the
  -- output is whatever consumer extracts.
  { point := a.point, poly := combined }

/-- Process a level-k (k ≥ 1) accumulator list, pairing adjacent entries
    and combining each pair. Odd-length lists carry the last entry forward. -/
noncomputable def eagenBuild_level_step (xs : List (EagenAccum E)) :
    List (EagenAccum E) :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if h : a.point.1 ≠ b.point.1 then
        EagenAccum.combine_higher_distinct E a b h :: eagenBuild_level_step rest
      else if hYY : a.point.2 = -b.point.2 then
        -- Vertical chord case (a.point = -b.point).
        EagenAccum.combine_higher_vertical E a b
          (Classical.byContradiction (fun h_neq => h h_neq)) hYY ::
          eagenBuild_level_step rest
      else
        -- Tangent doubling: a.point = b.point. Deferred.
        a :: b :: eagenBuild_level_step rest

/-! ## Top-level driver

Iterate `eagenBuild_level_step` until the list reduces to one entry. Use
`fuel := xs.length` as a termination measure (each step at least halves
the list, so log₂ of length is sufficient; length itself is overkill but
safe). -/

noncomputable def eagenBuild_iterate :
    ℕ → List (EagenAccum E) → List (EagenAccum E)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else eagenBuild_iterate n (eagenBuild_level_step E xs)

/-- Top-level eagenBuild: from a list of input points (assumed sum-zero),
    produces the polynomial witness whose divisor is `Σ (P_i) - n·O`. -/
noncomputable def eagenBuild (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingElt E.q :=
  let level1 := eagenBuild_level0 E Ps
  let final := eagenBuild_iterate E Ps.length level1
  match final with
  | [] => { a := 1, b := 0 }
  | [single] => single.poly
  | _ => { a := 1, b := 0 }  -- shouldn't happen if iterations sufficient

/-! ## Future work

The skeleton above defines the construction; correctness proofs require:

* **Length-4 reduction**: prove `eagenBuild [P_0, P_1, P_2, P_3]` (assuming
  sum-zero + genericity) reduces to `eagenBuild_length4_explicit` (or an
  equivalent form). Bridge between the recursive definition and the
  explicit length-4 case.
* **Divisor equation by induction**: prove
  `divisorOfD E (eagenBuild Ps) R = Σ_i (R = P_i ? 1 : 0) - n·(R = ∞ ? 1 : 0)`
  for sum-zero `Ps`, by induction on the iteration depth.
* **Carry-forward correctness**: odd lengths.
* **Doubling/vertical branches**: at each level, when adjacent entries have
  the same x-coordinate, dispatch to tangent or vertical-chord handling.

These are deferred to subsequent firings. -/

end Divisor
