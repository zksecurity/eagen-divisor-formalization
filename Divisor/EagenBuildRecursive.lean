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
import Divisor.LogDerivEagenLength4
import Divisor.WeilReciprocityDescent

open Polynomial Finset Classical

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

/-- Build a level-1 accumulator from two points that are negatives of
    each other (`P = -Q`, so same x, opposite y, sum-zero in group law).
    The chord through `(P, -P)` is the vertical line `(X - x(P))`, which
    has divisor `(P) + (-P) - 2·O`. The "third intersection" is `O`;
    the new accumulator carries the vertical line as polynomial and `P`
    as point (sentinel — actual contribution is at infinity). -/
noncomputable def EagenAccum.fromChordPair_vertical
    (P Q : ZMod E.q × ZMod E.q) (_h_xx : P.1 = Q.1) (_h_yy : P.2 = -Q.2) :
    EagenAccum E :=
  { point := P,  -- Sentinel; level transitions handle this.
    poly := { a := Polynomial.X - Polynomial.C P.1, b := 0 } }

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
      else if hYY : P.2 = -Q.2 then
        -- Vertical chord case: P = -Q.
        EagenAccum.fromChordPair_vertical E P Q
          (Classical.byContradiction (fun h_neq => h h_neq)) hYY ::
          eagenBuild_level0 rest
      else
        -- Tangent doubling case (P = Q): deferred.
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

/-! ## General-k correctness: foundational definitions

Working definitions for the recursive correctness proof. See the
strategy outline below for how these are intended to be used. -/

/-- The "residue" divisor at the running sum point `S`: a single +1 at
    `-S` and a -1 at infinity. Tracks the dangling third-intersection
    contribution after absorbing some sublist of points. -/
noncomputable def residueDivisor (S : ECPoint E) : ECPoint E → ℤ :=
  fun R => (if R = -S then (1 : ℤ) else 0) - (if R = (0 : ECPoint E) then 1 else 0)

/-- The formal divisor of a list of affine points on E: each point
    contributes +1 (with multiplicity = list count), and `-|Ps|·O`
    appears at infinity. -/
noncomputable def formalDivisorOfList
    (Ps : List (ZMod E.q × ZMod E.q)) : ECPoint E → ℤ :=
  fun R =>
    match R with
    | WeierstrassCurve.Affine.Point.zero => -((Ps.length : ℤ))
    | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
        (Ps.filter (fun P => P = (x, y))).length

/-- `formalDivisorOfList` is additive on list concatenation. -/
theorem formalDivisorOfList_append
    (xs ys : List (ZMod E.q × ZMod E.q)) (R : ECPoint E) :
    formalDivisorOfList E (xs ++ ys) R
      = formalDivisorOfList E xs R + formalDivisorOfList E ys R := by
  classical
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    show -(((xs ++ ys).length : ℤ)) = -((xs.length : ℤ)) + -((ys.length : ℤ))
    rw [List.length_append]
    push_cast; ring
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
    show (((xs ++ ys).filter (fun P => P = (x, y))).length : ℤ)
        = ((xs.filter (fun P => P = (x, y))).length : ℤ)
          + ((ys.filter (fun P => P = (x, y))).length : ℤ)
    rw [List.filter_append, List.length_append]
    push_cast; ring

/-- Accumulator invariant: at the non-degenerate stage, `a.point ∈ E.points`
    and represents the EC group sum of the absorbed list `xs` (lifted via
    `affineOfMem`). The polynomial's divisor decomposes into the formal
    divisor of `xs` plus the residue at the running sum.

    This invariant fails when the running sum is `O` (terminal case);
    that case is handled separately via the vertical combine step. -/
def AccInv (xs : List (ZMod E.q × ZMod E.q)) (a : EagenAccum E) : Prop :=
  ∃ h : a.point ∈ E.points,
    -- a.point's ECPoint lift equals the running EC sum of xs.
    (ECPoint.affineOfMem E h : ECPoint E) =
      xs.foldr (fun P S =>
        if h' : P ∈ E.points then ECPoint.affineOfMem E h' + S else S) 0
    ∧ ∀ R : ECPoint E,
        divisorOfD E a.poly R
          = formalDivisorOfList E xs R
            + residueDivisor E (ECPoint.affineOfMem E h) R

/-! ### Level-0 chord case: running-sum claim

For (P, Q) chord case (distinct x), the level-0 accumulator's
`point` lifts via `affineOfMem` to the EC group sum `P + Q`. -/

theorem accInv_level0_chord_running_sum
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1) :
    ∃ h_acc : (EagenAccum.fromChordPair_distinct E P Q h_xx).point ∈ E.points,
      (ECPoint.affineOfMem E h_acc : ECPoint E)
        = ECPoint.affineOfMem E hP + ECPoint.affineOfMem E hQ := by
  classical
  set lam := slopeOf P.1 P.2 Q.1 Q.2
  set Q₀x := lam ^ 2 - P.1 - Q.1 with hQ₀x_def
  set Q₀y := lam * Q₀x + (P.2 - lam * P.1) with hQ₀y_def
  -- The accumulator's point is (Q_0x, -Q_0y).
  have h_acc_point : (EagenAccum.fromChordPair_distinct E P Q h_xx).point
                    = (Q₀x, -Q₀y) := rfl
  -- Third intersection (Q_0x, Q_0y) ∈ E.points.
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E P Q hP hQ h_xx
  -- (Q_0x, -Q_0y) ∈ E.points.
  have hNegThirdMem : (Q₀x, -Q₀y) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hThirdMem
    show (-Q₀y) ^ 2 = Q₀x ^ 3 + E.curveA * Q₀x + E.curveB
    rw [neg_pow_two]; exact hC
  refine ⟨h_acc_point ▸ hNegThirdMem, ?_⟩
  -- thirdPoint of (P, Q) = some (Q_0x, Q_0y).
  have hT : thirdPoint E P Q = some (Q₀x, Q₀y) := by
    unfold thirdPoint
    rw [if_neg h_xx]
    rfl
  -- thirdPoint_some_eq_neg_add: P + Q = -third.
  have hSum := thirdPoint_some_eq_neg_add (E := E) hP hQ hT
  rw [hSum]
  -- Goal: affineOfMem (h_acc_point ▸ hNegThirdMem) = -affineOfMem of third.
  -- Reduce both via affine_eq_affineOfMem to ECPoint.affine.
  rw [← ECPoint.affine_eq_affineOfMem E (h_acc_point ▸ hNegThirdMem)]
  rw [← ECPoint.affine_eq_affineOfMem E (third_point_on_curve E P Q hP hQ hT)]
  -- Goal: ECPoint.affine (acc.point.1, acc.point.2) = -ECPoint.affine (Q₀x, Q₀y).
  show (ECPoint.affine E (EagenAccum.fromChordPair_distinct E P Q h_xx).point.1
        (EagenAccum.fromChordPair_distinct E P Q h_xx).point.2 : ECPoint E)
      = -ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
  rw [h_acc_point]
  show (ECPoint.affine E Q₀x (-Q₀y) : ECPoint E)
      = -ECPoint.affine E Q₀x Q₀y
  rw [ECPoint.affine_neg E Q₀x Q₀y]

/-! ### Level-0 chord case: divisor identity at infinity

For chord case (P, Q): divisorOfD chord at ∞ = -3 = -2 + (-1)
                    = formalDivisor [P, Q] at ∞ + residue (P+Q) at ∞. -/

theorem accInv_level0_chord_divisor_identity_at_infinity
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    divisorOfD E (chordCoordRingElt E P Q) (0 : ECPoint E)
      = formalDivisorOfList E [P, Q] (0 : ECPoint E)
        + residueDivisor E (ECPoint.affineOfMem E h_acc) (0 : ECPoint E) := by
  classical
  intro h_acc
  -- divisorOfD chord at ∞ = -3.
  have h_chord_inf := divisorOfD_chordCoordRingElt_chord_distinct E P Q hP hQ h_xx
                        hP_neq_A2 hQ_neq_A2
  rw [h_chord_inf.2.2.2]
  -- formalDivisor [P, Q] at ∞ = -2.
  rw [show formalDivisorOfList E [P, Q] (0 : ECPoint E) = -2 from rfl]
  -- residue at ∞: -1 since running sum ≠ 0.
  -- Running sum = affineOfMem h_acc.
  have h_run := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose_spec
  -- h_run : affineOfMem h_acc = affineOfMem hP + affineOfMem hQ.
  have h_run_ne_zero : (ECPoint.affineOfMem E h_acc : ECPoint E) ≠ 0 := by
    -- affineOfMem unfolds to .some hns; .some ≠ 0.
    intro h_eq
    unfold ECPoint.affineOfMem ECPoint.affineOfEqn at h_eq
    cases h_eq
  -- Inline residueDivisor at infinity = -1.
  unfold residueDivisor
  rw [if_pos rfl]
  rw [if_neg]
  · norm_num
  · -- 0 = -running_sum iff running_sum = 0.
    intro h_eq
    apply h_run_ne_zero
    have : -(ECPoint.affineOfMem E h_acc : ECPoint E) = 0 := h_eq.symm
    have := neg_eq_zero.mp this
    exact this

/-! ### Level-0 chord divisor identity at off-support affine R

For (x, y) on E that is none of P, Q, A₂: divisor identity simplifies
to 0 = 0 + 0. -/

theorem accInv_level0_chord_divisor_identity_at_off_support
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_off_P : (x, y) ≠ P) (h_off_Q : (x, y) ≠ Q)
    (h_off_A2 : (x, y) ≠
      (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1,
       slopeOf P.1 P.2 Q.1 Q.2 *
         (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
       (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1))) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    divisorOfD E (chordCoordRingElt E P Q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, Q]
          (WeierstrassCurve.Affine.Point.some hns)
        + residueDivisor E (ECPoint.affineOfMem E h_acc)
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  intro h_acc
  have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
    (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
  have hMem : (x, y) ∈ E.points := E.hComplete x y hOC
  -- divisorOfD = 0 (off-support).
  have h_pw := divisorOfD_chordCoordRingElt_chord_pointwise E P Q hP hQ h_xx
                hP_neq_A2 hQ_neq_A2
  have h_div_zero := h_pw (x, y) hMem h_off_P h_off_Q h_off_A2
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_div_zero]
  -- formalDivisor [P, Q] at affine (x, y) = 0.
  rw [show formalDivisorOfList E [P, Q] (ECPoint.affine E x y) = 0 by
      unfold formalDivisorOfList
      rw [ECPoint.affine_of_nonsingular E hns]
      show ((List.filter (fun p => p = (x, y)) [P, Q]).length : ℤ) = 0
      have : List.filter (fun p => p = (x, y)) [P, Q] = [] := by
        simp only [List.filter, decide_eq_true_eq, decide_false,
                   decide_eq_true_eq]
        have h1 : ¬ P = (x, y) := fun h => h_off_P h.symm
        have h2 : ¬ Q = (x, y) := fun h => h_off_Q h.symm
        simp [h1, h2]
      rw [this]
      rfl]
  -- residue at affine (x, y) = 0.
  set Q₀x := slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1 with hQ₀x_def
  set Q₀y := slopeOf P.1 P.2 Q.1 Q.2 * Q₀x +
              (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) with hQ₀y_def
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E P Q hP hQ h_xx
  have h_neg_run : (-ECPoint.affineOfMem E h_acc : ECPoint E)
                = ECPoint.affineOfMem E hThirdMem := by
    rw [← ECPoint.affine_eq_affineOfMem E hThirdMem]
    rw [← ECPoint.affine_eq_affineOfMem E h_acc]
    show -ECPoint.affine E
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.1
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.2
        = ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
    show -ECPoint.affine E Q₀x (-Q₀y) = ECPoint.affine E Q₀x Q₀y
    rw [← ECPoint.affine_neg E Q₀x Q₀y, neg_neg]
  unfold residueDivisor
  -- Both `if`s evaluate to 0.
  -- (1) ECPoint.affine (x, y) ≠ -running_sum = affineOfMem hThirdMem = ECPoint.affine (Q_0x, Q_0y).
  -- (2) ECPoint.affine (x, y) ≠ 0.
  have h_ne_neg : (ECPoint.affine E x y : ECPoint E)
                 ≠ -ECPoint.affineOfMem E h_acc := by
    rw [h_neg_run, ← ECPoint.affine_eq_affineOfMem E hThirdMem]
    intro h
    have hns_third : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hThirdMem))
    rw [ECPoint.affine_of_nonsingular E hns,
        ECPoint.affine_of_nonsingular E hns_third] at h
    apply h_off_A2
    -- h : .some hns = .some hns_third → (x, y) = (Q_0x, Q_0y).
    have : x = Q₀x ∧ y = Q₀y := by
      have h_eq := WeierstrassCurve.Affine.Point.some.inj h
      exact ⟨h_eq.1, h_eq.2⟩
    exact Prod.ext this.1 this.2
  have h_ne_zero : (ECPoint.affine E x y : ECPoint E) ≠ 0 := by
    rw [ECPoint.affine_of_nonsingular E hns]
    intro h; cases h
  rw [if_neg h_ne_neg, if_neg h_ne_zero]
  push_cast

/-! ### Level-0 chord divisor identity at affine R = A₂

For R = .some hns_third (third intersection): divisor identity becomes
1 = 0 + 1 (chord = 1 at A₂, formal = 0 since A₂ ∉ [P, Q] by hP_neq_A2,
residue = 1 since A₂ = -running_sum). -/

theorem accInv_level0_chord_divisor_identity_at_A₂
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hns : E.toW.toAffine.Nonsingular
            (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
            (slopeOf P.1 P.2 Q.1 Q.2 *
              (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
            (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1))) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    divisorOfD E (chordCoordRingElt E P Q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, Q]
          (WeierstrassCurve.Affine.Point.some hns)
        + residueDivisor E (ECPoint.affineOfMem E h_acc)
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  intro h_acc
  set Q₀x := slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1 with hQ₀x_def
  set Q₀y := slopeOf P.1 P.2 Q.1 Q.2 * Q₀x +
              (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) with hQ₀y_def
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E P Q hP hQ h_xx
  -- divisorOfD = 1 at A₂.
  have h_chord := divisorOfD_chordCoordRingElt_chord_distinct E P Q hP hQ h_xx
                    hP_neq_A2 hQ_neq_A2
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E Q₀x Q₀y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_chord.2.2.1]
  -- formalDivisor at A₂ = 0 (A₂ ≠ P, A₂ ≠ Q).
  have hA₂_ne_P : (Q₀x, Q₀y) ≠ P := fun h => hP_neq_A2 (by rw [← h])
  have hA₂_ne_Q : (Q₀x, Q₀y) ≠ Q := fun h => hQ_neq_A2 (by rw [← h])
  rw [show formalDivisorOfList E [P, Q] (ECPoint.affine E Q₀x Q₀y) = 0 by
      unfold formalDivisorOfList
      rw [ECPoint.affine_of_nonsingular E hns]
      show ((List.filter (fun p => p = (Q₀x, Q₀y)) [P, Q]).length : ℤ) = 0
      have : List.filter (fun p => p = (Q₀x, Q₀y)) [P, Q] = [] := by
        have h1 : ¬ P = (Q₀x, Q₀y) := fun h => hA₂_ne_P h.symm
        have h2 : ¬ Q = (Q₀x, Q₀y) := fun h => hA₂_ne_Q h.symm
        simp [List.filter, h1, h2]
      rw [this]; rfl]
  -- residue at A₂ = 1: A₂ = -running_sum.
  have h_neg_run : (-ECPoint.affineOfMem E h_acc : ECPoint E)
                = ECPoint.affineOfMem E hThirdMem := by
    rw [← ECPoint.affine_eq_affineOfMem E hThirdMem]
    rw [← ECPoint.affine_eq_affineOfMem E h_acc]
    show -ECPoint.affine E
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.1
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.2
        = ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
    show -ECPoint.affine E Q₀x (-Q₀y) = ECPoint.affine E Q₀x Q₀y
    rw [← ECPoint.affine_neg E Q₀x Q₀y, neg_neg]
  have h_eq_neg : (ECPoint.affine E Q₀x Q₀y : ECPoint E)
                = -ECPoint.affineOfMem E h_acc := by
    rw [h_neg_run, ← ECPoint.affine_eq_affineOfMem E hThirdMem]
  have h_ne_zero : (ECPoint.affine E Q₀x Q₀y : ECPoint E) ≠ 0 := by
    rw [ECPoint.affine_of_nonsingular E hns]
    intro h; cases h
  unfold residueDivisor
  rw [if_pos h_eq_neg, if_neg h_ne_zero]
  push_cast

/-! ### Level-0 chord divisor identity at affine R = P -/

theorem accInv_level0_chord_divisor_identity_at_P
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hns : E.toW.toAffine.Nonsingular P.1 P.2) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    divisorOfD E (chordCoordRingElt E P Q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, Q]
          (WeierstrassCurve.Affine.Point.some hns)
        + residueDivisor E (ECPoint.affineOfMem E h_acc)
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  intro h_acc
  set Q₀x := slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1 with hQ₀x_def
  set Q₀y := slopeOf P.1 P.2 Q.1 Q.2 * Q₀x +
              (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) with hQ₀y_def
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E P Q hP hQ h_xx
  have h_chord := divisorOfD_chordCoordRingElt_chord_distinct E P Q hP hQ h_xx
                    hP_neq_A2 hQ_neq_A2
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E P.1 P.2 from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_chord.1]
  -- formalDivisor at .some P = 1 (P in [P, Q]).
  have hPQ_ne : P ≠ Q := fun h_eq => h_xx (by rw [h_eq])
  rw [show formalDivisorOfList E [P, Q] (ECPoint.affine E P.1 P.2) = 1 by
      unfold formalDivisorOfList
      rw [ECPoint.affine_of_nonsingular E hns]
      show ((List.filter (fun p => p = P) [P, Q]).length : ℤ) = 1
      have : List.filter (fun p => p = P) [P, Q] = [P] := by
        have h1 : (P = P) := rfl
        have h2 : ¬ Q = P := fun h => hPQ_ne h.symm
        simp [List.filter, h1, h2]
      rw [this]
      simp]
  -- residue at .some P = 0: P ≠ -running_sum (= A₂) and P ≠ 0.
  have h_neg_run : (-ECPoint.affineOfMem E h_acc : ECPoint E)
                = ECPoint.affineOfMem E hThirdMem := by
    rw [← ECPoint.affine_eq_affineOfMem E hThirdMem]
    rw [← ECPoint.affine_eq_affineOfMem E h_acc]
    show -ECPoint.affine E
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.1
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.2
        = ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
    show -ECPoint.affine E Q₀x (-Q₀y) = ECPoint.affine E Q₀x Q₀y
    rw [← ECPoint.affine_neg E Q₀x Q₀y, neg_neg]
  have h_ne_neg : (ECPoint.affine E P.1 P.2 : ECPoint E)
                 ≠ -ECPoint.affineOfMem E h_acc := by
    rw [h_neg_run, ← ECPoint.affine_eq_affineOfMem E hThirdMem]
    intro h
    have hns_third : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hThirdMem))
    rw [ECPoint.affine_of_nonsingular E hns,
        ECPoint.affine_of_nonsingular E hns_third] at h
    apply hP_neq_A2
    have h_eq := WeierstrassCurve.Affine.Point.some.inj h
    exact h_eq.1
  have h_ne_zero : (ECPoint.affine E P.1 P.2 : ECPoint E) ≠ 0 := by
    rw [ECPoint.affine_of_nonsingular E hns]
    intro h; cases h
  unfold residueDivisor
  rw [if_neg h_ne_neg, if_neg h_ne_zero]
  push_cast

/-! ### Level-0 chord divisor identity at affine R = Q -/

theorem accInv_level0_chord_divisor_identity_at_Q
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hns : E.toW.toAffine.Nonsingular Q.1 Q.2) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    divisorOfD E (chordCoordRingElt E P Q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, Q]
          (WeierstrassCurve.Affine.Point.some hns)
        + residueDivisor E (ECPoint.affineOfMem E h_acc)
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  intro h_acc
  set Q₀x := slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1 with hQ₀x_def
  set Q₀y := slopeOf P.1 P.2 Q.1 Q.2 * Q₀x +
              (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) with hQ₀y_def
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E P Q hP hQ h_xx
  have h_chord := divisorOfD_chordCoordRingElt_chord_distinct E P Q hP hQ h_xx
                    hP_neq_A2 hQ_neq_A2
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E Q.1 Q.2 from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_chord.2.1]
  have hPQ_ne : P ≠ Q := fun h_eq => h_xx (by rw [h_eq])
  rw [show formalDivisorOfList E [P, Q] (ECPoint.affine E Q.1 Q.2) = 1 by
      unfold formalDivisorOfList
      rw [ECPoint.affine_of_nonsingular E hns]
      show ((List.filter (fun p => p = Q) [P, Q]).length : ℤ) = 1
      have : List.filter (fun p => p = Q) [P, Q] = [Q] := by
        have h1 : ¬ P = Q := hPQ_ne
        have h2 : (Q = Q) := rfl
        simp [List.filter, h1, h2]
      rw [this]
      simp]
  have h_neg_run : (-ECPoint.affineOfMem E h_acc : ECPoint E)
                = ECPoint.affineOfMem E hThirdMem := by
    rw [← ECPoint.affine_eq_affineOfMem E hThirdMem]
    rw [← ECPoint.affine_eq_affineOfMem E h_acc]
    show -ECPoint.affine E
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.1
            (EagenAccum.fromChordPair_distinct E P Q h_xx).point.2
        = ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
    show -ECPoint.affine E Q₀x (-Q₀y) = ECPoint.affine E Q₀x Q₀y
    rw [← ECPoint.affine_neg E Q₀x Q₀y, neg_neg]
  have h_ne_neg : (ECPoint.affine E Q.1 Q.2 : ECPoint E)
                 ≠ -ECPoint.affineOfMem E h_acc := by
    rw [h_neg_run, ← ECPoint.affine_eq_affineOfMem E hThirdMem]
    intro h
    have hns_third : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hThirdMem))
    rw [ECPoint.affine_of_nonsingular E hns,
        ECPoint.affine_of_nonsingular E hns_third] at h
    apply hQ_neq_A2
    have h_eq := WeierstrassCurve.Affine.Point.some.inj h
    exact h_eq.1
  have h_ne_zero : (ECPoint.affine E Q.1 Q.2 : ECPoint E) ≠ 0 := by
    rw [ECPoint.affine_of_nonsingular E hns]
    intro h; cases h
  unfold residueDivisor
  rw [if_neg h_ne_neg, if_neg h_ne_zero]
  push_cast

/-! ### Level-0 chord case: full divisor identity ∀ R

Combines infinity + at_P + at_Q + at_A₂ + off-support cases. -/

theorem accInv_level0_chord_divisor_identity
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) :
    let h_acc := (accInv_level0_chord_running_sum E P Q hP hQ h_xx).choose
    ∀ R : ECPoint E,
      divisorOfD E (chordCoordRingElt E P Q) R
        = formalDivisorOfList E [P, Q] R
          + residueDivisor E (ECPoint.affineOfMem E h_acc) R := by
  classical
  intro h_acc R
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    exact accInv_level0_chord_divisor_identity_at_infinity E P Q hP hQ h_xx
            hP_neq_A2 hQ_neq_A2
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
    -- Case-split: (x, y) = P, Q, A₂, or off-support.
    by_cases h_eqP : (x, y) = P
    · -- Use h_eqP to swap (x, y) ↔ P inside hns.
      have hP_eq : P = (x, y) := h_eqP.symm
      have hns_P : E.toW.toAffine.Nonsingular P.1 P.2 := by
        rw [hP_eq]; exact hns
      have h_eq : (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                = WeierstrassCurve.Affine.Point.some hns_P := by
        rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
              = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
        rw [show (WeierstrassCurve.Affine.Point.some hns_P : ECPoint E)
              = ECPoint.affine E P.1 P.2 from (ECPoint.affine_of_nonsingular E hns_P).symm]
        congr 1 <;> rw [← h_eqP]
      rw [h_eq]
      exact accInv_level0_chord_divisor_identity_at_P E P Q hP hQ h_xx
              hP_neq_A2 hQ_neq_A2 hns_P
    · by_cases h_eqQ : (x, y) = Q
      · have hQ_eq : Q = (x, y) := h_eqQ.symm
        have hns_Q : E.toW.toAffine.Nonsingular Q.1 Q.2 := by
          rw [hQ_eq]; exact hns
        have h_eq : (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                  = WeierstrassCurve.Affine.Point.some hns_Q := by
          rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
          rw [show (WeierstrassCurve.Affine.Point.some hns_Q : ECPoint E)
                = ECPoint.affine E Q.1 Q.2 from (ECPoint.affine_of_nonsingular E hns_Q).symm]
          congr 1 <;> rw [← h_eqQ]
        rw [h_eq]
        exact accInv_level0_chord_divisor_identity_at_Q E P Q hP hQ h_xx
                hP_neq_A2 hQ_neq_A2 hns_Q
      · by_cases h_eqA₂ : (x, y) = (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1,
                            slopeOf P.1 P.2 Q.1 Q.2 *
                              (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
                            (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1))
        · have hThird_eq : (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1,
                            slopeOf P.1 P.2 Q.1 Q.2 *
                              (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
                            (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1)) = (x, y) := h_eqA₂.symm
          have hx_eq : x = (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) := by
            have h := h_eqA₂
            have : (x, y).1 = _ := congrArg Prod.fst h
            exact this
          have hy_eq : y = slopeOf P.1 P.2 Q.1 Q.2 *
                            (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
                          (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1) := by
            have h := h_eqA₂
            have : (x, y).2 = _ := congrArg Prod.snd h
            exact this
          have hns_third : E.toW.toAffine.Nonsingular
              (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
              (slopeOf P.1 P.2 Q.1 Q.2 *
                (slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) +
              (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1)) := by
            convert hns using 2 <;> [rw [hx_eq]; rw [hy_eq]]
          have h_eq : (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                    = WeierstrassCurve.Affine.Point.some hns_third := by
            rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                  = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
            rw [show (WeierstrassCurve.Affine.Point.some hns_third : ECPoint E)
                  = ECPoint.affine E _ _ from (ECPoint.affine_of_nonsingular E hns_third).symm]
            rw [hx_eq, hy_eq]
          rw [h_eq]
          exact accInv_level0_chord_divisor_identity_at_A₂ E P Q hP hQ h_xx
                  hP_neq_A2 hQ_neq_A2 hns_third
        · exact accInv_level0_chord_divisor_identity_at_off_support E P Q hP hQ h_xx
                  hP_neq_A2 hQ_neq_A2 hns h_eqP h_eqQ h_eqA₂

/-! ### Level-0 chord case: full AccInv

Combines running-sum claim + universal divisor identity into the full
AccInv invariant. -/

theorem accInv_level0_chord_case
    (P Q : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1)
    (hP_neq_A2 : P.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1)
    (hQ_neq_A2 : Q.1 ≠ slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1) :
    AccInv E [P, Q] (EagenAccum.fromChordPair_distinct E P Q h_xx) := by
  classical
  unfold AccInv
  have h_run := accInv_level0_chord_running_sum E P Q hP hQ h_xx
  refine ⟨h_run.choose, ?_, ?_⟩
  · -- Running-sum claim.
    have h_sum := h_run.choose_spec
    show (ECPoint.affineOfMem E h_run.choose : ECPoint E) =
      [P, Q].foldr (fun P S =>
        if h' : P ∈ E.points then ECPoint.affineOfMem E h' + S else S) 0
    rw [h_sum]
    simp only [List.foldr, dif_pos hP, dif_pos hQ, add_zero]
  · -- Divisor identity ∀ R.
    have h_chord := chordCoordRingElt_ne_zero E P Q
    -- The accumulator's poly is chordCoordRingElt P Q.
    show ∀ R : ECPoint E,
      divisorOfD E (EagenAccum.fromChordPair_distinct E P Q h_xx).poly R
        = formalDivisorOfList E [P, Q] R
          + residueDivisor E (ECPoint.affineOfMem E h_run.choose) R
    show ∀ R : ECPoint E,
      divisorOfD E (chordCoordRingElt E P Q) R
        = formalDivisorOfList E [P, Q] R
          + residueDivisor E (ECPoint.affineOfMem E h_run.choose) R
    exact accInv_level0_chord_divisor_identity E P Q hP hQ h_xx hP_neq_A2 hQ_neq_A2

/-! ### Terminal invariant: sum-zero accumulators

When the running sum is `O` (e.g., after combining `(P, -P)` or any
sum-zero block), AccInv fails because `a.point` cannot represent the
identity. The terminal invariant captures this case directly: the
polynomial's divisor matches the formal divisor of the absorbed list
(no residue needed, since residue at `O` would cancel). -/

def TerminalInv (xs : List (ZMod E.q × ZMod E.q)) (a : EagenAccum E) : Prop :=
  ∀ R : ECPoint E,
    divisorOfD E a.poly R = formalDivisorOfList E xs R

/-! ### Level-0 vertical case helpers -/

/-- For (P, -P) input, the vertical line's divisor at infinity matches
    formalDivisor [P, -P] at infinity (both = -2). -/
theorem terminalInv_vertical_at_infinity
    (P : ZMod E.q × ZMod E.q) (h_xx : P.1 = (P.1, -P.2).1)
    (h_yy : P.2 = -((P.1, -P.2).2)) :
    divisorOfD E
        ((EagenAccum.fromChordPair_vertical E P (P.1, -P.2) h_xx h_yy).poly)
        (0 : ECPoint E)
      = formalDivisorOfList E [P, (P.1, -P.2)] (0 : ECPoint E) := by
  show divisorOfD E ({ a := Polynomial.X - Polynomial.C P.1, b := 0 }
                    : CoordRingElt E.q) (0 : ECPoint E)
      = formalDivisorOfList E [P, (P.1, -P.2)] (0 : ECPoint E)
  rw [divisorOfD_vertical_at_infinity_eq_neg_two]
  rfl

/-- For (P, -P) vertical case, divisor identity holds at affine R with
    x ≠ P.1 (off-support): both = 0. -/
theorem terminalInv_vertical_at_off_x₀
    (P : ZMod E.q × ZMod E.q) (h_xx : P.1 = (P.1, -P.2).1)
    (h_yy : P.2 = -((P.1, -P.2).2))
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_off : x ≠ P.1) :
    divisorOfD E
        ((EagenAccum.fromChordPair_vertical E P (P.1, -P.2) h_xx h_yy).poly)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
    (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
  have hMem : (x, y) ∈ E.points := E.hComplete x y hOC
  show divisorOfD E ({ a := Polynomial.X - Polynomial.C P.1, b := 0 }
                    : CoordRingElt E.q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns)
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [divisorOfD_vertical_at_off_x₀_affine E P.1 hMem h_off]
  unfold formalDivisorOfList
  rw [ECPoint.affine_of_nonsingular E hns]
  show (0 : ℤ) = ((List.filter (fun p => p = (x, y)) [P, (P.1, -P.2)]).length : ℤ)
  have h_filter : List.filter (fun p => p = (x, y)) [P, (P.1, -P.2)] = [] := by
    have h1 : ¬ P = (x, y) := by
      intro h
      have : P.1 = (x, y).1 := congrArg Prod.fst h
      exact h_off this.symm
    have h2 : ¬ (P.1, -P.2) = (x, y) := by
      intro h
      have : (P.1, -P.2).1 = (x, y).1 := congrArg Prod.fst h
      exact h_off this.symm
    simp [List.filter, h1, h2]
  rw [h_filter]; simp

/-- For (P, -P) vertical case (P non-2-torsion), divisor identity holds
    at affine R = .some hns_P. -/
theorem terminalInv_vertical_at_P
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (h_xx : P.1 = (P.1, -P.2).1) (h_yy : P.2 = -((P.1, -P.2).2))
    (hns : E.toW.toAffine.Nonsingular P.1 P.2) :
    divisorOfD E
        ((EagenAccum.fromChordPair_vertical E P (P.1, -P.2) h_xx h_yy).poly)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  show divisorOfD E ({ a := Polynomial.X - Polynomial.C P.1, b := 0 }
                    : CoordRingElt E.q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns)
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E P.1 P.2 from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [divisorOfD_vertical_at_x₀_nonTwoTorsion_affine E P.1 P.2 hP hY]
  unfold formalDivisorOfList
  rw [ECPoint.affine_of_nonsingular E hns]
  have h_negP_ne_P : (P.1, -P.2) ≠ P := by
    intro h
    have h_neg_eq : -P.2 = P.2 := congrArg Prod.snd h
    have h_2y : 2 * P.2 = 0 := by linear_combination -h_neg_eq
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    have hP2_zero : P.2 = 0 := by
      rcases mul_eq_zero.mp h_2y with h | h
      · exact absurd h h2
      · exact h
    exact hY hP2_zero
  show (1 : ℤ) = ((List.filter (fun p => p = (P.1, P.2)) [P, (P.1, -P.2)]).length : ℤ)
  rw [show ((List.filter (fun p => p = (P.1, P.2)) [P, (P.1, -P.2)]).length : ℤ) = 1 by
      rw [show [P, (P.1, -P.2)] = P :: [(P.1, -P.2)] from rfl]
      rw [List.filter_cons]
      rw [show decide (P = (P.1, P.2)) = true by simp]
      simp only [if_true]
      rw [List.filter_cons]
      rw [show decide ((P.1, -P.2) = (P.1, P.2)) = false from by
          rw [decide_eq_false_iff_not]; exact h_negP_ne_P]
      simp]

/-- For (P, -P) vertical case (P non-2-torsion), divisor identity holds
    at affine R = .some hns_(-P). -/
theorem terminalInv_vertical_at_negP
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (h_xx : P.1 = (P.1, -P.2).1) (h_yy : P.2 = -((P.1, -P.2).2))
    (hns : E.toW.toAffine.Nonsingular P.1 (-P.2)) :
    divisorOfD E
        ((EagenAccum.fromChordPair_vertical E P (P.1, -P.2) h_xx h_yy).poly)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  -- (P.1, -P.2) ∈ E.points.
  have hNegP : (P.1, -P.2) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hP
    show (-P.2) ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB
    rw [neg_pow_two]; exact hC
  show divisorOfD E ({ a := Polynomial.X - Polynomial.C P.1, b := 0 }
                    : CoordRingElt E.q)
        (WeierstrassCurve.Affine.Point.some hns)
      = formalDivisorOfList E [P, (P.1, -P.2)]
          (WeierstrassCurve.Affine.Point.some hns)
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E P.1 (-P.2) from (ECPoint.affine_of_nonsingular E hns).symm]
  have hY_neg : -P.2 ≠ 0 := neg_ne_zero.mpr hY
  rw [divisorOfD_vertical_at_x₀_nonTwoTorsion_affine E P.1 (-P.2) hNegP hY_neg]
  unfold formalDivisorOfList
  rw [ECPoint.affine_of_nonsingular E hns]
  have h_P_ne_negP : P ≠ (P.1, -P.2) := by
    intro h
    have h_neg_eq : P.2 = -P.2 := congrArg Prod.snd h
    have h_2y : 2 * P.2 = 0 := by linear_combination h_neg_eq
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    have hP2_zero : P.2 = 0 := by
      rcases mul_eq_zero.mp h_2y with h | h
      · exact absurd h h2
      · exact h
    exact hY hP2_zero
  show (1 : ℤ) = ((List.filter (fun p => p = (P.1, -P.2)) [P, (P.1, -P.2)]).length : ℤ)
  rw [show ((List.filter (fun p => p = (P.1, -P.2)) [P, (P.1, -P.2)]).length : ℤ) = 1 by
      rw [show [P, (P.1, -P.2)] = P :: [(P.1, -P.2)] from rfl]
      rw [List.filter_cons]
      rw [show decide (P = (P.1, -P.2)) = false from by
          rw [decide_eq_false_iff_not]; exact h_P_ne_negP]
      rw [List.filter_cons]
      rw [show decide ((P.1, -P.2) = (P.1, -P.2)) = true by simp]
      simp]

/-! ### Full TerminalInv for level-0 vertical case -/

theorem terminalInv_level0_vertical_case
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (h_xx : P.1 = (P.1, -P.2).1) (h_yy : P.2 = -((P.1, -P.2).2)) :
    TerminalInv E [P, (P.1, -P.2)]
      (EagenAccum.fromChordPair_vertical E P (P.1, -P.2) h_xx h_yy) := by
  classical
  unfold TerminalInv
  intro R
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    exact terminalInv_vertical_at_infinity E P h_xx h_yy
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
    by_cases hxx_eq : x = P.1
    · -- x = P.1: derive y = P.2 or y = -P.2.
      have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
        (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
      have hP_OC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
      have hy_sq : y ^ 2 = P.2 ^ 2 := by rw [hOC, hxx_eq]; exact hP_OC.symm
      have hy_factor : (y - P.2) * (y + P.2) = 0 := by linear_combination hy_sq
      rcases mul_eq_zero.mp hy_factor with hy_eq_P | hy_eq_negP
      · -- y = P.2.
        have hy : y = P.2 := sub_eq_zero.mp hy_eq_P
        have hns_P : E.toW.toAffine.Nonsingular P.1 P.2 := by rw [← hxx_eq, ← hy]; exact hns
        have h_eq : (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                  = WeierstrassCurve.Affine.Point.some hns_P := by
          rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
          rw [show (WeierstrassCurve.Affine.Point.some hns_P : ECPoint E)
                = ECPoint.affine E P.1 P.2 from (ECPoint.affine_of_nonsingular E hns_P).symm]
          rw [hxx_eq, hy]
        rw [h_eq]
        exact terminalInv_vertical_at_P E P hP hY h_xx h_yy hns_P
      · -- y = -P.2.
        have hy : y = -P.2 := add_eq_zero_iff_eq_neg.mp hy_eq_negP
        have hns_negP : E.toW.toAffine.Nonsingular P.1 (-P.2) := by
          rw [← hxx_eq, ← hy]; exact hns
        have h_eq : (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                  = WeierstrassCurve.Affine.Point.some hns_negP := by
          rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
                = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
          rw [show (WeierstrassCurve.Affine.Point.some hns_negP : ECPoint E)
                = ECPoint.affine E P.1 (-P.2) from (ECPoint.affine_of_nonsingular E hns_negP).symm]
          rw [hxx_eq, hy]
        rw [h_eq]
        exact terminalInv_vertical_at_negP E P hP hY h_xx h_yy hns_negP
    · -- x ≠ P.1.
      exact terminalInv_vertical_at_off_x₀ E P h_xx h_yy hns hxx_eq

/-! ### Helper lemmas for residue and formalDivisor -/

/-- residueDivisor evaluated at `-S` is `1` (when -S ≠ 0). -/
theorem residueDivisor_at_neg_self
    (S : ECPoint E) (h_neg_ne_zero : (-S : ECPoint E) ≠ 0) :
    residueDivisor E S (-S) = 1 := by
  unfold residueDivisor
  rw [if_pos rfl]
  rw [if_neg h_neg_ne_zero]
  ring

/-- residueDivisor at any R that is neither `-S` nor `0` is zero. -/
theorem residueDivisor_at_other
    (S R : ECPoint E) (h_ne_neg : R ≠ -S) (h_ne_zero : R ≠ 0) :
    residueDivisor E S R = 0 := by
  unfold residueDivisor
  rw [if_neg h_ne_neg, if_neg h_ne_zero]
  ring

/-- formalDivisorOfList at infinity = -(list length). -/
theorem formalDivisorOfList_at_infinity (Ps : List (ZMod E.q × ZMod E.q)) :
    formalDivisorOfList E Ps (0 : ECPoint E) = -((Ps.length : ℤ)) := rfl

/-- Sanity check: residueDivisor at infinity is -1 when S ≠ 0. -/
theorem residueDivisor_at_infinity_of_S_ne_zero
    (S : ECPoint E) (hS : S ≠ 0) :
    residueDivisor E S (0 : ECPoint E) = -1 := by
  unfold residueDivisor
  rw [if_pos rfl]
  rw [if_neg]
  · simp
  · -- 0 = -S iff S = 0 (group). But hS says S ≠ 0.
    intro h_eq
    apply hS
    have : -S = 0 := h_eq.symm
    have : S = -(0 : ECPoint E) := by rw [← this]; abel
    rw [this]; abel

/-! ## Sanity check: length-2 sum-zero base case

For input `[P, -P]` (the simplest sum-zero case), `eagenBuild` produces
the vertical line `(X - x(P))`, whose divisor is `(P) + (-P) - 2·O`. -/

theorem eagenBuild_length2_neg_eq_vertical
    (P : ZMod E.q × ZMod E.q) (hY : P.2 ≠ 0) :
    eagenBuild E [P, (P.1, -P.2)]
      = ({ a := Polynomial.X - Polynomial.C P.1, b := 0 } : CoordRingElt E.q) := by
  unfold eagenBuild eagenBuild_level0
  simp only [List.map]
  -- The pattern matches `P :: Q :: rest` with rest = [].
  -- The condition `P.1 ≠ (P.1, -P.2).1 = P.1` is false.
  have h_xx : ¬ (P.1 ≠ (P.1, -P.2).1) := fun h => h rfl
  have h_yy : P.2 = -((P.1, -P.2).2) := by simp
  -- Level 0 gives a single vertical accumulator; iteration is trivial.
  simp only [eagenBuild_level0, dif_neg h_xx, dif_pos h_yy,
    EagenAccum.fromChordPair_vertical]
  unfold eagenBuild_iterate
  simp

/-! ### divLin divisor identity

When `(X - x₀)` divides both `D.a` and `D.b`, the divisor of `D.divLin x₀`
is the divisor of `D` minus the vertical line's divisor at `x₀`. -/

theorem divisorOfD_divLin_subtract
    (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (ha : (Polynomial.X - Polynomial.C x₀) ∣ D.a)
    (hb : (Polynomial.X - Polynomial.C x₀) ∣ D.b)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) (R : ECPoint E) :
    divisorOfD E (D.divLin x₀) R
      = divisorOfD E D R
        - divisorOfD E ({ a := Polynomial.X - Polynomial.C x₀, b := 0 }
                        : CoordRingElt E.q) R := by
  -- D = (D.divLin x₀) · L_v.
  have h_recomp := mulCoordRingElt_divLin_vertical_recompose E D x₀ ha hb
  -- Need: D.divLin x₀ is also nonzero (a or b nonzero).
  have h_divLin_NZ : ¬ ((D.divLin x₀).a = 0 ∧ (D.divLin x₀).b = 0) :=
    divLin_not_both_zero E D hD
      (Polynomial.dvd_iff_isRoot.mp ha)
      (Polynomial.dvd_iff_isRoot.mp hb)
  -- divisorOfD (D.divLin · L_v) R = divisorOfD (D.divLin) R + divisorOfD L_v R.
  have h_split := divisorOfD_mul_vertical_add E (D.divLin x₀) h_divLin_NZ x₀ R
  -- D = D.divLin · L_v, so divisorOfD D R = divisorOfD (D.divLin · L_v) R.
  have hDD : divisorOfD E D R
           = divisorOfD E (mulCoordRingElt E (D.divLin x₀)
              ({ a := Polynomial.X - Polynomial.C x₀, b := 0 } : CoordRingElt E.q)) R :=
    congrArg (fun X => divisorOfD E X R) h_recomp
  have h_eq : divisorOfD E D R
            = divisorOfD E (D.divLin x₀) R
              + divisorOfD E ({ a := Polynomial.X - Polynomial.C x₀, b := 0 }
                              : CoordRingElt E.q) R := hDD.trans h_split
  linarith

/-! ### AccInv consequence: a.poly vanishes at -a.point

Under `AccInv xs a`, the polynomial `a.poly` vanishes (eval = 0) at the
sheet `(a.point.x, -a.point.y)`. This is because the residue contribution
at -a.point makes the ordAt there positive. -/

theorem accInv_poly_vanishes_at_neg_point
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h_acc : AccInv E xs a) (h_negPt_mem : (a.point.1, -a.point.2) ∈ E.points)
    (hY : a.point.2 ≠ 0)
    (h_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0)) :
    a.poly.eval a.point.1 (-a.point.2) = 0 := by
  classical
  obtain ⟨h_pt_mem, _h_run, h_div⟩ := h_acc
  -- Apply h_div at -a.point lifted to ECPoint.
  have hns_neg : E.toW.toAffine.Nonsingular a.point.1 (-a.point.2) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_negPt_mem))
  have h_div_at := h_div (WeierstrassCurve.Affine.Point.some hns_neg)
  -- divisorOfD a.poly at .some hns_neg = ordAt a.poly (a.point.1, -a.point.2) (cast).
  rw [show (WeierstrassCurve.Affine.Point.some hns_neg : ECPoint E)
        = ECPoint.affine E a.point.1 (-a.point.2) from
      (ECPoint.affine_of_nonsingular E hns_neg).symm] at h_div_at
  rw [show divisorOfD E a.poly (ECPoint.affine E a.point.1 (-a.point.2))
        = (ordAt E a.poly (a.point.1, -a.point.2) : ℤ) from by
      rw [ECPoint.affine_of_nonsingular E hns_neg]; rfl] at h_div_at
  -- The RHS at -a.point includes residue = 1.
  have h_residue_at_neg : residueDivisor E (ECPoint.affineOfMem E h_pt_mem)
      (ECPoint.affine E a.point.1 (-a.point.2)) = 1 := by
    unfold residueDivisor
    rw [if_pos, if_neg]
    · ring
    · -- ECPoint.affine E a.point.1 (-a.point.2) ≠ 0.
      rw [ECPoint.affine_of_nonsingular E hns_neg]
      intro h; cases h
    · -- ECPoint.affine E a.point.1 (-a.point.2) = -ECPoint.affineOfMem E h_pt_mem.
      rw [← ECPoint.affine_eq_affineOfMem E h_pt_mem]
      have hns_pt : E.toW.toAffine.Nonsingular a.point.1 a.point.2 :=
        E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_pt_mem))
      rw [ECPoint.affine_of_nonsingular E hns_neg,
          ECPoint.affine_of_nonsingular E hns_pt]
      -- -.some hns_pt = .some (negated witness) with x same, y negated.
      rw [show -((WeierstrassCurve.Affine.Point.some hns_pt) : ECPoint E)
            = ECPoint.affine E a.point.1 (-a.point.2) from by
          rw [show -((WeierstrassCurve.Affine.Point.some hns_pt) : ECPoint E)
                = ECPoint.affine E a.point.1 (-a.point.2) from by
              rw [show ((WeierstrassCurve.Affine.Point.some hns_pt) : ECPoint E)
                    = ECPoint.affine E a.point.1 a.point.2 from
                  (ECPoint.affine_of_nonsingular E hns_pt).symm]
              rw [ECPoint.affine_neg E a.point.1 a.point.2]]]
      rw [ECPoint.affine_of_nonsingular E hns_neg]
  -- formalDivisorOfList xs at -a.point ≥ 0 (since it's a count).
  have h_formal_at_neg :
      formalDivisorOfList E xs (ECPoint.affine E a.point.1 (-a.point.2)) ≥ 0 := by
    rw [ECPoint.affine_of_nonsingular E hns_neg]
    unfold formalDivisorOfList
    show ((List.filter (fun p => p = (a.point.1, -a.point.2)) xs).length : ℤ) ≥ 0
    exact Int.natCast_nonneg _
  -- So ordAt > 0.
  have h_ord_pos : 0 < ordAt E a.poly (a.point.1, -a.point.2) := by
    have h_eq : (ordAt E a.poly (a.point.1, -a.point.2) : ℤ)
              = formalDivisorOfList E xs (ECPoint.affine E a.point.1 (-a.point.2))
                + residueDivisor E (ECPoint.affineOfMem E h_pt_mem)
                  (ECPoint.affine E a.point.1 (-a.point.2)) := h_div_at
    rw [h_residue_at_neg] at h_eq
    have : (ordAt E a.poly (a.point.1, -a.point.2) : ℤ) ≥ 1 := by linarith
    exact_mod_cast this
  -- Apply ordAt_pos_iff_zero.
  exact (ordAt_pos_iff_zero E a.poly h_poly_NZ (a.point.1, -a.point.2) h_negPt_mem).mp h_ord_pos

/-! ### Combine step divisibility: (X - a.point.x) divides product

For combine_higher_distinct, the product `chord_ab · a.poly · b.poly`
vanishes on the full fiber at `a.point.x`:
- `chord_ab` vanishes at sheet (a.x, a.y) (a.point is on chord_ab).
- `a.poly` vanishes at sheet (a.x, -a.y) (via AccInv residue).

Hence `(X - a.point.x)` divides both `.a` and `.b` of the product, so
`divLin a.point.x` gives a proper polynomial reduction. -/

theorem combine_higher_distinct_divisible_at_a
    {xs : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    let chord := chordCoordRingElt E a.point b.point
    let prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
    prod.a.eval a.point.1 = 0 ∧ prod.b.eval a.point.1 = 0 := by
  classical
  intro chord prod
  have h_pt_mem : a.point ∈ E.points := h_acc_a.1
  -- Negation point (a.x, -a.y) ∈ E.points.
  have h_neg_mem : (a.point.1, -a.point.2) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ h_pt_mem
    show (-a.point.2) ^ 2 = a.point.1 ^ 3 + E.curveA * a.point.1 + E.curveB
    rw [neg_pow_two]; exact hC
  -- chord_ab evaluates to 0 at a.point.
  have h_chord_at_a : chord.eval a.point.1 a.point.2 = 0 :=
    chordCoordRingElt_eval_left E a.point b.point
  -- a.poly evaluates to 0 at -a.point (AccInv consequence).
  have h_aPoly_at_negA : a.poly.eval a.point.1 (-a.point.2) = 0 :=
    accInv_poly_vanishes_at_neg_point E h_acc_a h_neg_mem hY_a h_a_poly_NZ
  -- (chord · a.poly · b.poly) vanishes at both sheets of x = a.point.1.
  have h_prod_at_a : prod.eval a.point.1 a.point.2 = 0 := by
    rw [show prod = mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly from rfl]
    rw [mulCoordRingElt_eval_on_E E _ b.poly h_pt_mem]
    rw [mulCoordRingElt_eval_on_E E chord a.poly h_pt_mem]
    rw [h_chord_at_a, zero_mul, zero_mul]
  have h_prod_at_negA : prod.eval a.point.1 (-a.point.2) = 0 := by
    rw [show prod = mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly from rfl]
    rw [mulCoordRingElt_eval_on_E E _ b.poly h_neg_mem]
    rw [mulCoordRingElt_eval_on_E E chord a.poly h_neg_mem]
    rw [h_aPoly_at_negA, mul_zero, zero_mul]
  -- Apply Da_Db_eval_zero_of_both_sheets_zero.
  exact Da_Db_eval_zero_of_both_sheets_zero E prod hY_a h_prod_at_a h_prod_at_negA

/-! ### Combine step divisibility at b after divLin a

After `divLin a.point.1`, the resulting `after_div_a` evaluated at `b.point.1`
in both `.a` and `.b` is zero. This follows because the original product
vanishes on the b-fiber (chord vanishes at (b.x,b.y), b.poly vanishes at
(b.x,-b.y) via AccInv on b), and `b.point.1 ≠ a.point.1` lets us push the
vanishing through divLin's quotient. -/

theorem combine_higher_distinct_prod_vanish_at_b
    {ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_b : AccInv E ys b)
    (hY_b : b.point.2 ≠ 0)
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    let chord := chordCoordRingElt E a.point b.point
    let prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
    prod.a.eval b.point.1 = 0 ∧ prod.b.eval b.point.1 = 0 := by
  classical
  intro chord prod
  have h_pt_mem : b.point ∈ E.points := h_acc_b.1
  have h_neg_mem : (b.point.1, -b.point.2) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ h_pt_mem
    show (-b.point.2) ^ 2 = b.point.1 ^ 3 + E.curveA * b.point.1 + E.curveB
    rw [neg_pow_two]; exact hC
  -- chord vanishes at b.point.
  have h_chord_at_b : chord.eval b.point.1 b.point.2 = 0 :=
    chordCoordRingElt_eval_right E a.point b.point
  -- b.poly vanishes at -b.point.
  have h_bPoly_at_negB : b.poly.eval b.point.1 (-b.point.2) = 0 :=
    accInv_poly_vanishes_at_neg_point E h_acc_b h_neg_mem hY_b h_b_poly_NZ
  -- Product vanishes at sheet (b.x, b.y).
  have h_prod_at_b : prod.eval b.point.1 b.point.2 = 0 := by
    rw [show prod = mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly from rfl]
    rw [mulCoordRingElt_eval_on_E E _ b.poly h_pt_mem]
    rw [mulCoordRingElt_eval_on_E E chord a.poly h_pt_mem]
    rw [h_chord_at_b, zero_mul, zero_mul]
  -- Product vanishes at sheet (b.x, -b.y).
  have h_prod_at_negB : prod.eval b.point.1 (-b.point.2) = 0 := by
    rw [show prod = mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly from rfl]
    rw [mulCoordRingElt_eval_on_E E _ b.poly h_neg_mem]
    rw [h_bPoly_at_negB, mul_zero]
  exact Da_Db_eval_zero_of_both_sheets_zero E prod hY_b h_prod_at_b h_prod_at_negB

theorem combine_higher_distinct_divisible_at_b
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    let chord := chordCoordRingElt E a.point b.point
    let prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
    let after_div_a := prod.divLin a.point.1
    after_div_a.a.eval b.point.1 = 0 ∧ after_div_a.b.eval b.point.1 = 0 := by
  classical
  intro chord prod after_div_a
  -- Step 1: prod.a, prod.b both vanish at a.point.1 (combine_higher_distinct_divisible_at_a).
  have h_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_pa_at_a : prod.a.eval a.point.1 = 0 := h_at_a.1
  have h_pb_at_a : prod.b.eval a.point.1 = 0 := h_at_a.2
  -- Step 2: write prod.a = (X - C a.x) * after_div_a.a and similarly for .b.
  have h_pa_root : prod.a.IsRoot a.point.1 := h_pa_at_a
  have h_pb_root : prod.b.IsRoot a.point.1 := h_pb_at_a
  have h_pa_factored :
      (Polynomial.X - Polynomial.C a.point.1) * after_div_a.a = prod.a := by
    show (Polynomial.X - Polynomial.C a.point.1)
        * (prod.a /ₘ (Polynomial.X - Polynomial.C a.point.1)) = prod.a
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_pa_root
  have h_pb_factored :
      (Polynomial.X - Polynomial.C a.point.1) * after_div_a.b = prod.b := by
    show (Polynomial.X - Polynomial.C a.point.1)
        * (prod.b /ₘ (Polynomial.X - Polynomial.C a.point.1)) = prod.b
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_pb_root
  -- Step 3: prod.a, prod.b vanish at b.point.1.
  have h_at_b := combine_higher_distinct_prod_vanish_at_b (E := E) (a := a)
    h_acc_b hY_b h_b_poly_NZ
  have h_pa_at_b : prod.a.eval b.point.1 = 0 := h_at_b.1
  have h_pb_at_b : prod.b.eval b.point.1 = 0 := h_at_b.2
  -- Step 4: extract after_div_a.{a,b}.eval b.point.1 = 0.
  have h_factor_ne : b.point.1 - a.point.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h_xx)
  refine ⟨?_, ?_⟩
  · have heval : ((Polynomial.X - Polynomial.C a.point.1) * after_div_a.a).eval b.point.1
                = (b.point.1 - a.point.1) * after_div_a.a.eval b.point.1 := by
      simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [h_pa_factored] at heval
    rw [h_pa_at_b] at heval
    have : (b.point.1 - a.point.1) * after_div_a.a.eval b.point.1 = 0 := heval.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h_factor_ne
    · exact h
  · have heval : ((Polynomial.X - Polynomial.C a.point.1) * after_div_a.b).eval b.point.1
                = (b.point.1 - a.point.1) * after_div_a.b.eval b.point.1 := by
      simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [h_pb_factored] at heval
    rw [h_pb_at_b] at heval
    have : (b.point.1 - a.point.1) * after_div_a.b.eval b.point.1 = 0 := heval.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h_factor_ne
    · exact h

/-! ### Combine step running-sum claim

For combine_higher_distinct, the resulting accumulator's point lifts
to the EC group sum of the two input accumulators' points. -/

theorem combine_higher_distinct_running_sum
    (a b : EagenAccum E)
    (ha : a.point ∈ E.points) (hb : b.point ∈ E.points)
    (h_xx : a.point.1 ≠ b.point.1) :
    ∃ h_acc : (EagenAccum.combine_higher_distinct E a b h_xx).point ∈ E.points,
      (ECPoint.affineOfMem E h_acc : ECPoint E)
        = ECPoint.affineOfMem E ha + ECPoint.affineOfMem E hb := by
  classical
  -- combine_higher_distinct's point structure mirrors fromChordPair_distinct.
  set lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2 with hlam_def
  set Q₀x := lam ^ 2 - a.point.1 - b.point.1 with hQ₀x_def
  set Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1) with hQ₀y_def
  have h_acc_point : (EagenAccum.combine_higher_distinct E a b h_xx).point
                    = (Q₀x, -Q₀y) := rfl
  have hThirdMem : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point ha hb h_xx
  have hNegThirdMem : (Q₀x, -Q₀y) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hThirdMem
    show (-Q₀y) ^ 2 = Q₀x ^ 3 + E.curveA * Q₀x + E.curveB
    rw [neg_pow_two]; exact hC
  refine ⟨h_acc_point ▸ hNegThirdMem, ?_⟩
  have hT : thirdPoint E a.point b.point = some (Q₀x, Q₀y) := by
    unfold thirdPoint
    rw [if_neg h_xx]
    rfl
  have hSum := thirdPoint_some_eq_neg_add (E := E) ha hb hT
  rw [hSum]
  rw [← ECPoint.affine_eq_affineOfMem E (h_acc_point ▸ hNegThirdMem)]
  rw [← ECPoint.affine_eq_affineOfMem E (third_point_on_curve E a.point b.point ha hb hT)]
  show (ECPoint.affine E (EagenAccum.combine_higher_distinct E a b h_xx).point.1
        (EagenAccum.combine_higher_distinct E a b h_xx).point.2 : ECPoint E)
      = -ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
  rw [h_acc_point]
  show (ECPoint.affine E Q₀x (-Q₀y) : ECPoint E)
      = -ECPoint.affine E Q₀x Q₀y
  rw [ECPoint.affine_neg E Q₀x Q₀y]

/-! ### AccInv at infinity: natDegree of `normPoly` matches list length

Under `AccInv xs a`, the `normPoly` of `a.poly` has natDegree
`xs.length + 1` (since `a.poly`'s pole at `O` matches the formal
divisor's `-(xs.length)` plus the residue's `-1` at infinity). -/

theorem accInv_natDegree_normPoly
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h_acc : AccInv E xs a)
    (h_a_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0)) :
    (normPoly E a.poly).natDegree = xs.length + 1 := by
  classical
  obtain ⟨h_pt_mem, _, h_div⟩ := h_acc
  have h_div_inf := h_div (0 : ECPoint E)
  -- `a.lift ≠ 0` since affineOfMem produces a `some _` constructor.
  have h_lift_ne_zero : (ECPoint.affineOfMem E h_pt_mem : ECPoint E) ≠ 0 := by
    intro h_eq
    unfold ECPoint.affineOfMem ECPoint.affineOfEqn at h_eq
    cases h_eq
  -- Rewrite both sides explicitly.
  rw [show divisorOfD E a.poly (0 : ECPoint E)
        = -((normPoly E a.poly).natDegree : ℤ) from rfl,
      formalDivisorOfList_at_infinity,
      residueDivisor_at_infinity_of_S_ne_zero E _ h_lift_ne_zero] at h_div_inf
  -- h_div_inf : -((normPoly a.poly).natDeg : ℤ) = -(xs.length : ℤ) + -1.
  have h2 : ((normPoly E a.poly).natDegree : ℤ) = (xs.length : ℤ) + 1 := by linarith
  exact_mod_cast h2

/-! ### Combine step: at-infinity divisor identity

At infinity, the combine-step's divisor identity follows from
`normPoly` multiplicativity and the `normPoly_divLin_factor` reduction
(each `divLin` step removes a `(X-x₀)²` factor from `normPoly`). No
cross-case mul-additivity issues at infinity. -/

theorem accInv_combine_higher_distinct_divisor_at_infinity
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    divisorOfD E (EagenAccum.combine_higher_distinct E a b h_xx).poly
      (0 : ECPoint E)
      = -(((xs.length + ys.length + 1 : ℕ)) : ℤ) := by
  classical
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  -- non-zero: chord, chord·a.poly, prod = chord·a.poly·b.poly.
  have h_chord_NZ : ¬ (chord.a = 0 ∧ chord.b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_chord_a_NZ : ¬ ((mulCoordRingElt E chord a.poly).a = 0
      ∧ (mulCoordRingElt E chord a.poly).b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E (mulCoordRingElt E chord a.poly) = 0 := by
      rw [normPoly_eq, ha, hb]; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E chord h_chord_NZ)
      (normPoly_ne_zero E a.poly h_a_poly_NZ)) hN
  have h_prod_NZ : ¬ (prod.a = 0 ∧ prod.b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E prod = 0 := by
      rw [normPoly_eq, ha, hb]; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E _ h_chord_a_NZ)
      (normPoly_ne_zero E b.poly h_b_poly_NZ)) hN
  -- (X - C a.x) divides prod.a and prod.b.
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_prod_a_root : prod.a.eval a.point.1 = 0 := h_prod_at_a.1
  have h_prod_b_root : prod.b.eval a.point.1 = 0 := h_prod_at_a.2
  -- (X - C b.x) divides (prod.divLin a.x).a and .b.
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  have h_after_a_a_root : (prod.divLin a.point.1).a.eval b.point.1 = 0 :=
    h_after_a_at_b.1
  have h_after_a_b_root : (prod.divLin a.point.1).b.eval b.point.1 = 0 :=
    h_after_a_at_b.2
  -- normPoly prod = (X - C a.x)² · normPoly (prod.divLin a.x)
  have h_normProd_factor : normPoly E prod
      = (Polynomial.X - Polynomial.C a.point.1) ^ 2
        * normPoly E (prod.divLin a.point.1) :=
    normPoly_divLin_factor E prod h_prod_a_root h_prod_b_root
  -- prod.divLin a.x is non-zero (componentwise).
  have h_after_a_NZ : ¬ ((prod.divLin a.point.1).a = 0
      ∧ (prod.divLin a.point.1).b = 0) :=
    divLin_not_both_zero E prod h_prod_NZ h_prod_a_root h_prod_b_root
  -- normPoly (prod.divLin a.x) = (X - C b.x)² · normPoly (combine.poly)
  have h_normAfterA_factor : normPoly E (prod.divLin a.point.1)
      = (Polynomial.X - Polynomial.C b.point.1) ^ 2
        * normPoly E ((prod.divLin a.point.1).divLin b.point.1) :=
    normPoly_divLin_factor E (prod.divLin a.point.1)
      h_after_a_a_root h_after_a_b_root
  -- combine.poly's normPoly is non-zero.
  have h_combine_NZ : ¬ (((prod.divLin a.point.1).divLin b.point.1).a = 0
      ∧ ((prod.divLin a.point.1).divLin b.point.1).b = 0) :=
    divLin_not_both_zero E (prod.divLin a.point.1) h_after_a_NZ
      h_after_a_a_root h_after_a_b_root
  -- natDegree(normPoly combine.poly) = natDegree(normPoly prod) - 4.
  have h_xa_NZ : (Polynomial.X - Polynomial.C a.point.1) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero a.point.1
  have h_xb_NZ : (Polynomial.X - Polynomial.C b.point.1) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero b.point.1
  have h_xa_pow_NZ : ((Polynomial.X - Polynomial.C a.point.1) ^ 2 : Polynomial (ZMod E.q)) ≠ 0 :=
    pow_ne_zero _ h_xa_NZ
  have h_xb_pow_NZ : ((Polynomial.X - Polynomial.C b.point.1) ^ 2 : Polynomial (ZMod E.q)) ≠ 0 :=
    pow_ne_zero _ h_xb_NZ
  have h_normAfterA_NZ : normPoly E (prod.divLin a.point.1) ≠ 0 :=
    normPoly_ne_zero E _ h_after_a_NZ
  have h_normCombine_NZ : normPoly E ((prod.divLin a.point.1).divLin b.point.1) ≠ 0 :=
    normPoly_ne_zero E _ h_combine_NZ
  have h_xa_natDeg : ((Polynomial.X - Polynomial.C a.point.1) ^ 2
                      : Polynomial (ZMod E.q)).natDegree = 2 := by
    rw [Polynomial.natDegree_pow]
    rw [Polynomial.natDegree_X_sub_C]
  have h_xb_natDeg : ((Polynomial.X - Polynomial.C b.point.1) ^ 2
                      : Polynomial (ZMod E.q)).natDegree = 2 := by
    rw [Polynomial.natDegree_pow]
    rw [Polynomial.natDegree_X_sub_C]
  -- natDegree of normPoly factorings.
  have h_natDeg_prod : (normPoly E prod).natDegree
      = 2 + (normPoly E (prod.divLin a.point.1)).natDegree := by
    rw [h_normProd_factor]
    rw [Polynomial.natDegree_mul h_xa_pow_NZ h_normAfterA_NZ]
    rw [h_xa_natDeg]
  have h_natDeg_afterA : (normPoly E (prod.divLin a.point.1)).natDegree
      = 2 + (normPoly E ((prod.divLin a.point.1).divLin b.point.1)).natDegree := by
    rw [h_normAfterA_factor]
    rw [Polynomial.natDegree_mul h_xb_pow_NZ h_normCombine_NZ]
    rw [h_xb_natDeg]
  -- natDegree(normPoly prod) via mul-additivity.
  have h_natDeg_prod_total : (normPoly E prod).natDegree
      = 3 + (xs.length + 1) + (ys.length + 1) := by
    rw [hprod_def]
    rw [natDegree_normPoly_mul_eq E _ b.poly h_chord_a_NZ h_b_poly_NZ]
    rw [natDegree_normPoly_mul_eq E chord a.poly h_chord_NZ h_a_poly_NZ]
    -- natDegree(normPoly chord) = 3.
    have h_chord_natDeg : (normPoly E chord).natDegree = 3 := by
      have := divisorOfD_chordCoordRingElt_at_infinity_nonvertical E a.point b.point h_xx
      have hgoal : -((normPoly E chord).natDegree : ℤ) = -3 := by
        rw [hchord_def]; exact this
      have : ((normPoly E chord).natDegree : ℤ) = 3 := by linarith
      exact_mod_cast this
    rw [h_chord_natDeg]
    rw [accInv_natDegree_normPoly E h_acc_a h_a_poly_NZ]
    rw [accInv_natDegree_normPoly E h_acc_b h_b_poly_NZ]
  -- Combine the equalities.
  have h_combine_natDeg : (normPoly E
      ((prod.divLin a.point.1).divLin b.point.1)).natDegree
      = xs.length + ys.length + 1 := by
    have : (normPoly E prod).natDegree
        = 4 + (normPoly E ((prod.divLin a.point.1).divLin b.point.1)).natDegree := by
      rw [h_natDeg_prod, h_natDeg_afterA]; ring
    omega
  -- divisorOfD = -natDegree(normPoly).
  show -((normPoly E ((prod.divLin a.point.1).divLin b.point.1)).natDegree : ℤ)
      = -((xs.length + ys.length + 1 : ℕ) : ℤ)
  rw [h_combine_natDeg]

/-! ### Combine step: at-infinity divisor identity in AccInv form

Reformulates `accInv_combine_higher_distinct_divisor_at_infinity` to
match the `AccInv` divisor identity shape: the value equals
`formalDivisorOfList (xs ++ ys) 0 + residueDivisor (combine.lift) 0`,
where `combine.lift = a.lift + b.lift` (via running_sum). -/

theorem accInv_combine_higher_distinct_divisor_at_infinity_AccInv_form
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0)) :
    let combine := EagenAccum.combine_higher_distinct E a b h_xx
    ∃ h_combine_pt : combine.point ∈ E.points,
      divisorOfD E combine.poly (0 : ECPoint E)
        = formalDivisorOfList E (xs ++ ys) (0 : ECPoint E)
          + residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (0 : ECPoint E) := by
  classical
  intro combine
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- combine.point ∈ E.points (from running_sum).
  obtain ⟨h_combine_pt, _h_lift_eq⟩ := combine_higher_distinct_running_sum
    E a b h_a_pt h_b_pt h_xx
  refine ⟨h_combine_pt, ?_⟩
  -- combine.lift = a.lift + b.lift ≠ 0 (since a.point.1 ≠ b.point.1
  -- forces combine.lift ≠ ∞; affineOfMem is a `.some` constructor).
  have h_combine_ne_zero :
      (ECPoint.affineOfMem E h_combine_pt : ECPoint E) ≠ 0 := by
    intro h_eq
    unfold ECPoint.affineOfMem ECPoint.affineOfEqn at h_eq
    cases h_eq
  -- LHS via the at-infinity theorem.
  rw [accInv_combine_higher_distinct_divisor_at_infinity (E := E)
        h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ]
  -- RHS: formalDivisorOfList (xs++ys) 0 = -((xs++ys).length) = -(xs.length+ys.length).
  rw [formalDivisorOfList_at_infinity, List.length_append]
  rw [residueDivisor_at_infinity_of_S_ne_zero E _ h_combine_ne_zero]
  push_cast; ring

/-! ### Combine step: polynomial-factorization eval helper

Reusable helper extracting the algebraic identity
`prod.eval(x, y) = (x - a.x)(x - b.x) · combine.poly.eval(x, y)` for
any (x, y). Follows from the divLin recompositions
`prod.{a,b} = (X - a.x) · (prod.divLin a.x).{a,b}` and
`(prod.divLin a.x).{a,b} = (X - b.x) · combine.{a,b}`. -/

theorem combine_higher_distinct_prod_eval_factor
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (x y : ZMod E.q) :
    (mulCoordRingElt E (mulCoordRingElt E
        (chordCoordRingElt E a.point b.point) a.poly) b.poly).eval x y
      = (x - a.point.1) * (x - b.point.1)
        * (EagenAccum.combine_higher_distinct E a b h_xx).poly.eval x y := by
  classical
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  set combine := EagenAccum.combine_higher_distinct E a b h_xx with hcombine_def
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  have h_pa_eval : prod.a.eval x
      = (x - a.point.1) * (prod.divLin a.point.1).a.eval x := by
    have h_pa_recomp : prod.a
        = (Polynomial.X - Polynomial.C a.point.1)
          * (prod.divLin a.point.1).a := by
      show prod.a = (Polynomial.X - Polynomial.C a.point.1)
            * (prod.a /ₘ (Polynomial.X - Polynomial.C a.point.1))
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_prod_at_a.1).symm
    rw [h_pa_recomp]
    simp [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
  have h_pb_eval : prod.b.eval x
      = (x - a.point.1) * (prod.divLin a.point.1).b.eval x := by
    have h_pb_recomp : prod.b
        = (Polynomial.X - Polynomial.C a.point.1)
          * (prod.divLin a.point.1).b := by
      show prod.b = (Polynomial.X - Polynomial.C a.point.1)
            * (prod.b /ₘ (Polynomial.X - Polynomial.C a.point.1))
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_prod_at_a.2).symm
    rw [h_pb_recomp]
    simp [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
  have h_da_a_eval : (prod.divLin a.point.1).a.eval x
      = (x - b.point.1) * combine.poly.a.eval x := by
    have h_da_a_recomp : (prod.divLin a.point.1).a
        = (Polynomial.X - Polynomial.C b.point.1)
          * ((prod.divLin a.point.1).divLin b.point.1).a := by
      show (prod.divLin a.point.1).a
          = (Polynomial.X - Polynomial.C b.point.1)
            * ((prod.divLin a.point.1).a /ₘ (Polynomial.X - Polynomial.C b.point.1))
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_after_a_at_b.1).symm
    rw [show combine.poly = (prod.divLin a.point.1).divLin b.point.1 from rfl]
    rw [h_da_a_recomp]
    simp [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
  have h_da_b_eval : (prod.divLin a.point.1).b.eval x
      = (x - b.point.1) * combine.poly.b.eval x := by
    have h_da_b_recomp : (prod.divLin a.point.1).b
        = (Polynomial.X - Polynomial.C b.point.1)
          * ((prod.divLin a.point.1).divLin b.point.1).b := by
      show (prod.divLin a.point.1).b
          = (Polynomial.X - Polynomial.C b.point.1)
            * ((prod.divLin a.point.1).b /ₘ (Polynomial.X - Polynomial.C b.point.1))
      exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_after_a_at_b.2).symm
    rw [show combine.poly = (prod.divLin a.point.1).divLin b.point.1 from rfl]
    rw [h_da_b_recomp]
    simp [Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
  show prod.a.eval x - prod.b.eval x * y
      = (x - a.point.1) * (x - b.point.1)
        * (combine.poly.a.eval x - combine.poly.b.eval x * y)
  rw [h_pa_eval, h_pb_eval, h_da_a_eval, h_da_b_eval]
  ring

/-! ### Combine step: vanishing at third intersection point

Combine.poly.eval at `(Q₀x, Q₀y)` (the third intersection of the chord
through a.point and b.point) is zero. Follows from
prod_eval_factor and chord vanishing at third point. -/

theorem combine_higher_distinct_eval_third_zero
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    (EagenAccum.combine_higher_distinct E a b h_xx).poly.eval Q₀x Q₀y = 0 := by
  classical
  intro lam Q₀x Q₀y
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- prod_eval at (Q₀x, Q₀y) = (Q₀x - a.x)(Q₀x - b.x) · combine.eval(Q₀x, Q₀y)
  have h_factor :=
    combine_higher_distinct_prod_eval_factor (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ Q₀x Q₀y
  -- prod.eval at (Q₀x, Q₀y) = chord · a · b at (Q₀x, Q₀y) (Q₀ ∈ E).
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  have h_prod_eval :
      (mulCoordRingElt E (mulCoordRingElt E
          (chordCoordRingElt E a.point b.point) a.poly) b.poly).eval Q₀x Q₀y
        = ((chordCoordRingElt E a.point b.point).eval Q₀x Q₀y)
          * (a.poly.eval Q₀x Q₀y) * (b.poly.eval Q₀x Q₀y) := by
    rw [mulCoordRingElt_eval_on_E E _ b.poly hQ₀_on_E]
    rw [mulCoordRingElt_eval_on_E E _ a.poly hQ₀_on_E]
  -- chord vanishes at (Q₀x, Q₀y).
  have h_chord_zero :
      (chordCoordRingElt E a.point b.point).eval Q₀x Q₀y = 0 :=
    chordCoordRingElt_eval_thirdPoint_chord E h_a_pt h_b_pt h_xx
  -- prod.eval = 0.
  have h_prod_zero :
      (mulCoordRingElt E (mulCoordRingElt E
          (chordCoordRingElt E a.point b.point) a.poly) b.poly).eval Q₀x Q₀y = 0 := by
    rw [h_prod_eval, h_chord_zero, zero_mul, zero_mul]
  -- Now use the factor: (Q₀x - a.x)(Q₀x - b.x) ≠ 0 ⇒ combine.eval = 0.
  have h_diff_a : Q₀x - a.point.1 ≠ 0 := sub_ne_zero.mpr h_Q₀x_ne_a
  have h_diff_b : Q₀x - b.point.1 ≠ 0 := sub_ne_zero.mpr h_Q₀x_ne_b
  rw [h_prod_zero] at h_factor
  -- 0 = (Q₀x - a.x) * (Q₀x - b.x) * combine.eval.
  have : (Q₀x - a.point.1) * (Q₀x - b.point.1)
        * (EagenAccum.combine_higher_distinct E a b h_xx).poly.eval Q₀x Q₀y = 0 :=
    h_factor.symm
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h h_diff_a
    · exact absurd h h_diff_b
  · exact h

/-! ### Chord nonvanishes at the negation of the third intersection

`chord(Q₀x, -Q₀y) = -2 · Q₀y`, where `(Q₀x, Q₀y)` is the third
intersection of the chord through `a.point` and `b.point`. Hence
chord nonvanishes at `(Q₀x, -Q₀y)` whenever `Q₀y ≠ 0`. -/

theorem chordCoordRingElt_eval_at_neg_third
    (a b : EagenAccum E)
    (h_xx : a.point.1 ≠ b.point.1) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    (chordCoordRingElt E a.point b.point).eval Q₀x (-Q₀y) = -2 * Q₀y := by
  classical
  intro lam Q₀x Q₀y
  rw [chordCoordRingElt_eval_eq_lineThrough_chord E h_xx (Q₀x, -Q₀y)]
  -- (lineThrough a.point b.point).eval (Q₀x, -Q₀y).
  unfold Line.eval lineThrough
  show -Q₀y - lam * Q₀x - (a.point.2 - lam * a.point.1) = -2 * Q₀y
  -- Q₀y = lam * Q₀x + (a.point.2 - lam * a.point.1) by definition.
  show -(lam * Q₀x + (a.point.2 - lam * a.point.1)) - lam * Q₀x
        - (a.point.2 - lam * a.point.1) = -2 * (lam * Q₀x + (a.point.2 - lam * a.point.1))
  ring

/-! ### Combine nonvanishes at -third under generic hypotheses

Under the hypotheses `Q₀y ≠ 0`, `a.poly` and `b.poly` nonvanish at
`(Q₀x, -Q₀y)`, and `Q₀x ≠ a.point.1`, `Q₀x ≠ b.point.1`, we have
`combine.poly.eval(Q₀x, -Q₀y) ≠ 0`. Follows from the prod_eval_factor
identity plus chord nonvanish at -third. -/

theorem combine_higher_distinct_eval_neg_third_nonzero
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀y_ne_zero : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                      * (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                         - a.point.1 - b.point.1)
                      + (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                         * a.point.1)) ≠ 0)
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_a_neg_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_b_neg_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x (-Q₀y) ≠ 0) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    (EagenAccum.combine_higher_distinct E a b h_xx).poly.eval Q₀x (-Q₀y) ≠ 0 := by
  classical
  intro lam Q₀x Q₀y
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- (Q₀x, -Q₀y) ∈ E.points.
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  have h_negQ₀_on_E : (Q₀x, -Q₀y) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hQ₀_on_E
    show (-Q₀y) ^ 2 = Q₀x ^ 3 + E.curveA * Q₀x + E.curveB
    rw [neg_pow_two]; exact hC
  -- chord at (Q₀x, -Q₀y) = -2·Q₀y ≠ 0.
  have h_chord_neg : (chordCoordRingElt E a.point b.point).eval Q₀x (-Q₀y) ≠ 0 := by
    rw [chordCoordRingElt_eval_at_neg_third E a b h_xx]
    show (-2 : ZMod E.q) * Q₀y ≠ 0
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    have hneg2 : (-2 : ZMod E.q) ≠ 0 := neg_ne_zero.mpr h2
    exact mul_ne_zero hneg2 h_Q₀y_ne_zero
  -- prod.eval at (Q₀x, -Q₀y) ≠ 0.
  have h_prod_neg : (mulCoordRingElt E (mulCoordRingElt E
        (chordCoordRingElt E a.point b.point) a.poly) b.poly).eval Q₀x (-Q₀y) ≠ 0 := by
    rw [mulCoordRingElt_eval_on_E E _ b.poly h_negQ₀_on_E]
    rw [mulCoordRingElt_eval_on_E E _ a.poly h_negQ₀_on_E]
    exact mul_ne_zero (mul_ne_zero h_chord_neg h_a_neg_Q₀) h_b_neg_Q₀
  -- prod_eval_factor: prod.eval = (Q₀x - a.x)(Q₀x - b.x) · combine.eval.
  have h_factor :=
    combine_higher_distinct_prod_eval_factor (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ Q₀x (-Q₀y)
  -- Therefore combine.eval(Q₀x, -Q₀y) ≠ 0.
  intro h_combine_eval
  apply h_prod_neg
  rw [h_factor, h_combine_eval, mul_zero]

/-! ### Chord normPoly rootMult at third intersection x = 1

The chord through `a.point, b.point` (distinct) has `normPoly` with
rootMult ≤ 1 globally (chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord).
At the x-coordinate `Q₀x` of the third intersection, the normPoly
vanishes (since chord vanishes at `(Q₀x, Q₀y)`), so rootMult ≥ 1.
Combined: rootMult = 1. -/

theorem chordCoordRingElt_rootMult_normPoly_at_third_eq_one
    (a b : EagenAccum E)
    (ha : a.point ∈ E.points) (hb : b.point ∈ E.points)
    (h_xx : a.point.1 ≠ b.point.1)
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1) :
    let Q₀x := slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                - a.point.1 - b.point.1
    Polynomial.rootMultiplicity Q₀x
      (normPoly E (chordCoordRingElt E a.point b.point)) = 1 := by
  classical
  intro Q₀x
  -- Upper bound via chord-line lemma (note: lemma takes hypotheses in flipped form).
  have h_le := chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord E
    a.point b.point ha hb h_xx h_Q₀x_ne_a.symm h_Q₀x_ne_b.symm Q₀x
  -- Lower bound: chord vanishes at Q₀ ⟹ normPoly chord (Q₀x) = 0.
  have hQ₀_on_E : (Q₀x,
      slopeOf a.point.1 a.point.2 b.point.1 b.point.2 * Q₀x
        + (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2 * a.point.1))
      ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point ha hb h_xx
  have h_chord_zero :=
    chordCoordRingElt_eval_thirdPoint_chord E ha hb h_xx
  have h_normPoly_zero :
      (normPoly E (chordCoordRingElt E a.point b.point)).eval Q₀x = 0 := by
    rw [normPoly_eval_eq_D_mul_D_neg E (chordCoordRingElt E a.point b.point) hQ₀_on_E]
    rw [h_chord_zero, zero_mul]
  -- chord nonzero (so normPoly nonzero).
  have h_chord_NZ : ¬ ((chordCoordRingElt E a.point b.point).a = 0
      ∧ (chordCoordRingElt E a.point b.point).b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_normPoly_NZ : normPoly E (chordCoordRingElt E a.point b.point) ≠ 0 :=
    normPoly_ne_zero E _ h_chord_NZ
  -- rootMultiplicity ≥ 1 from eval = 0.
  have h_ge :
      1 ≤ Polynomial.rootMultiplicity Q₀x
        (normPoly E (chordCoordRingElt E a.point b.point)) := by
    have h_pos : 0 < Polynomial.rootMultiplicity Q₀x
        (normPoly E (chordCoordRingElt E a.point b.point)) :=
      (Polynomial.rootMultiplicity_pos h_normPoly_NZ).mpr h_normPoly_zero
    omega
  omega

/-! ### normPoly rootMult is zero when both fiber sheets are nonvanishing -/

theorem rootMult_normPoly_eq_zero_of_fiber_nonvanish
    (D : CoordRingElt E.q)
    {x y : ZMod E.q} (hP : (x, y) ∈ E.points)
    (h_pos : D.eval x y ≠ 0) (h_neg : D.eval x (-y) ≠ 0) :
    Polynomial.rootMultiplicity x (normPoly E D) = 0 := by
  classical
  apply Polynomial.rootMultiplicity_eq_zero
  show (normPoly E D).eval x ≠ 0
  rw [normPoly_eval_eq_D_mul_D_neg E D hP]
  exact mul_ne_zero h_pos h_neg

/-! ### Combine rootMult(normPoly)(Q₀x) = 1

Assembling the previous helpers:
* chord normPoly rootMult at Q₀x = 1.
* a.poly, b.poly normPoly rootMult at Q₀x = 0 (fiber nonvanish).
* (X-a.x)², (X-b.x)² rootMult at Q₀x = 0 (Q₀x ≠ a.x, b.x).
* normPoly mul = product, so rootMults add. -/

theorem combine_higher_distinct_rootMult_normPoly_at_third_eq_one
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_a_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x Q₀y ≠ 0)
    (h_a_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_b_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x Q₀y ≠ 0)
    (h_b_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x (-Q₀y) ≠ 0) :
    Polynomial.rootMultiplicity
      (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
       - a.point.1 - b.point.1)
      (normPoly E (EagenAccum.combine_higher_distinct E a b h_xx).poly) = 1 := by
  classical
  set lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2 with hlam_def
  set Q₀x := lam ^ 2 - a.point.1 - b.point.1 with hQ₀x_def
  set Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1) with hQ₀y_def
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- Q₀ is on E.
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  -- Set up needed values.
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  set combine := EagenAccum.combine_higher_distinct E a b h_xx with hcombine_def
  -- prod, prod.divLin a.x, combine all nonzero.
  have h_chord_NZ : ¬ (chord.a = 0 ∧ chord.b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_chord_a_NZ : ¬ ((mulCoordRingElt E chord a.poly).a = 0
      ∧ (mulCoordRingElt E chord a.poly).b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E (mulCoordRingElt E chord a.poly) = 0 := by
      rw [normPoly_eq, ha, hb]; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E chord h_chord_NZ)
      (normPoly_ne_zero E a.poly h_a_poly_NZ)) hN
  have h_prod_NZ : ¬ (prod.a = 0 ∧ prod.b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E prod = 0 := by rw [normPoly_eq, ha, hb]; ring
    rw [hprod_def, normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E _ h_chord_a_NZ)
      (normPoly_ne_zero E b.poly h_b_poly_NZ)) hN
  -- Divisibility (X-C a.x) ∣ prod.{a, b}; (X-C b.x) ∣ (prod.divLin a.x).{a, b}.
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  -- divLin reduction: normPoly prod = (X-a.x)² · normPoly (prod.divLin a.x).
  have h_normProd_factor : normPoly E prod
      = (Polynomial.X - Polynomial.C a.point.1) ^ 2
        * normPoly E (prod.divLin a.point.1) :=
    normPoly_divLin_factor E prod h_prod_at_a.1 h_prod_at_a.2
  have h_after_a_NZ : ¬ ((prod.divLin a.point.1).a = 0
      ∧ (prod.divLin a.point.1).b = 0) :=
    divLin_not_both_zero E prod h_prod_NZ h_prod_at_a.1 h_prod_at_a.2
  have h_normAfterA_factor : normPoly E (prod.divLin a.point.1)
      = (Polynomial.X - Polynomial.C b.point.1) ^ 2
        * normPoly E ((prod.divLin a.point.1).divLin b.point.1) :=
    normPoly_divLin_factor E (prod.divLin a.point.1)
      h_after_a_at_b.1 h_after_a_at_b.2
  -- combine.poly = (prod.divLin a.x).divLin b.x.
  have h_combine_poly_eq : combine.poly = (prod.divLin a.point.1).divLin b.point.1 := rfl
  -- normPoly prod = (X-a.x)²(X-b.x)² · normPoly combine.poly.
  have h_normProd_full : normPoly E prod
      = (Polynomial.X - Polynomial.C a.point.1) ^ 2
        * ((Polynomial.X - Polynomial.C b.point.1) ^ 2
           * normPoly E combine.poly) := by
    rw [h_normProd_factor, h_normAfterA_factor, h_combine_poly_eq]
  -- Also normPoly prod = normPoly chord · normPoly a.poly · normPoly b.poly.
  have h_normProd_split : normPoly E prod
      = normPoly E chord * normPoly E a.poly * normPoly E b.poly := by
    rw [hprod_def, normPoly_mul_eq, normPoly_mul_eq]
  -- Take rootMult at Q₀x of both expressions.
  have h_xa_NZ : (Polynomial.X - Polynomial.C a.point.1) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero a.point.1
  have h_xb_NZ : (Polynomial.X - Polynomial.C b.point.1) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero b.point.1
  have h_xa_pow_NZ : ((Polynomial.X - Polynomial.C a.point.1) ^ 2
                      : Polynomial (ZMod E.q)) ≠ 0 := pow_ne_zero _ h_xa_NZ
  have h_xb_pow_NZ : ((Polynomial.X - Polynomial.C b.point.1) ^ 2
                      : Polynomial (ZMod E.q)) ≠ 0 := pow_ne_zero _ h_xb_NZ
  have h_combine_NZ : ¬ (combine.poly.a = 0 ∧ combine.poly.b = 0) := by
    rw [h_combine_poly_eq]
    exact divLin_not_both_zero E (prod.divLin a.point.1) h_after_a_NZ
      h_after_a_at_b.1 h_after_a_at_b.2
  have h_normCombine_NZ : normPoly E combine.poly ≠ 0 :=
    normPoly_ne_zero E _ h_combine_NZ
  have h_xb_pow_normC_NZ : ((Polynomial.X - Polynomial.C b.point.1) ^ 2
                            * normPoly E combine.poly : Polynomial (ZMod E.q)) ≠ 0 :=
    mul_ne_zero h_xb_pow_NZ h_normCombine_NZ
  -- rootMult at Q₀x of factor pieces.
  have h_xa_pow_rootMult :
      Polynomial.rootMultiplicity Q₀x
        ((Polynomial.X - Polynomial.C a.point.1) ^ 2 : Polynomial (ZMod E.q)) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    show (((Polynomial.X - Polynomial.C a.point.1) ^ 2
           : Polynomial (ZMod E.q))).eval Q₀x ≠ 0
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
               Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr h_Q₀x_ne_a)
  have h_xb_pow_rootMult :
      Polynomial.rootMultiplicity Q₀x
        ((Polynomial.X - Polynomial.C b.point.1) ^ 2 : Polynomial (ZMod E.q)) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    show (((Polynomial.X - Polynomial.C b.point.1) ^ 2
           : Polynomial (ZMod E.q))).eval Q₀x ≠ 0
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
               Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr h_Q₀x_ne_b)
  -- rootMult at Q₀x of normPoly chord = 1 (proved earlier).
  have h_chord_rootMult :=
    chordCoordRingElt_rootMult_normPoly_at_third_eq_one E a b h_a_pt h_b_pt
      h_xx h_Q₀x_ne_a h_Q₀x_ne_b
  -- rootMult at Q₀x of normPoly a.poly = 0 (fiber nonvanish).
  have h_a_rootMult :=
    rootMult_normPoly_eq_zero_of_fiber_nonvanish E a.poly hQ₀_on_E h_a_at_Q₀ h_a_at_negQ₀
  -- rootMult at Q₀x of normPoly b.poly = 0.
  have h_b_rootMult :=
    rootMult_normPoly_eq_zero_of_fiber_nonvanish E b.poly hQ₀_on_E h_b_at_Q₀ h_b_at_negQ₀
  -- rootMult of normPoly prod at Q₀x via the split:
  have h_normChord_NZ : normPoly E chord ≠ 0 := normPoly_ne_zero E chord h_chord_NZ
  have h_normA_NZ : normPoly E a.poly ≠ 0 := normPoly_ne_zero E a.poly h_a_poly_NZ
  have h_normB_NZ : normPoly E b.poly ≠ 0 := normPoly_ne_zero E b.poly h_b_poly_NZ
  have h_normChord_a_NZ : normPoly E chord * normPoly E a.poly ≠ 0 :=
    mul_ne_zero h_normChord_NZ h_normA_NZ
  have h_normChord_a_b_NZ : normPoly E chord * normPoly E a.poly * normPoly E b.poly ≠ 0 :=
    mul_ne_zero h_normChord_a_NZ h_normB_NZ
  have h_rootMult_prod_split :
      Polynomial.rootMultiplicity Q₀x (normPoly E prod) = 1 := by
    rw [h_normProd_split]
    rw [Polynomial.rootMultiplicity_mul h_normChord_a_b_NZ]
    rw [Polynomial.rootMultiplicity_mul h_normChord_a_NZ]
    rw [h_chord_rootMult, h_a_rootMult, h_b_rootMult]
  -- rootMult of normPoly prod at Q₀x via the divLin split: equals rootMult of combine.
  have h_rootMult_prod_via_combine :
      Polynomial.rootMultiplicity Q₀x (normPoly E prod)
        = Polynomial.rootMultiplicity Q₀x (normPoly E combine.poly) := by
    rw [h_normProd_full]
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero h_xa_pow_NZ h_xb_pow_normC_NZ)]
    rw [Polynomial.rootMultiplicity_mul h_xb_pow_normC_NZ]
    rw [h_xa_pow_rootMult, h_xb_pow_rootMult]
    ring
  rw [← h_rootMult_prod_via_combine, h_rootMult_prod_split]

/-! ### Lone-sheet ordAt at non-2-torsion: ordAt = rootMult(normPoly)

Reusable closed-form: when D vanishes at +sheet only (lone-sheet at +)
of a non-2-torsion fiber, `ordAt E D P = rootMult P.1 (normPoly E D)`.
Direct from the recursive ordAt's lone-sheet branch. -/

theorem ordAt_lone_sheet_eq_rootMult_normPoly
    {D : CoordRingElt E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (hDP : D.eval P.1 P.2 = 0) (hDnegP : D.eval P.1 (-P.2) ≠ 0) :
    ordAt E D P = Polynomial.rootMultiplicity P.1 (normPoly E D) := by
  classical
  rw [ordAt_eq_dispatch E D hP hD]
  rw [if_neg hY]
  unfold ordAt_nonTwoTorsion
  obtain ⟨n, hn⟩ : ∃ n, D.a.natDegree + D.b.natDegree + 1 = n + 1 := ⟨_, rfl⟩
  rw [hn]
  show (if D.a = 0 ∧ D.b = 0 then 0
        else if D.eval P.1 P.2 ≠ 0 then 0
        else if D.eval P.1 (-P.2) ≠ 0
                then Polynomial.rootMultiplicity P.1 (normPoly E D)
                else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P)
      = Polynomial.rootMultiplicity P.1 (normPoly E D)
  rw [if_neg hD, if_neg (not_not.mpr hDP), if_pos hDnegP]

/-! ### Combine step divisor identity at third intersection

`divisorOfD combine.poly (-combine.lift) = 1` under generic
hypotheses. Combines:
* eval_third_zero: combine vanish at +sheet (Q₀x, Q₀y).
* eval_neg_third_nonzero: combine nonvanish at -sheet (Q₀x, -Q₀y).
* ordAt_lone_sheet_eq_rootMult_normPoly: ordAt = rootMult.
* rootMult_normPoly_at_third_eq_one: rootMult = 1. -/

theorem accInv_combine_higher_distinct_divisor_at_third_intersection
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_Q₀y_ne_zero : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                      * (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                         - a.point.1 - b.point.1)
                      + (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                         * a.point.1)) ≠ 0)
    (h_a_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x Q₀y ≠ 0)
    (h_a_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_b_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x Q₀y ≠ 0)
    (h_b_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x (-Q₀y) ≠ 0) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    divisorOfD E (EagenAccum.combine_higher_distinct E a b h_xx).poly
      (ECPoint.affine E Q₀x Q₀y) = 1 := by
  classical
  intro lam Q₀x Q₀y
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- (Q₀x, Q₀y) ∈ E.points.
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  -- combine.poly is non-zero (as CoordRingElt).
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  set combine := EagenAccum.combine_higher_distinct E a b h_xx with hcombine_def
  have h_chord_NZ : ¬ (chord.a = 0 ∧ chord.b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_chord_a_NZ : ¬ ((mulCoordRingElt E chord a.poly).a = 0
      ∧ (mulCoordRingElt E chord a.poly).b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E (mulCoordRingElt E chord a.poly) = 0 := by
      rw [normPoly_eq, ha, hb]; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E chord h_chord_NZ)
      (normPoly_ne_zero E a.poly h_a_poly_NZ)) hN
  have h_prod_NZ : ¬ (prod.a = 0 ∧ prod.b = 0) := by
    intro ⟨ha, hb⟩
    have hN : normPoly E prod = 0 := by rw [normPoly_eq, ha, hb]; ring
    rw [hprod_def, normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E _ h_chord_a_NZ)
      (normPoly_ne_zero E b.poly h_b_poly_NZ)) hN
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  have h_after_a_NZ : ¬ ((prod.divLin a.point.1).a = 0
      ∧ (prod.divLin a.point.1).b = 0) :=
    divLin_not_both_zero E prod h_prod_NZ h_prod_at_a.1 h_prod_at_a.2
  have h_combine_NZ : ¬ (combine.poly.a = 0 ∧ combine.poly.b = 0) :=
    divLin_not_both_zero E (prod.divLin a.point.1) h_after_a_NZ
      h_after_a_at_b.1 h_after_a_at_b.2
  -- combine.eval at (Q₀x, Q₀y) = 0.
  have h_combine_at_Q₀ :
      combine.poly.eval Q₀x Q₀y = 0 :=
    combine_higher_distinct_eval_third_zero (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
      h_Q₀x_ne_a h_Q₀x_ne_b
  -- combine.eval at (Q₀x, -Q₀y) ≠ 0.
  have h_combine_at_negQ₀ :
      combine.poly.eval Q₀x (-Q₀y) ≠ 0 :=
    combine_higher_distinct_eval_neg_third_nonzero (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
      h_Q₀y_ne_zero h_Q₀x_ne_a h_Q₀x_ne_b h_a_at_negQ₀ h_b_at_negQ₀
  -- ordAt(combine.poly)(Q₀x, Q₀y) = rootMult(normPoly combine)(Q₀x).
  have h_ordAt :=
    ordAt_lone_sheet_eq_rootMult_normPoly (E := E) h_combine_NZ hQ₀_on_E
      h_Q₀y_ne_zero h_combine_at_Q₀ h_combine_at_negQ₀
  -- rootMult(normPoly combine)(Q₀x) = 1.
  have h_rootMult :=
    combine_higher_distinct_rootMult_normPoly_at_third_eq_one (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
      h_Q₀x_ne_a h_Q₀x_ne_b h_a_at_Q₀ h_a_at_negQ₀ h_b_at_Q₀ h_b_at_negQ₀
  -- Conclude.
  have hns : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hQ₀_on_E))
  rw [ECPoint.affine_of_nonsingular E hns]
  show (ordAt E combine.poly (Q₀x, Q₀y) : ℤ) = 1
  rw [h_ordAt, h_rootMult]
  rfl

/-! ### AccInv form of at-third divisor identity

At R = -combine.lift = ECPoint.affine Q₀x Q₀y:
* LHS: divisorOfD combine.poly R = 1 (at-third theorem).
* RHS: formalDivisorOfList(xs++ys) R + residueDivisor(combine.lift) R.
       formalDivisor = 0 since (Q₀x, Q₀y) ∉ xs ∪ ys (hypothesis).
       residueDivisor = 1 since R = -combine.lift, R ≠ O.
       Sum = 1. -/

theorem accInv_combine_higher_distinct_divisor_at_third_AccInv_form
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_Q₀y_ne_zero : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                      * (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                         - a.point.1 - b.point.1)
                      + (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                         * a.point.1)) ≠ 0)
    (h_a_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x Q₀y ≠ 0)
    (h_a_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_b_at_Q₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x Q₀y ≠ 0)
    (h_b_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_Q₀_not_in_xs :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        (Q₀x, Q₀y) ∉ xs)
    (h_Q₀_not_in_ys :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        (Q₀x, Q₀y) ∉ ys) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    let combine := EagenAccum.combine_higher_distinct E a b h_xx
    ∃ h_combine_pt : combine.point ∈ E.points,
      divisorOfD E combine.poly (ECPoint.affine E Q₀x Q₀y)
        = formalDivisorOfList E (xs ++ ys) (ECPoint.affine E Q₀x Q₀y)
          + residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (ECPoint.affine E Q₀x Q₀y) := by
  classical
  intro lam Q₀x Q₀y combine
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  obtain ⟨h_combine_pt, _⟩ := combine_higher_distinct_running_sum
    E a b h_a_pt h_b_pt h_xx
  refine ⟨h_combine_pt, ?_⟩
  -- LHS = 1.
  rw [accInv_combine_higher_distinct_divisor_at_third_intersection (E := E)
      h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
      h_Q₀x_ne_a h_Q₀x_ne_b h_Q₀y_ne_zero
      h_a_at_Q₀ h_a_at_negQ₀ h_b_at_Q₀ h_b_at_negQ₀]
  -- formalDivisor (xs++ys) at (Q₀x, Q₀y) = 0.
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  have hns : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hQ₀_on_E))
  have h_formal_zero : formalDivisorOfList E (xs ++ ys)
      (ECPoint.affine E Q₀x Q₀y) = 0 := by
    rw [ECPoint.affine_of_nonsingular E hns]
    rw [formalDivisorOfList_append, show
      formalDivisorOfList E xs (WeierstrassCurve.Affine.Point.some hns
                                : ECPoint E)
      = ((xs.filter (fun P => P = (Q₀x, Q₀y))).length : ℤ) from rfl,
      show formalDivisorOfList E ys (WeierstrassCurve.Affine.Point.some hns
                                     : ECPoint E)
      = ((ys.filter (fun P => P = (Q₀x, Q₀y))).length : ℤ) from rfl]
    have h1 : xs.filter (fun P => P = (Q₀x, Q₀y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_Q₀_not_in_xs
      rwa [decide_eq_true_eq.mp heq] at hP_in
    have h2 : ys.filter (fun P => P = (Q₀x, Q₀y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_Q₀_not_in_ys
      rwa [decide_eq_true_eq.mp heq] at hP_in
    rw [h1, h2]; simp
  rw [h_formal_zero, zero_add]
  -- residueDivisor combine.lift R = 1 since R = -combine.lift.
  -- combine.point = (Q₀x, -Q₀y) per definition; -combine.lift = ECPoint.affine Q₀x Q₀y.
  show 1 = residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (ECPoint.affine E Q₀x Q₀y)
  -- residueDivisor S R = (R = -S ? 1 : 0) - (R = 0 ? 1 : 0).
  unfold residueDivisor
  -- Need R = -S to make first term 1.
  have h_neg_combine_eq : -(ECPoint.affineOfMem E h_combine_pt : ECPoint E)
      = ECPoint.affine E Q₀x Q₀y := by
    rw [← ECPoint.affine_eq_affineOfMem E h_combine_pt]
    -- combine.point = (Q₀x, -Q₀y), so affineOfMem = ECPoint.affine Q₀x (-Q₀y);
    -- negation flips y to Q₀y.
    show -(ECPoint.affine E combine.point.1 combine.point.2 : ECPoint E)
        = ECPoint.affine E Q₀x Q₀y
    rw [show combine.point.1 = Q₀x from rfl, show combine.point.2 = -Q₀y from rfl]
    rw [ECPoint.affine_neg E Q₀x (-Q₀y), neg_neg]
  rw [if_pos h_neg_combine_eq.symm]
  rw [if_neg]
  · norm_num
  · -- ECPoint.affine E Q₀x Q₀y ≠ (0 : ECPoint E).
    intro h_eq
    rw [ECPoint.affine_of_nonsingular E hns] at h_eq
    cases h_eq

/-! ### Combine step: at-affine off-support divisor identity

When R = `ECPoint.affine x y` has x ≠ a.point.1, x ≠ b.point.1, and
the three factors (chord, a.poly, b.poly) all nonvanish at (x, y),
the polynomial identity prod = (X-C a.x)(X-C b.x) · combine.poly
forces combine.poly to nonvanish at (x, y). Then `ordAt = 0` by the
nonvanish branch, so `divisorOfD combine.poly R = 0`. -/

theorem accInv_combine_higher_distinct_divisor_at_off_support_zero
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    {x y : ZMod E.q} (hP : (x, y) ∈ E.points)
    (h_chord_pos : (chordCoordRingElt E a.point b.point).eval x y ≠ 0)
    (h_a_pos : a.poly.eval x y ≠ 0)
    (h_b_pos : b.poly.eval x y ≠ 0)
    (h_x_ne_a : x ≠ a.point.1)
    (h_x_ne_b : x ≠ b.point.1) :
    divisorOfD E (EagenAccum.combine_higher_distinct E a b h_xx).poly
      (ECPoint.affine E x y) = 0 := by
  classical
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  -- prod's eval at (x, y) is the product of the three factors' evals (on E).
  have h_prod_pos : prod.eval x y ≠ 0 := by
    rw [hprod_def, mulCoordRingElt_eval_on_E E _ b.poly hP,
        mulCoordRingElt_eval_on_E E chord a.poly hP]
    exact mul_ne_zero (mul_ne_zero h_chord_pos h_a_pos) h_b_pos
  -- Divisibility (X-C a.x) ∣ prod.a, prod.b.
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  -- Divisibility (X-C b.x) ∣ (prod.divLin a.x).a, .b.
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  -- Polynomial recompositions:
  -- prod.a = (X-C a.x) * (prod.divLin a.x).a;  similarly for .b.
  have h_pa_recomp : prod.a
      = (Polynomial.X - Polynomial.C a.point.1) * (prod.divLin a.point.1).a := by
    show prod.a
        = (Polynomial.X - Polynomial.C a.point.1)
          * (prod.a /ₘ (Polynomial.X - Polynomial.C a.point.1))
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_prod_at_a.1).symm
  have h_pb_recomp : prod.b
      = (Polynomial.X - Polynomial.C a.point.1) * (prod.divLin a.point.1).b := by
    show prod.b
        = (Polynomial.X - Polynomial.C a.point.1)
          * (prod.b /ₘ (Polynomial.X - Polynomial.C a.point.1))
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_prod_at_a.2).symm
  have h_div_a_a_recomp : (prod.divLin a.point.1).a
      = (Polynomial.X - Polynomial.C b.point.1)
        * ((prod.divLin a.point.1).divLin b.point.1).a := by
    show (prod.divLin a.point.1).a
        = (Polynomial.X - Polynomial.C b.point.1)
          * ((prod.divLin a.point.1).a /ₘ (Polynomial.X - Polynomial.C b.point.1))
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_after_a_at_b.1).symm
  have h_div_a_b_recomp : (prod.divLin a.point.1).b
      = (Polynomial.X - Polynomial.C b.point.1)
        * ((prod.divLin a.point.1).divLin b.point.1).b := by
    show (prod.divLin a.point.1).b
        = (Polynomial.X - Polynomial.C b.point.1)
          * ((prod.divLin a.point.1).b /ₘ (Polynomial.X - Polynomial.C b.point.1))
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h_after_a_at_b.2).symm
  -- combine.a, combine.b in terms of prod.a, prod.b.
  set combine := EagenAccum.combine_higher_distinct E a b h_xx with hcombine_def
  have h_combine_poly_eq : combine.poly = (prod.divLin a.point.1).divLin b.point.1 := by
    show ((mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly).divLin
            a.point.1).divLin b.point.1
        = ((prod.divLin a.point.1).divLin b.point.1)
    rw [hprod_def]
  -- Now combine.eval(x, y) at (x, y).
  -- Goal: ordAt(combine.poly)(x, y) = 0 from non-vanishing.
  have h_x_diff_a : x - a.point.1 ≠ 0 := sub_ne_zero.mpr h_x_ne_a
  have h_x_diff_b : x - b.point.1 ≠ 0 := sub_ne_zero.mpr h_x_ne_b
  -- prod.a.eval x = (x - a.x) * (prod.divLin a.x).a.eval x
  have h_pa_eval : prod.a.eval x
      = (x - a.point.1) * (prod.divLin a.point.1).a.eval x := by
    rw [h_pa_recomp]; simp [Polynomial.eval_mul, Polynomial.eval_sub,
                            Polynomial.eval_X, Polynomial.eval_C]
  have h_pb_eval : prod.b.eval x
      = (x - a.point.1) * (prod.divLin a.point.1).b.eval x := by
    rw [h_pb_recomp]; simp [Polynomial.eval_mul, Polynomial.eval_sub,
                            Polynomial.eval_X, Polynomial.eval_C]
  -- (prod.divLin a.x).a.eval x = (x - b.x) * combine.a.eval x
  have h_da_a_eval : (prod.divLin a.point.1).a.eval x
      = (x - b.point.1) * ((prod.divLin a.point.1).divLin b.point.1).a.eval x := by
    rw [h_div_a_a_recomp]; simp [Polynomial.eval_mul, Polynomial.eval_sub,
                                  Polynomial.eval_X, Polynomial.eval_C]
  have h_da_b_eval : (prod.divLin a.point.1).b.eval x
      = (x - b.point.1) * ((prod.divLin a.point.1).divLin b.point.1).b.eval x := by
    rw [h_div_a_b_recomp]; simp [Polynomial.eval_mul, Polynomial.eval_sub,
                                  Polynomial.eval_X, Polynomial.eval_C]
  -- prod.eval x y = (x - a.x)(x - b.x) · combine.eval x y.
  have h_prod_factored : prod.eval x y
      = (x - a.point.1) * (x - b.point.1) * combine.poly.eval x y := by
    show prod.a.eval x - prod.b.eval x * y
        = (x - a.point.1) * (x - b.point.1) *
          (combine.poly.a.eval x - combine.poly.b.eval x * y)
    rw [h_combine_poly_eq]
    rw [h_pa_eval, h_pb_eval, h_da_a_eval, h_da_b_eval]
    ring
  -- Therefore combine.eval x y ≠ 0.
  have h_combine_eval : combine.poly.eval x y ≠ 0 := by
    intro h_eq
    apply h_prod_pos
    rw [h_prod_factored, h_eq, mul_zero]
  -- Hence divisorOfD combine.poly at affine (x,y) = 0.
  have hns : E.toW.toAffine.Nonsingular x y :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP))
  rw [ECPoint.affine_of_nonsingular E hns]
  show (ordAt E combine.poly (x, y) : ℤ) = 0
  rw [ordAt_eq_zero_of_eval_ne_zero E combine.poly hP h_combine_eval]
  rfl

/-! ### AccInv form of off-support combine identity

When R is off all relevant supports (xs, ys, ±a.lift, ±b.lift,
±combine.lift), both LHS (divisorOfD combine.poly R) and RHS
(formalDivisorOfList (xs++ys) R + residueDivisor combine.lift R)
are zero, matching the AccInv shape. -/

theorem accInv_combine_higher_distinct_divisor_at_off_support_AccInv_form
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    {x y : ZMod E.q} (hP : (x, y) ∈ E.points)
    (h_chord_pos : (chordCoordRingElt E a.point b.point).eval x y ≠ 0)
    (h_a_pos : a.poly.eval x y ≠ 0)
    (h_b_pos : b.poly.eval x y ≠ 0)
    (h_x_ne_a : x ≠ a.point.1) (h_x_ne_b : x ≠ b.point.1)
    (h_x_ne_combine : x ≠ (EagenAccum.combine_higher_distinct E a b h_xx).point.1)
    (h_xy_not_in_xs : (x, y) ∉ xs) (h_xy_not_in_ys : (x, y) ∉ ys) :
    let combine := EagenAccum.combine_higher_distinct E a b h_xx
    ∃ h_combine_pt : combine.point ∈ E.points,
      divisorOfD E combine.poly (ECPoint.affine E x y)
        = formalDivisorOfList E (xs ++ ys) (ECPoint.affine E x y)
          + residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (ECPoint.affine E x y) := by
  classical
  intro combine
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  -- combine.point ∈ E.points.
  obtain ⟨h_combine_pt, _⟩ := combine_higher_distinct_running_sum
    E a b h_a_pt h_b_pt h_xx
  refine ⟨h_combine_pt, ?_⟩
  -- LHS: divisorOfD combine.poly R = 0 via off_support_zero.
  rw [accInv_combine_higher_distinct_divisor_at_off_support_zero (E := E)
        h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
        hP h_chord_pos h_a_pos h_b_pos h_x_ne_a h_x_ne_b]
  -- RHS: formalDivisorOfList (xs++ys) R = 0 (R-affine ∉ xs ∪ ys).
  have h_formal_zero : formalDivisorOfList E (xs ++ ys)
      (ECPoint.affine E x y) = 0 := by
    have hns : E.toW.toAffine.Nonsingular x y :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP))
    rw [ECPoint.affine_of_nonsingular E hns]
    rw [formalDivisorOfList_append, show
      formalDivisorOfList E xs (WeierstrassCurve.Affine.Point.some hns
                                : ECPoint E)
      = ((xs.filter (fun P => P = (x, y))).length : ℤ) from rfl,
      show formalDivisorOfList E ys (WeierstrassCurve.Affine.Point.some hns
                                     : ECPoint E)
      = ((ys.filter (fun P => P = (x, y))).length : ℤ) from rfl]
    have h1 : xs.filter (fun P => P = (x, y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_xy_not_in_xs
      rwa [decide_eq_true_eq.mp heq] at hP_in
    have h2 : ys.filter (fun P => P = (x, y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_xy_not_in_ys
      rwa [decide_eq_true_eq.mp heq] at hP_in
    rw [h1, h2]; simp
  -- RHS: residueDivisor combine.lift R = 0 (R ≠ -combine.lift, R ≠ 0).
  -- The "≠ -combine.lift" follows since x ≠ a.x ≠ b.x but combine.lift's
  -- x-coord is the third intersection x, which isn't a or b. But this
  -- could equal x. Hmm — without more hypotheses, can't conclude. We
  -- need an extra hypothesis.
  -- For now, fall back to assuming R ≠ -combine.lift via
  -- a generic chord-third-intersection mismatch.
  -- Simpler: include `R ≠ ECPoint.affine E x y` as an extra hypothesis.
  -- However, for the off-support purposes, we'd typically also have
  -- (x, y) ∉ {(combine.point.1, combine.point.2)} (i.e. R isn't
  -- the third-intersection-point's negation).
  rw [h_formal_zero, zero_add]
  -- Need: residueDivisor (lift) R = 0.
  -- R ≠ -lift since -lift's x-coord = combine.point.1 (lift = -third pt),
  -- and h_x_ne_combine ensures x ≠ combine.point.1, so R ≠ -lift.
  -- R ≠ 0 since R is affine.
  symm
  apply residueDivisor_at_other
  · -- R ≠ -(combine.lift) = ECPoint.affine combine.point.1 (-combine.point.2).
    intro h_eq
    -- ECPoint.affine x y = -ECPoint.affine combine.point.1 combine.point.2
    --   = ECPoint.affine combine.point.1 (-combine.point.2)
    rw [show -(ECPoint.affineOfMem E h_combine_pt : ECPoint E)
          = ECPoint.affine E combine.point.1 (-combine.point.2) from ?_] at h_eq
    · -- Now (x, y) and (combine.point.1, -combine.point.2) match.
      -- ECPoint.affine equality forces .1 = .1 and .2 = .2, so x = combine.point.1.
      have h_xeq : x = combine.point.1 := by
        have hns_l : E.toW.toAffine.Nonsingular x y :=
          E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP))
        rw [ECPoint.affine_of_nonsingular E hns_l] at h_eq
        have hC_pt : (combine.point.1, -combine.point.2) ∈ E.points := by
          apply E.hComplete
          have hC := E.hOnCurve _ h_combine_pt
          show (-combine.point.2) ^ 2
              = combine.point.1 ^ 3 + E.curveA * combine.point.1 + E.curveB
          rw [neg_pow_two]; exact hC
        have hns_r : E.toW.toAffine.Nonsingular combine.point.1 (-combine.point.2) :=
          E.equation_iff_nonsingular.mp
            ((E.equation_iff _ _).mpr (E.hOnCurve _ hC_pt))
        rw [ECPoint.affine_of_nonsingular E hns_r] at h_eq
        cases h_eq
        rfl
      exact h_x_ne_combine h_xeq
    · -- -ECPoint.affineOfMem combine.point = ECPoint.affine combine.point.1 (-combine.point.2)
      rw [← ECPoint.affine_eq_affineOfMem E h_combine_pt]
      exact ECPoint.affine_neg E combine.point.1 combine.point.2
  · -- R ≠ 0.
    intro h_eq
    have hns : E.toW.toAffine.Nonsingular x y :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hP))
    rw [ECPoint.affine_of_nonsingular E hns] at h_eq
    cases h_eq

/-! ### AccInv form of divisor identity at +combine.lift

R = combine.lift = ECPoint.affine Q₀x (-Q₀y) is NOT in chord's affine
support (chord vanishes only at a, b, Q₀, not at -Q₀). With a.poly,
b.poly nonvanish at -Q₀, the off-support-zero theorem gives LHS = 0.
The RHS = formalDivisor(off-support) + residue(R, S=R, but R ≠ -S
since Q₀y ≠ 0) = 0 + 0 = 0. -/

theorem accInv_combine_higher_distinct_divisor_at_combine_lift_AccInv_form
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_Q₀y_ne_zero : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                      * (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                         - a.point.1 - b.point.1)
                      + (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2
                         * a.point.1)) ≠ 0)
    (h_a_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        a.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_b_at_negQ₀ :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        b.poly.eval Q₀x (-Q₀y) ≠ 0)
    (h_negQ₀_not_in_xs :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        (Q₀x, -Q₀y) ∉ xs)
    (h_negQ₀_not_in_ys :
        let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
        let Q₀x := lam ^ 2 - a.point.1 - b.point.1
        let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
        (Q₀x, -Q₀y) ∉ ys) :
    let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
    let Q₀x := lam ^ 2 - a.point.1 - b.point.1
    let Q₀y := lam * Q₀x + (a.point.2 - lam * a.point.1)
    let combine := EagenAccum.combine_higher_distinct E a b h_xx
    ∃ h_combine_pt : combine.point ∈ E.points,
      divisorOfD E combine.poly (ECPoint.affine E Q₀x (-Q₀y))
        = formalDivisorOfList E (xs ++ ys) (ECPoint.affine E Q₀x (-Q₀y))
          + residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (ECPoint.affine E Q₀x (-Q₀y)) := by
  classical
  intro lam Q₀x Q₀y combine
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  obtain ⟨h_combine_pt, _⟩ := combine_higher_distinct_running_sum
    E a b h_a_pt h_b_pt h_xx
  refine ⟨h_combine_pt, ?_⟩
  -- (Q₀x, Q₀y) ∈ E.points and (Q₀x, -Q₀y) ∈ E.points.
  have hQ₀_on_E : (Q₀x, Q₀y) ∈ E.points := by
    apply E.hComplete
    exact chord_third_point_on_E E a.point b.point h_a_pt h_b_pt h_xx
  have h_negQ₀_on_E : (Q₀x, -Q₀y) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hQ₀_on_E
    show (-Q₀y) ^ 2 = Q₀x ^ 3 + E.curveA * Q₀x + E.curveB
    rw [neg_pow_two]; exact hC
  -- chord at (Q₀x, -Q₀y) ≠ 0.
  have h_chord_neg : (chordCoordRingElt E a.point b.point).eval Q₀x (-Q₀y) ≠ 0 := by
    rw [chordCoordRingElt_eval_at_neg_third E a b h_xx]
    show (-2 : ZMod E.q) * Q₀y ≠ 0
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    exact mul_ne_zero (neg_ne_zero.mpr h2) h_Q₀y_ne_zero
  -- Apply off_support_zero at (Q₀x, -Q₀y).
  rw [accInv_combine_higher_distinct_divisor_at_off_support_zero (E := E)
        h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
        h_negQ₀_on_E h_chord_neg h_a_at_negQ₀ h_b_at_negQ₀
        h_Q₀x_ne_a h_Q₀x_ne_b]
  -- formalDivisorOfList (xs++ys) at (Q₀x, -Q₀y) = 0.
  have hns_neg : E.toW.toAffine.Nonsingular Q₀x (-Q₀y) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_negQ₀_on_E))
  have h_formal_zero : formalDivisorOfList E (xs ++ ys)
      (ECPoint.affine E Q₀x (-Q₀y)) = 0 := by
    rw [ECPoint.affine_of_nonsingular E hns_neg]
    rw [formalDivisorOfList_append, show
      formalDivisorOfList E xs (WeierstrassCurve.Affine.Point.some hns_neg
                                : ECPoint E)
      = ((xs.filter (fun P => P = (Q₀x, -Q₀y))).length : ℤ) from rfl,
      show formalDivisorOfList E ys (WeierstrassCurve.Affine.Point.some hns_neg
                                     : ECPoint E)
      = ((ys.filter (fun P => P = (Q₀x, -Q₀y))).length : ℤ) from rfl]
    have h1 : xs.filter (fun P => P = (Q₀x, -Q₀y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_negQ₀_not_in_xs
      rwa [decide_eq_true_eq.mp heq] at hP_in
    have h2 : ys.filter (fun P => P = (Q₀x, -Q₀y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro P hP_in heq
      apply h_negQ₀_not_in_ys
      rwa [decide_eq_true_eq.mp heq] at hP_in
    rw [h1, h2]; simp
  rw [h_formal_zero, zero_add]
  -- residueDivisor combine.lift R = 0 (R = combine.lift ≠ -combine.lift since Q₀y ≠ 0).
  symm
  apply residueDivisor_at_other
  · -- R ≠ -combine.lift.
    intro h_eq
    rw [show -(ECPoint.affineOfMem E h_combine_pt : ECPoint E)
          = ECPoint.affine E Q₀x Q₀y from ?_] at h_eq
    · rw [ECPoint.affine_of_nonsingular E hns_neg] at h_eq
      have hQ₀ns : E.toW.toAffine.Nonsingular Q₀x Q₀y :=
        E.equation_iff_nonsingular.mp
          ((E.equation_iff _ _).mpr (E.hOnCurve _ hQ₀_on_E))
      rw [ECPoint.affine_of_nonsingular E hQ₀ns] at h_eq
      -- h_eq : .some hns_neg = .some hQ₀ns, forcing -Q₀y = Q₀y.
      injection h_eq with _ h_y_eq
      have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
      apply h_Q₀y_ne_zero
      have : (2 : ZMod E.q) * Q₀y = 0 := by linear_combination -h_y_eq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    · rw [← ECPoint.affine_eq_affineOfMem E h_combine_pt]
      show -(ECPoint.affine E combine.point.1 combine.point.2 : ECPoint E)
          = ECPoint.affine E Q₀x Q₀y
      rw [show combine.point.1 = Q₀x from rfl, show combine.point.2 = -Q₀y from rfl]
      rw [ECPoint.affine_neg E Q₀x (-Q₀y), neg_neg]
  · intro h_eq
    rw [ECPoint.affine_of_nonsingular E hns_neg] at h_eq
    cases h_eq

/-! ### Chord lone-sheet at +a, divisor = 1

Chord through `a.point, b.point` (distinct chord case) vanishes at
+sheet `(a.x, a.y)` (chord-eval-left) and nonvanishes at -sheet
`(a.x, -a.y)` when `a.y ≠ 0` (algebraic computation similar to
chord-eval-at-neg-third). Hence divisorOfD chord (a.lift) = 1. -/

theorem chordCoordRingElt_eval_at_neg_a
    (a b : EagenAccum E)
    (h_xx : a.point.1 ≠ b.point.1) :
    (chordCoordRingElt E a.point b.point).eval a.point.1 (-a.point.2)
      = -2 * a.point.2 := by
  classical
  rw [chordCoordRingElt_eval_eq_lineThrough_chord E h_xx (a.point.1, -a.point.2)]
  unfold Line.eval lineThrough
  show -a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2 * a.point.1
        - (a.point.2 - slopeOf a.point.1 a.point.2 b.point.1 b.point.2 * a.point.1)
      = -2 * a.point.2
  ring

theorem chordCoordRingElt_divisor_at_a_lift_eq_one
    (a b : EagenAccum E)
    (ha : a.point ∈ E.points) (hb : b.point ∈ E.points)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0)
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1) :
    divisorOfD E (chordCoordRingElt E a.point b.point)
      (ECPoint.affine E a.point.1 a.point.2) = 1 := by
  classical
  -- chord vanish at +sheet (a.x, a.y), nonvanish at -sheet (a.x, -a.y).
  have h_chord_at_a : (chordCoordRingElt E a.point b.point).eval a.point.1 a.point.2 = 0 :=
    chordCoordRingElt_eval_left E a.point b.point
  have h_chord_at_neg_a : (chordCoordRingElt E a.point b.point).eval
        a.point.1 (-a.point.2) ≠ 0 := by
    rw [chordCoordRingElt_eval_at_neg_a E a b h_xx]
    show (-2 : ZMod E.q) * a.point.2 ≠ 0
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    exact mul_ne_zero (neg_ne_zero.mpr h2) hY_a
  have h_chord_NZ : ¬ ((chordCoordRingElt E a.point b.point).a = 0
      ∧ (chordCoordRingElt E a.point b.point).b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  -- Apply ordAt_lone_sheet_eq_rootMult_normPoly.
  have h_ordAt :=
    ordAt_lone_sheet_eq_rootMult_normPoly (E := E) h_chord_NZ ha hY_a
      h_chord_at_a h_chord_at_neg_a
  have h_rootMult :=
    chordCoordRingElt_rootMult_normPoly_at_third_eq_one (E := E) a b ha hb h_xx
      h_Q₀x_ne_a h_Q₀x_ne_b
  -- For x = a.point.1 (≠ Q₀x by h_Q₀x_ne_a.symm): rootMult ≤ 1.
  have h_rootMult_a : Polynomial.rootMultiplicity a.point.1
      (normPoly E (chordCoordRingElt E a.point b.point)) = 1 := by
    have h_le := chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord E
      a.point b.point ha hb h_xx h_Q₀x_ne_a.symm h_Q₀x_ne_b.symm a.point.1
    -- chord vanishes at a.lift fiber: normPoly chord (a.x) = chord(a.x, a.y) · chord(a.x, -a.y) = 0.
    have h_normPoly_zero :
        (normPoly E (chordCoordRingElt E a.point b.point)).eval a.point.1 = 0 := by
      rw [normPoly_eval_eq_D_mul_D_neg E (chordCoordRingElt E a.point b.point) ha]
      rw [h_chord_at_a, zero_mul]
    have h_normPoly_NZ : normPoly E (chordCoordRingElt E a.point b.point) ≠ 0 :=
      normPoly_ne_zero E _ h_chord_NZ
    have h_pos : 0 < Polynomial.rootMultiplicity a.point.1
        (normPoly E (chordCoordRingElt E a.point b.point)) :=
      (Polynomial.rootMultiplicity_pos h_normPoly_NZ).mpr h_normPoly_zero
    omega
  have hns : E.toW.toAffine.Nonsingular a.point.1 a.point.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ ha))
  rw [ECPoint.affine_of_nonsingular E hns]
  show (ordAt E (chordCoordRingElt E a.point b.point) (a.point.1, a.point.2) : ℤ) = 1
  rw [h_ordAt, h_rootMult_a]
  rfl

/-! ### Prod divisor splits at affine R when b.poly nonvanish on R fiber

`divisorOfD prod R = div(chord)(R) + div(a.poly)(R) + div(b.poly)(R)`
where prod = chord · a.poly · b.poly. Conditions:
* chord-line additivity applies (h_Q₀x_ne_a, h_Q₀x_ne_b).
* b.poly nonvanish on R's fiber (both sheets). -/

theorem combine_higher_distinct_prod_divisor_split_when_b_nonvanish_fiber
    {a b : EagenAccum E}
    (ha : a.point ∈ E.points) (hb : b.point ∈ E.points)
    (h_xx : a.point.1 ≠ b.point.1)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : a.point.1
        ≠ slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
            - a.point.1 - b.point.1)
    (h_Q₀x_ne_b : b.point.1
        ≠ slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
            - a.point.1 - b.point.1)
    {x y : ZMod E.q} (hP : (x, y) ∈ E.points)
    (h_b_at_pos : b.poly.eval x y ≠ 0)
    (h_b_at_neg : b.poly.eval x (-y) ≠ 0) :
    divisorOfD E
      (mulCoordRingElt E (mulCoordRingElt E (chordCoordRingElt E a.point b.point)
        a.poly) b.poly) (ECPoint.affine E x y)
      = divisorOfD E (chordCoordRingElt E a.point b.point) (ECPoint.affine E x y)
        + divisorOfD E a.poly (ECPoint.affine E x y)
        + divisorOfD E b.poly (ECPoint.affine E x y) := by
  classical
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  -- chord nonzero, mul(chord, a.poly) nonzero.
  have h_chord_NZ : ¬ (chord.a = 0 ∧ chord.b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_chord_a_NZ : ¬ ((mulCoordRingElt E chord a.poly).a = 0
      ∧ (mulCoordRingElt E chord a.poly).b = 0) := by
    intro ⟨ha', hb'⟩
    have hN : normPoly E (mulCoordRingElt E chord a.poly) = 0 := by
      rw [normPoly_eq, ha', hb']; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E chord h_chord_NZ)
      (normPoly_ne_zero E a.poly h_a_poly_NZ)) hN
  -- div(prod) = div(mul(chord, a.poly)) + div(b.poly) via mul-add.
  have h_step1 :
      divisorOfD E (mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly)
          (ECPoint.affine E x y)
        = divisorOfD E (mulCoordRingElt E chord a.poly) (ECPoint.affine E x y)
          + divisorOfD E b.poly (ECPoint.affine E x y) :=
    divisorOfD_mul_add_when_one_factor_nonvanish_fiber E
      h_chord_a_NZ h_b_poly_NZ hP (Or.inr ⟨h_b_at_pos, h_b_at_neg⟩)
  -- div(mul(chord, a.poly)) = div(mul(a.poly, chord)) by comm.
  have h_comm : mulCoordRingElt E chord a.poly = mulCoordRingElt E a.poly chord :=
    mulCoordRingElt_comm E chord a.poly
  -- div(mul(a.poly, chord)) = div(a.poly) + div(chord) via chord-line.
  have h_step2 :
      divisorOfD E (mulCoordRingElt E a.poly chord) (ECPoint.affine E x y)
        = divisorOfD E a.poly (ECPoint.affine E x y)
          + divisorOfD E chord (ECPoint.affine E x y) :=
    divisorOfD_mul_add_by_chordCoordRingElt_distinct E h_a_poly_NZ
      a.point b.point ha hb h_xx h_Q₀x_ne_a h_Q₀x_ne_b _
  rw [h_step1, h_comm, h_step2]
  ring

/-! ### Combine.poly = prod.divLin² applied: divisor relates by two vert subtractions

Two applications of divisorOfD_divLin_subtract give:
  divisorOfD combine.poly R
    = divisorOfD prod R
      - divisorOfD vert(a.x) R - divisorOfD vert(b.x) R. -/

theorem combine_higher_distinct_divisor_via_prod_minus_two_verts
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (R : ECPoint E) :
    divisorOfD E (EagenAccum.combine_higher_distinct E a b h_xx).poly R
      = divisorOfD E (mulCoordRingElt E (mulCoordRingElt E
          (chordCoordRingElt E a.point b.point) a.poly) b.poly) R
        - divisorOfD E ({ a := Polynomial.X - Polynomial.C a.point.1, b := 0 }
                        : CoordRingElt E.q) R
        - divisorOfD E ({ a := Polynomial.X - Polynomial.C b.point.1, b := 0 }
                        : CoordRingElt E.q) R := by
  classical
  set chord := chordCoordRingElt E a.point b.point with hchord_def
  set prod := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly with hprod_def
  -- non-zero predicates.
  have h_chord_NZ : ¬ (chord.a = 0 ∧ chord.b = 0) :=
    chordCoordRingElt_ne_zero E a.point b.point
  have h_chord_a_NZ : ¬ ((mulCoordRingElt E chord a.poly).a = 0
      ∧ (mulCoordRingElt E chord a.poly).b = 0) := by
    intro ⟨ha', hb'⟩
    have hN : normPoly E (mulCoordRingElt E chord a.poly) = 0 := by
      rw [normPoly_eq, ha', hb']; ring
    rw [normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E chord h_chord_NZ)
      (normPoly_ne_zero E a.poly h_a_poly_NZ)) hN
  have h_prod_NZ : ¬ (prod.a = 0 ∧ prod.b = 0) := by
    intro ⟨ha', hb'⟩
    have hN : normPoly E prod = 0 := by rw [normPoly_eq, ha', hb']; ring
    rw [hprod_def, normPoly_mul_eq] at hN
    exact (mul_ne_zero (normPoly_ne_zero E _ h_chord_a_NZ)
      (normPoly_ne_zero E b.poly h_b_poly_NZ)) hN
  -- Divisibility hypotheses.
  have h_prod_at_a := combine_higher_distinct_divisible_at_a (E := E)
    h_acc_a h_xx hY_a h_a_poly_NZ h_b_poly_NZ
  have h_after_a_at_b := combine_higher_distinct_divisible_at_b (E := E)
    h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
  have h_pa_dvd : (Polynomial.X - Polynomial.C a.point.1) ∣ prod.a :=
    Polynomial.dvd_iff_isRoot.mpr h_prod_at_a.1
  have h_pb_dvd : (Polynomial.X - Polynomial.C a.point.1) ∣ prod.b :=
    Polynomial.dvd_iff_isRoot.mpr h_prod_at_a.2
  have h_da_a_dvd : (Polynomial.X - Polynomial.C b.point.1)
      ∣ (prod.divLin a.point.1).a :=
    Polynomial.dvd_iff_isRoot.mpr h_after_a_at_b.1
  have h_da_b_dvd : (Polynomial.X - Polynomial.C b.point.1)
      ∣ (prod.divLin a.point.1).b :=
    Polynomial.dvd_iff_isRoot.mpr h_after_a_at_b.2
  -- Step 1: div(prod.divLin a.x) = div(prod) - div(vert(a.x)).
  have h_step1 := divisorOfD_divLin_subtract (E := E) prod a.point.1
    h_pa_dvd h_pb_dvd h_prod_NZ R
  -- Step 2: div((prod.divLin a.x).divLin b.x) = div(prod.divLin a.x) - div(vert(b.x)).
  have h_after_a_NZ : ¬ ((prod.divLin a.point.1).a = 0
      ∧ (prod.divLin a.point.1).b = 0) :=
    divLin_not_both_zero E prod h_prod_NZ h_prod_at_a.1 h_prod_at_a.2
  have h_step2 := divisorOfD_divLin_subtract (E := E) (prod.divLin a.point.1)
    b.point.1 h_da_a_dvd h_da_b_dvd h_after_a_NZ R
  -- Combine.poly = (prod.divLin a.x).divLin b.x.
  show divisorOfD E ((prod.divLin a.point.1).divLin b.point.1) R
      = divisorOfD E prod R
        - divisorOfD E ({ a := Polynomial.X - Polynomial.C a.point.1, b := 0 }
                        : CoordRingElt E.q) R
        - divisorOfD E ({ a := Polynomial.X - Polynomial.C b.point.1, b := 0 }
                        : CoordRingElt E.q) R
  rw [h_step2, h_step1]

/-! ### Combine step at-a.lift AccInv-form divisor identity

R = a.lift = ECPoint.affine a.x a.y. Under generic hypotheses
(b.poly nonvanish on a fiber, a.lift ≠ -b.lift, a.lift ≠ -combine.lift):

  divisorOfD combine.poly (a.lift)
    = divisorOfD prod (a.lift) - 1 - 0    (via vert(a.x) at a.lift = 1)
    = (1 + div(a.poly)(a.lift) + div(b.poly)(a.lift)) - 1
    = div(a.poly)(a.lift) + div(b.poly)(a.lift)

By AccInv:
  div(a.poly)(a.lift) = formalDivisor xs (a.lift) + 0
  div(b.poly)(a.lift) = formalDivisor ys (a.lift) + 0

So the result equals formalDivisor (xs++ys) (a.lift), and the RHS
residue is 0, matching. -/

theorem accInv_combine_higher_distinct_divisor_at_a_lift_AccInv_form
    {xs ys : List (ZMod E.q × ZMod E.q)} {a b : EagenAccum E}
    (h_acc_a : AccInv E xs a) (h_acc_b : AccInv E ys b)
    (h_xx : a.point.1 ≠ b.point.1)
    (hY_a : a.point.2 ≠ 0) (hY_b : b.point.2 ≠ 0)
    (h_a_poly_NZ : ¬ (a.poly.a = 0 ∧ a.poly.b = 0))
    (h_b_poly_NZ : ¬ (b.poly.a = 0 ∧ b.poly.b = 0))
    (h_Q₀x_ne_a : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ a.point.1)
    (h_Q₀x_ne_b : (slopeOf a.point.1 a.point.2 b.point.1 b.point.2 ^ 2
                    - a.point.1 - b.point.1) ≠ b.point.1)
    (h_b_at_a : b.poly.eval a.point.1 a.point.2 ≠ 0)
    (h_b_at_neg_a : b.poly.eval a.point.1 (-a.point.2) ≠ 0)
    (h_a_lift_ne_neg_b_lift :
        ECPoint.affineOfMem E h_acc_a.1
          ≠ -(ECPoint.affineOfMem E h_acc_b.1 : ECPoint E))
    (h_a_lift_ne_neg_combine_lift :
        ECPoint.affineOfMem E h_acc_a.1
          ≠ -(ECPoint.affineOfMem E
              (combine_higher_distinct_running_sum E a b
                  h_acc_a.1 h_acc_b.1 h_xx).choose : ECPoint E)) :
    let combine := EagenAccum.combine_higher_distinct E a b h_xx
    ∃ h_combine_pt : combine.point ∈ E.points,
      divisorOfD E combine.poly (ECPoint.affine E a.point.1 a.point.2)
        = formalDivisorOfList E (xs ++ ys) (ECPoint.affine E a.point.1 a.point.2)
          + residueDivisor E (ECPoint.affineOfMem E h_combine_pt)
              (ECPoint.affine E a.point.1 a.point.2) := by
  classical
  intro combine
  have h_a_pt : a.point ∈ E.points := h_acc_a.1
  have h_b_pt : b.point ∈ E.points := h_acc_b.1
  obtain ⟨h_combine_pt, _⟩ := combine_higher_distinct_running_sum
    E a b h_a_pt h_b_pt h_xx
  refine ⟨h_combine_pt, ?_⟩
  -- a.lift ≠ 0.
  have h_a_lift_ne_zero :
      (ECPoint.affineOfMem E h_a_pt : ECPoint E) ≠ 0 := by
    intro h_eq
    unfold ECPoint.affineOfMem ECPoint.affineOfEqn at h_eq
    cases h_eq
  -- a.lift ≠ -a.lift (since y ≠ 0, char ≠ 2).
  have hns_a : E.toW.toAffine.Nonsingular a.point.1 a.point.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_a_pt))
  -- Express R via affine_of_nonsingular.
  have h_R_eq : (ECPoint.affine E a.point.1 a.point.2 : ECPoint E)
      = ECPoint.affineOfMem E h_a_pt := ECPoint.affine_eq_affineOfMem E h_a_pt
  -- Use the universal divLin double-subtract.
  rw [combine_higher_distinct_divisor_via_prod_minus_two_verts (E := E)
        h_acc_a h_acc_b h_xx hY_a hY_b h_a_poly_NZ h_b_poly_NZ
        (ECPoint.affine E a.point.1 a.point.2)]
  -- Use the prod_split helper for divisorOfD prod (a.lift).
  rw [combine_higher_distinct_prod_divisor_split_when_b_nonvanish_fiber (E := E)
        h_a_pt h_b_pt h_xx h_a_poly_NZ h_b_poly_NZ
        h_Q₀x_ne_a.symm h_Q₀x_ne_b.symm
        (E.hComplete _ _ ((E.equation_iff _ _).mp
          ((E.equation_iff_nonsingular).mpr hns_a)))
        h_b_at_a h_b_at_neg_a]
  -- Compute divisor of chord at a.lift = 1.
  rw [chordCoordRingElt_divisor_at_a_lift_eq_one E a b h_a_pt h_b_pt h_xx hY_a
        h_Q₀x_ne_a h_Q₀x_ne_b]
  -- Compute divisor of vert(a.x) at a.lift = 1.
  rw [divisorOfD_vertical_at_x₀_nonTwoTorsion_affine E a.point.1 a.point.2
        h_a_pt hY_a]
  -- Compute divisor of vert(b.x) at a.lift = 0 (a.x ≠ b.x).
  rw [divisorOfD_vertical_at_off_x₀_affine E b.point.1 h_a_pt h_xx]
  -- Replace divisorOfD a.poly (a.lift), b.poly (a.lift) via AccInv.
  obtain ⟨_, _, h_div_a⟩ := h_acc_a
  obtain ⟨_, _, h_div_b⟩ := h_acc_b
  rw [show (ECPoint.affine E a.point.1 a.point.2 : ECPoint E)
        = ECPoint.affineOfMem E h_a_pt from h_R_eq]
  rw [h_div_a (ECPoint.affineOfMem E h_a_pt)]
  rw [h_div_b (ECPoint.affineOfMem E h_a_pt)]
  -- residueDivisor a.lift (a.lift) = 0 (a.lift ≠ -a.lift, a.lift ≠ 0).
  have h_a_ne_neg_a : (ECPoint.affineOfMem E h_a_pt : ECPoint E)
      ≠ -(ECPoint.affineOfMem E h_a_pt : ECPoint E) := by
    -- -a.lift = ECPoint.affine a.x (-a.y). Equal to a.lift iff y = -y iff y = 0.
    rw [← ECPoint.affine_eq_affineOfMem E h_a_pt]
    rw [show -(ECPoint.affine E a.point.1 a.point.2 : ECPoint E)
          = ECPoint.affine E a.point.1 (-a.point.2) from
        ECPoint.affine_neg E a.point.1 a.point.2]
    intro h_eq
    rw [ECPoint.affine_of_nonsingular E hns_a] at h_eq
    have h_neg_a_pt : (a.point.1, -a.point.2) ∈ E.points := by
      apply E.hComplete
      have hC := E.hOnCurve _ h_a_pt
      show (-a.point.2) ^ 2 = a.point.1 ^ 3 + E.curveA * a.point.1 + E.curveB
      rw [neg_pow_two]; exact hC
    have hns_neg_a : E.toW.toAffine.Nonsingular a.point.1 (-a.point.2) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_neg_a_pt))
    rw [ECPoint.affine_of_nonsingular E hns_neg_a] at h_eq
    injection h_eq with _ h_y_eq
    have h2 : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    apply hY_a
    have : (2 : ZMod E.q) * a.point.2 = 0 := by linear_combination h_y_eq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  have h_residue_a_at_a : residueDivisor E (ECPoint.affineOfMem E h_a_pt)
        (ECPoint.affineOfMem E h_a_pt) = 0 :=
    residueDivisor_at_other E _ _ h_a_ne_neg_a h_a_lift_ne_zero
  rw [h_residue_a_at_a]
  -- residueDivisor b.lift (a.lift) = 0 (a.lift ≠ -b.lift, a.lift ≠ 0).
  have h_residue_b_at_a : residueDivisor E (ECPoint.affineOfMem E h_b_pt)
        (ECPoint.affineOfMem E h_a_pt) = 0 :=
    residueDivisor_at_other E _ _ h_a_lift_ne_neg_b_lift h_a_lift_ne_zero
  rw [h_residue_b_at_a]
  -- residueDivisor combine.lift (a.lift) = 0.
  have h_residue_combine_at_a : residueDivisor E
        (ECPoint.affineOfMem E h_combine_pt) (ECPoint.affineOfMem E h_a_pt) = 0 :=
    residueDivisor_at_other E _ _
      (by convert h_a_lift_ne_neg_combine_lift using 2)
      h_a_lift_ne_zero
  rw [h_residue_combine_at_a, add_zero]
  -- formalDivisorOfList (xs ++ ys) at affine (a.x, a.y) = formal_xs + formal_ys.
  rw [formalDivisorOfList_append]
  ring

/-! ## General-k correctness: status

Progress so far:

* `residueDivisor`, `formalDivisorOfList` definitions ✓
* `AccInv` invariant for non-degenerate accumulators ✓
* `TerminalInv` invariant for sum-zero (terminal) accumulators ✓
* Helper lemmas (`residueDivisor_at_*`, `formalDivisorOfList_at_*`) ✓
* `formalDivisorOfList_append` ✓
* `accInv_level0_chord_running_sum` ✓
* `accInv_level0_chord_divisor_identity_at_{infinity, P, Q, A₂, off_support}` ✓
* `accInv_level0_chord_divisor_identity` (universal ∀ R) ✓
* `accInv_level0_chord_case` (full level-0 chord AccInv) ✓
* `terminalInv_vertical_at_{infinity, off_x₀, P, negP}` ✓
* `terminalInv_level0_vertical_case` (full TerminalInv for `(P, -P)`) ✓
* `accInv_poly_vanishes_at_neg_point` (AccInv ⟹ a.poly vanishes at -a) ✓
* `combine_higher_distinct_divisible_at_a` (X-a.x divides chord·a·b) ✓
* `combine_higher_distinct_prod_vanish_at_b` (chord·a·b vanishes at ±b) ✓
* `combine_higher_distinct_divisible_at_b` (X-b.x divides after-divLin-a) ✓
* `combine_higher_distinct_running_sum` ✓
* `accInv_natDegree_normPoly` (AccInv ⟹ natDeg(normPoly a.poly) = xs.length+1) ✓
* `accInv_combine_higher_distinct_divisor_at_infinity` (raw + AccInv form) ✓
* `combine_higher_distinct_prod_eval_factor` (prod.eval = (X-a.x)(X-b.x)·combine.eval) ✓
* `combine_higher_distinct_eval_third_zero` ✓
* `chordCoordRingElt_eval_at_neg_third` ✓
* `combine_higher_distinct_eval_neg_third_nonzero` ✓
* `chordCoordRingElt_rootMult_normPoly_at_third_eq_one` ✓
* `ordAt_lone_sheet_eq_rootMult_normPoly` ✓
* `accInv_combine_higher_distinct_divisor_at_third_intersection` ✓
* `accInv_combine_higher_distinct_divisor_at_third_AccInv_form` ✓
* `combine_higher_distinct_rootMult_normPoly_at_third_eq_one` ✓
* `rootMult_normPoly_eq_zero_of_fiber_nonvanish` ✓
* `accInv_combine_higher_distinct_divisor_at_off_support_zero` ✓
* `accInv_combine_higher_distinct_divisor_at_off_support_AccInv_form` ✓
* `accInv_combine_higher_distinct_divisor_at_combine_lift_AccInv_form` ✓
* `chordCoordRingElt_eval_at_neg_a` ✓
* `chordCoordRingElt_divisor_at_a_lift_eq_one` ✓

## Next: at-a.lift case (ready for assembly)

Building blocks now in place for `divisorOfD combine.poly (a.lift) = ...`:
* chord_divisor_at_a_lift = 1 (chord-line additivity, lone-sheet at +a).
* a.poly's divisor at a.lift via AccInv: count(xs, a.point) (since
  residue is at -a.lift, contributes 0 at +a.lift).
* b.poly's divisor via AccInv: count(ys, a.point) (with a.lift ≠ -b.lift).
* div(vert(a.x))(a.lift) = 1 via `divisorOfD_vertical_at_x₀_nonTwoTorsion_affine`.
* div(vert(b.x))(a.lift) = 0 via `divisorOfD_vertical_at_off_x₀_affine`.
* mul-add for prod = b.poly·(chord·a.poly): need b.poly nonvanish on
  a fiber (genericity hypothesis); apply
  `divisorOfD_mul_add_when_one_factor_nonvanish_fiber`.
* div(chord·a.poly) = div(a.poly·chord) by mulCoordRingElt_comm, then
  `divisorOfD_mul_add_by_chordCoordRingElt_distinct`.

Final equation at a.lift:
  div(combine.poly)(a.lift)
    = (div(chord) + div(a.poly) + div(b.poly))(a.lift) - 1 - 0
    = (1 + count(xs, a) + count(ys, a)) - 1
    = count(xs, a) + count(ys, a)
    = formalDivisor(xs++ys)(a.lift)

residueDivisor(combine.lift)(a.lift) = 0 (assuming a.lift ≠ -combine.lift,
i.e. 2a + b ≠ 0 in EC group).

Symmetric at -a.lift, b.lift, -b.lift cases follow same pattern.

## Cross-case wall (combine-step pointwise mul-additivity)

The remaining piece for `accInv_combine_higher_distinct_step` is the
pointwise divisor identity at every R. The clean route via existing
`divisorOfD_mul_add_when_chord_line_D2` (chord-line additivity) lets
us peel off the outer chord, leaving:
  `div(a.poly · b.poly) at R = div(a.poly) at R + div(b.poly) at R`.

This is *the* cross case: at R = a.lift, a.poly is lone-sheet at -a
(via AccInv residue), and b.poly may be lone-sheet at +a (depending on
whether xs/ys carry a.point). When neither factor is a chord-line and
neither has rootMult ≤ 1 globally, no existing additivity lemma applies.

**Strategy options (Codex consultation 2026-05-05):**
1. Build a local valuation v_P on F_q(E) and prove agreement with the
   recursive `ordAt`. Long local-ring project (~500+ LOC).
2. Strengthen `AccInv` to track that the accumulator's polynomial has
   normPoly rootMult ≤ 1 globally. *Counterexample*: combine of two
   level-1 polys produces rootMult 2-3 at A₂.x and at residue x's,
   so this invariant doesn't propagate.
3. Strengthen `AccInv` further with a *support-disjointness* invariant
   between accumulators in a level (so combine never multiplies two
   factors that vanish on overlapping fibers). Eagen's algorithm
   maintains this naturally if input list has all distinct points.
   Tracking it requires substantial bookkeeping.

For now, level-0 (length-4 simple) is fully constructive (see
`Divisor/Soundness.lean:ma_completeness_for_length4Simple`). General-k
correctness is deferred multi-firing work.

Remaining (multi-firing):

* `accInv_singleton_carry`: odd-length carry needs special handling (the
  carried point isn't yet absorbed; subtle).
* `accInv_combine_higher_distinct_step`: AccInv preserved on append for
  the chord combine. Algebraic skeleton:
  ```
  div(combine(a, b)) = div(chord_ab) + div(a.poly) + div(b.poly)
                       - div(vert(a.point.1)) - div(vert(b.point.1))
                     = formalDivisor(xs ++ ys) + residue(a.point + b.point)
  ```
  Key structural observation for divLin divisibility:
  the outer chord(a.point, b.point) vanishes at a.point (so
  chord · a.poly · b.poly vanishes at sheet (a.x, a.y));
  separately a.poly vanishes at -a.point via its AccInv-tracked residue
  (so chord · a.poly · b.poly vanishes at sheet (a.x, -a.y));
  hence (X - a.x) | both .a and .b of the product, allowing divLin a.x.
  Symmetric argument for divLin b.x. Once divisibility is established,
  the divisor identity reduces to algebra via existing
  `divisorOfD_divLin_subtract` + `divisorOfD_mul_vertical_add`.
* `terminalInv_combine_higher_vertical_step`: TerminalInv for sum-zero
  combine (when a.point + b.point = O).
* `eagenBuild_correctness`: ∀ sum-zero `Ps`, `divisorOfD (eagenBuild Ps) =
  formalDivisor Ps`. -/

/-! ## Length-4 reduction (deferred)

For length-4 sum-zero distinct inputs, the recursive `eagenBuild`
produces the same polynomial as `eagenBuild_length4_explicit`. The
proof requires careful unfolding of the recursive structure and
matching against the explicit length-4 formula. Substantial bookkeeping
deferred to subsequent firings. -/

/-! ## `IsHonestForExplicit` predicate (any-k completeness path)

After strengthening `MAProverMsg.isHonestFor` (in `Protocol.lean`) to
include the extensional divisor identity and the on-curve invariants,
`IsHonestForExplicit` is now a definitional alias of `isHonestFor`.
Existing call sites that destructure `IsHonestForExplicit` as
`(isHonestFor) ∧ (divisor identity)` continue to work via the
projections: `.1` is scalar reduction, `.2.1` is `IsPrincipal`,
`.2.2.1` is the divisor identity, `.2.2.2.1` and `.2.2.2.2` are the
on-curve invariants. -/

def MAProverMsg.IsHonestForExplicit (E : ECSetup) (msg : MAProverMsg E.q)
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hkm : stmt.k = msg.k) : Prop :=
  msg.isHonestFor E stmt wit hk hkm

/-! ## General hQline derivation from `hGood`

For any nonzero D, if `(A_0, A_1) ∉ badChallengesCompleteness E D`, then
the chord through `A_0, A_1` doesn't pass through any zero of D.

Proof: Bezout — chord intersects E in `{A_0, A_1, A_2}`. Any zero of
D on E that's also on the chord must be in this set, but `¬bad` excludes
D vanishing at A_0, A_1, or A_2. -/

theorem hQline_of_hGood_general
    {D : CoordRingElt E.q} (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {A₀ A₁ : ZMod E.q × ZMod E.q}
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E D) :
    ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 := by
  classical
  intro Q hQzeros
  -- Q ∈ zerosFinset E D = E.points.filter (D.eval = 0).
  unfold zerosFinset zeros at hQzeros
  rw [Finset.mem_filter] at hQzeros
  obtain ⟨hQE, hQzero⟩ := hQzeros
  intro hChord
  -- By chord_line_support_in_E (Bezout), Q ∈ {A_0, A_1, A_2}.
  have hQ_in_chord : Q = A₀ ∨ Q = A₁ ∨
      Q = (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
           slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
           (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) :=
    chord_line_support_in_E E A₀ A₁ hA₀ hA₁ hNV Q hQE hChord
  -- ¬bad: D doesn't vanish at A_0, A_1, A_2.
  have hMem : (A₀, A₁) ∈ E.points ×ˢ E.points := Finset.mk_mem_product hA₀ hA₁
  have h_unbad : ¬ badPairCompletenessPred E D (A₀, A₁) := fun hbad =>
    hGood (Finset.mem_filter.mpr ⟨hMem, hbad⟩)
  have hThirdEq : thirdPoint E A₀ A₁ =
      some (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
            slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
            (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) := by
    unfold thirdPoint
    rw [if_neg hNV]
    rfl
  rcases hQ_in_chord with hQ | hQ | hQ
  · -- Q = A_0: D(A_0) = 0 contradicts ¬bad.
    apply h_unbad
    exact Or.inl (by rw [← hQ]; exact hQzero)
  · -- Q = A_1.
    apply h_unbad
    exact Or.inr (Or.inl (by rw [← hQ]; exact hQzero))
  · -- Q = A_2.
    apply h_unbad
    refine Or.inr (Or.inr (Or.inl ?_))
    show (match thirdPoint E (A₀, A₁).1 (A₀, A₁).2 with
      | none => True
      | some (x, y) => D.eval x y = 0)
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq]
    rw [← hQ]; exact hQzero

/-! ## Any-k bridge: `logDerivCheckFn = 0` for any honest D with explicit hypotheses

Takes a generic msg with `IsHonestForExplicit` plus the splitsOnE,
hAccount, and residue-match side conditions (protocol- and D-specific).
Produces logDerivCheckFn = 0.

For length-4 simple, all these can be discharged via length-4 work.
For general k, the user provides them (e.g., via recursive eagenBuild). -/

theorem logDerivCheckFn_zero_via_isHonestForExplicit_with_sides
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD)
    (hResidueMatch :
      (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2))⁻¹
          + (Finset.univ : Finset (Fin stmt.k)).sum
              (fun j => msg.m (hkm ▸ j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (stmt.bases j).1
                  (stmt.bases j).2)⁻¹)) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 := by
  classical
  -- β_fun = ordAt = betaTrue (definitional).
  have hβsup : ∀ Q, ordAt E msg.toD Q ≠ 0 →
      Q ∈ E.points ∧ msg.toD.eval Q.1 Q.2 = 0 :=
    betaTrue_support E msg.toD hD
  have hβcov : ∀ Q ∈ E.points, msg.toD.eval Q.1 Q.2 = 0 →
      ordAt E msg.toD Q ≠ 0 := by
    intro Q hQE hQeval
    have h_pos : 0 < ordAt E msg.toD Q := (ordAt_pos_iff_zero E msg.toD hD Q hQE).mpr hQeval
    omega
  have hβtrue : ∀ Q, ordAt E msg.toD Q = betaTrue E msg.toD hD Q := fun _ => rfl
  -- hQline from general lemma.
  have hQline := hQline_of_hGood_general E hD hA₀ hA₁ hNV hGood
  -- hDen from general lemma (in LogDerivEagenLength4).
  have hDen := hDen_of_hGood E msg.toD A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply logDerivCheckFn_zero_of_explicit_divisor_data.
  exact logDerivCheckFn_zero_of_explicit_divisor_data E msg.toD stmt.target
    stmt.bases (fun i => msg.m (hkm ▸ i)) (ordAt E msg.toD)
    hD hSplit hβsup hβcov hAccount hβtrue
    A₀ A₁ hA₀ hA₁ hNV hGood hQline hDen hResidueMatch

/-! ## Any-k MA completeness via IsHonestForExplicit + side conditions

This is the any-k analog of `ma_completeness_via_isHonestForLength4Simple`.
Takes the protocol-level side conditions (splitsOnE, hAccount, residue
match) as user-provided hypotheses. -/

theorem ma_completeness_via_isHonestForExplicit_with_sides
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hResidueMatchAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      (A₀, A₁) ∉ badChallengesCompleteness E msg.toD →
      (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2))⁻¹
          + (Finset.univ : Finset (Fin stmt.k)).sum
              (fun j => msg.m (hkm ▸ j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (stmt.bases j).1
                  (stmt.bases j).2)⁻¹)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  apply ma_completeness_parameterized E stmt msg hkm hDegK hAdm
  intro A₀ A₁ hA₀ hA₁ hGood
  have hNV : A₀.1 ≠ A₁.1 := hNV_of_hGood E hA₀ hA₁ hGood
  exact logDerivCheckFn_zero_via_isHonestForExplicit_with_sides E
    stmt wit hk msg hkm h_honest hD hSplit hAccount A₀ A₁ hA₀ hA₁ hNV hGood
    (hResidueMatchAll A₀ A₁ hA₀ hA₁ hNV hGood)

/-! ## Padding lemma: extend zerosFinset sum to E.points

For any function f, the sum `∑ Q ∈ zerosFinset E D, ordAt(Q) * f(Q)` equals
`∑ Q ∈ E.points, ordAt(Q) * f(Q)`, since ordAt is zero outside zerosFinset
on E.points. -/

theorem ordAt_sum_extend_to_E_points
    {D : CoordRingElt E.q} (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E D, (ordAt E D Q : ZMod E.q) * f Q)
      = ∑ Q ∈ E.points, (ordAt E D Q : ZMod E.q) * f Q := by
  classical
  -- zerosFinset = E.points.filter (D.eval = 0).
  have hSub : zerosFinset E D ⊆ E.points := by
    unfold zerosFinset zeros; exact Finset.filter_subset _ _
  -- Off zerosFinset, ordAt = 0.
  rw [← Finset.sum_subset hSub]
  intro Q hQE hQnZ
  -- Q ∈ E.points, Q ∉ zerosFinset → D.eval Q ≠ 0 → ordAt Q = 0.
  have hQnZ' : ¬ (D.eval Q.1 Q.2 = 0) := by
    intro h; apply hQnZ
    unfold zerosFinset zeros
    rw [Finset.mem_filter]
    exact ⟨hQE, h⟩
  have h_ord : ordAt E D Q = 0 := by
    by_contra h
    apply hQnZ'
    exact (ordAt_pos_iff_zero E D hD Q hQE).mp (Nat.pos_of_ne_zero h)
  rw [h_ord]
  push_cast
  ring

/-! ## ordAt-to-honestDivisorCoeffs conversion at affine points

When `divisorOfD msg.toD = honestDivisorCoeffs`, the relationship at
affine points is `(ordAt msg.toD Q : ℤ) = honestDivisorCoeffs(affine Q)`. -/

theorem ordAt_eq_honestDivisorCoeffs_at_affine
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    (ordAt E msg.toD Q : ℤ)
      = honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) := by
  have h := h_div (ECPoint.affine E Q.1 Q.2)
  rw [show divisorOfD E msg.toD (ECPoint.affine E Q.1 Q.2)
      = (ordAtPoint E msg.toD (ECPoint.affine E Q.1 Q.2) : ℤ) from ?_,
      ordAtPoint_affine E _ hQ] at h
  · exact h
  · rw [ECPoint.affine_of_nonsingular E
          (E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ)))]
    rfl

/-! ## ZMod-cast of the affine bridge

In ZMod E.q: `(ordAt : ZMod) = (honestDivisorCoeffs : ZMod)` at affine points,
via the ℤ→ZMod cast. -/

theorem ordAt_cast_eq_honestDivisorCoeffs_cast_at_affine
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ((ordAt E msg.toD Q : ℤ) : ZMod E.q)
      = ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
          : ZMod E.q) := by
  rw [ordAt_eq_honestDivisorCoeffs_at_affine E stmt wit hk msg h_div hQ]

/-! ## Residue match identity from divisor identity

Combines the padding lemma and affine-bridge to derive the residue-sum
identity from `IsHonestForExplicit`. -/

theorem residue_sum_eq_honest_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) * f Q)
      = ∑ Q ∈ E.points,
          ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
            : ZMod E.q) * f Q := by
  classical
  rw [ordAt_sum_extend_to_E_points E hD f]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [show ((ordAt E msg.toD Q : ZMod E.q))
      = ((ordAt E msg.toD Q : ℤ) : ZMod E.q) from by push_cast; rfl]
  rw [ordAt_cast_eq_honestDivisorCoeffs_cast_at_affine E stmt wit hk msg h_div hQ]

/-! ## honestDivisorCoeffs unfolding at affine

The honest divisor coefficient at an affine point splits into:
* An indicator `(if (x,y) = -P_target then 1 else 0)`.
* A bases-sum `Σ_{i: bases i = (x,y)} scalars i`.

Sum over E.points + L-evaluation produces the protocol RHS form. -/

theorem honestDivisorCoeffs_at_affine_split
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2)
      = (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
          (fun i => stmt.bases i = Q),
          (wit.scalars (hk ▸ i) : ℤ) := by
  rw [ECPoint.affine_of_nonsingular E
        (E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ)))]
  rcases Q with ⟨x, y⟩
  rfl

/-! ## Indicator-term reduction

The "indicator" component of `honestDivisorCoeffs` (the `(if (x,y) = -P_target then 1 else 0)`
term), summed over E.points and weighted by L(Q)^{-1}, reduces to `L(-P_target)^{-1}`. -/

theorem indicator_sum_eq_eval_at_negTarget
    (target : ZMod E.q × ZMod E.q) (h_negT : (target.1, -target.2) ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ E.points,
        ((if Q = (target.1, -target.2) then (1 : ℤ) else 0) : ZMod E.q) * f Q)
      = f (target.1, -target.2) := by
  classical
  rw [Finset.sum_eq_single (target.1, -target.2)]
  · simp
  · intro b _ hb
    rw [if_neg hb]
    push_cast
    ring
  · intro h
    exact absurd h_negT h

/-! ## Bases-term reduction

The "bases-sum" component of `honestDivisorCoeffs`, summed over E.points
and weighted by L(Q)^{-1}, reduces to `∑_i (scalars i) · L(bases i)^{-1}`.
Requires bases i ∈ E.points for all i. -/

theorem bases_sum_eq_index_sum
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ E.points, ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
      (fun i => stmt.bases i = Q), (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q)
      = (Finset.univ : Finset (Fin stmt.k)).sum
          (fun i => ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) * f (stmt.bases i)) := by
  classical
  -- Convert the inner filter-sum to an indicator sum.
  rw [show (∑ Q ∈ E.points, ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
    (fun i => stmt.bases i = Q), (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q)
    = (∑ Q ∈ E.points, ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)),
        ((if stmt.bases i = Q then (wit.scalars (hk ▸ i) : ℤ) else 0) : ZMod E.q) * f Q) from by
    apply Finset.sum_congr rfl
    intro Q _
    rw [Finset.sum_filter]
    push_cast
    rw [Finset.sum_mul]]
  -- Swap the sums (inner is now Q-dependent only via the if-branch, but the index set is fixed).
  rw [Finset.sum_comm]
  -- Now: ∑_i ∑_Q (if bases i = Q then scalars i else 0 : ZMod) · f Q.
  apply Finset.sum_congr rfl
  intro i _
  -- For each i, only Q = bases i contributes.
  rw [Finset.sum_eq_single (stmt.bases i)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    push_cast
    ring
  · intro h
    exact absurd (h_bases i) h

/-! ## Full residue-match derivation from IsHonestForExplicit

Combine the helpers to produce `hResidueMatchAll` from divisor identity.

For honest msg with `IsHonestForExplicit`, plus the assumption that
`-P_target ∈ E.points` and all `bases ∈ E.points`, the residue sum equals
the protocol RHS. -/

theorem hResidueMatch_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) * f Q)
      = f (stmt.target.1, -stmt.target.2)
        + (Finset.univ : Finset (Fin stmt.k)).sum
            (fun i => ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) * f (stmt.bases i)) := by
  classical
  have h_div := h_honest.2.2.1
  -- Step 1: convert to honestDivisorCoeffs sum over E.points.
  rw [residue_sum_eq_honest_via_isHonestForExplicit E stmt wit hk msg h_div hD f]
  -- Step 2: split honestDivisorCoeffs into indicator + bases-sum.
  rw [show (∑ Q ∈ E.points,
        ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
          : ZMod E.q) * f Q)
      = (∑ Q ∈ E.points,
          (((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
             ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
               (fun i => stmt.bases i = Q),
               (wit.scalars (hk ▸ i) : ℤ) : ℤ) : ZMod E.q) * f Q) from by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [honestDivisorCoeffs_at_affine_split E stmt wit hk msg hQ]]
  -- Step 3: distribute the addition.
  rw [show (∑ Q ∈ E.points,
        ((((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
           ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
             (fun i => stmt.bases i = Q),
             (wit.scalars (hk ▸ i) : ℤ)) : ℤ) : ZMod E.q) * f Q)
      = (∑ Q ∈ E.points,
            ((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) : ZMod E.q) * f Q)
        + (∑ Q ∈ E.points,
            ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
              (fun i => stmt.bases i = Q),
              (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q) from by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    push_cast
    ring]
  -- Step 4: apply the indicator and bases lemmas.
  rw [indicator_sum_eq_eval_at_negTarget E stmt.target h_negT f]
  rw [bases_sum_eq_index_sum E stmt wit hk h_bases f]

/-! ## Tighter any-k MA completeness: hResidueMatchAll discharged

Same as `ma_completeness_via_isHonestForExplicit_with_sides` but with
`hResidueMatchAll` discharged automatically from `IsHonestForExplicit`. -/

theorem ma_completeness_via_isHonestForExplicit_no_residue_match
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (h_m_eq_scalars : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q))
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  apply ma_completeness_via_isHonestForExplicit_with_sides E stmt wit hk msg hkm
    h_honest hD hSplit hAccount hDegK hAdm
  intro A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply hResidueMatch_via_isHonestForExplicit with f = L^{-1}.
  rw [hResidueMatch_via_isHonestForExplicit E stmt wit hk msg hkm h_honest hD
      h_negT h_bases (fun Q => ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)]
  -- Now we need: f(-target) + Σ_i (scalars : ZMod) · f(bases i) = ((lineThrough.eval target.1 (-target.2))⁻¹) + Σ_j m_j · ...
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h_m_eq_scalars i]

/-! ## hAccount from splitsOnE (existing infrastructure wrapper)

Wrapper around `sum_ordAt_eq_natDegree_under_split` for ergonomic use. -/

theorem hAccount_of_splitsOnE
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D) :
    (∑ Q ∈ E.points, ordAt E D Q) = (normPoly E D).natDegree :=
  sum_ordAt_eq_natDegree_under_split E D hD hSplit

/-! ## Tighter any-k completeness with hAccount discharged

If splitsOnE D, then hAccount is automatic. Combined with the residue
match discharge, we now only need splitsOnE as a side condition. -/

theorem ma_completeness_via_isHonestForExplicit_splitsOnE_only
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  apply ma_completeness_via_isHonestForExplicit_no_residue_match E stmt wit hk msg hkm
    h_honest hD hSplit
  · exact hAccount_of_splitsOnE E msg.toD hD hSplit
  · exact h_negT
  · exact h_bases
  · exact h_honest.1
  · exact hDegK
  · exact hAdm

/-! ## Sum of ordAt as ℤ via divisor identity

Cast the natural-number `∑ ordAt` to ℤ, using `divisorOfD = honestDivisorCoeffs`. -/

theorem ordAt_sum_eq_honestDivisorCoeffs_sum_at_affines
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R) :
    ((∑ Q ∈ E.points, ordAt E msg.toD Q : ℕ) : ℤ)
      = ∑ Q ∈ E.points,
          honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) := by
  push_cast
  apply Finset.sum_congr rfl
  intro Q hQ
  exact ordAt_eq_honestDivisorCoeffs_at_affine E stmt wit hk msg h_div hQ

/-! ## honestDivisorCoeffs at infinity

The infinity coefficient of `honestDivisorCoeffs` is `-degE(msg.toD)`,
directly from the definition. -/

theorem honestDivisorCoeffs_at_infinity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) :
    honestDivisorCoeffs E stmt wit hk msg (0 : ECPoint E) = -(msg.toD.degE : ℤ) := rfl

/-! ## honestDivisorCoeffs has finite support (via divisor identity)

By divisor identity, honestDivisorCoeffs equals the finitely-supported
divisorOfD, hence is also finitely supported. -/

theorem honestDivisorCoeffs_finiteSupport_of_divisor_identity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R) :
    Set.Finite (Function.support (honestDivisorCoeffs E stmt wit hk msg)) := by
  have h_eq : honestDivisorCoeffs E stmt wit hk msg = divisorOfD E msg.toD := by
    funext R
    exact (h_div R).symm
  rw [h_eq]
  exact divisorOfD_finiteSupport E msg.toD

/-! ## Deg-zero from IsPrincipal (via principal_divisor_iff)

Combines `IsPrincipal honestDivisorCoeffs` (from `isHonestFor`) with
`principal_divisor_iff` to extract the degree-zero condition. -/

theorem honestDivisorCoeffs_deg_zero_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    ∃ hFinSupp : Set.Finite (Function.support
        (honestDivisorCoeffs E stmt wit hk msg)),
      ∑ P ∈ hFinSupp.toFinset, honestDivisorCoeffs E stmt wit hk msg P = 0 := by
  have hFin := honestDivisorCoeffs_finiteSupport_of_divisor_identity E
    stmt wit hk msg h_honest.2.2.1
  have hIsP : IsPrincipal E (honestDivisorCoeffs E stmt wit hk msg) := h_honest.2.1
  exact ⟨hFin, ((principal_divisor_iff E _ hFin).mp hIsP).1⟩

/-! ## ECPoint.some-to-affinePoints bijection

For any nonsingular .some ECPoint, the underlying (x, y) pair is in
E.points, and `ECPoint.affine E x y` recovers the original ECPoint. -/

theorem some_in_affinePoints {x y : ZMod E.q}
    (h : E.toW.toAffine.Nonsingular x y) :
    (.some h : ECPoint E) ∈ ECPoint.affinePoints E := by
  classical
  unfold ECPoint.affinePoints
  rw [Finset.mem_image]
  -- (x, y) ∈ E.points: from Nonsingular → Equation → on-curve → hComplete.
  have hEq : E.toW.toAffine.Equation x y := E.equation_iff_nonsingular.mpr h
  have hYsq : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
    (E.equation_iff x y).mp hEq
  have hQ : (x, y) ∈ E.points := E.hComplete x y hYsq
  refine ⟨(x, y), hQ, ?_⟩
  rw [ECPoint.affine_of_nonsingular E h]

/-! ## honestDivisorCoeffs support contained in affinePoints ∪ {0}

Per the previous lemma, every `.some` ECPoint is in `affinePoints E`.
The infinity ECPoint is the additional element. Hence the support of
`honestDivisorCoeffs` (or any function on ECPoints) is contained in
`insert 0 (affinePoints E)`. -/

theorem honestDivisorCoeffs_support_subset_affineAndInfinity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) :
    Function.support (honestDivisorCoeffs E stmt wit hk msg)
      ⊆ ↑(insert (0 : ECPoint E) (ECPoint.affinePoints E)) := by
  classical
  intro R _hR
  match R with
  | 0 =>
    rw [Finset.coe_insert]
    exact Set.mem_insert _ _
  | .some h =>
    rw [Finset.coe_insert, Set.mem_insert_iff]
    right
    exact some_in_affinePoints E h

/-! ## Affine-sum equals degE: derivation deferred

The goal is: `∑_{R ∈ affinePoints E} honestDivisorCoeffs(R) = degE(D)`.

The proof plan:
1. From `IsPrincipal honestDivisorCoeffs` (via `principal_divisor_iff`),
   `∑_{P ∈ hFinSupp.toFinset} coeffs P = 0`.
2. Extend sum to `insert 0 (affinePoints E)`: both cover support; outside
   support coeff = 0.
3. `0 ∉ affinePoints E` (affinePoints contains only `.some`).
4. Decompose: `coeffs(0) + affine_sum = 0`.
5. `coeffs(0) = -degE` (from `honestDivisorCoeffs_at_infinity`).
6. Hence `affine_sum = degE`.

Each step is a small Finset manipulation; full assembly deferred.

## Notes on remaining infrastructure for any-k completeness (general)

To prove `ma_completeness_via_isHonestForExplicit` for ANY k, we need:

1. **Divisor identity → β-properties** (β_fun = ordAt = betaTrue):
   - hβsup, hβcov: standard from any nonzero D (no divisor identity needed).
   - hβtrue: trivial (`betaTrue = ordAt`).
   - hAccount: ∑ ordAt = natDegree(normPoly E D). Provable from
     `sum_ordAt_eq_natDegree_under_split` IF splitsOnE.

2. **splitsOnE D**: Provable from divisor identity (zeros are at honest
   support, all rational). Substantial — defer or take as explicit hyp.

3. **hQline**: `hQline_of_hGood_general` (proved above) — general for any D.

4. **hDen**: `hDen_of_hGood` (in `Divisor/LogDerivEagenLength4.lean`) is
   already general (no length-4 specifics).

5. **hResidueMatch**: `∑ zerosFinset · L^{-1} = ∑ E.points honestDivisorCoeffs · L^{-1}`
   (since coeff = 0 outside support), then unfold to `L(-P)^{-1} + Σ m_j L(B_j)^{-1}`.
   Requires careful Finset.sum manipulation; substantial.

The full integration is feasible but multi-firing. Length-4 simple
remains the headline demonstration.

## Future work

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

/-! ## `0 ∉ affinePoints E`

The infinity ECPoint is not in `affinePoints E`, since `affinePoints E`
is the image of `E.points` under `affine`, and for any `Q ∈ E.points`,
`affine E Q.1 Q.2 = .some _` (which is `≠ 0`). -/

theorem zero_notMem_affinePoints : (0 : ECPoint E) ∉ ECPoint.affinePoints E := by
  classical
  unfold ECPoint.affinePoints
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨Q, hQ, hEq⟩ := h
  -- ECPoint.affine E Q.1 Q.2 = 0 forces Nonsingular to fail, but it holds for Q ∈ E.points.
  have hNs : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hNs] at hEq
  cases hEq

/-! ## Affine sum = degE for honest divisor

Combines deg-zero (from IsPrincipal) with the support subset and the
infinity coefficient unfolding. -/

theorem honestDivisorCoeffs_affine_sum_eq_degE
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ R ∈ ECPoint.affinePoints E, honestDivisorCoeffs E stmt wit hk msg R)
      = (msg.toD.degE : ℤ) := by
  classical
  obtain ⟨hFin, hSum_zero⟩ :=
    honestDivisorCoeffs_deg_zero_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hSubset := honestDivisorCoeffs_support_subset_affineAndInfinity E stmt wit hk msg
  have hZeroNotIn := zero_notMem_affinePoints E
  have h_ext_sum : (∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
      honestDivisorCoeffs E stmt wit hk msg R) = 0 := by
    rw [show (∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
              honestDivisorCoeffs E stmt wit hk msg R)
        = ∑ R ∈ hFin.toFinset, honestDivisorCoeffs E stmt wit hk msg R from ?_]
    · exact hSum_zero
    · apply (Finset.sum_subset (s₁ := hFin.toFinset)
              (s₂ := insert (0 : ECPoint E) (ECPoint.affinePoints E)) ?_ ?_).symm
      · intro R hR
        rw [Set.Finite.mem_toFinset] at hR
        exact hSubset hR
      · intro R _hR_in hR_notIn
        rw [Set.Finite.mem_toFinset] at hR_notIn
        by_contra h
        exact hR_notIn h
  rw [Finset.sum_insert hZeroNotIn,
      honestDivisorCoeffs_at_infinity E stmt wit hk msg] at h_ext_sum
  linarith

/-! ## Bridge: `∑_{R ∈ affinePoints E} f R = ∑_{Q ∈ E.points} f (affine E Q.1 Q.2)` -/

theorem affinePoints_sum_eq_image_sum {α : Type*} [AddCommMonoid α]
    (f : ECPoint E → α) :
    (∑ R ∈ ECPoint.affinePoints E, f R)
      = ∑ Q ∈ E.points, f (ECPoint.affine E Q.1 Q.2) := by
  classical
  unfold ECPoint.affinePoints
  rw [Finset.sum_image]
  intro P hP Q hQ h_eq
  simp only at h_eq
  have hPns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  have hQns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hPns,
      ECPoint.affine_of_nonsingular E hQns] at h_eq
  -- .some hPns = .some hQns implies the implicit x, y match.
  injection h_eq with hx_some hy_some
  exact Prod.ext hx_some hy_some

/-! ## Step 3: ∑ ordAt = degE from divisor identity -/

theorem ordAt_sum_eq_degE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    ((∑ Q ∈ E.points, ordAt E msg.toD Q : ℕ) : ℤ) = (msg.toD.degE : ℤ) := by
  rw [ordAt_sum_eq_honestDivisorCoeffs_sum_at_affines E stmt wit hk msg h_honest.2.2.1]
  rw [← affinePoints_sum_eq_image_sum E (honestDivisorCoeffs E stmt wit hk msg)]
  exact honestDivisorCoeffs_affine_sum_eq_degE E stmt wit hk msg hkm h_honest

/-! ## Step 4: ∑ ordAt = degE (cast back to ℕ) and natDegree = degE -/

theorem ordAt_sum_eq_degE_nat_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ Q ∈ E.points, ordAt E msg.toD Q) = msg.toD.degE := by
  have h := ordAt_sum_eq_degE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  exact_mod_cast h

theorem natDegree_normPoly_eq_degE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (normPoly E msg.toD).natDegree = msg.toD.degE := by
  -- ∑ ordAt ≤ natDegree ≤ degE (existing infrastructure).
  -- ∑ ordAt = degE (step 4).
  -- Pinch.
  have hSum := ordAt_sum_eq_degE_nat_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hLe1 : (∑ P ∈ E.points, ordAt E msg.toD P) ≤ (normPoly E msg.toD).natDegree := by
    classical
    rw [sum_E_points_eq_sum_fiberwise E]
    by_cases hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)
    · calc (∑ x₀ : ZMod E.q,
              ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) :=
            Finset.sum_le_sum (fun x₀ _ => sum_ordAt_fst_eq_le E msg.toD hD x₀)
        _ ≤ (normPoly E msg.toD).natDegree :=
            sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
    · push_neg at hD
      have : ∀ P ∈ E.points, ordAt E msg.toD P = 0 :=
        fun P _ => ordAt_eq_zero_of_zero E hD P
      have h_inner : ∀ x₀ : ZMod E.q,
          (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P) = 0 := by
        intro x₀
        apply Finset.sum_eq_zero
        intro P hP
        exact this P (Finset.mem_filter.mp hP).1
      rw [show (∑ x₀ : ZMod E.q,
              ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P) = 0 from
            Finset.sum_eq_zero (fun x₀ _ => h_inner x₀)]
      exact Nat.zero_le _
  have hLe2 : (normPoly E msg.toD).natDegree ≤ msg.toD.degE :=
    normPoly_natDegree_le E msg.toD
  omega

/-! ## hAccount from isHonestForExplicit (no splitsOnE needed) -/

theorem hAccount_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree := by
  rw [ordAt_sum_eq_degE_nat_of_isHonestForExplicit E stmt wit hk msg hkm h_honest,
      natDegree_normPoly_eq_degE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest]

/-! ## Step 5: normPoly splits — `Multiset.card .roots = natDegree` -/

theorem normPoly_splits_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    normPoly_splits_over_Fq E msg.toD := by
  classical
  -- Pinching: ∑ ordAt ≤ ∑ rootMult ≤ natDegree, with ∑ ordAt = natDegree.
  have hSum := hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hFiber : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        ≤ rootMultiplicity x₀ (normPoly E msg.toD) :=
    fun x₀ => sum_ordAt_fst_eq_le E msg.toD hD x₀
  have hFiber_sum : (∑ x₀ : ZMod E.q,
      ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = ∑ Q ∈ E.points, ordAt E msg.toD Q := by
    rw [sum_E_points_eq_sum_fiberwise E (fun P => ordAt E msg.toD P)]
  have hRootMult_sum_le : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        ≤ (normPoly E msg.toD).natDegree :=
    sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
  have hSum_rootMult_eq : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        = (normPoly E msg.toD).natDegree := by
    have h1 : (∑ Q ∈ E.points, ordAt E msg.toD Q)
            ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [← hFiber_sum]
      exact Finset.sum_le_sum (fun x₀ _ => hFiber x₀)
    omega
  unfold normPoly_splits_over_Fq
  rw [← sum_rootMultiplicity_eq_card_roots]
  exact hSum_rootMult_eq

/-! ## Step 6: fiber rationality

Every root α of normPoly E msg.toD has a y-lift in E.points.
Reason: rootMult > 0 + fiber sum equality from pinching ⇒ fiber non-empty. -/

theorem fiber_rationality_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ∀ α ∈ (normPoly E msg.toD).roots, ∃ y : ZMod E.q, (α, y) ∈ E.points := by
  classical
  intro α hα
  -- α has rootMult > 0.
  have hRootMult_pos : 0 < rootMultiplicity α (normPoly E msg.toD) := by
    rw [Polynomial.mem_roots (normPoly_ne_zero E msg.toD hD)] at hα
    exact (Polynomial.rootMultiplicity_pos (normPoly_ne_zero E msg.toD hD)).mpr hα
  -- From the pinching equality (proved in normPoly_splits_of_isHonestForExplicit),
  -- ∑ x₀, fiber_sum x₀ = ∑ x₀, rootMult x₀.
  -- With pointwise fiber_sum ≤ rootMult, and total equality, pointwise equality holds.
  have hSum := hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hFiber_sum_eq_total : (∑ x₀ : ZMod E.q,
      ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = ∑ Q ∈ E.points, ordAt E msg.toD Q := by
    rw [sum_E_points_eq_sum_fiberwise E (fun P => ordAt E msg.toD P)]
  have hFiber_le : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        ≤ rootMultiplicity x₀ (normPoly E msg.toD) :=
    fun x₀ => sum_ordAt_fst_eq_le E msg.toD hD x₀
  have hRootMult_le_natDegree :
      ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        ≤ (normPoly E msg.toD).natDegree :=
    sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
  have hSum_eq : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        = (normPoly E msg.toD).natDegree := by
    have h1 : (∑ Q ∈ E.points, ordAt E msg.toD Q)
            ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [← hFiber_sum_eq_total]
      exact Finset.sum_le_sum (fun x₀ _ => hFiber_le x₀)
    omega
  -- Pointwise equality: fiber_sum = rootMult at each x₀.
  have hFiber_eq_rootMult : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = rootMultiplicity x₀ (normPoly E msg.toD) := by
    -- Total equality + pointwise inequality ⇒ pointwise equality.
    have h_total_fiber : (∑ x₀ : ZMod E.q,
        ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          = ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [hFiber_sum_eq_total, hSum, hSum_eq]
    intro x₀
    by_contra h_ne
    have h_lt : (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
                < rootMultiplicity x₀ (normPoly E msg.toD) :=
      lt_of_le_of_ne (hFiber_le x₀) h_ne
    have h_strict : (∑ x₀ : ZMod E.q,
        ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          < ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) :=
      Finset.sum_lt_sum (fun x₀ _ => hFiber_le x₀) ⟨x₀, Finset.mem_univ _, h_lt⟩
    omega
  -- At α, fiber_sum = rootMult > 0, so fiber is nonempty.
  have hFiber_pos : 0 <
      ∑ P ∈ E.points.filter (fun P => P.1 = α), ordAt E msg.toD P := by
    rw [hFiber_eq_rootMult α]
    exact hRootMult_pos
  have hFiber_nonempty : (E.points.filter (fun P => P.1 = α)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hFiber_pos
    exact lt_irrefl 0 hFiber_pos
  obtain ⟨P, hP⟩ := hFiber_nonempty
  refine ⟨P.2, ?_⟩
  rw [show α = P.1 from (Finset.mem_filter.mp hP).2.symm]
  exact (Finset.mem_filter.mp hP).1

/-! ## Final: splitsOnE from IsHonestForExplicit -/

theorem splitsOnE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    splitsOnE E msg.toD :=
  ⟨normPoly_splits_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD,
   fiber_rationality_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD⟩

/-! ## Bridge: IsHonestForLength4Simple → isHonestFor

Building blocks for the bridge from `IsHonestForLength4Simple` to the
strengthened `MAProverMsg.isHonestFor`. Below we discharge:
* the divisor identity at infinity (needs `degE = 4`, now proved);
* the on-curve invariant for `(target.1, -target.2)` (`= P_0`);

Affine divisor identity, on-curve invariant for bases, and the
IsPrincipal conjunct require multi-firing case-analysis; deferred. -/

/-- Divisor identity at infinity: both `divisorOfD` and
    `honestDivisorCoeffs` evaluate to `-4` at the point at infinity. -/
theorem divisor_identity_at_infinity_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k) :
    divisorOfD E msg.toD (0 : ECPoint E)
      = honestDivisorCoeffs E stmt wit hk msg (0 : ECPoint E) := by
  rw [h_simple.h_toD_eq]
  rw [eagenBuild_length4_div_at_infinity E
        h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
        h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
        h_simple.h_xx_01 h_simple.h_xx_23
        h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
        h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion]
  show (-4 : ℤ) = -((msg.toD.degE : ℤ))
  have h_degE : msg.toD.degE = 4 := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_degE_eq_four E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  rw [h_degE]; norm_num

/-- On-curve invariant for `(-target)`: `(target.1, -target.2) ∈ E.points`. -/
theorem negTarget_on_curve_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    (stmt.target.1, -stmt.target.2) ∈ E.points := by
  rw [← h_simple.h_P₀_eq]
  exact h_simple.hP₀


/-! ### EC group sum lemma for length-4 simple

`thirdPoint E P_0 P_1 = some Q_0` and `thirdPoint E P_2 P_3 = some (-Q_0)`
(via `h_third_match` and `h_y_match`). Combined with the standard
EC identity "third intersection = negation of sum", we get
`P_0 + P_1 + P_2 + P_3 = O` in `ECPoint E`. -/

/-- The thirdPoint of `(P_0, P_1)` for the chord case. -/
theorem thirdPoint_chord_case
    {E : ECSetup} {P₀ P₁ : ZMod E.q × ZMod E.q}
    (h_xx : P₀.1 ≠ P₁.1) :
    thirdPoint E P₀ P₁ = some
      (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1,
       slopeOf P₀.1 P₀.2 P₁.1 P₁.2
         * (slopeOf P₀.1 P₀.2 P₁.1 P₁.2 ^ 2 - P₀.1 - P₁.1)
         + (P₀.2 - slopeOf P₀.1 P₀.2 P₁.1 P₁.2 * P₀.1)) := by
  unfold thirdPoint slopeOf
  rw [if_neg h_xx]

/-- For length-4 simple, the EC group sum of the four input points is zero. -/
theorem ec_sum_zero_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    (ECPoint.affineOfMem E h_simple.hP₀ + ECPoint.affineOfMem E h_simple.hP₁
      + ECPoint.affineOfMem E h_simple.hP₂ + ECPoint.affineOfMem E h_simple.hP₃
      : ECPoint E) = 0 := by
  classical
  -- Q_0 = thirdPoint of (P_0, P_1).
  set Q₀x := slopeOf h_simple.P₀.1 h_simple.P₀.2 h_simple.P₁.1 h_simple.P₁.2 ^ 2
            - h_simple.P₀.1 - h_simple.P₁.1 with hQ₀x_def
  set Q₀y := slopeOf h_simple.P₀.1 h_simple.P₀.2 h_simple.P₁.1 h_simple.P₁.2 * Q₀x
            + (h_simple.P₀.2 - slopeOf h_simple.P₀.1 h_simple.P₀.2
                                  h_simple.P₁.1 h_simple.P₁.2 * h_simple.P₀.1)
            with hQ₀y_def
  -- Q_0 is on E.
  have hQ₀_mem : (Q₀x, Q₀y) ∈ E.points := by
    have hOC := chord_third_point_on_E E h_simple.P₀ h_simple.P₁
                  h_simple.hP₀ h_simple.hP₁ h_simple.h_xx_01
    exact E.hComplete _ _ hOC
  -- thirdPoint of (P_0, P_1) = some (Q_0x, Q_0y).
  have hT01 : thirdPoint E h_simple.P₀ h_simple.P₁ = some (Q₀x, Q₀y) :=
    thirdPoint_chord_case h_simple.h_xx_01
  -- thirdPoint of (P_2, P_3) = some (Q_0x, -Q_0y) (via h_third_match, h_y_match).
  have hT23 : thirdPoint E h_simple.P₂ h_simple.P₃ = some (Q₀x, -Q₀y) := by
    have h := thirdPoint_chord_case (E := E)
                (P₀ := h_simple.P₂) (P₁ := h_simple.P₃) h_simple.h_xx_23
    rw [h]
    congr 1
    apply Prod.ext
    · simp only []; rw [hQ₀x_def]; exact h_simple.h_third_match
    · simp only []
      rw [hQ₀y_def]
      have h_y := h_simple.h_y_match
      linear_combination h_y
  -- Negation of (Q_0x, Q_0y) on the curve.
  have h_negQ₀_mem : (Q₀x, -Q₀y) ∈ E.points := by
    apply E.hComplete
    have hC := E.hOnCurve _ hQ₀_mem
    show (-Q₀y) ^ 2 = Q₀x ^ 3 + E.curveA * Q₀x + E.curveB
    rw [neg_pow_two]; exact hC
  -- Apply thirdPoint_some_eq_neg_add for (P_0, P_1).
  have hSum01 : ECPoint.affineOfMem E h_simple.hP₀ + ECPoint.affineOfMem E h_simple.hP₁
              = -ECPoint.affineOfMem E
                  (third_point_on_curve E h_simple.P₀ h_simple.P₁
                    h_simple.hP₀ h_simple.hP₁ hT01) :=
    thirdPoint_some_eq_neg_add (E := E) h_simple.hP₀ h_simple.hP₁ hT01
  -- Apply thirdPoint_some_eq_neg_add for (P_2, P_3).
  have hSum23 : ECPoint.affineOfMem E h_simple.hP₂ + ECPoint.affineOfMem E h_simple.hP₃
              = -ECPoint.affineOfMem E
                  (third_point_on_curve E h_simple.P₂ h_simple.P₃
                    h_simple.hP₂ h_simple.hP₃ hT23) :=
    thirdPoint_some_eq_neg_add (E := E) h_simple.hP₂ h_simple.hP₃ hT23
  -- Identify affineOfMem of (Q_0x, -Q_0y) with -affineOfMem of (Q_0x, Q_0y).
  have h_Q₀_eq : ECPoint.affineOfMem E
                  (third_point_on_curve E h_simple.P₀ h_simple.P₁
                    h_simple.hP₀ h_simple.hP₁ hT01)
                = ECPoint.affineOfMem E hQ₀_mem := by
    rfl
  have h_negQ₀_eq : ECPoint.affineOfMem E
                  (third_point_on_curve E h_simple.P₂ h_simple.P₃
                    h_simple.hP₂ h_simple.hP₃ hT23)
                = ECPoint.affineOfMem E h_negQ₀_mem := by
    rfl
  rw [h_Q₀_eq] at hSum01
  rw [h_negQ₀_eq] at hSum23
  -- affineOfMem (Q_0x, -Q_0y) = -affineOfMem (Q_0x, Q_0y).
  have h_affNeg : ECPoint.affineOfMem E h_negQ₀_mem
                = -ECPoint.affineOfMem E hQ₀_mem := by
    rw [← ECPoint.affine_eq_affineOfMem E hQ₀_mem]
    rw [← ECPoint.affine_eq_affineOfMem E h_negQ₀_mem]
    show ECPoint.affine E (Q₀x, -Q₀y).1 (Q₀x, -Q₀y).2
        = -ECPoint.affine E (Q₀x, Q₀y).1 (Q₀x, Q₀y).2
    show ECPoint.affine E Q₀x (-Q₀y) = -ECPoint.affine E Q₀x Q₀y
    rw [ECPoint.affine_neg E Q₀x Q₀y]
  -- Combine. Goal is `(P₀ + P₁) + P₂ + P₃ = 0`.
  -- First reassociate: P₀ + P₁ + P₂ + P₃ = (P₀ + P₁) + (P₂ + P₃).
  have h_assoc : (ECPoint.affineOfMem E h_simple.hP₀ + ECPoint.affineOfMem E h_simple.hP₁
                  + ECPoint.affineOfMem E h_simple.hP₂ + ECPoint.affineOfMem E h_simple.hP₃
                  : ECPoint E)
              = (ECPoint.affineOfMem E h_simple.hP₀ + ECPoint.affineOfMem E h_simple.hP₁)
                + (ECPoint.affineOfMem E h_simple.hP₂ + ECPoint.affineOfMem E h_simple.hP₃) := by
    abel
  rw [h_assoc, hSum01, hSum23, h_affNeg]
  -- Goal: -A + (-(-A)) = 0.
  abel

/-- Cast helper: `(h ▸ jj : Fin stmt.k).val = jj.val` where `h : stmt.k = 3`. -/
private theorem cast_subst_val_l4
    {stmt : DlogStatement E.q} (h : stmt.k = 3) (jj : Fin 3) :
    ((h ▸ jj : Fin stmt.k)).val = jj.val := by
  generalize stmt.k = k at h jj
  cases h
  rfl

/-- Helper: extract a specific basis from IsHonestForLength4Simple. The
    cast-rewriting is encapsulated here so the bridge theorem doesn't
    need to fight Lean's dependent-type machinery directly. -/
private theorem bases_at_cast_index_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (j : Fin 3) :
    stmt.bases (h_simple.hk_eq_3 ▸ j) ∈ E.points := by
  fin_cases j
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨0, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨0, by decide⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₁_eq]; exact h_simple.hP₁
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨1, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨1, by decide⟩ : Fin 3) = (1 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₂_eq]; exact h_simple.hP₂
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨2, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₃_eq]; exact h_simple.hP₃

/-- Affine divisor identity at points in `{P_0..P_3}`: at any of the
    four sum-zero affine points (each appearing with multiplicity 1),
    `divisorOfD = 1` and `honestDivisorCoeffs = 1` (under the simple-case
    hypotheses with `wit.scalars = 1`). -/
theorem divisor_identity_at_affine_off_support_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (hP : (x, y) ∈ E.points)
    (h_off : (x, y) ≠ h_simple.P₀ ∧ (x, y) ≠ h_simple.P₁ ∧
             (x, y) ≠ h_simple.P₂ ∧ (x, y) ≠ h_simple.P₃) :
    divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some hns)
      = honestDivisorCoeffs E stmt wit hk msg
          (WeierstrassCurve.Affine.Point.some hns) := by
  classical
  -- divisorOfD = ordAt (cast to ℤ) at affine.
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  -- Step 1: divisorOfD = 0. Use zerosFinset characterization.
  have h_zeros := zerosFinset_eagenBuild_length4_eq E
    h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
    h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
    h_simple.h_xx_01 h_simple.h_xx_23
    h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
    h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
    h_simple.h_P₀_off_L₂ h_simple.h_P₁_off_L₂ h_simple.h_P₂_off_L₁ h_simple.h_P₃_off_L₁
    h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
    h_simple.h_Q₀_off_L₂_inputs h_simple.h_negQ₀_off_L₁_inputs
  have h_notin : (x, y) ∉ zerosFinset E msg.toD := by
    rw [h_simple.h_toD_eq, h_zeros]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨h_off.1, h_off.2.1, h_off.2.2.1, h_off.2.2.2⟩
  have h_eval_ne : msg.toD.eval x y ≠ 0 := by
    intro h
    apply h_notin
    unfold zerosFinset zeros
    rw [Finset.mem_filter]
    exact ⟨hP, h⟩
  have hD_NZ : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_ne_zero E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  have h_ord_zero : ordAt E msg.toD (x, y) = 0 := by
    by_contra h_ne
    have h_pos : 0 < ordAt E msg.toD (x, y) := Nat.pos_of_ne_zero h_ne
    have := (ordAt_pos_iff_zero E msg.toD hD_NZ (x, y) hP).mp h_pos
    exact h_eval_ne this
  -- Step 2: honestDivisorCoeffs = 0. (x, y) ≠ -target = P_0, no base = (x, y).
  have h_negT : (stmt.target.1, -stmt.target.2) = h_simple.P₀ := h_simple.h_P₀_eq.symm
  have h_indic_zero : ((x, y) = (stmt.target.1, -stmt.target.2)) = False := by
    apply propext
    constructor
    · intro h; rw [h_negT] at h; exact h_off.1 h
    · intro h; exact False.elim h
  -- Bases at h_simple.hk_eq_3 ▸ (0,1,2) are P_1, P_2, P_3, none equal (x, y).
  have h_bases_ne : ∀ i : Fin stmt.k, stmt.bases i ≠ (x, y) := by
    intro i
    have h3 := h_simple.hk_eq_3
    -- Helper: stmt.bases (h3 ▸ j) ≠ (x, y) for any j : Fin 3.
    have h_b_ne_at : ∀ (j : Fin 3), stmt.bases (h3 ▸ j) ≠ (x, y) := by
      intro j
      fin_cases j
      · show stmt.bases (h3 ▸ (⟨0, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨0, by decide⟩ : Fin 3) = (0 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₁_eq]
        intro h; exact h_off.2.1 h.symm
      · show stmt.bases (h3 ▸ (⟨1, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨1, by decide⟩ : Fin 3) = (1 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₂_eq]
        intro h; exact h_off.2.2.1 h.symm
      · show stmt.bases (h3 ▸ (⟨2, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₃_eq]
        intro h; exact h_off.2.2.2 h.symm
    -- Cast i to Fin 3 and apply.
    have h_eq : stmt.bases i = stmt.bases (h3 ▸ Fin.cast h3 i) := by
      congr 1
      apply Fin.ext
      have h_subst_val : ∀ (h : stmt.k = 3) (jj : Fin 3),
          ((h ▸ jj : Fin stmt.k)).val = jj.val := by
        intro h jj
        generalize stmt.k = k at h jj
        cases h
        rfl
      rw [h_subst_val h3]
      rfl
    rw [h_eq]
    exact h_b_ne_at (Fin.cast h3 i)
  -- Now compute both sides.
  -- divisorOfD at affine = (ordAt : ℤ).
  rw [show divisorOfD E msg.toD (ECPoint.affine E x y)
        = (ordAt E msg.toD (x, y) : ℤ) by
      rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  rw [h_ord_zero]
  show (0 : ℤ) = honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
  rw [show honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
        = (if (x, y) = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
            (fun i => stmt.bases i = (x, y)),
            (wit.scalars (hk ▸ i)) by
        rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  rw [if_neg (by intro h; rw [h_negT] at h; exact h_off.1 h)]
  -- The bases-filter is empty since no base = (x, y).
  have h_filter_empty : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact h_bases_ne i
  rw [h_filter_empty]
  simp

/-! ### Affine on-support case: R ∈ {P_0..P_3}

For each P_i, the divisor identity at .some P_i is `1 = 1`:
* `divisorOfD = 1` from `eagenBuild_length4_div_at_P_i`.
* `honestDivisorCoeffs = 1` from indicator (i = 0) or base-sum (i ≥ 1).

Each sub-case is structurally the same; we keep them separate for
readability. -/

/-- Helper: extract divisorOfD msg.toD = 1 at any of P_0..P_3 (under
    IsHonestForLength4Simple's hypotheses). -/
private theorem div_eq_one_at_P_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_xy : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
            (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃) :
    divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some hns) = 1 := by
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_simple.h_toD_eq]
  rcases h_xy with h0 | h1 | h2 | h3
  · -- (x, y) = P_0: divisorOfD = 1.
    have hx : x = h_simple.P₀.1 := by rw [show x = (x, y).1 from rfl, h0]
    have hy : y = h_simple.P₀.2 := by rw [show y = (x, y).2 from rfl, h0]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₀ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₀_off_L₂ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₁.1 := by rw [show x = (x, y).1 from rfl, h1]
    have hy : y = h_simple.P₁.2 := by rw [show y = (x, y).2 from rfl, h1]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₁ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₁_off_L₂ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₂.1 := by rw [show x = (x, y).1 from rfl, h2]
    have hy : y = h_simple.P₂.2 := by rw [show y = (x, y).2 from rfl, h2]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₂ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₂_off_L₁ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₃.1 := by rw [show x = (x, y).1 from rfl, h3]
    have hy : y = h_simple.P₃.2 := by rw [show y = (x, y).2 from rfl, h3]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₃ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₃_off_L₁ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion

/-! ### On-support helper: filter-singleton characterisation

For each j : Fin 3, the filter `{i : Fin stmt.k | stmt.bases i = stmt.bases (h3 ▸ j)}`
is the singleton `{h3 ▸ j}`. Uses `h_inputs_distinct` (P_1, P_2, P_3 distinct
modulo P_0 not being a basis index). -/
private theorem bases_filter_singleton_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (j : Fin 3) :
    (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ j))
      = {h_simple.hk_eq_3 ▸ j} := by
  classical
  have h3 := h_simple.hk_eq_3
  have h_dist := h_simple.h_inputs_distinct
  -- The base identifications.
  have hb0 : stmt.bases (h3 ▸ (0 : Fin 3)) = h_simple.P₁ := h_simple.h_P₁_eq.symm
  have hb1 : stmt.bases (h3 ▸ (1 : Fin 3)) = h_simple.P₂ := h_simple.h_P₂_eq.symm
  have hb2 : stmt.bases (h3 ▸ (2 : Fin 3)) = h_simple.P₃ := h_simple.h_P₃_eq.symm
  -- Distinctness facts in the form needed.
  have hP12 : h_simple.P₁ ≠ h_simple.P₂ := h_dist.2.2.2.1
  have hP13 : h_simple.P₁ ≠ h_simple.P₃ := h_dist.2.2.2.2.1
  have hP23 : h_simple.P₂ ≠ h_simple.P₃ := h_dist.2.2.2.2.2
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · -- Forward: stmt.bases i = stmt.bases (h3 ▸ j) → i = h3 ▸ j.
    intro h_bi
    -- Cast i to a fresh Fin 3 variable ji by obtaining.
    obtain ⟨ji, hji⟩ : ∃ ji : Fin 3, ji = Fin.cast h3 i := ⟨Fin.cast h3 i, rfl⟩
    -- Show stmt.bases i = stmt.bases (h3 ▸ ji).
    have h_i_eq : stmt.bases i = stmt.bases (h3 ▸ ji) := by
      congr 1
      apply Fin.ext
      rw [cast_subst_val_l4 (E := E) h3 ji, hji]
      rfl
    rw [h_i_eq] at h_bi
    -- Now stmt.bases (h3 ▸ ji) = stmt.bases (h3 ▸ j). Case-split on ji and j.
    have h_eq : ji = j := by
      have h_contra : ∀ (h_bi' : stmt.bases (h3 ▸ (0 : Fin 3))
                              = stmt.bases (h3 ▸ (1 : Fin 3))), False := fun h =>
        hP12 ((hb0.symm.trans h).trans hb1)
      have h_contra2 : ∀ (h_bi' : stmt.bases (h3 ▸ (0 : Fin 3))
                              = stmt.bases (h3 ▸ (2 : Fin 3))), False := fun h =>
        hP13 ((hb0.symm.trans h).trans hb2)
      have h_contra3 : ∀ (h_bi' : stmt.bases (h3 ▸ (1 : Fin 3))
                              = stmt.bases (h3 ▸ (0 : Fin 3))), False := fun h =>
        (Ne.symm hP12) ((hb1.symm.trans h).trans hb0)
      have h_contra4 : ∀ (h_bi' : stmt.bases (h3 ▸ (1 : Fin 3))
                              = stmt.bases (h3 ▸ (2 : Fin 3))), False := fun h =>
        hP23 ((hb1.symm.trans h).trans hb2)
      have h_contra5 : ∀ (h_bi' : stmt.bases (h3 ▸ (2 : Fin 3))
                              = stmt.bases (h3 ▸ (0 : Fin 3))), False := fun h =>
        (Ne.symm hP13) ((hb2.symm.trans h).trans hb0)
      have h_contra6 : ∀ (h_bi' : stmt.bases (h3 ▸ (2 : Fin 3))
                              = stmt.bases (h3 ▸ (1 : Fin 3))), False := fun h =>
        (Ne.symm hP23) ((hb2.symm.trans h).trans hb1)
      fin_cases ji <;> fin_cases j
      · rfl
      · exact (h_contra h_bi).elim
      · exact (h_contra2 h_bi).elim
      · exact (h_contra3 h_bi).elim
      · rfl
      · exact (h_contra4 h_bi).elim
      · exact (h_contra5 h_bi).elim
      · exact (h_contra6 h_bi).elim
      · rfl
    -- ji = j, recover i.
    apply Fin.ext
    rw [cast_subst_val_l4 (E := E) h3 j]
    rw [show j.val = ji.val from h_eq ▸ rfl, hji]
    rfl
  · -- Backward.
    intro h_eq
    rw [h_eq]

/-- For (x, y) = P_0: filter (bases i = (x, y)) is empty (P_0 ∉ bases). -/
private theorem bases_filter_empty_at_P0
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = h_simple.P₀) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro i _
  -- Cast i to Fin 3 and case-split.
  have h3 := h_simple.hk_eq_3
  have h_dist := h_simple.h_inputs_distinct
  obtain ⟨ji, hji⟩ : ∃ ji : Fin 3, ji = Fin.cast h3 i := ⟨Fin.cast h3 i, rfl⟩
  have h_i_eq : stmt.bases i = stmt.bases (h3 ▸ ji) := by
    congr 1
    apply Fin.ext
    rw [cast_subst_val_l4 (E := E) h3 ji, hji]
    rfl
  rw [h_i_eq]
  fin_cases ji
  · -- ji = 0: bases (h3 ▸ 0) = P_1 ≠ P_0.
    simp only [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl]
    rw [← h_simple.h_P₁_eq]
    exact (Ne.symm h_dist.1)
  · simp only [show (⟨1, by decide⟩ : Fin 3) = 1 from rfl]
    rw [← h_simple.h_P₂_eq]
    exact (Ne.symm h_dist.2.1)
  · simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl]
    rw [← h_simple.h_P₃_eq]
    exact (Ne.symm h_dist.2.2.1)

/-- Helper: at any (x, y) = P_k for k ∈ {0, 1, 2, 3}, honestDivisorCoeffs = 1. -/
private theorem honestCoeffs_eq_one_at_P_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_xy : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
            (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃) :
    honestDivisorCoeffs E stmt wit hk msg
        (WeierstrassCurve.Affine.Point.some hns) = 1 := by
  classical
  rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [show honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
        = (if (x, y) = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
            (fun i => stmt.bases i = (x, y)),
            (wit.scalars (hk ▸ i)) by
        rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  have h_negT : (stmt.target.1, -stmt.target.2) = h_simple.P₀ := h_simple.h_P₀_eq.symm
  have h_dist := h_simple.h_inputs_distinct
  rcases h_xy with h0 | h1 | h2 | h3'
  · -- (x, y) = P_0. Indicator = 1, filter = ∅, sum = 0. Total = 1.
    have h_eq_negT : (x, y) = (stmt.target.1, -stmt.target.2) := by
      rw [h_negT]; exact h0
    rw [if_pos h_eq_negT]
    -- Filter is empty.
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = h_simple.P₀) := by
      rw [h0]
    rw [h_filter_eq, bases_filter_empty_at_P0 E h_simple]
    simp
  · -- (x, y) = P_1. Indicator = 0, filter = {h3 ▸ 0}, sum = 1. Total = 1.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h1]; exact (Ne.symm h_dist.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (0 : Fin 3))) := by
      rw [h1, ← h_simple.h_P₁_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 0]
    rw [Finset.sum_singleton, h_scalars]
  · -- (x, y) = P_2.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h2]; exact (Ne.symm h_dist.2.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (1 : Fin 3))) := by
      rw [h2, ← h_simple.h_P₂_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 1]
    rw [Finset.sum_singleton, h_scalars]
  · -- (x, y) = P_3.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h3']; exact (Ne.symm h_dist.2.2.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (2 : Fin 3))) := by
      rw [h3', ← h_simple.h_P₃_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 2]
    rw [Finset.sum_singleton, h_scalars]

/-! ### Full divisor identity ∀ R for length-4 simple

Combines the infinity case, the affine on-support case (R ∈ {P_0..P_3}),
and the affine off-support case (R ∉ {P_0..P_3}). -/

/-- Universal divisor identity: `∀ R : ECPoint E, divisorOfD msg.toD R = honestDivisorCoeffs R`. -/
theorem divisor_identity_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R := by
  classical
  intro R
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    exact divisor_identity_at_infinity_for_length4Simple E h_simple hk
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
    have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
      (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
    have hP : (x, y) ∈ E.points := E.hComplete x y hOC
    -- Case-split on (x, y) ∈ {P_0..P_3} or not.
    by_cases h_in : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
                    (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃
    · -- On support.
      rw [div_eq_one_at_P_for_length4Simple E h_simple hns h_in]
      rw [honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns h_in]
    · -- Off support.
      push_neg at h_in
      obtain ⟨h0, h1, h2, h3⟩ := h_in
      exact divisor_identity_at_affine_off_support_for_length4Simple E h_simple hk h_scalars
        hns hP ⟨h0, h1, h2, h3⟩

/-! ### Affine sum of honestDivisorCoeffs = 4 (length-4 simple)

Direct enumeration: for each P ∈ E.points, `honestDivisorCoeffs (affine P)`
is 1 iff P ∈ {P_0..P_3}, else 0. Sum over E.points = 4. -/

theorem honestCoeffs_affine_sum_eq_four_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    (∑ Q ∈ E.points,
        honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2))
      = 4 := by
  classical
  -- Split E.points into {P_0..P_3} and the rest.
  -- For each P_i: honestCoeffs (affine P_i) = 1.
  -- For other P: honestCoeffs (affine P) = 0.
  have h_dist := h_simple.h_inputs_distinct
  have h_in_set : ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
                    : Finset (ZMod E.q × ZMod E.q)) ⊆ E.points := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP | hP
    · rw [hP]; exact h_simple.hP₀
    · rw [hP]; exact h_simple.hP₁
    · rw [hP]; exact h_simple.hP₂
    · rw [hP]; exact h_simple.hP₃
  -- Σ over E.points = Σ over {P_0..P_3} + Σ over (E.points \ {P_0..P_3}).
  -- The second term is 0 since honestCoeffs is 0 off-support.
  -- The first term is 4 (each P_i contributes 1).
  rw [← Finset.sum_sdiff h_in_set]
  -- Σ over (E.points \ {P_0..P_3}) = 0.
  have h_off_zero : (∑ Q ∈ E.points \ ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
                          : Finset (ZMod E.q × ZMod E.q)),
        honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro Q hQ
    rw [Finset.mem_sdiff] at hQ
    obtain ⟨hQ_in, hQ_notIn⟩ := hQ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ_notIn
    have hns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hQ_in))
    have h_off : Q ≠ h_simple.P₀ ∧ Q ≠ h_simple.P₁ ∧
                 Q ≠ h_simple.P₂ ∧ Q ≠ h_simple.P₃ :=
      ⟨hQ_notIn.1, hQ_notIn.2.1, hQ_notIn.2.2.1, hQ_notIn.2.2.2⟩
    have hQ_pair : Q = (Q.1, Q.2) := rfl
    have h_off_pair : (Q.1, Q.2) ≠ h_simple.P₀ ∧ (Q.1, Q.2) ≠ h_simple.P₁ ∧
                      (Q.1, Q.2) ≠ h_simple.P₂ ∧ (Q.1, Q.2) ≠ h_simple.P₃ := by
      rw [← hQ_pair]; exact h_off
    have hQ_in_pair : (Q.1, Q.2) ∈ E.points := by rw [← hQ_pair]; exact hQ_in
    have h_eq := divisor_identity_at_affine_off_support_for_length4Simple E h_simple
                  hk h_scalars hns hQ_in_pair h_off_pair
    -- divisorOfD msg.toD (.some hns) = honestCoeffs (.some hns).
    -- divisorOfD = 0 (proved at off-support).
    have h_div_zero :
        divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some hns) = 0 := by
      -- divisorOfD = ordAt at affine, and ordAt = 0 at off-support.
      rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
            = ECPoint.affine E Q.1 Q.2 from (ECPoint.affine_of_nonsingular E hns).symm]
      have h_zeros := zerosFinset_eagenBuild_length4_eq E
        h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
        h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
        h_simple.h_xx_01 h_simple.h_xx_23
        h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
        h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
        h_simple.h_P₀_off_L₂ h_simple.h_P₁_off_L₂ h_simple.h_P₂_off_L₁ h_simple.h_P₃_off_L₁
        h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
        h_simple.h_Q₀_off_L₂_inputs h_simple.h_negQ₀_off_L₁_inputs
      have h_notin : (Q.1, Q.2) ∉ zerosFinset E msg.toD := by
        rw [h_simple.h_toD_eq, h_zeros]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact h_off_pair
      have h_eval_ne : msg.toD.eval Q.1 Q.2 ≠ 0 := by
        intro h
        apply h_notin
        unfold zerosFinset zeros
        rw [Finset.mem_filter]
        exact ⟨hQ_in_pair, h⟩
      have hD_NZ : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
        rw [h_simple.h_toD_eq]
        exact eagenBuild_length4_explicit_ne_zero E
          h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
          h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
          h_simple.h_xx_01 h_simple.h_xx_23
          h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
      have h_ord_zero : ordAt E msg.toD (Q.1, Q.2) = 0 := by
        by_contra h_ne
        have h_pos : 0 < ordAt E msg.toD (Q.1, Q.2) := Nat.pos_of_ne_zero h_ne
        have := (ordAt_pos_iff_zero E msg.toD hD_NZ (Q.1, Q.2) hQ_in_pair).mp h_pos
        exact h_eval_ne this
      rw [show divisorOfD E msg.toD (ECPoint.affine E Q.1 Q.2)
            = (ordAt E msg.toD (Q.1, Q.2) : ℤ) by
          rw [ECPoint.affine_of_nonsingular E hns]; rfl]
      rw [h_ord_zero]
      rfl
    -- Combine: divisorOfD = 0 and divisorOfD = honestCoeffs (universal identity).
    rw [show honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2)
          = divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some hns) by
        rw [divisor_identity_for_length4Simple E h_simple hk h_scalars]
        rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
              = ECPoint.affine E Q.1 Q.2 from (ECPoint.affine_of_nonsingular E hns).symm]]
    exact h_div_zero
  rw [h_off_zero, zero_add]
  -- Σ over {P_0..P_3} = 4.
  rw [show ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
              : Finset (ZMod E.q × ZMod E.q))
        = insert h_simple.P₀ (insert h_simple.P₁ (insert h_simple.P₂ {h_simple.P₃})) from rfl]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h_dist.1, h_dist.2.1, h_dist.2.2.1⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h_dist.2.2.2.1, h_dist.2.2.2.2.1⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact h_dist.2.2.2.2.2)]
  rw [Finset.sum_singleton]
  -- Each term = 1 by honestCoeffs_eq_one_at_P_for_length4Simple.
  have hns0 : E.toW.toAffine.Nonsingular h_simple.P₀.1 h_simple.P₀.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₀))
  have hns1 : E.toW.toAffine.Nonsingular h_simple.P₁.1 h_simple.P₁.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₁))
  have hns2 : E.toW.toAffine.Nonsingular h_simple.P₂.1 h_simple.P₂.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₂))
  have hns3 : E.toW.toAffine.Nonsingular h_simple.P₃.1 h_simple.P₃.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₃))
  have eq0 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₀.1 h_simple.P₀.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns0]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns0
      (Or.inl rfl)
  have eq1 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₁.1 h_simple.P₁.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns1]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns1
      (Or.inr (Or.inl rfl))
  have eq2 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₂.1 h_simple.P₂.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns2]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns2
      (Or.inr (Or.inr (Or.inl rfl)))
  have eq3 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₃.1 h_simple.P₃.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns3]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns3
      (Or.inr (Or.inr (Or.inr rfl)))
  rw [eq0, eq1, eq2, eq3]
  norm_num

/-! ### Total Σ over (insert 0 affinePoints) = 0

Combines `honestCoeffs_at_infinity` (= -degE = -4) with the affine sum
(= 4) to give Σ = 0. -/

theorem honestCoeffs_total_sum_eq_zero_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    (∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
        honestDivisorCoeffs E stmt wit hk msg R) = 0 := by
  classical
  rw [Finset.sum_insert (zero_notMem_affinePoints E)]
  rw [honestDivisorCoeffs_at_infinity E stmt wit hk msg]
  rw [affinePoints_sum_eq_image_sum E (honestDivisorCoeffs E stmt wit hk msg)]
  rw [honestCoeffs_affine_sum_eq_four_for_length4Simple E h_simple hk h_scalars]
  -- -degE + 4 = 0 with degE = 4.
  have h_degE : msg.toD.degE = 4 := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_degE_eq_four E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  rw [h_degE]
  norm_num

/-! ### Total weightedSum over (insert 0 affinePoints) = 0

The infinity entry contributes 0 (since zsmul any · 0 = 0). The affine
contributions sum to .some P_0 + ... + .some P_3 = 0 (from EC sum lemma). -/

theorem honestCoeffs_total_weightedSum_eq_zero_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    ECPoint.weightedSum E (insert (0 : ECPoint E) (ECPoint.affinePoints E))
        (fun P => ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg P) P) = 0 := by
  classical
  rw [ECPoint.weightedSum_insert E (zero_notMem_affinePoints E)]
  -- zsmul applied at 0 (infinity).
  have h_zero_term :
      ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg (0 : ECPoint E))
        (0 : ECPoint E) = 0 :=
    ECPoint.zsmul_infinity E _
  rw [h_zero_term, zero_add]
  -- Affine part: weighted sum over affinePoints = sum over E.points.
  rw [show ECPoint.weightedSum E (ECPoint.affinePoints E)
        (fun P => ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg P) P)
        = ∑ Q ∈ E.points,
            ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg
              (ECPoint.affine E Q.1 Q.2)) (ECPoint.affine E Q.1 Q.2) by
      exact affinePoints_sum_eq_image_sum E _]
  -- Split E.points into {P_0..P_3} and rest.
  have h_in_set : ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
                    : Finset (ZMod E.q × ZMod E.q)) ⊆ E.points := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hP | hP | hP | hP
    · rw [hP]; exact h_simple.hP₀
    · rw [hP]; exact h_simple.hP₁
    · rw [hP]; exact h_simple.hP₂
    · rw [hP]; exact h_simple.hP₃
  rw [← Finset.sum_sdiff h_in_set]
  -- Off-support: each term = 0 (affine point has scalar 0 in honestCoeffs).
  have h_off_zero : (∑ Q ∈ E.points \ ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
                          : Finset (ZMod E.q × ZMod E.q)),
        ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg
          (ECPoint.affine E Q.1 Q.2)) (ECPoint.affine E Q.1 Q.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro Q hQ
    rw [Finset.mem_sdiff] at hQ
    obtain ⟨hQ_in, hQ_notIn⟩ := hQ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ_notIn
    have hns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ hQ_in))
    have h_off_pair : (Q.1, Q.2) ≠ h_simple.P₀ ∧ (Q.1, Q.2) ≠ h_simple.P₁ ∧
                      (Q.1, Q.2) ≠ h_simple.P₂ ∧ (Q.1, Q.2) ≠ h_simple.P₃ := by
      have hQ_pair : Q = (Q.1, Q.2) := rfl
      rw [← hQ_pair]
      exact ⟨hQ_notIn.1, hQ_notIn.2.1, hQ_notIn.2.2.1, hQ_notIn.2.2.2⟩
    have hQ_in_pair : (Q.1, Q.2) ∈ E.points := by
      have hQ_pair : Q = (Q.1, Q.2) := rfl
      rw [← hQ_pair]; exact hQ_in
    have h_eq := divisor_identity_at_affine_off_support_for_length4Simple E h_simple
                  hk h_scalars hns hQ_in_pair h_off_pair
    -- divisorOfD = 0, so honestCoeffs (.some hns) = 0.
    have h_div_zero :
        divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some hns) = 0 := by
      rw [show (WeierstrassCurve.Affine.Point.some hns : ECPoint E)
            = ECPoint.affine E Q.1 Q.2 from (ECPoint.affine_of_nonsingular E hns).symm]
      have h_zeros := zerosFinset_eagenBuild_length4_eq E
        h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
        h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
        h_simple.h_xx_01 h_simple.h_xx_23
        h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
        h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
        h_simple.h_P₀_off_L₂ h_simple.h_P₁_off_L₂ h_simple.h_P₂_off_L₁ h_simple.h_P₃_off_L₁
        h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
        h_simple.h_Q₀_off_L₂_inputs h_simple.h_negQ₀_off_L₁_inputs
      have h_notin : (Q.1, Q.2) ∉ zerosFinset E msg.toD := by
        rw [h_simple.h_toD_eq, h_zeros]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact h_off_pair
      have h_eval_ne : msg.toD.eval Q.1 Q.2 ≠ 0 := by
        intro h
        apply h_notin
        unfold zerosFinset zeros
        rw [Finset.mem_filter]
        exact ⟨hQ_in_pair, h⟩
      have hD_NZ : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
        rw [h_simple.h_toD_eq]
        exact eagenBuild_length4_explicit_ne_zero E
          h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
          h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
          h_simple.h_xx_01 h_simple.h_xx_23
          h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
      have h_ord_zero : ordAt E msg.toD (Q.1, Q.2) = 0 := by
        by_contra h_ne
        have h_pos : 0 < ordAt E msg.toD (Q.1, Q.2) := Nat.pos_of_ne_zero h_ne
        have := (ordAt_pos_iff_zero E msg.toD hD_NZ (Q.1, Q.2) hQ_in_pair).mp h_pos
        exact h_eval_ne this
      rw [show divisorOfD E msg.toD (ECPoint.affine E Q.1 Q.2)
            = (ordAt E msg.toD (Q.1, Q.2) : ℤ) by
          rw [ECPoint.affine_of_nonsingular E hns]; rfl]
      rw [h_ord_zero]
      rfl
    have h_honest_zero :
        honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) = 0 := by
      rw [← divisor_identity_for_length4Simple E h_simple hk h_scalars]
      rw [show (ECPoint.affine E Q.1 Q.2 : ECPoint E)
            = WeierstrassCurve.Affine.Point.some hns from
        ECPoint.affine_of_nonsingular E hns]
      exact h_div_zero
    rw [h_honest_zero]
    show ECPoint.zsmul E (0 : ℤ) (ECPoint.affine E Q.1 Q.2 : ECPoint E)
        = (0 : ECPoint E)
    exact ECPoint.zsmul_zero E _
  rw [h_off_zero, zero_add]
  -- On-support: Σ over {P_0..P_3} = sum of zsmul 1 · .some P_i = .some P_0 + ... + .some P_3 = 0.
  have h_dist := h_simple.h_inputs_distinct
  rw [show ({h_simple.P₀, h_simple.P₁, h_simple.P₂, h_simple.P₃}
              : Finset (ZMod E.q × ZMod E.q))
        = insert h_simple.P₀ (insert h_simple.P₁ (insert h_simple.P₂ {h_simple.P₃})) from rfl]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h_dist.1, h_dist.2.1, h_dist.2.2.1⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨h_dist.2.2.2.1, h_dist.2.2.2.2.1⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact h_dist.2.2.2.2.2)]
  rw [Finset.sum_singleton]
  -- Each term: zsmul 1 (affine P_i) = affine P_i.
  have hns0 : E.toW.toAffine.Nonsingular h_simple.P₀.1 h_simple.P₀.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₀))
  have hns1 : E.toW.toAffine.Nonsingular h_simple.P₁.1 h_simple.P₁.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₁))
  have hns2 : E.toW.toAffine.Nonsingular h_simple.P₂.1 h_simple.P₂.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₂))
  have hns3 : E.toW.toAffine.Nonsingular h_simple.P₃.1 h_simple.P₃.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff _ _).mpr (E.hOnCurve _ h_simple.hP₃))
  have eq0 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₀.1 h_simple.P₀.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns0]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns0 (Or.inl rfl)
  have eq1 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₁.1 h_simple.P₁.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns1]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns1
      (Or.inr (Or.inl rfl))
  have eq2 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₂.1 h_simple.P₂.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns2]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns2
      (Or.inr (Or.inr (Or.inl rfl)))
  have eq3 : honestDivisorCoeffs E stmt wit hk msg
        (ECPoint.affine E h_simple.P₃.1 h_simple.P₃.2) = 1 := by
    rw [ECPoint.affine_of_nonsingular E hns3]
    exact honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns3
      (Or.inr (Or.inr (Or.inr rfl)))
  rw [eq0, eq1, eq2, eq3]
  -- Goal: zsmul 1 (.some hns0) + zsmul 1 (.some hns1) + zsmul 1 (.some hns2) + zsmul 1 (.some hns3) = 0.
  -- Note: ECPoint.zsmul E 1 P = 1 • P = P.
  show (1 : ℤ) • (ECPoint.affine E h_simple.P₀.1 h_simple.P₀.2 : ECPoint E)
      + ((1 : ℤ) • (ECPoint.affine E h_simple.P₁.1 h_simple.P₁.2 : ECPoint E)
        + ((1 : ℤ) • (ECPoint.affine E h_simple.P₂.1 h_simple.P₂.2 : ECPoint E)
          + (1 : ℤ) • (ECPoint.affine E h_simple.P₃.1 h_simple.P₃.2 : ECPoint E))) = 0
  simp only [one_smul]
  -- Convert affine to affineOfMem.
  rw [ECPoint.affine_eq_affineOfMem E h_simple.hP₀,
      ECPoint.affine_eq_affineOfMem E h_simple.hP₁,
      ECPoint.affine_eq_affineOfMem E h_simple.hP₂,
      ECPoint.affine_eq_affineOfMem E h_simple.hP₃]
  -- Use ec_sum_zero_for_length4Simple.
  have h_ec := ec_sum_zero_for_length4Simple E h_simple
  -- The EC sum is left-associated: (P₀+P₁)+P₂+P₃, our goal is right-assoc: P₀+(P₁+(P₂+P₃)).
  -- Use abel to reassociate.
  rw [show (ECPoint.affineOfMem E h_simple.hP₀
              + (ECPoint.affineOfMem E h_simple.hP₁
                + (ECPoint.affineOfMem E h_simple.hP₂
                  + ECPoint.affineOfMem E h_simple.hP₃)) : ECPoint E)
        = ECPoint.affineOfMem E h_simple.hP₀ + ECPoint.affineOfMem E h_simple.hP₁
          + ECPoint.affineOfMem E h_simple.hP₂ + ECPoint.affineOfMem E h_simple.hP₃ by abel]
  exact h_ec

/-! ### IsPrincipal honestDivisorCoeffs for length-4 simple

Apply `principal_divisor_iff.mpr` with the universal sum and weightedSum
identities. -/

theorem isPrincipal_honestDivisorCoeffs_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    IsPrincipal E (honestDivisorCoeffs E stmt wit hk msg) := by
  classical
  have h_div := divisor_identity_for_length4Simple E h_simple hk h_scalars
  have hFin := honestDivisorCoeffs_finiteSupport_of_divisor_identity E
    stmt wit hk msg h_div
  have hSubset := honestDivisorCoeffs_support_subset_affineAndInfinity E stmt wit hk msg
  -- Use the cover insert 0 (affinePoints E).
  rw [principal_divisor_iff E _ hFin]
  refine ⟨?_, ?_⟩
  · -- Σ = 0.
    have h_total := honestCoeffs_total_sum_eq_zero_for_length4Simple E h_simple hk h_scalars
    -- Σ over hFin.toFinset = Σ over (insert 0 affinePoints) (extension).
    have h_ext :
        (∑ R ∈ hFin.toFinset, honestDivisorCoeffs E stmt wit hk msg R)
        = ∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
            honestDivisorCoeffs E stmt wit hk msg R := by
      apply Finset.sum_subset
      · intro R hR
        rw [Set.Finite.mem_toFinset] at hR
        exact hSubset hR
      · intro R _hR_in hR_notIn
        rw [Set.Finite.mem_toFinset] at hR_notIn
        by_contra h
        exact hR_notIn h
    rw [h_ext]
    exact h_total
  · -- weightedSum = 0.
    have h_total := honestCoeffs_total_weightedSum_eq_zero_for_length4Simple E h_simple
                      hk h_scalars
    have h_ext :
        ECPoint.weightedSum E (insert (0 : ECPoint E) (ECPoint.affinePoints E))
            (fun P => ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg P) P)
        = ECPoint.weightedSum E hFin.toFinset
            (fun P => ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg P) P) := by
      apply ECPoint.weightedSum_subset_of_zero_outside
      · intro R hR
        rw [Set.Finite.mem_toFinset] at hR
        exact hSubset hR
      · intro R _hR_in hR_notIn
        rw [Set.Finite.mem_toFinset] at hR_notIn
        have hR_zero : honestDivisorCoeffs E stmt wit hk msg R = 0 := by
          by_contra h
          exact hR_notIn h
        show ECPoint.zsmul E (honestDivisorCoeffs E stmt wit hk msg R) R
            = (0 : ECPoint E)
        rw [hR_zero]
        exact ECPoint.zsmul_zero E _
    rw [← h_ext]
    exact h_total

/-- Scalar reduction for the length-4 simple case (with `wit.scalars = 1`). -/
theorem scalar_reduction_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    let hkm : stmt.k = msg.k := h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm
    ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)) := by
  intro hkm i
  rw [h_simple.h_m_eq_one (hkm ▸ i)]
  rw [h_scalars (hk ▸ i)]
  push_cast; rfl

/-- On-curve invariant: every `bases i` is on E. -/
theorem bases_on_curve_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    ∀ i : Fin stmt.k, stmt.bases i ∈ E.points := by
  intro i
  have h3 := h_simple.hk_eq_3
  -- We need: stmt.bases i ∈ E.points.
  -- Strategy: show stmt.bases i = stmt.bases (h3 ▸ Fin.cast h3 i) and use the helper.
  set j : Fin 3 := Fin.cast h3 i with hj_def
  have h_eq : stmt.bases i = stmt.bases (h3 ▸ j) := by
    congr 1
    -- Goal: i = h3 ▸ j (in Fin stmt.k).
    apply Fin.ext
    -- Goal: i.val = (h3 ▸ j).val
    -- (Fin.cast h3 i).val = i.val by definition.
    have h_cast_val : (Fin.cast h3 i).val = i.val := rfl
    -- (h3 ▸ j).val = j.val (cast preserves val).
    -- This is the tricky part; use generalization.
    have h_subst_val : ∀ (h : stmt.k = 3) (j : Fin 3),
        ((h ▸ j : Fin stmt.k)).val = j.val := by
      intro h jj
      -- Case on h.
      generalize stmt.k = k at h jj
      cases h
      rfl
    rw [h_subst_val h3 j, hj_def, h_cast_val]
  rw [h_eq]
  exact bases_at_cast_index_for_length4Simple E h_simple j

/-! ## Bridge: IsHonestForLength4Simple → isHonestFor (full assembly)

Combines all 5 helper components into the full bridge theorem.
Given a `IsHonestForLength4Simple` plus a `DlogWitness` with all
scalars = 1, produces the strengthened `isHonestFor` predicate.

This is the construction-side validation that the strengthened
`isHonestFor` is satisfiable for the length-4 simple case. -/

theorem isHonestFor_of_isHonestForLength4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    msg.isHonestFor E stmt wit hk
      (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact scalar_reduction_for_length4Simple E h_simple hk h_scalars
  · exact isPrincipal_honestDivisorCoeffs_for_length4Simple E h_simple hk h_scalars
  · exact divisor_identity_for_length4Simple E h_simple hk h_scalars
  · exact negTarget_on_curve_for_length4Simple E h_simple
  · exact bases_on_curve_for_length4Simple E h_simple

/-! ## Hypothesis-light any-k completeness

`splitsOnE` and `hAccount` are now both derived from `IsHonestForExplicit`.
The remaining hypotheses are just protocol-level invariants. -/

theorem ma_completeness_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  -- The scalar reduction (`isHonestFor`'s first conjunct) gives us h_m_eq_scalars.
  have h_m_eq_scalars : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) := by
    intro i
    have := h_honest.1 i
    push_cast at this
    convert this
  apply ma_completeness_via_isHonestForExplicit_no_residue_match E stmt wit hk msg hkm
    h_honest hD
    (splitsOnE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD)
    (hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest)
    h_negT h_bases h_m_eq_scalars hDegK hAdm

end Divisor
