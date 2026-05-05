/-
  Divisor/EagenBuildLandmark.lean

  Axiom-free landmark theorem for Eagen's recursive construction.

  Given a sum-zero list `Ps` of distinct affine points on `E`, the
  recursion builds a polynomial `D : CoordRingElt E.q` satisfying:

    (1) `D ≠ 0` (i.e., `¬ (D.a = 0 ∧ D.b = 0)`)
    (2) `D.eval P.1 P.2 = 0` for every `P ∈ Ps`
    (3) `(normPoly E D).natDegree = Ps.length`

  These three properties — "vanishing + right degree" — are the
  geometric content of Eagen's algorithm. They imply, when combined
  with `splitsOnE` and `Nodup`, the full per-`R` divisor identity
  `divisorOfD E D = formalDivisorOfList Ps` (proved separately,
  outside this file, since the `ordAt`-based machinery pulls in
  project axioms).

  The recursion data model here is a sub-namespace `Divisor.Landmark`
  to avoid clashing with the chord-only path in
  `Divisor.EagenBuildRecursive`. The `EagenAccum.point` field uses
  `ECPoint E` so the `O` carry (running sum of an absorbed sub-list
  hitting the identity) is representable.

  ## Status

  This file is the foundation for a multi-session work: M1 (data
  model), M2 (tangent combine), M3 (ungate chord/vertical), M4
  (preservation), M5 (landmark + divisor-identity bridge). See
  `docs/binary-completeness-plan.md`.
-/
import Divisor.Defs
import Divisor.IncrementalConstruction
import Divisor.OrdP.Uniformizer

open Polynomial

namespace Divisor.Landmark

variable (E : ECSetup)

/-! ## Data model

`EagenAccum` carries a running-sum point on `E` (admitting `O` =
infinity for sub-lists summing to zero) and the accumulated
polynomial. -/

/-- Accumulator for the Landmark recursion. `point : ECPoint E`
admits `0 = ∞` so vertical-internal sub-sums are first-class.

The invariant `LandmarkInv xs a` (see below) ties the field to a
list of absorbed inputs `xs`. Singletons (odd-carry leftovers from
`level0`) are NOT yet absorbed; they're staging entries with
`poly = 1` whose `LandmarkInv` is the trivial `xs = []` form. -/
structure EagenAccum where
  point : ECPoint E
  poly : CoordRingElt E.q

/-- Trivial accumulator: identity polynomial, point at infinity.
    Acts as the unit of `combine`. Used as the level-0 staging for
    "no absorbed inputs". -/
noncomputable def EagenAccum.unit : EagenAccum E :=
  { point := 0, poly := { a := 1, b := 0 } }

/-- Singleton accumulator: holds a single point with identity
    polynomial (no inputs absorbed yet). The `level0` of an
    odd-trailing element produces this; subsequent combines absorb
    it. -/
noncomputable def EagenAccum.singleton (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) : EagenAccum E :=
  { point := ECPoint.affine E P.1 P.2, poly := { a := 1, b := 0 } }

/-! ## Combine helpers

Per Codex's design recommendation, the per-pair combine logic is
split into six helpers, one for each branch of the
`(a.point, b.point)` ECPoint pair. The public `combine` matches and
dispatches; preservation lemmas are proved on the helpers.

  - `combine_oo` — both points = O. Multiply polynomials, new point = O.
  - `combine_ol` — only `a.point` = O. Forward `b.point`.
  - `combine_or` — only `b.point` = O. Forward `a.point`.
  - `combine_distinct` — both .some with `a.point.1 ≠ b.point.1`.
    Chord case: line through them, third intersection is the new running sum.
  - `combine_vertical` — both .some with `a.point.1 = b.point.1, a.point.2 ≠ b.point.2`.
    Equivalently `a.point + b.point = O`. Vertical line, new point = O.
  - `combine_tangent` — both .some at the same affine. Tangent doubling.
    Sub-case 2-torsion (`a.point.2 = 0`): vertical, new point = O.
    Sub-case non-2-torsion: tangent line, new point = -2·a.point.

The line factor in each affine-affine case is taken from
`chordCoordRingElt`, which already has its own 4-way dispatch on
the (P, Q) shape. -/

/-- Both running sums are zero: just multiply polynomials. -/
noncomputable def EagenAccum.combine_oo (a b : EagenAccum E) : EagenAccum E :=
  { point := 0, poly := mulCoordRingElt E a.poly b.poly }

/-- `a.point = 0`, `b.point ≠ 0`: forward `b`'s residue. -/
noncomputable def EagenAccum.combine_ol (a b : EagenAccum E) : EagenAccum E :=
  { point := b.point, poly := mulCoordRingElt E a.poly b.poly }

/-- `a.point ≠ 0`, `b.point = 0`: forward `a`'s residue. -/
noncomputable def EagenAccum.combine_or (a b : EagenAccum E) : EagenAccum E :=
  { point := a.point, poly := mulCoordRingElt E a.poly b.poly }

/-- Both points affine with distinct x-coordinates: chord case.
    The chord through `a.point`, `b.point` meets `E` at a third
    rational point; the new running sum is its negation
    `-(a + b)` in the group law. The polynomial is
    `(line · a.poly · b.poly) / ((X - a.x)(X - b.x))`. -/
noncomputable def EagenAccum.combine_distinct
    (a b : EagenAccum E)
    (xa ya xb yb : ZMod E.q)
    (_h_xx : xa ≠ xb) :
    EagenAccum E :=
  let line := chordCoordRingElt E (xa, ya) (xb, yb)
  let lam := slopeOf xa ya xb yb
  let Qx := lam ^ 2 - xa - xb
  let Qy := lam * Qx + (ya - lam * xa)
  let prod := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly
  let after_a := prod.divLin xa
  let after_b := after_a.divLin xb
  -- New running sum = -(a + b) = (Qx, -Qy) lifted to ECPoint.
  { point := ECPoint.affine E Qx (-Qy), poly := after_b }

/-- Both points affine, same x, opposite y: vertical line.
    `a.point + b.point = O`, so the new running sum is `O`.
    Polynomial is `(a.poly · b.poly) / (X - a.x)`. -/
noncomputable def EagenAccum.combine_vertical
    (a b : EagenAccum E) (xa : ZMod E.q) :
    EagenAccum E :=
  let prod := mulCoordRingElt E a.poly b.poly
  { point := 0, poly := prod.divLin xa }

/-- Both points affine, equal, with `y = 0`: 2-torsion doubling.
    Tangent line is vertical `X - x_a`; new running sum = O. -/
noncomputable def EagenAccum.combine_tangent_torsion
    (a b : EagenAccum E) (xa : ZMod E.q) :
    EagenAccum E :=
  -- Identical to vertical case at the data level.
  EagenAccum.combine_vertical E a b xa

/-- Both points affine, equal, with `y ≠ 0`: tangent doubling.
    Tangent line at `(xa, ya)`. The "third intersection" is the
    point `(x₂, y₂)` with `x₂ = λ² - 2·xa`, where
    `λ = (3·xa² + curveA)/(2·ya)`. New running sum = `-(2·a)` =
    `(x₂, -y₂)`. -/
noncomputable def EagenAccum.combine_tangent_smooth
    (a b : EagenAccum E)
    (xa ya : ZMod E.q) (_h_y : ya ≠ 0) :
    EagenAccum E :=
  let line := chordCoordRingElt E (xa, ya) (xa, ya)
  let lam : ZMod E.q := (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹
  let Qx := lam ^ 2 - 2 * xa
  let Qy := lam * Qx + (ya - lam * xa)
  let prod := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly
  -- Tangent doubling shares xa = xb: divide twice by (X - xa) since
  -- line vanishes doubly at xa (sheet-aware: `(xa, ya)` is the
  -- shared running sum, and the third intersection contributes
  -- via the multiplicity).
  let after := (prod.divLin xa).divLin xa
  { point := ECPoint.affine E Qx (-Qy), poly := after }

/-! ## Public `combine`

Dispatches on `(a.point, b.point)`. Total via `match`; the
`some_some` cases delegate to `chordCoordRingElt`'s own 4-way
dispatch through the helpers above. -/

noncomputable def EagenAccum.combine (a b : EagenAccum E) : EagenAccum E :=
  match h_a : a.point, h_b : b.point with
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.zero =>
      EagenAccum.combine_oo E a b
  | WeierstrassCurve.Affine.Point.zero,
    WeierstrassCurve.Affine.Point.some _ =>
      EagenAccum.combine_ol E a b
  | WeierstrassCurve.Affine.Point.some _,
    WeierstrassCurve.Affine.Point.zero =>
      EagenAccum.combine_or E a b
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) _,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) _ =>
      if h_xx : xa ≠ xb then
        EagenAccum.combine_distinct E a b xa ya xb yb h_xx
      else if h_yy : ya = -yb then
        -- a.point + b.point = O.
        EagenAccum.combine_vertical E a b xa
      else
        -- Same x AND not y-flipped ⇒ ya = yb (curve dichotomy).
        if h_y0 : ya = 0 then
          EagenAccum.combine_tangent_torsion E a b xa
        else
          EagenAccum.combine_tangent_smooth E a b xa ya h_y0

/-! ## Level-0 pair construction

`levelInitPair P Q` takes two raw input points `P, Q ∈ E.points`
and produces a level-1 accumulator. The resulting accumulator's
polynomial is the chord/tangent/vertical line through `P, Q`, NOT
yet divided by anything (level-0 polynomials are pure lines). The
running sum is the negation of the third intersection,
i.e. `-(P + Q)` in the group law.

Three branches via `chordCoordRingElt` + `thirdPoint`:
  - `thirdPoint = some (x₂, y₂)`: chord/tangent non-vertical;
    new point = `(x₂, -y₂)` lifted.
  - `thirdPoint = none`: vertical case (`P = -Q` or 2-torsion
    doubling); new point = O. -/

noncomputable def levelInitPair
    (P Q : ZMod E.q × ZMod E.q) : EagenAccum E :=
  let line := chordCoordRingElt E P Q
  match thirdPoint E P Q with
  | none =>
      -- Vertical: P + Q = O. Polynomial is the vertical line.
      { point := 0, poly := line }
  | some (x₂, y₂) =>
      -- Non-vertical: third intersection on E. New running sum
      -- is the negation in the group law: ECPoint.affine x₂ (-y₂).
      { point := ECPoint.affine E x₂ (-y₂), poly := line }

/-! ## Driver: level0 (even-length), level_step, iterate, eagenBuild

This first cut handles **even-length** input lists. Odd-length
lists with sum-zero are conceivable (e.g. `[P, Q, R]` with
`P+Q+R = O`), but the level-0 stage requires either a
`combineSingletonInput` primitive or a different recursion shape;
that's deferred. For binary completeness, even-length covers the
case where `1 + #{i : scalars i = 1}` is even, i.e. the number of
selected bases is odd. -/

/-- Pair adjacent input points; even length only. Each pair becomes
    one level-1 accumulator via `levelInitPair`. -/
noncomputable def level0 :
    List (ZMod E.q × ZMod E.q) → List (EagenAccum E)
  | [] => []
  | [_] => []  -- ill-formed for sum-zero inputs; produces empty
  | P :: Q :: rest => levelInitPair E P Q :: level0 rest

/-- One level: pair adjacent accumulators and combine each pair.
    Trailing odd element is forwarded unchanged (so `level_step`
    on odd-length input doesn't lose the residual; it converges
    in `⌈log₂ n⌉` levels). -/
noncomputable def level_step :
    List (EagenAccum E) → List (EagenAccum E)
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      EagenAccum.combine E a b :: level_step rest

/-- Iterate `level_step` `n` times (or until length ≤ 1). -/
noncomputable def iterate :
    ℕ → List (EagenAccum E) → List (EagenAccum E)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else iterate n (level_step E xs)

/-- Top-level Eagen build for a sum-zero list of input points.
    Returns the polynomial of the final singleton accumulator. -/
noncomputable def eagenBuild
    (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingElt E.q :=
  let acc_list := iterate E Ps.length (level0 E Ps)
  match acc_list with
  | [a] => a.poly
  | _ => { a := 1, b := 0 }  -- shouldn't fire if iterate sufficient

/-! ## Sum-on-curve helper

The running EC sum of a list of inputs, lifted to `ECPoint E`. Off
`E.points` an input contributes nothing (junk on `E.points` membership
is benign because the recursion's `LandmarkInv` will require all
inputs to be on `E`). -/

noncomputable def sumOnE (xs : List (ZMod E.q × ZMod E.q)) : ECPoint E :=
  xs.foldr
    (fun P S =>
      if h : P ∈ E.points then ECPoint.affineOfMem E h + S else S)
    0

@[simp] theorem sumOnE_nil : sumOnE E [] = 0 := rfl

theorem sumOnE_cons {P : ZMod E.q × ZMod E.q} {xs : List _}
    (hP : P ∈ E.points) :
    sumOnE E (P :: xs) = ECPoint.affineOfMem E hP + sumOnE E xs := by
  classical
  unfold sumOnE
  rw [List.foldr_cons]
  rw [dif_pos hP]

/-! ## LandmarkInv — the lightweight invariant

`LandmarkInv xs a` says an accumulator `a` represents the absorbed
sub-list `xs` in the following sense:

  1. `a.point = sumOnE xs` (running EC sum matches).
  2. `a.poly` vanishes at every `P ∈ xs`.
  3. `(normPoly E a.poly).natDegree = xs.length + (if a.point ≠ 0 then 1 else 0)`.

The third conjunct's offset of `1` when `point ≠ 0` accounts for the
"residue" zero of the polynomial at `-a.point` (the carried third
intersection). When `point = 0` (running sum hit identity), no
residue zero remains and the polynomial's degree exactly equals
the absorbed list length.

This invariant is preserved through every level transition under
appropriate hypotheses; see preservation lemmas below. -/

noncomputable def LandmarkInv
    (xs : List (ZMod E.q × ZMod E.q)) (a : EagenAccum E) : Prop :=
  a.point = sumOnE E xs ∧
  (∀ P ∈ xs, a.poly.eval P.1 P.2 = 0) ∧
  letI : Decidable (a.point = (0 : ECPoint E)) :=
    Classical.dec _
  (normPoly E a.poly).natDegree =
    xs.length + (if a.point = (0 : ECPoint E) then 0 else 1)

/-- The synchronized `Forall₂` form: a list of absorbed sub-lists
    and a list of accumulators, pointwise satisfying `LandmarkInv`. -/
def LandmarkInvList (xss : List (List (ZMod E.q × ZMod E.q)))
    (accs : List (EagenAccum E)) : Prop :=
  List.Forall₂ (LandmarkInv E) xss accs

/-! ## Helper: sumOnE on append -/

theorem sumOnE_append (xs ys : List (ZMod E.q × ZMod E.q)) :
    sumOnE E (xs ++ ys) = sumOnE E xs + sumOnE E ys := by
  classical
  induction xs with
  | nil => simp [sumOnE]
  | cons P xs ih =>
    show List.foldr _ 0 (P :: xs ++ ys) =
         List.foldr _ 0 (P :: xs) + List.foldr _ 0 ys
    simp only [List.cons_append, List.foldr_cons]
    by_cases hP : P ∈ E.points
    · rw [dif_pos hP, dif_pos hP]
      change ECPoint.affineOfMem E hP + sumOnE E (xs ++ ys)
        = ECPoint.affineOfMem E hP + sumOnE E xs + sumOnE E ys
      rw [ih, add_assoc]
    · rw [dif_neg hP, dif_neg hP]
      change sumOnE E (xs ++ ys) = sumOnE E xs + sumOnE E ys
      exact ih

/-! ## Preservation: `combine_oo` (both running sums = O)

When two accumulators with `point = 0` are combined, the result
just multiplies the polynomials. `LandmarkInv` is preserved. -/

theorem landmarkInv_combine_oo
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (ha : LandmarkInv E xs a) (hb : LandmarkInv E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0) :
    LandmarkInv E (xs ++ ys) (EagenAccum.combine_oo E a b) := by
  classical
  obtain ⟨ha_sum, ha_van, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_deg⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · -- (combine_oo).point = 0 = sumOnE (xs ++ ys)
    show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append]
    rw [← ha_sum, ← hb_sum, ha_pt, hb_pt, zero_add]
  · -- Vanishing at every P ∈ xs ++ ys
    intro P hP_mem
    show (mulCoordRingElt E a.poly b.poly).eval P.1 P.2 = 0
    rw [List.mem_append] at hP_mem
    rcases hP_mem with hP_xs | hP_ys
    · have hP_on : P ∈ E.points := hxs_on P hP_xs
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [ha_van P hP_xs]
      ring
    · have hP_on : P ∈ E.points := hys_on P hP_ys
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [hb_van P hP_ys]
      ring
  · -- Degree: (normPoly (a.poly · b.poly)).natDegree = (xs ++ ys).length.
    show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_oo E a b).point
                                  = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq]
    have h_combined_zero : (EagenAccum.combine_oo E a b).point = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    rw [if_pos ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    rw [Polynomial.natDegree_mul ha_nz hb_nz]
    rw [ha_deg, hb_deg, List.length_append]
    omega

end Divisor.Landmark
