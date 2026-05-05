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

/-- The "negation coordinates" of an `ECPoint`. Returns `none` for
    infinity, `some (x, -y)` for an affine `(x, y)`. Used to spell
    out residue vanishing (the polynomial vanishes at `-a.point`). -/
noncomputable def negCoords (P : ECPoint E) : Option (ZMod E.q × ZMod E.q) :=
  match P with
  | WeierstrassCurve.Affine.Point.zero => none
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ => some (x, -y)

noncomputable def LandmarkInv
    (xs : List (ZMod E.q × ZMod E.q)) (a : EagenAccum E) : Prop :=
  a.point = sumOnE E xs ∧
  (∀ P ∈ xs, a.poly.eval P.1 P.2 = 0) ∧
  -- Residue vanishing: when running sum is non-zero, the polynomial
  -- vanishes at the *negation* of the running sum (the third intersection
  -- of the latest chord, geometrically).
  (∀ Q : ZMod E.q × ZMod E.q,
    negCoords E a.point = some Q → a.poly.eval Q.1 Q.2 = 0) ∧
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
  obtain ⟨ha_sum, ha_van, ha_res, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_res, hb_deg⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · -- Residue: result.point = 0, so negCoords = none. Vacuous.
    intro Q hQ
    simp [negCoords, EagenAccum.combine_oo] at hQ
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

/-! ## Preservation: `combine_ol` (a.point = O, b.point ≠ O)

The combined accumulator forwards `b`'s residue point. Polynomial
is `a.poly · b.poly`. -/

theorem landmarkInv_combine_ol
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_b_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E b.point = some Q → Q ∈ E.points)
    (ha : LandmarkInv E xs a) (hb : LandmarkInv E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point ≠ (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0) :
    LandmarkInv E (xs ++ ys) (EagenAccum.combine_ol E a b) := by
  classical
  obtain ⟨ha_sum, ha_van, ha_res, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_res, hb_deg⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · show b.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← ha_sum, ← hb_sum, ha_pt, zero_add]
  · intro P hP_mem
    show (mulCoordRingElt E a.poly b.poly).eval P.1 P.2 = 0
    rw [List.mem_append] at hP_mem
    rcases hP_mem with hP_xs | hP_ys
    · have hP_on : P ∈ E.points := hxs_on P hP_xs
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [ha_van P hP_xs]; ring
    · have hP_on : P ∈ E.points := hys_on P hP_ys
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [hb_van P hP_ys]; ring
  · -- Residue: combined.point = b.point. Show vanishing at neg(b.point).
    intro Q hQ
    have h_combined_pt : (EagenAccum.combine_ol E a b).point = b.point := rfl
    rw [h_combined_pt] at hQ
    -- Q comes from negCoords b.point.
    have hQ_on : Q ∈ E.points := h_neg_b_on Q hQ
    show (mulCoordRingElt E a.poly b.poly).eval Q.1 Q.2 = 0
    rw [mulCoordRingElt_eval_on_E E a.poly b.poly hQ_on]
    rw [hb_res Q hQ]
    ring
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_ol E a b).point
                                  = (0 : ECPoint E) then 0 else 1)
    have h_combined_pt : (EagenAccum.combine_ol E a b).point = b.point := rfl
    rw [h_combined_pt, if_neg hb_pt]
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    rw [if_pos ha_pt] at ha_deg
    rw [if_neg hb_pt] at hb_deg
    rw [ha_deg, hb_deg, List.length_append]
    omega

/-! ## Preservation: `combine_or` (a.point ≠ O, b.point = O)

Symmetric to `combine_ol`. -/

theorem landmarkInv_combine_or
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_a_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E a.point = some Q → Q ∈ E.points)
    (ha : LandmarkInv E xs a) (hb : LandmarkInv E ys b)
    (ha_pt : a.point ≠ (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0) :
    LandmarkInv E (xs ++ ys) (EagenAccum.combine_or E a b) := by
  classical
  obtain ⟨ha_sum, ha_van, ha_res, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_res, hb_deg⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · show a.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← ha_sum, ← hb_sum, hb_pt, add_zero]
  · intro P hP_mem
    show (mulCoordRingElt E a.poly b.poly).eval P.1 P.2 = 0
    rw [List.mem_append] at hP_mem
    rcases hP_mem with hP_xs | hP_ys
    · have hP_on : P ∈ E.points := hxs_on P hP_xs
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [ha_van P hP_xs]; ring
    · have hP_on : P ∈ E.points := hys_on P hP_ys
      rw [mulCoordRingElt_eval_on_E E a.poly b.poly hP_on]
      rw [hb_van P hP_ys]; ring
  · intro Q hQ
    have h_combined_pt : (EagenAccum.combine_or E a b).point = a.point := rfl
    rw [h_combined_pt] at hQ
    have hQ_on : Q ∈ E.points := h_neg_a_on Q hQ
    show (mulCoordRingElt E a.poly b.poly).eval Q.1 Q.2 = 0
    rw [mulCoordRingElt_eval_on_E E a.poly b.poly hQ_on]
    rw [ha_res Q hQ]
    ring
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_or E a b).point
                                  = (0 : ECPoint E) then 0 else 1)
    have h_combined_pt : (EagenAccum.combine_or E a b).point = a.point := rfl
    rw [h_combined_pt, if_neg ha_pt]
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    rw [if_neg ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    rw [ha_deg, hb_deg, List.length_append]
    omega

/-! ## divLin helpers (axiom-free)

Polynomial-level lemmas about `divLin`'s interaction with
evaluation. These are used by the affine-affine combine
preservation lemmas. -/

/-- If `(X - C x₀)` divides both `D.a` and `D.b`, and `D` vanishes
    at `(x, y)` with `x ≠ x₀`, then `D.divLin x₀` also vanishes at
    `(x, y)`. -/
theorem divLin_eval_zero_of_x_ne
    (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (haDvd : (X - C x₀) ∣ D.a) (hbDvd : (X - C x₀) ∣ D.b)
    {x y : ZMod E.q} (h_eval : D.eval x y = 0) (h_xx : x ≠ x₀) :
    (D.divLin x₀).eval x y = 0 := by
  have h := divLin_eval_mul_X_sub_C E D x₀ haDvd hbDvd x y
  -- h : (D.divLin x₀).eval x y * (x - x₀) = D.eval x y
  rw [h_eval] at h
  have hne : (x - x₀) ≠ 0 := sub_ne_zero.mpr h_xx
  exact (mul_eq_zero.mp h).resolve_right hne

/-- `(X - C x₀)` divides any polynomial `p` such that `p.eval x₀ = 0`. -/
theorem dvd_X_sub_C_of_eval_eq_zero
    {p : (ZMod E.q)[X]} {x₀ : ZMod E.q} (h : p.eval x₀ = 0) :
    (X - C x₀) ∣ p := by
  rw [Polynomial.dvd_iff_isRoot]
  exact h

/-- `(X - C x₀)^2` divides any polynomial `p` if `p` has a double
    root at `x₀`, i.e. both `p.eval x₀ = 0` and the derivative
    `p.derivative.eval x₀ = 0`. -/
theorem dvd_pow_two_X_sub_C_of_double_root
    {p : (ZMod E.q)[X]} {x₀ : ZMod E.q}
    (h_eval : p.eval x₀ = 0)
    (h_deriv : p.derivative.eval x₀ = 0) :
    (X - C x₀) ^ 2 ∣ p := by
  -- (X - C x₀) | p from h_eval. Write p = (X - C x₀) · q.
  -- Then p.derivative = q + (X - C x₀) · q.derivative.
  -- At x₀: 0 = q(x₀) + 0 = q(x₀). So (X - C x₀) | q. Hence (X - C x₀)² | p.
  have h1 : (X - C x₀) ∣ p := dvd_X_sub_C_of_eval_eq_zero E h_eval
  obtain ⟨q, hq⟩ := h1
  have h2 : q.eval x₀ = 0 := by
    have hderiv : p.derivative = q + (X - C x₀) * q.derivative := by
      rw [hq, derivative_mul]
      simp [derivative_X, derivative_C]
    rw [hderiv] at h_deriv
    simp at h_deriv
    exact h_deriv
  have h3 : (X - C x₀) ∣ q := dvd_X_sub_C_of_eval_eq_zero E h2
  obtain ⟨r, hr⟩ := h3
  refine ⟨r, ?_⟩
  rw [hq, hr]; ring

/-! ## Helpers: deducing univariate vanishing from bivariate fiber

When a bivariate polynomial `q : CoordRingElt E.q` vanishes at both
`(x₀, y₀)` and `(x₀, -y₀)` for `y₀ ≠ 0`, the components `q.a` and
`q.b` both vanish at `x₀`. (Char ≠ 2 plumbing handled via
`E.hq_ge`.) -/

theorem two_ne_zero_in_zmod : (2 : ZMod E.q) ≠ 0 := by
  have hq5 : E.q ≥ 5 := E.hq_ge
  have h2eq : (2 : ZMod E.q) = ((2 : ℕ) : ZMod E.q) := by norm_cast
  rw [h2eq, Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
  intro hdvd
  have : E.q ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem qa_qb_eval_zero_of_double_fiber_vanish
    (q : CoordRingElt E.q) (x₀ y₀ : ZMod E.q)
    (hy_ne : y₀ ≠ 0)
    (hq_pos : q.eval x₀ y₀ = 0) (hq_neg : q.eval x₀ (-y₀) = 0) :
    q.a.eval x₀ = 0 ∧ q.b.eval x₀ = 0 := by
  -- q.eval x₀ y = q.a.eval x₀ - q.b.eval x₀ · y.
  have heq1 : q.a.eval x₀ - q.b.eval x₀ * y₀ = 0 := hq_pos
  have heq2 : q.a.eval x₀ - q.b.eval x₀ * (-y₀) = 0 := hq_neg
  have h2_ne : (2 : ZMod E.q) ≠ 0 := two_ne_zero_in_zmod E
  refine ⟨?_, ?_⟩
  · -- q.a.eval x₀ = 0 from heq1 + heq2.
    have hprod : 2 * q.a.eval x₀ = 0 := by linear_combination heq1 + heq2
    exact (mul_eq_zero.mp hprod).resolve_left h2_ne
  · -- q.b.eval x₀ * y₀ = 0 from heq2 - heq1.
    have hprod : 2 * (q.b.eval x₀ * y₀) = 0 := by
      linear_combination heq2 - heq1
    have hmid : q.b.eval x₀ * y₀ = 0 :=
      (mul_eq_zero.mp hprod).resolve_left h2_ne
    exact (mul_eq_zero.mp hmid).resolve_right hy_ne

/-! ## Helper: normPoly factorization through divLin

When `(X - C x₀)` divides both `D.a` and `D.b`,
`normPoly E (D.divLin x₀) * (X - C x₀)^2 = normPoly E D`.

This gives the natDegree drop of 2 when divLin "absorbs" a
fiber. -/

theorem normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    (D : CoordRingElt E.q) (x₀ : ZMod E.q)
    (haDvd : (X - C x₀) ∣ D.a) (hbDvd : (X - C x₀) ∣ D.b) :
    normPoly E D = (X - C x₀) ^ 2 * normPoly E (D.divLin x₀) := by
  obtain ⟨qa, hqa⟩ := haDvd
  obtain ⟨qb, hqb⟩ := hbDvd
  have hMonic : (X - C x₀ : (ZMod E.q)[X]).Monic := monic_X_sub_C _
  have ha_eq : D.a /ₘ (X - C x₀) = qa := by
    rw [hqa]; exact mul_divByMonic_cancel_left _ hMonic
  have hb_eq : D.b /ₘ (X - C x₀) = qb := by
    rw [hqb]; exact mul_divByMonic_cancel_left _ hMonic
  rw [normPoly_eq, normPoly_eq]
  rw [CoordRingElt.divLin_a, CoordRingElt.divLin_b]
  rw [ha_eq, hb_eq, hqa, hqb]
  ring

/-! ## Preservation: `combine_vertical` (a.point = -b.point, both .some)

The vertical case: `a.point + b.point = O` on `E`, with both
`a.point` and `b.point` affine and (necessarily) non-2-torsion (`ya ≠ 0`).
The combined accumulator's residue is `O`, polynomial is the product
`a.poly · b.poly` divided by one factor of `(X - C xa)`.

The divisibility argument: `q := a.poly · b.poly` vanishes at both
`(xa, ya)` (from `b`'s residue at `-b.point = (xa, ya)`) and
`(xa, -ya)` (from `a`'s residue at `-a.point = (xa, -ya)`).
Both sheets ⇒ `q.a.eval xa = 0 ∧ q.b.eval xa = 0` ⇒
`(X - C xa) ∣ q.a` and `(X - C xa) ∣ q.b` ⇒ divLin succeeds cleanly.

Conditional on no `P ∈ xs ++ ys` having `P.1 = xa`. Future work:
unconditional via richer multiplicity invariant (Codex-flagged sheet
dichotomy). -/

theorem landmarkInv_combine_vertical_no_collision
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya : ZMod E.q}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_no_collision : ∀ P ∈ xs ++ ys, P.1 ≠ xa)
    (hxy_on : (xa, ya) ∈ E.points)
    (hxy_neg_on : (xa, -ya) ∈ E.points)
    (hy_ne : ya ≠ 0)
    (ha : LandmarkInv E xs a) (hb : LandmarkInv E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xa (-ya))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0) :
    LandmarkInv E (xs ++ ys) (EagenAccum.combine_vertical E a b xa) := by
  classical
  obtain ⟨ha_sum, ha_van, ha_res, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_res, hb_deg⟩ := hb
  -- Step 1: residue evaluations from a/b.
  have ha_neg : negCoords E a.point = some (xa, -ya) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hb_neg : negCoords E b.point = some (xa, ya) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa (-ya) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa (-ya)).mpr (E.hOnCurve _ hxy_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show some (xa, -(-ya)) = some (xa, ya)
    rw [neg_neg]
  have ha_van_neg : a.poly.eval xa (-ya) = 0 := ha_res (xa, -ya) ha_neg
  have hb_van_pos : b.poly.eval xa ya = 0 := hb_res (xa, ya) hb_neg
  -- Step 2: product q vanishes on both fibers.
  set q := mulCoordRingElt E a.poly b.poly with hq_def
  have hq_eval_pos : q.eval xa ya = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_on, hb_van_pos]; ring
  have hq_eval_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_neg_on, ha_van_neg]; ring
  -- Step 3: deduce univariate vanishing at xa.
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hy_ne hq_eval_pos hq_eval_neg
  have h_dvd_a : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_b : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  -- Step 4: assemble the four LandmarkInv conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (combine_vertical).point = 0 = sumOnE (xs ++ ys).
    show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← ha_sum, ← hb_sum, ha_pt_eq, hb_pt_eq]
    -- ECPoint.affine xa ya + ECPoint.affine xa (-ya) = 0 (group law).
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    have hns_b : E.toW.toAffine.Nonsingular xa (-ya) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa (-ya)).mpr (E.hOnCurve _ hxy_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    -- Use mathlib's Affine.Point negation: .some (x, y) + .some (x, -y) = 0.
    show (0 : ECPoint E) = (.some hns_a + .some hns_b : ECPoint E)
    -- The sum of a point with its negative is the identity.
    -- mathlib: WeierstrassCurve.Affine.Point.add_neg or similar.
    have h_neg : (.some hns_b : ECPoint E) = -(.some hns_a) := by
      show WeierstrassCurve.Affine.Point.some hns_b
            = -WeierstrassCurve.Affine.Point.some hns_a
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg]
    show (0 : ECPoint E) = .some hns_a + (-.some hns_a)
    rw [add_neg_cancel]
  · -- Vanishing at every P ∈ xs ++ ys (using no-collision hypothesis).
    intro P hP_mem
    show (q.divLin xa).eval P.1 P.2 = 0
    have hP_ne : P.1 ≠ xa := h_no_collision P hP_mem
    -- q.eval P = 0 from a/b's vanishing.
    have hP_on : P ∈ E.points := by
      rw [List.mem_append] at hP_mem
      rcases hP_mem with hP_xs | hP_ys
      · exact hxs_on P hP_xs
      · exact hys_on P hP_ys
    have h_q_eval : q.eval P.1 P.2 = 0 := by
      rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hP_on]
      rw [List.mem_append] at hP_mem
      rcases hP_mem with hP_xs | hP_ys
      · rw [ha_van P hP_xs]; ring
      · rw [hb_van P hP_ys]; ring
    exact divLin_eval_zero_of_x_ne E q xa h_dvd_a h_dvd_b h_q_eval hP_ne
  · -- Residue: result.point = 0, vacuous.
    intro Q hQ
    have h_combined_pt : (EagenAccum.combine_vertical E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [h_combined_pt] at hQ
    simp [negCoords] at hQ
  · -- Degree.
    show (normPoly E (q.divLin xa)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_vertical E a b xa).point
                                  = (0 : ECPoint E) then 0 else 1)
    have h_combined_zero : (EagenAccum.combine_vertical E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    -- normPoly q = (X - C xa)^2 · normPoly (q.divLin xa).
    have h_factorize := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
      E q xa h_dvd_a h_dvd_b
    -- Take natDegree of both sides; compute.
    have hq_nz : normPoly E q ≠ 0 := by
      rw [hq_def, normPoly_mul_eq]
      exact mul_ne_zero ha_nz hb_nz
    have hX_sub_ne : (X - C xa : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    have hSq_ne : ((X - C xa) ^ 2 : (ZMod E.q)[X]) ≠ 0 := pow_ne_zero _ hX_sub_ne
    have h_div_nz : normPoly E (q.divLin xa) ≠ 0 := by
      intro hzero
      apply hq_nz
      rw [h_factorize, hzero, mul_zero]
    have h_natDeg : (normPoly E q).natDegree
        = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
          + (normPoly E (q.divLin xa)).natDegree := by
      rw [h_factorize, Polynomial.natDegree_mul hSq_ne h_div_nz]
    have h_X_sq_deg : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    -- natDegree(normPoly q) = natDegree(normPoly a.poly · normPoly b.poly)
    --                      = natDegree(normPoly a.poly) + natDegree(normPoly b.poly)
    --                      = (xs.length + 1) + (ys.length + 1).
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 2 := by
      rw [hq_def, normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
      have hap : a.point ≠ (0 : ECPoint E) := by
        rw [ha_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa ya :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      have hbp : b.point ≠ (0 : ECPoint E) := by
        rw [hb_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa (-ya) :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa (-ya)).mpr (E.hOnCurve _ hxy_neg_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      rw [if_neg hap] at ha_deg
      rw [if_neg hbp] at hb_deg
      omega
    rw [List.length_append]
    omega

end Divisor.Landmark
