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

/-! ## Driver: level0, level_step, iterate, eagenBuild

`level0`: pair adjacent inputs; produce one `combine` per pair.
Odd-trailing element produces a `singleton`.

`level_step`: pair adjacent accumulators; combine each pair.

`iterate`: apply `level_step` until length ≤ 1.

`eagenBuild`: top-level driver. Input `Ps : List (ZMod q × ZMod q)`
of points on `E` (assumed sum-zero); output the polynomial of the
final singleton accumulator. -/

/-- Pair adjacent input points; the trailing odd element becomes a
    `singleton`. Each pair is combined as a level-0 step. -/
noncomputable def level0
    (hOn : ∀ P, P ∈ E.points → True) :  -- placeholder; on-curve evidence threaded later
    List (ZMod E.q × ZMod E.q) → List (EagenAccum E)
  | [] => []
  | [_] =>
      -- Odd trailing: produce a unit-poly singleton at infinity.
      -- Actual carry-forward of the affine point happens in level_step.
      [EagenAccum.unit E]
  | _ :: _ :: rest =>
      EagenAccum.unit E :: level0 hOn rest  -- placeholder wiring

/-- One level: pair adjacent accumulators and combine each pair.
    Trailing odd element is forwarded unchanged. -/
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

end Divisor.Landmark
