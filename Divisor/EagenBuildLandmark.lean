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

The invariant that ties the field to a list of absorbed inputs
`xs : List (ZMod q × ZMod q)` is that
  - `point = sum_E(xs.map ECPoint.affineOfMem)` (group-law sum on E),
  - `poly` vanishes at every input in `xs`,
  - `(normPoly poly).natDegree = xs.length + (1 if point ≠ 0 else 0)`.

The first conjunct is enforced via the recursion's structure (each
combine respects the group law). The latter two are the "Landmark"
content. -/
structure EagenAccum where
  point : ECPoint E
  poly : CoordRingElt E.q

/-! ## The recursive driver

The recursion has three layers:

  - `level0`: from a list of input points `Ps`, produce a list of
    accumulators by pairing adjacent inputs. Each pair becomes one
    accumulator; an odd trailing element is carried forward as a
    "trivial" accumulator (its point = the input lifted, poly = 1).

  - `level_step`: combine adjacent accumulators in the list. Each
    pair `(a, b)` produces one new accumulator via `combine`, which
    dispatches on the relationship between `a.point` and `b.point`.

  - `iterate`: apply `level_step` until the list reduces to a
    singleton.

The case analysis in `combine`:

  - both points are 0 (= O): the absorbed sub-lists are sum-zero;
    multiply polynomials, new point = 0.
  - one point is 0, the other isn't: forward the non-zero point
    along, multiply polynomials.
  - both are .some affine, with different x-coords: chord case.
    Use `chordCoordRingElt` (which dispatches further on chord
    vs. tangent vs. vertical based on point comparison).
  - both are .some affine, same x but different y: vertical line
    `(X - C a.point.1)`; new point = O.
  - both are the same affine point with y = 0: vertical line
    again; new point = O (2-torsion doubling).
  - both are the same affine point with y ≠ 0: tangent line; new
    point = -2·a.point.

The 4-case `chordCoordRingElt` already handles the line-shape
dispatch internally. The combine logic only needs to determine
the new running-sum point and the divLin schedule.
-/

end Divisor.Landmark
