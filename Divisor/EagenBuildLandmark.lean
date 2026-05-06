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

/-! ## Constructive local multiplicity, independent of `ordAt`

The definitions below are deliberately parallel to the local-order
construction in `OrdP.Uniformizer`, but they do not mention `ordAt`.
They are the polynomial recursion needed for the stronger Landmark
invariant: on a non-2-torsion sheet, a twin-sheet zero cancels one
vertical factor `(X - x₀)` from both coordinates and recurses; a lone
sheet zero is measured by the root multiplicity of the norm polynomial.

This gives a local, point/sheet-level multiplicity suitable for
combine-step bookkeeping without importing divisor identities. -/

noncomputable def localMultTwoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if D.a = 0 ∧ D.b = 0 then 0
    else if D.a = 0 then 2 * rootMultiplicity P.1 D.b + 1
    else if D.b = 0 then 2 * rootMultiplicity P.1 D.a
    else min (2 * rootMultiplicity P.1 D.a) (2 * rootMultiplicity P.1 D.b + 1)

noncomputable def localMultNonTwoAux :
    ℕ → CoordRingElt E.q → (ZMod E.q × ZMod E.q) → ℕ
  | 0,       _, _ => 0
  | fuel + 1, D, P =>
      if D.a = 0 ∧ D.b = 0 then 0
      else if D.eval P.1 P.2 ≠ 0 then 0
      else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
      else 1 + localMultNonTwoAux fuel (D.divLin P.1) P

noncomputable def localMultNonTwo
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ :=
  localMultNonTwoAux E (D.a.natDegree + D.b.natDegree + 1) D P

noncomputable def localMult
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact
    if P ∈ E.points ∧ ¬ (D.a = 0 ∧ D.b = 0) then
      if P.2 = 0 then localMultTwoTorsion E D P
      else localMultNonTwo E D P
    else 0

theorem localMult_eq_zero_of_offE_or_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (h : ¬ (P ∈ E.points ∧ ¬ (D.a = 0 ∧ D.b = 0))) :
    localMult E D P = 0 := by
  classical
  unfold localMult
  rw [if_neg h]

theorem localMult_eq_dispatch
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    localMult E D P =
      (if P.2 = 0 then localMultTwoTorsion E D P
       else localMultNonTwo E D P) := by
  classical
  unfold localMult
  rw [if_pos ⟨hP, hD⟩]

theorem localMultTwoTorsion_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (h : D.eval x₀ 0 ≠ 0) :
    localMultTwoTorsion E D (x₀, 0) = 0 := by
  classical
  have ha_ne : D.a.eval x₀ ≠ 0 := by
    have := h
    unfold CoordRingElt.eval at this
    simpa using this
  have hRootA : Polynomial.rootMultiplicity x₀ D.a = 0 :=
    Polynomial.rootMultiplicity_eq_zero ha_ne
  have ha_poly_ne : D.a ≠ 0 := by
    intro hzero
    apply ha_ne
    rw [hzero]
    simp
  unfold localMultTwoTorsion
  by_cases hb : D.b = 0
  · simp [ha_poly_ne, hb, hRootA]
  · simp [ha_poly_ne, hb, hRootA]

theorem localMultNonTwo_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (h : D.eval P.1 P.2 ≠ 0) :
    localMultNonTwo E D P = 0 := by
  classical
  unfold localMultNonTwo localMultNonTwoAux
  by_cases hZero : D.a = 0 ∧ D.b = 0
  · exfalso
    apply h
    obtain ⟨ha, hb⟩ := hZero
    unfold CoordRingElt.eval
    rw [ha, hb]
    simp
  · simp [hZero, h]

theorem localMult_eq_zero_of_eval_ne_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points)
    (hEval : D.eval P.1 P.2 ≠ 0) :
    localMult E D P = 0 := by
  classical
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := by
    intro ⟨ha, hb⟩
    apply hEval
    unfold CoordRingElt.eval
    rw [ha, hb]
    simp
  rw [localMult_eq_dispatch E D hP hD]
  by_cases h2 : P.2 = 0
  · rw [if_pos h2]
    have hPeq : P = (P.1, 0) := by
      ext <;> simp [h2]
    rw [hPeq]
    apply localMultTwoTorsion_eq_zero_of_eval_ne_zero E D
    rw [show D.eval P.1 0 = D.eval P.1 P.2 from by rw [h2]]
    exact hEval
  · rw [if_neg h2]
    exact localMultNonTwo_eq_zero_of_eval_ne_zero E D hEval

theorem eval_eq_zero_of_localMult_pos
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hpos : 0 < localMult E D P) :
    D.eval P.1 P.2 = 0 := by
  classical
  by_contra hne
  have hzero := localMult_eq_zero_of_eval_ne_zero E D hP hne
  omega

theorem localMult_ge_one_of_eval_eq_zero
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hEval : D.eval P.1 P.2 = 0) :
    localMult E D P ≥ 1 := by
  classical
  rw [localMult_eq_dispatch E D hP hD]
  by_cases h2 : P.2 = 0
  · rw [if_pos h2]
    have ha_eval : D.a.eval P.1 = 0 := by
      have hEval' := hEval
      unfold CoordRingElt.eval at hEval'
      rw [h2] at hEval'
      simpa using hEval'
    unfold localMultTwoTorsion
    rw [if_neg hD]
    by_cases ha : D.a = 0
    · rw [if_pos ha]
      omega
    · rw [if_neg ha]
      have hRootA_pos : 0 < rootMultiplicity P.1 D.a := by
        rw [Polynomial.rootMultiplicity_pos ha]
        exact ha_eval
      by_cases hb : D.b = 0
      · rw [if_pos hb]
        omega
      · rw [if_neg hb]
        exact le_min (by omega) (by omega)
  · rw [if_neg h2]
    unfold localMultNonTwo localMultNonTwoAux
    rw [if_neg hD, if_neg (not_not.mpr hEval)]
    by_cases hNeg : D.eval P.1 (-P.2) ≠ 0
    · rw [if_pos hNeg]
      exact rootMultiplicity_normPoly_pos E D hP hEval hD
    · rw [if_neg hNeg]
      omega

theorem localMultTwoTorsion_eq_ordAt_twoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    localMultTwoTorsion E D P = ordAt_twoTorsion E D P := by
  classical
  unfold localMultTwoTorsion ordAt_twoTorsion
  rfl

theorem localMultNonTwoAux_eq_ordAt_nonTwoTorsion_aux
    (fuel : ℕ) (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    localMultNonTwoAux E fuel D P = ordAt_nonTwoTorsion_aux E fuel D P := by
  classical
  induction fuel generalizing D with
  | zero => rfl
  | succ fuel ih =>
      unfold localMultNonTwoAux ordAt_nonTwoTorsion_aux
      by_cases hD : D.a = 0 ∧ D.b = 0
      · rw [if_pos hD, if_pos hD]
      · rw [if_neg hD, if_neg hD]
        by_cases hEval : D.eval P.1 P.2 ≠ 0
        · rw [if_pos hEval, if_pos hEval]
        · rw [if_neg hEval, if_neg hEval]
          by_cases hNeg : D.eval P.1 (-P.2) ≠ 0
          · rw [if_pos hNeg, if_pos hNeg]
          · rw [if_neg hNeg, if_neg hNeg, ih]

theorem localMultNonTwo_eq_ordAt_nonTwoTorsion
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    localMultNonTwo E D P = ordAt_nonTwoTorsion E D P := by
  unfold localMultNonTwo ordAt_nonTwoTorsion
  exact localMultNonTwoAux_eq_ordAt_nonTwoTorsion_aux E _ D P

theorem localMult_eq_ordAt
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q) :
    localMult E D P = ordAt E D P := by
  classical
  unfold localMult ordAt
  by_cases h : P ∈ E.points ∧ ¬ (D.a = 0 ∧ D.b = 0)
  · rw [if_pos h, if_pos h]
    by_cases h2 : P.2 = 0
    · rw [if_pos h2, if_pos h2]
      exact localMultTwoTorsion_eq_ordAt_twoTorsion E D P
    · rw [if_neg h2, if_neg h2]
      exact localMultNonTwo_eq_ordAt_nonTwoTorsion E D P
  · rw [if_neg h, if_neg h]

theorem localMult_mulCoordRingElt_eq_add_when_rootMult_le_one
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hD₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (hD₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 1) :
    localMult E (mulCoordRingElt E D₁ D₂) P
      = localMult E D₁ P + localMult E D₂ P := by
  simpa [localMult_eq_ordAt] using
    (Divisor.ordAt_mul_add_when_normPoly_D2_le_one (E := E)
      (D₁ := D₁) (D₂ := D₂) hD₁ hD₂ hP hRoot)

theorem localMult_mulCoordRingElt_ge_add_general
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hD₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (hD₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 1
              ∨ Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 1) :
    localMult E D₁ P + localMult E D₂ P
      ≤ localMult E (mulCoordRingElt E D₁ D₂) P := by
  rcases hRoot with hRoot₂ | hRoot₁
  · have hEq := localMult_mulCoordRingElt_eq_add_when_rootMult_le_one
      (E := E) D₁ D₂ P hP hD₁ hD₂ hRoot₂
    exact le_of_eq hEq.symm
  · have hEq := localMult_mulCoordRingElt_eq_add_when_rootMult_le_one
      (E := E) D₂ D₁ P hP hD₂ hD₁ hRoot₁
    refine le_of_eq ?_
    calc
      localMult E D₁ P + localMult E D₂ P
          = localMult E D₂ P + localMult E D₁ P := by rw [add_comm]
      _ = localMult E (mulCoordRingElt E D₂ D₁) P := hEq.symm
      _ = localMult E (mulCoordRingElt E D₁ D₂) P := by
        rw [mulCoordRingElt_comm E D₁ D₂]

theorem localMult_divLin_decreases_at_fiber
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hDvd_a : (X - C P.1) ∣ D.a)
    (hDvd_b : (X - C P.1) ∣ D.b)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    localMult E (D.divLin P.1) P + 1 ≤ localMult E D P
      ∨ localMult E D P = 0 := by
  classical
  left
  have ha_eval : D.a.eval P.1 = 0 := Polynomial.dvd_iff_isRoot.mp hDvd_a
  have hb_eval : D.b.eval P.1 = 0 := Polynomial.dvd_iff_isRoot.mp hDvd_b
  by_cases h2 : P.2 = 0
  · have hrec :=
      ordAt_twoTorsion_divLin_rec E D hD hP h2 ha_eval hb_eval
    have hrec_local :
        localMult E D P = 2 + localMult E (D.divLin P.1) P := by
      simpa [localMult_eq_ordAt] using hrec
    omega
  · have hD' : ¬ ((D.divLin P.1).a = 0 ∧ (D.divLin P.1).b = 0) :=
      divLin_not_both_zero E D hD ha_eval hb_eval
    have hEval : D.eval P.1 P.2 = 0 := by
      unfold CoordRingElt.eval
      rw [ha_eval, hb_eval]
      ring
    have hEvalNeg : D.eval P.1 (-P.2) = 0 := by
      unfold CoordRingElt.eval
      rw [ha_eval, hb_eval]
      ring
    have hrec :=
      ordAt_nonTwoTorsion_twin_rec E D hD h2 hEval hEvalNeg
    have hrec_local :
        localMult E D P = 1 + localMult E (D.divLin P.1) P := by
      rw [localMult_eq_dispatch E D hP hD,
          localMult_eq_dispatch E (D.divLin P.1) hP hD',
          if_neg h2, if_neg h2]
      simpa [localMultNonTwo_eq_ordAt_nonTwoTorsion] using hrec
    omega

theorem localMult_divLin_decreases_by_two_at_twoTorsion_fiber
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (h2 : P.2 = 0)
    (hDvd_a : (X - C P.1) ∣ D.a)
    (hDvd_b : (X - C P.1) ∣ D.b)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    localMult E D P = 2 + localMult E (D.divLin P.1) P := by
  have ha_eval : D.a.eval P.1 = 0 := Polynomial.dvd_iff_isRoot.mp hDvd_a
  have hb_eval : D.b.eval P.1 = 0 := Polynomial.dvd_iff_isRoot.mp hDvd_b
  simpa [localMult_eq_ordAt] using
    (ordAt_twoTorsion_divLin_rec E D hD hP h2 ha_eval hb_eval)

/-! ## Target multiplicity carried by a Landmark accumulator -/

noncomputable def target
    (xs : List (ZMod E.q × ZMod E.q)) (R : ECPoint E)
    (P : ZMod E.q × ZMod E.q) : ℕ := by
  classical
  exact xs.count P + if negCoords E R = some P then 1 else 0

noncomputable def targetMass
    (xs : List (ZMod E.q × ZMod E.q)) (R : ECPoint E) : ℕ :=
  ∑ P ∈ E.points, target E xs R P

theorem target_def
    (xs : List (ZMod E.q × ZMod E.q)) (R : ECPoint E)
    (P : ZMod E.q × ZMod E.q) :
    target E xs R P =
      xs.count P + if negCoords E R = some P then 1 else 0 := by
  classical
  rfl

@[simp] theorem target_nil_zero (P : ZMod E.q × ZMod E.q) :
    target E [] (0 : ECPoint E) P = 0 := by
  classical
  simp [target, negCoords]

theorem target_append
    (xs ys : List (ZMod E.q × ZMod E.q)) (R : ECPoint E)
    (P : ZMod E.q × ZMod E.q) :
    target E (xs ++ ys) R P = target E xs R P + ys.count P := by
  classical
  simp [target, List.count_append]
  omega

theorem one_le_target_of_mem
    {xs : List (ZMod E.q × ZMod E.q)} {R : ECPoint E}
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ xs) :
    1 ≤ target E xs R P := by
  classical
  unfold target
  have hcount : 0 < xs.count P := List.count_pos_iff.mpr hP
  omega

theorem one_le_target_of_residue
    {xs : List (ZMod E.q × ZMod E.q)} {R : ECPoint E}
    {P : ZMod E.q × ZMod E.q}
    (hR : negCoords E R = some P) :
    1 ≤ target E xs R P := by
  classical
  unfold target
  rw [if_pos hR]
  omega

/-! ## Strengthened Landmark invariant sketch

`LandmarkInvStrong xs a` is the intended replacement for the older
vanishing-only invariant.  The pointwise lower bound says the
accumulator polynomial has at least the required sheet-level
multiplicity at every affine point of `E`; the `natDegree` equality
keeps the old global mass accounting. -/

noncomputable def LandmarkInvStrong
    (xs : List (ZMod E.q × ZMod E.q)) (a : EagenAccum E) : Prop :=
  a.point = sumOnE E xs ∧
  (∀ P : ZMod E.q × ZMod E.q,
    P ∈ E.points → target E xs a.point P ≤ localMult E a.poly P) ∧
  letI : Decidable (a.point = (0 : ECPoint E)) :=
    Classical.dec _
  (normPoly E a.poly).natDegree =
    xs.length + (if a.point = (0 : ECPoint E) then 0 else 1)

theorem LandmarkInvStrong.running_sum
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a) :
    a.point = sumOnE E xs := h.1

theorem LandmarkInvStrong.target_le
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a) :
    ∀ P : ZMod E.q × ZMod E.q,
      P ∈ E.points → target E xs a.point P ≤ localMult E a.poly P := h.2.1

theorem LandmarkInvStrong.natDegree
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a) :
    letI : Decidable (a.point = (0 : ECPoint E)) :=
      Classical.dec _
    (normPoly E a.poly).natDegree =
      xs.length + (if a.point = (0 : ECPoint E) then 0 else 1) := h.2.2

theorem LandmarkInvStrong.vanish_of_mem
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a)
    {P : ZMod E.q × ZMod E.q} (hPxs : P ∈ xs) (hPon : P ∈ E.points) :
    a.poly.eval P.1 P.2 = 0 := by
  have htarget : 1 ≤ target E xs a.point P :=
    one_le_target_of_mem E hPxs
  have hle := LandmarkInvStrong.target_le E h P hPon
  exact eval_eq_zero_of_localMult_pos E a.poly hPon (by omega)

theorem LandmarkInvStrong.vanish_of_residue
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a)
    {P : ZMod E.q × ZMod E.q}
    (hR : negCoords E a.point = some P) (hPon : P ∈ E.points) :
    a.poly.eval P.1 P.2 = 0 := by
  have htarget : 1 ≤ target E xs a.point P :=
    one_le_target_of_residue E hR
  have hle := LandmarkInvStrong.target_le E h P hPon
  exact eval_eq_zero_of_localMult_pos E a.poly hPon (by omega)

/-!
Major follow-up obligations needed to make `PairwiseCombineHyp`
unconditional:

* `localMult_mulCoordRingElt_ge_add`:
  lower-bound multiplicity of a product by the sum of local
  multiplicities.

* `localMult_divLin_same_fiber`:
  if both coordinates of `D` are divisible by `X - C P.1`, then
  `localMult E (D.divLin P.1) P + verticalTarget P =
   localMult E D P`.

* `localMult_chordCoordRingElt_exact`:
  pointwise local multiplicity of `chordCoordRingElt E A B`; this is
  the `L(A,B)` term in the identity, including tangent double contact.

* `landmarkInvStrong_combine_oo`, `landmarkInvStrong_combine_ol`,
  `landmarkInvStrong_combine_or`, `landmarkInvStrong_combine_vertical`,
  `landmarkInvStrong_combine_distinct`, `landmarkInvStrong_combine_tangent`:
  the five-plus preservation cases against `LandmarkInvStrong`.

* `pairwiseCombineHyp_of_landmarkInvStrong`:
  convert the strengthened preservation theorem back to the existing
  `Landmark.PairwiseCombineHyp E`, or replace downstream uses of the
  old invariant with `LandmarkInvStrong` directly.
-/

theorem localMult_chordCoordRingElt_at_left
    {P Q : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) :
    localMult E (chordCoordRingElt E P Q) P ≥ 1 := by
  exact localMult_ge_one_of_eval_eq_zero E (chordCoordRingElt E P Q) hP
    (chordCoordRingElt_ne_zero E P Q)
    (chordCoordRingElt_eval_left E P Q)

theorem localMult_chordCoordRingElt_at_right
    {P Q : ZMod E.q × ZMod E.q}
    (hQ : Q ∈ E.points) :
    localMult E (chordCoordRingElt E P Q) Q ≥ 1 := by
  exact localMult_ge_one_of_eval_eq_zero E (chordCoordRingElt E P Q) hQ
    (chordCoordRingElt_ne_zero E P Q)
    (chordCoordRingElt_eval_right E P Q)

theorem localMult_chordCoordRingElt_at_third
    {P Q : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (hxx : P.1 ≠ Q.1) :
    let lam := slopeOf P.1 P.2 Q.1 Q.2
    let x₂ := lam ^ 2 - P.1 - Q.1
    let y₂ := lam * x₂ + (P.2 - lam * P.1)
    localMult E (chordCoordRingElt E P Q) (x₂, y₂) ≥ 1 := by
  intro lam x₂ y₂
  have hT : thirdPoint E P Q = some (x₂, y₂) := by
    unfold thirdPoint
    rw [if_neg hxx]
    simp [x₂, y₂, lam, slopeOf]
  have hThirdOn : (x₂, y₂) ∈ E.points :=
    third_point_on_curve E P Q hP hQ hT
  apply localMult_ge_one_of_eval_eq_zero E (chordCoordRingElt E P Q) hThirdOn
  · exact chordCoordRingElt_ne_zero E P Q
  · have hEval := chordCoordRingElt_eval_thirdPoint_chord (E := E) hP hQ hxx
    simpa [x₂, y₂, lam, slopeOf] using hEval

theorem localMult_chordCoordRingElt_at_third_neg
    {P Q : ZMod E.q × ZMod E.q}
    (_hP : P ∈ E.points) (_hQ : Q ∈ E.points)
    (_hxx : P.1 ≠ Q.1) :
    let lam := slopeOf P.1 P.2 Q.1 Q.2
    let x₂ := lam ^ 2 - P.1 - Q.1
    let y₂ := lam * x₂ + (P.2 - lam * P.1)
    localMult E (chordCoordRingElt E P Q) (x₂, -y₂) ≥ 0 := by
  intro lam x₂ y₂
  exact Nat.zero_le _

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

theorem LandmarkInvStrong.to_LandmarkInv
    {xs : List (ZMod E.q × ZMod E.q)} {a : EagenAccum E}
    (h : LandmarkInvStrong E xs a)
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hres_on : ∀ P : ZMod E.q × ZMod E.q,
      negCoords E a.point = some P → P ∈ E.points) :
    LandmarkInv E xs a := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact LandmarkInvStrong.running_sum E h
  · intro P hP
    exact LandmarkInvStrong.vanish_of_mem E h hP (hxs_on P hP)
  · intro P hP
    exact LandmarkInvStrong.vanish_of_residue E h hP (hres_on P hP)
  · exact LandmarkInvStrong.natDegree E h

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

theorem landmarkInvStrong_combine_oo_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_oo E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt, hb_pt, zero_add]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_count_le : xs.count P ≤ localMult E a.poly P := by
      have htarget : target E xs a.point P = xs.count P := by
        rw [ha_pt]
        simp [target, negCoords]
      simpa [htarget] using ha_target_le
    have hb_count_le : ys.count P ≤ localMult E b.poly P := by
      have htarget : target E ys b.point P = ys.count P := by
        rw [hb_pt]
        simp [target, negCoords]
      simpa [htarget] using hb_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      apply localMult_mulCoordRingElt_ge_add_general E a.poly b.poly P
        hPon ha_poly_nz hb_poly_nz
      rcases h_root_le P hPon with hroot_a | hroot_b
      · exact Or.inr hroot_a
      · exact Or.inl hroot_b
    calc
      target E (xs ++ ys) (EagenAccum.combine_oo E a b).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_oo, negCoords, List.count_append]
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_count_le hb_count_le
      _ ≤ localMult E (EagenAccum.combine_oo E a b).poly P := by
            simpa [EagenAccum.combine_oo] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_oo E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_pos ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    have h_combined_zero : (EagenAccum.combine_oo E a b).point = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero, ha_deg, hb_deg, List.length_append]
    omega

theorem landmarkInvStrong_combine_ol_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_b_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E b.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point ≠ (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_ol E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have _h_neg_b_on := h_neg_b_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show b.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt, zero_add]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_count_le : xs.count P ≤ localMult E a.poly P := by
      have htarget : target E xs a.point P = xs.count P := by
        rw [ha_pt]
        simp [target, negCoords]
      simpa [htarget] using ha_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      apply localMult_mulCoordRingElt_ge_add_general E a.poly b.poly P
        hPon ha_poly_nz hb_poly_nz
      rcases h_root_le P hPon with hroot_a | hroot_b
      · exact Or.inr hroot_a
      · exact Or.inl hroot_b
    calc
      target E (xs ++ ys) (EagenAccum.combine_ol E a b).point P
          = xs.count P + target E ys b.point P := by
            simp [target, EagenAccum.combine_ol, List.count_append]
            omega
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_count_le hb_target_le
      _ ≤ localMult E (EagenAccum.combine_ol E a b).poly P := by
            simpa [EagenAccum.combine_ol] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_ol E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_pos ha_pt] at ha_deg
    rw [if_neg hb_pt] at hb_deg
    have h_combined_pt : (EagenAccum.combine_ol E a b).point = b.point := rfl
    rw [h_combined_pt, if_neg hb_pt, ha_deg, hb_deg, List.length_append]
    omega

theorem landmarkInvStrong_combine_or_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_a_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E a.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point ≠ (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_or E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have _h_neg_a_on := h_neg_a_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show a.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, hb_pt, add_zero]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have hb_count_le : ys.count P ≤ localMult E b.poly P := by
      have htarget : target E ys b.point P = ys.count P := by
        rw [hb_pt]
        simp [target, negCoords]
      simpa [htarget] using hb_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      apply localMult_mulCoordRingElt_ge_add_general E a.poly b.poly P
        hPon ha_poly_nz hb_poly_nz
      rcases h_root_le P hPon with hroot_a | hroot_b
      · exact Or.inr hroot_a
      · exact Or.inl hroot_b
    calc
      target E (xs ++ ys) (EagenAccum.combine_or E a b).point P
          = target E xs a.point P + ys.count P := by
            simp [target, EagenAccum.combine_or, List.count_append]
            omega
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_target_le hb_count_le
      _ ≤ localMult E (EagenAccum.combine_or E a b).poly P := by
            simpa [EagenAccum.combine_or] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_or E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_neg ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    have h_combined_pt : (EagenAccum.combine_or E a b).point = a.point := rfl
    rw [h_combined_pt, if_neg ha_pt, ha_deg, hb_deg, List.length_append]
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

theorem mul_components_eval_zero_at_twoTorsion
    (D₁ D₂ : CoordRingElt E.q) {x₀ : ZMod E.q}
    (hP : (x₀, (0 : ZMod E.q)) ∈ E.points)
    (hD₁ : D₁.eval x₀ 0 = 0) (hD₂ : D₂.eval x₀ 0 = 0) :
    (mulCoordRingElt E D₁ D₂).a.eval x₀ = 0 ∧
      (mulCoordRingElt E D₁ D₂).b.eval x₀ = 0 := by
  have hD₁a : D₁.a.eval x₀ = 0 := by
    simpa [CoordRingElt.eval] using hD₁
  have hD₂a : D₂.a.eval x₀ = 0 := by
    simpa [CoordRingElt.eval] using hD₂
  have hCurveX : (curveX E).eval x₀ = 0 := by
    have hOC : (0 : ZMod E.q) ^ 2 = x₀ ^ 3 + E.curveA * x₀ + E.curveB :=
      E.hOnCurve _ hP
    unfold curveX
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    simpa using hOC.symm
  refine ⟨?_, ?_⟩
  · show (D₁.a * D₂.a + D₁.b * D₂.b * curveX E).eval x₀ = 0
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hD₁a, hD₂a, hCurveX]
    ring
  · show (D₁.a * D₂.b + D₂.a * D₁.b).eval x₀ = 0
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    rw [hD₁a, hD₂a]
    ring

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

theorem ord_vertical_at_x₀_twoTorsion
    (x₀ : ZMod E.q) (hP : (x₀, (0 : ZMod E.q)) ∈ E.points) :
    ordAt E ({ a := X - C x₀, b := 0 } : CoordRingElt E.q) (x₀, 0) = 2 := by
  let Lv : CoordRingElt E.q := { a := X - C x₀, b := 0 }
  have hLv_NZ : ¬ (Lv.a = 0 ∧ Lv.b = 0) := by
    intro hzero
    exact (X_sub_C_ne_zero x₀) hzero.1
  have hNorm : normPoly E Lv = (X - C x₀) ^ 2 := by
    simp [Lv, normPoly_eq]
  calc
    ordAt E ({ a := X - C x₀, b := 0 } : CoordRingElt E.q) (x₀, 0)
        = ordAt E Lv (x₀, 0) := rfl
    _ = ordAt_twoTorsion E Lv (x₀, 0) := by
          rw [ordAt_eq_dispatch E Lv hP hLv_NZ, if_pos rfl]
    _ = rootMultiplicity x₀ (normPoly E Lv) := by
          exact ordAt_twoTorsion_eq_rootMult_normPoly E Lv hLv_NZ hP rfl
    _ = rootMultiplicity x₀ ((X - C x₀) ^ 2 : (ZMod E.q)[X]) := by
          rw [hNorm]
    _ = 2 := by
          rw [Polynomial.rootMultiplicity_X_sub_C_pow]

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

theorem landmarkInvStrong_combine_vertical_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya : ZMod E.q}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxy_on : (xa, ya) ∈ E.points)
    (hxy_neg_on : (xa, -ya) ∈ E.points)
    (hy_ne : ya ≠ 0)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xa (-ya))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_vertical E a b xa) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  -- Residue evaluations from the two inputs give vanishing on both sheets
  -- of the vertical fiber.
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
  have ha_van_neg : a.poly.eval xa (-ya) = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxy_neg_on
  have hb_van_pos : b.poly.eval xa ya = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxy_on
  set q := mulCoordRingElt E a.poly b.poly with hq_def
  have hq_eval_pos : q.eval xa ya = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_on, hb_van_pos]
    ring
  have hq_eval_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_neg_on, ha_van_neg]
    ring
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hy_ne hq_eval_pos hq_eval_neg
  have h_dvd_a : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_b : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq]
    exact mul_ne_zero ha_nz hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_div_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) :=
    divLin_not_both_zero E q hq_poly_nz h_qa_xa h_qb_xa
  let Lv : CoordRingElt E.q := { a := X - C xa, b := 0 }
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lv := by
    simpa [Lv] using mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_a h_dvd_b
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    have hns_b : E.toW.toAffine.Nonsingular xa (-ya) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa (-ya)).mpr (E.hOnCurve _ hxy_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    show (0 : ECPoint E) = (.some hns_a + .some hns_b : ECPoint E)
    have h_neg : (.some hns_b : ECPoint E) = -(.some hns_a) := by
      show WeierstrassCurve.Affine.Point.some hns_b
            = -WeierstrassCurve.Affine.Point.some hns_a
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg]
    show (0 : ECPoint E) = .some hns_a + (-.some hns_a)
    rw [add_neg_cancel]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if negCoords E a.point = some P then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target] using ha_target_le
    have hb_target_le' :
        ys.count P + (if negCoords E b.point = some P then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target] using hb_target_le
    have hLv_bound :
        localMult E Lv P
          ≤ (if negCoords E a.point = some P then 1 else 0)
            + (if negCoords E b.point = some P then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : ya = P.2 ∨ ya = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxy_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xa, ya) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using ord_vertical_at_x₀_nonTwoTorsion E xa ya hxy_on hy_ne
          rw [hLv_eq, hP_eq, if_pos hb_neg]
          omega
        · have hP_eq : P = (xa, -ya) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -ya ≠ 0 := by
            simpa using (neg_ne_zero.mpr hy_ne)
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, -ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using
                  ord_vertical_at_x₀_nonTwoTorsion E xa (-ya) hxy_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos ha_neg]
          omega
      · have hLv_eval_ne : Lv.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lv, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lv P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lv hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have htargets_plus_vertical_le :
        xs.count P + ys.count P + localMult E Lv P
          ≤ localMult E a.poly P + localMult E b.poly P := by
      omega
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E q P := by
      rw [hq_def]
      apply localMult_mulCoordRingElt_ge_add_general E a.poly b.poly P
        hPon ha_poly_nz hb_poly_nz
      rcases h_root_le P hPon with hroot_a | hroot_b
      · exact Or.inr hroot_a
      · exact Or.inl hroot_b
    have hq_local_eq :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) hq_div_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lv) P :=
          congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lv P := by simpa [Lv] using h
        _ = localMult E (q.divLin xa) P + localMult E Lv P := by
          rw [← localMult_eq_ordAt E (q.divLin xa) P,
              ← localMult_eq_ordAt E Lv P]
    calc
      target E (xs ++ ys) (EagenAccum.combine_vertical E a b xa).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_vertical, negCoords, List.count_append]
      _ ≤ localMult E (q.divLin xa) P := by
            have h :
                xs.count P + ys.count P + localMult E Lv P
                  ≤ localMult E (q.divLin xa) P + localMult E Lv P := by
              calc
                xs.count P + ys.count P + localMult E Lv P
                    ≤ localMult E a.poly P + localMult E b.poly P :=
                      htargets_plus_vertical_le
                _ ≤ localMult E q P := hprod_le
                _ = localMult E (q.divLin xa) P + localMult E Lv P := hq_local_eq
            omega
      _ = localMult E (EagenAccum.combine_vertical E a b xa).poly P := by
            simp [EagenAccum.combine_vertical, hq_def]
  · show (normPoly E (q.divLin xa)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_vertical E a b xa).point
                                  = (0 : ECPoint E) then 0 else 1)
    have h_combined_zero : (EagenAccum.combine_vertical E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    have h_factorize := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
      E q xa h_dvd_a h_dvd_b
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
      have ha_deg := LandmarkInvStrong.natDegree E ha
      have hb_deg := LandmarkInvStrong.natDegree E hb
      rw [if_neg hap] at ha_deg
      rw [if_neg hbp] at hb_deg
      omega
    rw [List.length_append]
    omega

theorem landmarkInvStrong_combine_tangent_torsion_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa : ZMod E.q}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxy_on : (xa, (0 : ZMod E.q)) ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa 0)
    (hb_pt_eq : b.point = ECPoint.affine E xa 0)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_tangent_torsion E a b xa) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have ha_neg : negCoords E a.point = some (xa, (0 : ZMod E.q)) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show some (xa, -(0 : ZMod E.q)) = some (xa, 0)
    rw [neg_zero]
  have hb_neg : negCoords E b.point = some (xa, (0 : ZMod E.q)) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show some (xa, -(0 : ZMod E.q)) = some (xa, 0)
    rw [neg_zero]
  have ha_van : a.poly.eval xa 0 = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxy_on
  have hb_van : b.poly.eval xa 0 = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxy_on
  set q := mulCoordRingElt E a.poly b.poly with hq_def
  obtain ⟨h_qa_xa, h_qb_xa⟩ : q.a.eval xa = 0 ∧ q.b.eval xa = 0 := by
    rw [hq_def]
    exact mul_components_eval_zero_at_twoTorsion E a.poly b.poly hxy_on ha_van hb_van
  have h_dvd_a : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_b : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq]
    exact mul_ne_zero ha_nz hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have _hdrop_torsion :
      localMult E q (xa, (0 : ZMod E.q))
        = 2 + localMult E (q.divLin xa) (xa, (0 : ZMod E.q)) :=
    localMult_divLin_decreases_by_two_at_twoTorsion_fiber
      E q (xa, (0 : ZMod E.q)) hxy_on rfl h_dvd_a h_dvd_b hq_poly_nz
  have hq_div_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) :=
    divLin_not_both_zero E q hq_poly_nz h_qa_xa h_qb_xa
  let Lv : CoordRingElt E.q := { a := X - C xa, b := 0 }
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lv := by
    simpa [Lv] using mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_a h_dvd_b
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show (0 : ECPoint E) = (.some hns + .some hns : ECPoint E)
    have hself_neg : (-(.some hns : ECPoint E)) = .some hns := by
      show -(WeierstrassCurve.Affine.Point.some hns : ECPoint E)
          = WeierstrassCurve.Affine.Point.some hns
      simp [WeierstrassCurve.Affine.Point.neg_some]
    calc
      (0 : ECPoint E) = (.some hns : ECPoint E) + (-.some hns) := by
        rw [add_neg_cancel]
      _ = (.some hns : ECPoint E) + .some hns := by
        rw [hself_neg]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if negCoords E a.point = some P then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target] using ha_target_le
    have hb_target_le' :
        ys.count P + (if negCoords E b.point = some P then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target] using hb_target_le
    have hLv_bound :
        localMult E Lv P
          ≤ (if negCoords E a.point = some P then 1 else 0)
            + (if negCoords E b.point = some P then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : (0 : ZMod E.q) = P.2 ∨ (0 : ZMod E.q) = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxy_on hP_on_x
        have hP_eq : P = (xa, (0 : ZMod E.q)) := by
          rcases hy_dich with hy_eq | hy_eq_neg
          · ext
            · exact hPx
            · exact hy_eq.symm
          · ext
            · exact hPx
            · exact neg_eq_zero.mp hy_eq_neg.symm
        have hLv_eq : localMult E Lv P = 2 := by
          calc
            localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
            _ = ordAt E Lv (xa, (0 : ZMod E.q)) := by rw [hP_eq]
            _ = 2 := by
              simpa [Lv] using ord_vertical_at_x₀_twoTorsion E xa hxy_on
        rw [hLv_eq, hP_eq, if_pos ha_neg, if_pos hb_neg]
      · have hLv_eval_ne : Lv.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lv, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lv P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lv hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have htargets_plus_vertical_le :
        xs.count P + ys.count P + localMult E Lv P
          ≤ localMult E a.poly P + localMult E b.poly P := by
      omega
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E q P := by
      rw [hq_def]
      apply localMult_mulCoordRingElt_ge_add_general E a.poly b.poly P
        hPon ha_poly_nz hb_poly_nz
      rcases h_root_le P hPon with hroot_a | hroot_b
      · exact Or.inr hroot_a
      · exact Or.inl hroot_b
    have hq_local_eq :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) hq_div_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lv) P :=
          congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lv P := by simpa [Lv] using h
        _ = localMult E (q.divLin xa) P + localMult E Lv P := by
          rw [← localMult_eq_ordAt E (q.divLin xa) P,
              ← localMult_eq_ordAt E Lv P]
    calc
      target E (xs ++ ys) (EagenAccum.combine_tangent_torsion E a b xa).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_tangent_torsion,
              EagenAccum.combine_vertical, negCoords, List.count_append]
      _ ≤ localMult E (q.divLin xa) P := by
            have h :
                xs.count P + ys.count P + localMult E Lv P
                  ≤ localMult E (q.divLin xa) P + localMult E Lv P := by
              calc
                xs.count P + ys.count P + localMult E Lv P
                    ≤ localMult E a.poly P + localMult E b.poly P :=
                      htargets_plus_vertical_le
                _ ≤ localMult E q P := hprod_le
                _ = localMult E (q.divLin xa) P + localMult E Lv P := hq_local_eq
            omega
      _ = localMult E (EagenAccum.combine_tangent_torsion E a b xa).poly P := by
            simp [EagenAccum.combine_tangent_torsion,
              EagenAccum.combine_vertical, hq_def]
  · show (normPoly E (q.divLin xa)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_tangent_torsion E a b xa).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_zero : (EagenAccum.combine_tangent_torsion E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    have h_factorize := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
      E q xa h_dvd_a h_dvd_b
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
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 2 := by
      rw [hq_def, normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
      have hap : a.point ≠ (0 : ECPoint E) := by
        rw [ha_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa 0 :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      have hbp : b.point ≠ (0 : ECPoint E) := by
        rw [hb_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa 0 :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      have ha_deg := LandmarkInvStrong.natDegree E ha
      have hb_deg := LandmarkInvStrong.natDegree E hb
      rw [if_neg hap] at ha_deg
      rw [if_neg hbp] at hb_deg
      omega
    rw [List.length_append]
    omega

/-! ## Helper: divLin preserves divisibility by an unrelated linear factor

When `(X - C x₁)` and `(X - C x₂)` both divide a polynomial `p`,
and `x₁ ≠ x₂`, then `p /ₘ (X - C x₁)` is still divisible by
`(X - C x₂)`. (Coprimality of the two linear factors.) -/

theorem dvd_X_sub_C_divByMonic_X_sub_C_of_ne
    {p : (ZMod E.q)[X]} {x₁ x₂ : ZMod E.q}
    (hdvd₁ : (X - C x₁) ∣ p) (hdvd₂ : (X - C x₂) ∣ p) (h_x12 : x₁ ≠ x₂) :
    (X - C x₂) ∣ p /ₘ (X - C x₁) := by
  have hcoprime : IsCoprime (X - C x₂ : (ZMod E.q)[X]) (X - C x₁) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h_x12.symm))
  obtain ⟨qa, hqa⟩ := hdvd₁
  have hMonic : (X - C x₁ : (ZMod E.q)[X]).Monic := monic_X_sub_C _
  have h_div : p /ₘ (X - C x₁) = qa := by
    rw [hqa]; exact mul_divByMonic_cancel_left _ hMonic
  rw [h_div]
  -- (X - C x₂) | (X - C x₁) * qa = p, coprime to (X - C x₁), so (X - C x₂) | qa.
  exact hcoprime.dvd_of_dvd_mul_left (hqa ▸ hdvd₂)

/-- If a polynomial has a double factor `(X - C x₀)^2`, then after one
`divByMonic (X - C x₀)` it still has a factor `(X - C x₀)`. -/
theorem dvd_X_sub_C_divByMonic_of_sq_dvd
    {p : (ZMod E.q)[X]} {x₀ : ZMod E.q}
    (hdvd : (X - C x₀) ^ 2 ∣ p) :
    (X - C x₀) ∣ p /ₘ (X - C x₀) := by
  obtain ⟨r, hr⟩ := hdvd
  refine ⟨r, ?_⟩
  have hMonic : (X - C x₀ : (ZMod E.q)[X]).Monic := monic_X_sub_C _
  rw [hr]
  have hfactor :
      ((X - C x₀) ^ 2 : (ZMod E.q)[X]) * r
        = (X - C x₀) * ((X - C x₀) * r) := by
    ring
  rw [hfactor]
  exact mul_divByMonic_cancel_left _ hMonic

/-! ## Helper: chained divLin preserves vanishing

After two divLin operations at distinct x-coords, vanishing at a
third x-coord (different from both) is preserved. -/

theorem divLin_chain_eval_zero
    (D : CoordRingElt E.q) (x₁ x₂ : ZMod E.q)
    (haDvd₁ : (X - C x₁) ∣ D.a) (hbDvd₁ : (X - C x₁) ∣ D.b)
    (haDvd₂ : (X - C x₂) ∣ D.a) (hbDvd₂ : (X - C x₂) ∣ D.b)
    (h_x12 : x₁ ≠ x₂)
    {x y : ZMod E.q} (h_eval : D.eval x y = 0)
    (h_xx₁ : x ≠ x₁) (h_xx₂ : x ≠ x₂) :
    ((D.divLin x₁).divLin x₂).eval x y = 0 := by
  -- After divLin x₁, vanishing at (x, y) is preserved.
  have h1 : (D.divLin x₁).eval x y = 0 :=
    divLin_eval_zero_of_x_ne E D x₁ haDvd₁ hbDvd₁ h_eval h_xx₁
  -- divLin x₁ also preserves divisibility by (X - C x₂).
  have h_dvd_a₂ : (X - C x₂) ∣ (D.divLin x₁).a := by
    rw [CoordRingElt.divLin_a]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E haDvd₁ haDvd₂ h_x12
  have h_dvd_b₂ : (X - C x₂) ∣ (D.divLin x₁).b := by
    rw [CoordRingElt.divLin_b]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E hbDvd₁ hbDvd₂ h_x12
  exact divLin_eval_zero_of_x_ne E (D.divLin x₁) x₂ h_dvd_a₂ h_dvd_b₂ h1 h_xx₂

/-! ## Helper: curve symmetry — `(x, -y) ∈ E.points` from `(x, y) ∈ E.points` -/

theorem points_neg_y {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    (P.1, -P.2) ∈ E.points := by
  have hOC : P.2 ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB := E.hOnCurve P hP
  apply E.hComplete
  show (-P.2) ^ 2 = P.1 ^ 3 + E.curveA * P.1 + E.curveB
  rw [neg_pow_two]; exact hOC


/-! ## TODO: combine_tangent_torsion, combine_tangent_smooth

The two tangent-doubling cases need (X - C xa)^2 divisibility into
the product polynomial, which requires either a derivative-based
argument (Taylor expansion on q.a, q.b) or strengthening the
LandmarkInv invariant to track multiplicity at running-sum fibers.
Deferred. -/

/-! ## Helpers (re-positioned for forward reference) -/

theorem Polynomial_ne_zero_of_natDegree_pos
    {p : (ZMod E.q)[X]} (h : 0 < p.natDegree) : p ≠ 0 := by
  intro h0
  rw [h0, Polynomial.natDegree_zero] at h
  exact Nat.lt_irrefl _ h

theorem chordCoordRingElt_normPoly_ne_zero_of_xx_ne
    {P Q : ZMod E.q × ZMod E.q} (h_xx : P.1 ≠ Q.1) :
    normPoly E (chordCoordRingElt E P Q) ≠ 0 := by
  have h_natDeg : (normPoly E (chordCoordRingElt E P Q)).natDegree = 3 := by
    unfold chordCoordRingElt
    rw [dif_neg h_xx]
    exact natDegree_normPoly_chordCoordRingElt_nonvertical E _ _
  apply Polynomial_ne_zero_of_natDegree_pos
  rw [h_natDeg]
  norm_num

theorem chordCoordRingElt_natDegree_normPoly_of_xx_ne
    {P Q : ZMod E.q × ZMod E.q} (h_xx : P.1 ≠ Q.1) :
    (normPoly E (chordCoordRingElt E P Q)).natDegree = 3 := by
  unfold chordCoordRingElt
  rw [dif_neg h_xx]
  exact natDegree_normPoly_chordCoordRingElt_nonvertical E _ _

/-! ## levelInitPair satisfies LandmarkInv (chord case)

For an input pair `(P, Q)` on `E` with `P.1 ≠ Q.1`, the level-0
output `levelInitPair P Q` satisfies `LandmarkInv [P, Q]`. -/

theorem landmarkInv_levelInitPair_chord
    {P Q : ZMod E.q × ZMod E.q}
    (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h_xx : P.1 ≠ Q.1) :
    LandmarkInv E [P, Q] (levelInitPair E P Q) := by
  classical
  -- thirdPoint = some (Qx, Qy). levelInitPair gives chord polynomial,
  -- result.point = ECPoint.affine E Qx (-Qy).
  have hns_P : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  have hns_Q : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  set Qx := slopeOf P.1 P.2 Q.1 Q.2 ^ 2 - P.1 - Q.1 with hQx_def
  set Qy := slopeOf P.1 P.2 Q.1 Q.2 * Qx + (P.2 - slopeOf P.1 P.2 Q.1 Q.2 * P.1)
    with hQy_def
  have hT : thirdPoint E P Q = some (Qx, Qy) := by
    unfold thirdPoint
    rw [if_neg h_xx]
    simp [Qx, Qy, slopeOf]
  have h_QxQy_on : (Qx, Qy) ∈ E.points :=
    third_point_on_curve E P Q hP hQ hT
  have h_QxQy_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E h_QxQy_on
  have hns_Qneg : E.toW.toAffine.Nonsingular Qx (-Qy) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ h_QxQy_neg_on))
  -- levelInitPair unfolds.
  have h_levelInit_pt : (levelInitPair E P Q).point = ECPoint.affine E Qx (-Qy) := by
    unfold levelInitPair
    rw [hT]
  have h_levelInit_poly : (levelInitPair E P Q).poly = chordCoordRingElt E P Q := by
    unfold levelInitPair
    rw [hT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- result.point = sumOnE [P, Q] = ECPoint.affineOfMem hP + ECPoint.affineOfMem hQ.
    rw [h_levelInit_pt]
    show ECPoint.affine E Qx (-Qy) = sumOnE E [P, Q]
    rw [show sumOnE E [P, Q] = ECPoint.affineOfMem E hP + sumOnE E [Q] from sumOnE_cons E hP]
    rw [show sumOnE E [Q] = ECPoint.affineOfMem E hQ + sumOnE E [] from sumOnE_cons E hQ]
    rw [sumOnE_nil, add_zero]
    have heq_P : ECPoint.affineOfMem E hP = (.some hns_P : ECPoint E) := rfl
    have heq_Q : ECPoint.affineOfMem E hQ = (.some hns_Q : ECPoint E) := rfl
    rw [heq_P, heq_Q]
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    -- (.some hns_P) + (.some hns_Q) = -(.some hns_Qpos) = .some hns_Qneg.
    have hSum := thirdPoint_some_eq_neg_add (E := E) hP hQ hT
    have heq_QxQy : ECPoint.affineOfMem E h_QxQy_on
        = (.some (E.equation_iff_nonsingular.mp
                  ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ h_QxQy_on))) : ECPoint E) := rfl
    rw [heq_P, heq_Q, heq_QxQy] at hSum
    -- (.some hns_Qneg) = -(.some hns_third).
    set hns_third := E.equation_iff_nonsingular.mp ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ h_QxQy_on))
    have h_neg : (.some hns_Qneg : ECPoint E) = -(.some hns_third : ECPoint E) := by
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg]
    exact hSum.symm
  · -- Vanishing at P and Q.
    intro pt hpt
    rw [h_levelInit_poly]
    rcases List.mem_cons.mp hpt with h | h
    · rw [h]; exact chordCoordRingElt_eval_left E P Q
    · rcases List.mem_singleton.mp h with h_eq
      rw [h_eq]; exact chordCoordRingElt_eval_right E P Q
  · -- Residue: result.point = ECPoint.affine E Qx (-Qy); negCoords = some (Qx, Qy).
    -- chord vanishes at (Qx, Qy) by chordCoordRingElt_eval_thirdPoint_chord.
    intro pt hpt_neg
    rw [h_levelInit_pt] at hpt_neg
    rw [ECPoint.affine_of_nonsingular E hns_Qneg] at hpt_neg
    have hpt_eq : pt = (Qx, Qy) := by
      have : negCoords E (.some hns_Qneg : ECPoint E) = some (Qx, Qy) := by
        show some (Qx, -(-Qy)) = some (Qx, Qy)
        rw [neg_neg]
      rw [this] at hpt_neg
      exact (Option.some.inj hpt_neg).symm
    rw [hpt_eq, h_levelInit_poly]
    have := chordCoordRingElt_eval_thirdPoint_chord (E := E) hP hQ h_xx
    simp [Qx, Qy, slopeOf] at this ⊢
    exact this
  · -- Degree: natDegree(normPoly chord) = 3 = 2 + 1.
    rw [h_levelInit_poly, h_levelInit_pt]
    -- result.point = ECPoint.affine E Qx (-Qy), nonzero.
    have h_pt_ne : ECPoint.affine E Qx (-Qy) ≠ (0 : ECPoint E) := by
      rw [ECPoint.affine_of_nonsingular E hns_Qneg]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns_Qneg
    rw [if_neg h_pt_ne]
    rw [chordCoordRingElt_natDegree_normPoly_of_xx_ne E h_xx]
    rfl

/-! ## Preservation: `combine_distinct` (chord case, distinct x)

Two affine accumulators with `xa ≠ xb`. Combined polynomial:
`((line · a.poly · b.poly).divLin xa).divLin xb`.

Same template as combine_vertical: at each fiber `x ∈ {xa, xb}`,
two sheets vanish (one from chord/line, one from a/b residue),
giving univariate vanishing of `q.a, q.b` at xa AND xb, hence
divisibility by `(X - C xa)(X - C xb)`. Since xa ≠ xb, factors
coprime; chained divLin works.

Conditional hypotheses:
  - No `P ∈ xs ++ ys` has `P.1 ∈ {xa, xb}`.
  - Third intersection x-coord `Qx ∉ {xa, xb}`. -/


/-! ## Helper: thirdPoint = none for sum-zero pair

`P + Q = 0` on `E` translates to `P.1 = Q.1` AND (`P.2 = -Q.2` for
non-2-torsion, or `P = Q` with `P.2 = 0` for 2-torsion). In both
cases, `thirdPoint E P Q = none` (vertical line). -/

theorem thirdPoint_eq_none_of_sum_zero_data
    (P Q : ZMod E.q × ZMod E.q)
    (hxx : P.1 = Q.1)
    (hyy : P.2 = -Q.2 ∨ (P = Q ∧ P.2 = 0)) :
    thirdPoint E P Q = none := by
  unfold thirdPoint
  rw [if_pos hxx]
  rcases hyy with h | ⟨hPQ, hP_zero⟩
  · by_cases hY : P.2 = Q.2
    · rw [if_pos hY]
      have hP_zero : P.2 = 0 := by
        have h2y : 2 * P.2 = 0 := by linear_combination hY + h
        have h2_ne : (2 : ZMod E.q) ≠ 0 := two_ne_zero_in_zmod E
        exact (mul_eq_zero.mp h2y).resolve_left h2_ne
      rw [if_pos hP_zero]
    · rw [if_neg hY]
  · subst hPQ
    rw [if_pos rfl, if_pos hP_zero]

/-- For sum-zero pair, the chord/tangent line reduces to a vertical line. -/
theorem chordCoordRingElt_eq_vertical_of_sum_zero
    (P Q : ZMod E.q × ZMod E.q)
    (hxx : P.1 = Q.1)
    (hyy : P.2 = -Q.2 ∨ (P = Q ∧ P.2 = 0)) :
    chordCoordRingElt E P Q = { a := X - C P.1, b := 0 } := by
  unfold chordCoordRingElt
  rw [dif_pos hxx]
  rcases hyy with h | ⟨hPQ, hP_zero⟩
  · by_cases hY : P.2 = Q.2
    · rw [dif_pos hY]
      have hP_zero : P.2 = 0 := by
        have h2y : 2 * P.2 = 0 := by linear_combination hY + h
        have h2_ne : (2 : ZMod E.q) ≠ 0 := two_ne_zero_in_zmod E
        exact (mul_eq_zero.mp h2y).resolve_left h2_ne
      rw [if_pos hP_zero]
    · rw [dif_neg hY]
  · subst hPQ
    rw [dif_pos rfl, if_pos hP_zero]

/-! ## Codex insight: levelInitSingleton bypasses levelInitPair

Per Codex consultation, the cleanest level-0 construction is to
make every input point an "absorbed singleton": each P becomes the
accumulator `{ point := ECPoint.affine E P.1 P.2, poly := (X - C P.1, 0) }`,
which satisfies `LandmarkInv [P]` directly. Then level_step
handles all the pairing logic uniformly.

The vertical line `(X - C P.1, 0)` has divisor on E:
  - vanishes at (P.1, P.2) and (P.1, -P.2) (the fiber).
  - infinity coefficient: -(normPoly).natDegree = -2.

For LandmarkInv [P]:
  - point = ECPoint.affine E P.1 P.2 = sumOnE [P] ✓
  - vanishing at P (and at -P via residue) ✓
  - normPoly natDegree = 2 = 1 (xs.length) + 1 (point ≠ 0) ✓ -/

/-- The on-curve assumption is unused at the data level (Junk if off-curve
    via `ECPoint.affine`'s `dif_*` fallback to 0). LandmarkInv requires it. -/
noncomputable def levelInitSingleton
    (P : ZMod E.q × ZMod E.q) : EagenAccum E :=
  { point := ECPoint.affine E P.1 P.2,
    poly := { a := X - C P.1, b := 0 } }

theorem landmarkInv_levelInitSingleton
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    LandmarkInv E [P] (levelInitSingleton E P) := by
  classical
  have hns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- point = sumOnE [P].
    show (levelInitSingleton E P).point = sumOnE E [P]
    rw [show sumOnE E [P] = ECPoint.affineOfMem E hP + sumOnE E [] from sumOnE_cons E hP]
    rw [sumOnE_nil, add_zero]
    show ECPoint.affine E P.1 P.2 = ECPoint.affineOfMem E hP
    exact ECPoint.affine_eq_affineOfMem E hP
  · -- Vanishing at every Q ∈ [P].
    intro Q hQ
    rw [List.mem_singleton] at hQ
    rw [hQ]
    show (X - C P.1).eval P.1 - (0 : (ZMod E.q)[X]).eval P.1 * P.2 = 0
    simp
  · -- Residue: vertical line vanishes at (P.1, -P.2) too.
    intro Q hQ
    show ((X - C P.1 : (ZMod E.q)[X])).eval Q.1 - ((0 : (ZMod E.q)[X])).eval Q.1 * Q.2 = 0
    have h_levelInit_pt : (levelInitSingleton E P).point = ECPoint.affine E P.1 P.2 := rfl
    rw [h_levelInit_pt] at hQ
    rw [ECPoint.affine_of_nonsingular E hns] at hQ
    have hQ_eq : Q = (P.1, -P.2) := by
      have : negCoords E (.some hns : ECPoint E) = some (P.1, -P.2) := rfl
      rw [this] at hQ
      exact (Option.some.inj hQ).symm
    rw [hQ_eq]
    show (X - C P.1).eval P.1 - (0 : (ZMod E.q)[X]).eval P.1 * (-P.2) = 0
    simp
  · -- Degree.
    show (normPoly E { a := X - C P.1, b := 0 }).natDegree
        = [P].length + (if (levelInitSingleton E P).point = (0 : ECPoint E) then 0 else 1)
    have h_levelInit_pt : (levelInitSingleton E P).point = ECPoint.affine E P.1 P.2 := rfl
    have h_pt_ne : (levelInitSingleton E P).point ≠ (0 : ECPoint E) := by
      rw [h_levelInit_pt, ECPoint.affine_of_nonsingular E hns]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns
    rw [if_neg h_pt_ne]
    show (normPoly E { a := X - C P.1, b := 0 }).natDegree = 2
    rw [normPoly_eq]
    show ((X - C P.1) ^ 2 - 0 ^ 2 * curveX E).natDegree = 2
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]

/-- Singletonized level-0: each input becomes a vertical-line accumulator. -/
noncomputable def level0_singletons (Ps : List (ZMod E.q × ZMod E.q)) :
    List (EagenAccum E) :=
  Ps.map (levelInitSingleton E)

theorem landmarkInvList_level0_singletons
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points) :
    LandmarkInvList E (Ps.map (fun P => [P])) (level0_singletons E Ps) := by
  classical
  induction Ps with
  | nil =>
    show List.Forall₂ _ [] []
    exact List.Forall₂.nil
  | cons P rest ih =>
    have h_rest_on : ∀ Q ∈ rest, Q ∈ E.points :=
      fun Q hQ => hPs_on Q (List.mem_cons_of_mem P hQ)
    have h_ih := ih h_rest_on
    show List.Forall₂ _ ([P] :: rest.map (fun P => [P]))
        (levelInitSingleton E P :: rest.map (levelInitSingleton E))
    refine List.Forall₂.cons ?_ h_ih
    exact landmarkInv_levelInitSingleton E P (hPs_on P (List.mem_cons_self))

theorem landmarkInv_combine_distinct_no_collision
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya xb yb : ZMod E.q}
    (h_xx : xa ≠ xb)
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_no_collision_a : ∀ P ∈ xs ++ ys, P.1 ≠ xa)
    (h_no_collision_b : ∀ P ∈ xs ++ ys, P.1 ≠ xb)
    (hxa_on : (xa, ya) ∈ E.points)
    (hxb_on : (xb, yb) ∈ E.points)
    (hya_ne : ya ≠ 0)
    (hyb_ne : yb ≠ 0)
    (h_third_xa : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xa)
    (h_third_xb : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xb)
    (ha : LandmarkInv E xs a) (hb : LandmarkInv E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xb yb)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0) :
    LandmarkInv E (xs ++ ys)
      (EagenAccum.combine_distinct E a b xa ya xb yb h_xx) := by
  classical
  obtain ⟨ha_sum, ha_van, ha_res, ha_deg⟩ := ha
  obtain ⟨hb_sum, hb_van, hb_res, hb_deg⟩ := hb
  have hxa_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
  have hxb_neg_on : (xb, -yb) ∈ E.points := points_neg_y E hxb_on
  -- Residue evaluations.
  have ha_neg_eval : a.poly.eval xa (-ya) = 0 := by
    apply ha_res (xa, -ya)
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hb_neg_eval : b.poly.eval xb (-yb) = 0 := by
    apply hb_res (xb, -yb)
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  set line := chordCoordRingElt E (xa, ya) (xb, yb) with hline_def
  set q := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly with hq_def
  have hxx_pair : ((xa, ya) : ZMod E.q × ZMod E.q).1 ≠ ((xb, yb) : ZMod E.q × ZMod E.q).1 := h_xx
  have hline_eval_a : line.eval xa ya = 0 :=
    chordCoordRingElt_eval_left E (xa, ya) (xb, yb)
  have hline_eval_b : line.eval xb yb = 0 :=
    chordCoordRingElt_eval_right E (xa, ya) (xb, yb)
  have hq_eval_xa_pos : q.eval xa ya = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_on]
    rw [hline_eval_a]; ring
  have hq_eval_xa_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_neg_on]
    rw [ha_neg_eval]; ring
  have hq_eval_xb_pos : q.eval xb yb = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_on]
    rw [hline_eval_b]; ring
  have hq_eval_xb_neg : q.eval xb (-yb) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_neg_on]
    rw [hb_neg_eval]; ring
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hya_ne hq_eval_xa_pos hq_eval_xa_neg
  obtain ⟨h_qa_xb, h_qb_xb⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xb yb hyb_ne hq_eval_xb_pos hq_eval_xb_neg
  have h_dvd_qa_xa : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_qb_xa : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have h_dvd_qa_xb : (X - C xb) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xb
  have h_dvd_qb_xb : (X - C xb) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xb
  -- Build LandmarkInv conjuncts.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Running sum.
    show (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← ha_sum, ← hb_sum, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    have hns_b : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    show (ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
            (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb)
                + (ya - slopeOf xa ya xb yb * xa))))
        = (.some hns_a + .some hns_b : ECPoint E)
    set Qx := slopeOf xa ya xb yb ^ 2 - xa - xb with hQx_def
    set Qy := slopeOf xa ya xb yb * Qx + (ya - slopeOf xa ya xb yb * xa) with hQy_def
    have hT : thirdPoint E (xa, ya) (xb, yb) = some (Qx, Qy) := by
      unfold thirdPoint
      rw [if_neg h_xx]
      simp [Qx, Qy, slopeOf]
    have hSum := thirdPoint_some_eq_neg_add (E := E) hxa_on hxb_on hT
    have heq_a : ECPoint.affineOfMem E hxa_on = (.some hns_a : ECPoint E) := rfl
    have heq_b : ECPoint.affineOfMem E hxb_on = (.some hns_b : ECPoint E) := rfl
    rw [heq_a, heq_b] at hSum
    have h_Qxy_on : (Qx, Qy) ∈ E.points :=
      third_point_on_curve E (xa, ya) (xb, yb) hxa_on hxb_on hT
    have hns_third : E.toW.toAffine.Nonsingular Qx Qy :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ h_Qxy_on))
    have heq_third : ECPoint.affineOfMem E h_Qxy_on = (.some hns_third : ECPoint E) := rfl
    rw [heq_third] at hSum
    have h_Qxy_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E h_Qxy_on
    have hns_third_neg : E.toW.toAffine.Nonsingular Qx (-Qy) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ h_Qxy_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns_third_neg]
    have h_neg_third : (.some hns_third_neg : ECPoint E) = -(.some hns_third : ECPoint E) := by
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg_third]
    exact hSum.symm
  · -- Vanishing at every P ∈ xs ++ ys.
    intro P hP_mem
    have hP_on : P ∈ E.points := by
      rw [List.mem_append] at hP_mem
      rcases hP_mem with hP_xs | hP_ys
      · exact hxs_on P hP_xs
      · exact hys_on P hP_ys
    have hP_ne_xa : P.1 ≠ xa := h_no_collision_a P hP_mem
    have hP_ne_xb : P.1 ≠ xb := h_no_collision_b P hP_mem
    have h_q_eval : q.eval P.1 P.2 = 0 := by
      rw [hq_def]
      rw [mulCoordRingElt_eval_on_E E _ b.poly hP_on]
      rw [mulCoordRingElt_eval_on_E E line a.poly hP_on]
      rw [List.mem_append] at hP_mem
      rcases hP_mem with hP_xs | hP_ys
      · rw [ha_van P hP_xs]; ring
      · rw [hb_van P hP_ys]; ring
    show ((q.divLin xa).divLin xb).eval P.1 P.2 = 0
    exact divLin_chain_eval_zero E q xa xb h_dvd_qa_xa h_dvd_qb_xa h_dvd_qa_xb h_dvd_qb_xb h_xx h_q_eval hP_ne_xa hP_ne_xb
  · -- Residue.
    intro Q hQ
    show ((q.divLin xa).divLin xb).eval Q.1 Q.2 = 0
    have h_combined_pt : (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
        = ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
          (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb)
              + (ya - slopeOf xa ya xb yb * xa))) := rfl
    rw [h_combined_pt] at hQ
    set Qx := slopeOf xa ya xb yb ^ 2 - xa - xb with hQx_def
    set Qy := slopeOf xa ya xb yb * Qx + (ya - slopeOf xa ya xb yb * xa) with hQy_def
    have hT : thirdPoint E (xa, ya) (xb, yb) = some (Qx, Qy) := by
      unfold thirdPoint
      rw [if_neg h_xx]
      simp [Qx, Qy, slopeOf]
    have h_on : (Qx, Qy) ∈ E.points :=
      third_point_on_curve E (xa, ya) (xb, yb) hxa_on hxb_on hT
    have h_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E h_on
    have hns : E.toW.toAffine.Nonsingular Qx (-Qy) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ h_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns] at hQ
    have hQ_eq : Q = (Qx, Qy) := by
      have : negCoords E (.some hns : ECPoint E) = some (Qx, Qy) := by
        show some (Qx, -(-Qy)) = some (Qx, Qy)
        rw [neg_neg]
      rw [this] at hQ
      exact (Option.some.inj hQ).symm
    rw [hQ_eq]
    have h_line_eval_third : line.eval Qx Qy = 0 := by
      have := chordCoordRingElt_eval_thirdPoint_chord (E := E)
        (P := (xa, ya)) (Q := (xb, yb)) hxa_on hxb_on h_xx
      simp [Qx, Qy, slopeOf] at this ⊢
      exact this
    have h_q_eval_third : q.eval Qx Qy = 0 := by
      rw [hq_def]
      rw [mulCoordRingElt_eval_on_E E _ b.poly h_on]
      rw [mulCoordRingElt_eval_on_E E line a.poly h_on]
      rw [h_line_eval_third]; ring
    exact divLin_chain_eval_zero E q xa xb h_dvd_qa_xa h_dvd_qb_xa h_dvd_qa_xb h_dvd_qb_xb h_xx h_q_eval_third h_third_xa h_third_xb
  · -- Degree.
    show (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_ne : (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
        ≠ (0 : ECPoint E) := by
      have h_combined_pt : (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
          = ECPoint.affine E (slopeOf xa ya xb yb ^ 2 - xa - xb)
            (-(slopeOf xa ya xb yb * (slopeOf xa ya xb yb ^ 2 - xa - xb)
                + (ya - slopeOf xa ya xb yb * xa))) := rfl
      rw [h_combined_pt]
      set Qx := slopeOf xa ya xb yb ^ 2 - xa - xb
      set Qy := slopeOf xa ya xb yb * Qx + (ya - slopeOf xa ya xb yb * xa)
      have hT : thirdPoint E (xa, ya) (xb, yb) = some (Qx, Qy) := by
        unfold thirdPoint
        rw [if_neg h_xx]
        simp [Qx, Qy, slopeOf]
      have h_on : (Qx, Qy) ∈ E.points :=
        third_point_on_curve E (xa, ya) (xb, yb) hxa_on hxb_on hT
      have h_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E h_on
      have hns : E.toW.toAffine.Nonsingular Qx (-Qy) :=
        E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ h_neg_on))
      rw [ECPoint.affine_of_nonsingular E hns]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns
    rw [if_neg h_combined_ne]
    -- Two-step factorization: drop natDegree by 4.
    have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin E q xa h_dvd_qa_xa h_dvd_qb_xa
    have h_dvd_a_after : (X - C xb) ∣ (q.divLin xa).a := by
      rw [CoordRingElt.divLin_a]
      exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qa_xa h_dvd_qa_xb h_xx
    have h_dvd_b_after : (X - C xb) ∣ (q.divLin xa).b := by
      rw [CoordRingElt.divLin_b]
      exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qb_xa h_dvd_qb_xb h_xx
    have h_factor2 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin E (q.divLin xa) xb h_dvd_a_after h_dvd_b_after
    -- Compute natDegrees.
    have h_line_nz : normPoly E line ≠ 0 := chordCoordRingElt_normPoly_ne_zero_of_xx_ne E h_xx
    have h_line_deg : (normPoly E line).natDegree = 3 :=
      chordCoordRingElt_natDegree_normPoly_of_xx_ne E h_xx
    have hap : a.point ≠ (0 : ECPoint E) := by
      rw [ha_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xa ya :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have hbp : b.point ≠ (0 : ECPoint E) := by
      rw [hb_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xb yb :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    rw [if_neg hap] at ha_deg
    rw [if_neg hbp] at hb_deg
    -- Compute (normPoly q).natDegree = (xs+1) + (ys+1) + 3 = xs+ys+5.
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 5 := by
      rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
      have h_inner_nz : normPoly E line * normPoly E a.poly ≠ 0 := mul_ne_zero h_line_nz ha_nz
      rw [Polynomial.natDegree_mul h_inner_nz hb_nz,
          Polynomial.natDegree_mul h_line_nz ha_nz]
      rw [h_line_deg, ha_deg, hb_deg]
      omega
    -- (normPoly q).natDegree = ((X - C xa)^2 * normPoly (q.divLin xa)).natDegree
    --                       = 2 + (normPoly (q.divLin xa)).natDegree.
    have h_X_sub_a_pow_ne : ((X - C xa) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_X_sub_b_pow_ne : ((X - C xb) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
      intro h0
      have : normPoly E q = 0 := by rw [h_factor1, h0, mul_zero]
      have := this ▸ h_qnp
      simp at this
    have h_div2_nz : normPoly E ((q.divLin xa).divLin xb) ≠ 0 := by
      intro h0
      apply h_div1_nz
      rw [h_factor2, h0, mul_zero]
    have h_natDeg1 : (normPoly E (q.divLin xa)).natDegree
        = (normPoly E q).natDegree - 2 := by
      have hh : (normPoly E q).natDegree
          = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E (q.divLin xa)).natDegree := by
        rw [h_factor1, Polynomial.natDegree_mul h_X_sub_a_pow_ne h_div1_nz]
      have hp : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_natDeg2 : (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (normPoly E (q.divLin xa)).natDegree - 2 := by
      have hh : (normPoly E (q.divLin xa)).natDegree
          = ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E ((q.divLin xa).divLin xb)).natDegree := by
        rw [h_factor2, Polynomial.natDegree_mul h_X_sub_b_pow_ne h_div2_nz]
      have hp : ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    rw [h_natDeg2, h_natDeg1, h_qnp, List.length_append]
    omega

theorem mulCoordRingElt_assoc (D₁ D₂ D₃ : CoordRingElt E.q) :
    mulCoordRingElt E (mulCoordRingElt E D₁ D₂) D₃
      = mulCoordRingElt E D₁ (mulCoordRingElt E D₂ D₃) := by
  unfold mulCoordRingElt
  refine CoordRingElt.mk.injEq _ _ _ _ |>.mpr ?_
  refine ⟨?_, ?_⟩ <;> ring

/-- Product of two non-zero coordinate-ring elements is non-zero. -/
theorem mulCoordRingElt_not_both_zero
    (D₁ D₂ : CoordRingElt E.q)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0)) :
    ¬ ((mulCoordRingElt E D₁ D₂).a = 0
        ∧ (mulCoordRingElt E D₁ D₂).b = 0) := by
  intro ⟨ha, hb⟩
  have hN : normPoly E (mulCoordRingElt E D₁ D₂) = 0 := by
    rw [normPoly_eq, ha, hb]
    ring
  rw [normPoly_mul_eq] at hN
  exact (mul_ne_zero (normPoly_ne_zero E D₁ h₁)
    (normPoly_ne_zero E D₂ h₂)) hN

/-- If a common `divLin` step is available and the original norm root
multiplicity is at most two, the reduced norm has no root at that
x-coordinate. -/
theorem rootMultiplicity_normPoly_divLin_eq_zero_of_rootMult_le_two
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hax : D.a.eval P.1 = 0) (hbx : D.b.eval P.1 = 0)
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D) ≤ 2) :
    Polynomial.rootMultiplicity P.1 (normPoly E (D.divLin P.1)) = 0 := by
  have hD' : ¬ ((D.divLin P.1).a = 0 ∧ (D.divLin P.1).b = 0) :=
    divLin_not_both_zero E D hD hax hbx
  have hFactor :
      normPoly E D =
        (Polynomial.X - Polynomial.C P.1) ^ 2
          * normPoly E (D.divLin P.1) :=
    normPoly_divLin_factor E D hax hbx
  have hMul_NZ :
      (Polynomial.X - Polynomial.C P.1) ^ 2
          * normPoly E (D.divLin P.1) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero P.1))
      (normPoly_ne_zero E (D.divLin P.1) hD')
  have hEq :
      Polynomial.rootMultiplicity P.1 (normPoly E D)
        = 2 + Polynomial.rootMultiplicity P.1
            (normPoly E (D.divLin P.1)) := by
    rw [hFactor, Polynomial.rootMultiplicity_mul hMul_NZ,
      Polynomial.rootMultiplicity_X_sub_C_pow]
  omega

/-- Multiplicativity when the right factor is a simple twin-fiber factor
over the current non-2-torsion x-coordinate.  The common linear factor is
peeled as a vertical line, and the reduced right factor falls under the
existing `rootMult ≤ 1` theorem. -/
theorem ordAt_mul_add_when_right_twin_rootMult_le_two
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hD₂P : D₂.eval P.1 P.2 = 0)
    (hD₂negP : D₂.eval P.1 (-P.2) = 0)
    (hRoot₂ : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2) :
    ordAt E (mulCoordRingElt E D₁ D₂) P
      = ordAt E D₁ P + ordAt E D₂ P := by
  let D₂' : CoordRingElt E.q := D₂.divLin P.1
  let Lv : CoordRingElt E.q := { a := Polynomial.X - Polynomial.C P.1, b := 0 }
  obtain ⟨hax, hbx⟩ :=
    Da_Db_eval_zero_of_both_sheets_zero E D₂ hY hD₂P hD₂negP
  have hD₂' : ¬ (D₂'.a = 0 ∧ D₂'.b = 0) := by
    simpa [D₂'] using divLin_not_both_zero E D₂ h₂ hax hbx
  have hRoot₂' :
      Polynomial.rootMultiplicity P.1 (normPoly E D₂') ≤ 1 := by
    have hZero :
        Polynomial.rootMultiplicity P.1 (normPoly E (D₂.divLin P.1)) = 0 :=
      rootMultiplicity_normPoly_divLin_eq_zero_of_rootMult_le_two
        E D₂ h₂ hax hbx hRoot₂
    simpa [D₂'] using (by omega : Polynomial.rootMultiplicity P.1
      (normPoly E (D₂.divLin P.1)) ≤ 1)
  have hD₁D₂' : ¬ ((mulCoordRingElt E D₁ D₂').a = 0
      ∧ (mulCoordRingElt E D₁ D₂').b = 0) :=
    mulCoordRingElt_not_both_zero E D₁ D₂' h₁ hD₂'
  have hDvdA : (Polynomial.X - Polynomial.C P.1) ∣ D₂.a :=
    Polynomial.dvd_iff_isRoot.mpr hax
  have hDvdB : (Polynomial.X - Polynomial.C P.1) ∣ D₂.b :=
    Polynomial.dvd_iff_isRoot.mpr hbx
  have hRecomp : D₂ = mulCoordRingElt E D₂' Lv := by
    simpa [D₂', Lv] using
      mulCoordRingElt_divLin_vertical_recompose E D₂ P.1 hDvdA hDvdB
  have hAssoc :
      mulCoordRingElt E D₁ D₂
        = mulCoordRingElt E (mulCoordRingElt E D₁ D₂') Lv := by
    rw [hRecomp]
    exact (mulCoordRingElt_assoc E D₁ D₂' Lv).symm
  have hAddReduced :
      ordAt E (mulCoordRingElt E D₁ D₂') P
        = ordAt E D₁ P + ordAt E D₂' P :=
    Divisor.ordAt_mul_add_when_normPoly_D2_le_one
      (E := E) (D₁ := D₁) (D₂ := D₂') h₁ hD₂' hP hRoot₂'
  have hVertProd :
      ordAt E (mulCoordRingElt E (mulCoordRingElt E D₁ D₂') Lv) P
        = ordAt E (mulCoordRingElt E D₁ D₂') P + ordAt E Lv P := by
    simpa [Lv] using
      Divisor.ordAt_mul_vertical_add (E := E)
        (D := mulCoordRingElt E D₁ D₂') hD₁D₂' P.1 hP
  have hVertD₂ :
      ordAt E D₂ P = ordAt E D₂' P + ordAt E Lv P := by
    rw [hRecomp]
    simpa [Lv] using
      Divisor.ordAt_mul_vertical_add (E := E) (D := D₂') hD₂' P.1 hP
  calc
    ordAt E (mulCoordRingElt E D₁ D₂) P
        = ordAt E (mulCoordRingElt E (mulCoordRingElt E D₁ D₂') Lv) P := by
          rw [hAssoc]
    _ = ordAt E (mulCoordRingElt E D₁ D₂') P + ordAt E Lv P := hVertProd
    _ = (ordAt E D₁ P + ordAt E D₂' P) + ordAt E Lv P := by
          rw [hAddReduced]
    _ = ordAt E D₁ P + (ordAt E D₂' P + ordAt E Lv P) := by
          rw [Nat.add_assoc]
    _ = ordAt E D₁ P + ordAt E D₂ P := by
          rw [hVertD₂]

/-- Cross-case additivity under `rootMult ≤ 2` for both factors, with
the remaining `2 × 2` case supplied as explicit iterated-`divLin`
invariants. -/
theorem ordAt_mul_add_in_cross_when_rootMult_le_two_of_iterDivLin
    {D₁ D₂ : CoordRingElt E.q}
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (hD₁P : D₁.eval P.1 P.2 = 0)
    (hD₁negP : D₁.eval P.1 (-P.2) ≠ 0)
    (hD₂P : D₂.eval P.1 P.2 ≠ 0)
    (hD₂negP : D₂.eval P.1 (-P.2) = 0)
    (hRoot₁ : Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 2)
    (hRoot₂ : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2)
    (hCross₂₂ :
      Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 →
        commonRootMultRat E (mulCoordRingElt E D₁ D₂) P.1 = 2
        ∧ (iterDivLin E (mulCoordRingElt E D₁ D₂) P.1 2).eval P.1 P.2 ≠ 0) :
    ordAt E (mulCoordRingElt E D₁ D₂) P
      = ordAt E D₁ P + ordAt E D₂ P := by
  have hm₁_pos : 0 < Polynomial.rootMultiplicity P.1 (normPoly E D₁) :=
    cross_case_m1_pos E h₁ hP hD₁P
  have hm₂_pos : 0 < Polynomial.rootMultiplicity P.1 (normPoly E D₂) :=
    cross_case_m2_pos E h₂ hP hD₂negP
  by_cases hm₁_one : Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 1
  · have hMin : min (Polynomial.rootMultiplicity P.1 (normPoly E D₁))
        (Polynomial.rootMultiplicity P.1 (normPoly E D₂)) = 1 := by
      rw [hm₁_one]
      exact Nat.min_eq_left hm₂_pos
    exact Divisor.ordAt_mul_add_in_cross_when_min_eq_one
      (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP hMin
  · by_cases hm₂_one : Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 1
    · have hMin : min (Polynomial.rootMultiplicity P.1 (normPoly E D₁))
          (Polynomial.rootMultiplicity P.1 (normPoly E D₂)) = 1 := by
        rw [hm₂_one]
        exact Nat.min_eq_right hm₁_pos
      exact Divisor.ordAt_mul_add_in_cross_when_min_eq_one
        (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP hMin
    · have hm₁_two :
          Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 := by
        omega
      have hm₂_two :
          Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 := by
        omega
      obtain ⟨hCommon, hResidual⟩ := hCross₂₂ hm₁_two hm₂_two
      exact Divisor.ordAt_mul_add_in_cross_when_m1_eq_m2_eq_two_of_iterDivLin
        (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP
        hm₁_two hm₂_two hCommon hResidual

/-- A weakened `rootMult ≤ 2` multiplicativity bridge.  Besides the
right-factor bound, this version assumes the matching left-factor bound
and explicit iterated-`divLin` invariants in the two oriented `2 × 2`
cross cases. -/
theorem ordAt_mul_add_when_normPoly_D2_le_two_of_iterDivLin
    {D₁ D₂ : CoordRingElt E.q}
    (h₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (h₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points)
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2)
    (hRoot₁ : Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 2)
    (hCross₁₂ :
      P.2 ≠ 0 →
      D₁.eval P.1 P.2 = 0 →
      D₁.eval P.1 (-P.2) ≠ 0 →
      D₂.eval P.1 P.2 ≠ 0 →
      D₂.eval P.1 (-P.2) = 0 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 →
        commonRootMultRat E (mulCoordRingElt E D₁ D₂) P.1 = 2
        ∧ (iterDivLin E (mulCoordRingElt E D₁ D₂) P.1 2).eval P.1 P.2 ≠ 0)
    (hCross₂₁ :
      P.2 ≠ 0 →
      D₂.eval P.1 P.2 = 0 →
      D₂.eval P.1 (-P.2) ≠ 0 →
      D₁.eval P.1 P.2 ≠ 0 →
      D₁.eval P.1 (-P.2) = 0 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 →
        commonRootMultRat E (mulCoordRingElt E D₂ D₁) P.1 = 2
        ∧ (iterDivLin E (mulCoordRingElt E D₂ D₁) P.1 2).eval P.1 P.2 ≠ 0) :
    ordAt E (mulCoordRingElt E D₁ D₂) P
      = ordAt E D₁ P + ordAt E D₂ P := by
  by_cases hY0 : P.2 = 0
  · exact Divisor.ordAt_mul_add_twoTorsion E h₁ h₂ hP hY0
  · have hY : P.2 ≠ 0 := hY0
    by_cases hD₁P : D₁.eval P.1 P.2 = 0
    · by_cases hD₁negP : D₁.eval P.1 (-P.2) = 0
      · have hSwap :=
          ordAt_mul_add_when_right_twin_rootMult_le_two
            E D₂ D₁ P hP hY h₂ h₁ hD₁P hD₁negP hRoot₁
        rw [mulCoordRingElt_comm E D₁ D₂, Nat.add_comm]
        exact hSwap
      · push_neg at hD₁negP
        by_cases hD₂P : D₂.eval P.1 P.2 = 0
        · by_cases hD₂negP : D₂.eval P.1 (-P.2) = 0
          · exact ordAt_mul_add_when_right_twin_rootMult_le_two
              E D₁ D₂ P hP hY h₁ h₂ hD₂P hD₂negP hRoot
          · push_neg at hD₂negP
            exact Divisor.ordAt_mul_add_at_both_lone_same_sheet
              (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP
        · push_neg at hD₂P
          by_cases hD₂negP : D₂.eval P.1 (-P.2) = 0
          · exact ordAt_mul_add_in_cross_when_rootMult_le_two_of_iterDivLin
              (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP
              hRoot₁ hRoot
              (fun hm₁ hm₂ =>
                hCross₁₂ hY hD₁P hD₁negP hD₂P hD₂negP hm₁ hm₂)
          · push_neg at hD₂negP
            exact Divisor.ordAt_mul_add_at_lone_sheet
              (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP
    · push_neg at hD₁P
      by_cases hD₂P : D₂.eval P.1 P.2 = 0
      · by_cases hD₂negP : D₂.eval P.1 (-P.2) = 0
        · exact ordAt_mul_add_when_right_twin_rootMult_le_two
            E D₁ D₂ P hP hY h₁ h₂ hD₂P hD₂negP hRoot
        · push_neg at hD₂negP
          by_cases hD₁negP : D₁.eval P.1 (-P.2) = 0
          · have hSwap :=
              ordAt_mul_add_in_cross_when_rootMult_le_two_of_iterDivLin
                (E := E) h₂ h₁ hP hY hD₂P hD₂negP hD₁P hD₁negP
                hRoot hRoot₁
                (fun hm₂ hm₁ =>
                  hCross₂₁ hY hD₂P hD₂negP hD₁P hD₁negP hm₂ hm₁)
            rw [mulCoordRingElt_comm E D₁ D₂, Nat.add_comm]
            exact hSwap
          · push_neg at hD₁negP
            exact Divisor.ordAt_mul_add_at_lone_sheet_swap
              (E := E) h₁ h₂ hP hY hD₁P hD₁negP hD₂P hD₂negP
      · push_neg at hD₂P
        exact Divisor.ordAt_mul_add_at_nonvanish
          (E := E) h₁ h₂ hP hD₁P hD₂P

theorem localMult_mulCoordRingElt_eq_add_when_rootMult_le_two
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hD₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (hD₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2)
    (hRoot₁ : Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 2)
    (hCross₁₂ :
      P.2 ≠ 0 →
      D₁.eval P.1 P.2 = 0 →
      D₁.eval P.1 (-P.2) ≠ 0 →
      D₂.eval P.1 P.2 ≠ 0 →
      D₂.eval P.1 (-P.2) = 0 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 →
        commonRootMultRat E (mulCoordRingElt E D₁ D₂) P.1 = 2
        ∧ (iterDivLin E (mulCoordRingElt E D₁ D₂) P.1 2).eval P.1 P.2 ≠ 0)
    (hCross₂₁ :
      P.2 ≠ 0 →
      D₂.eval P.1 P.2 = 0 →
      D₂.eval P.1 (-P.2) ≠ 0 →
      D₁.eval P.1 P.2 ≠ 0 →
      D₁.eval P.1 (-P.2) = 0 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₂) = 2 →
      Polynomial.rootMultiplicity P.1 (normPoly E D₁) = 2 →
        commonRootMultRat E (mulCoordRingElt E D₂ D₁) P.1 = 2
        ∧ (iterDivLin E (mulCoordRingElt E D₂ D₁) P.1 2).eval P.1 P.2 ≠ 0) :
    localMult E (mulCoordRingElt E D₁ D₂) P
      = localMult E D₁ P + localMult E D₂ P := by
  simpa [localMult_eq_ordAt] using
    ordAt_mul_add_when_normPoly_D2_le_two_of_iterDivLin
      (E := E) hD₁ hD₂ hP hRoot hRoot₁ hCross₁₂ hCross₂₁

theorem localMult_mulCoordRingElt_eq_add_when_rootMult_le_two_unconditional
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hD₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (hD₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hRoot : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2)
    (hRoot₁ : Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 2) :
    localMult E (mulCoordRingElt E D₁ D₂) P
      = localMult E D₁ P + localMult E D₂ P := by
  refine localMult_mulCoordRingElt_eq_add_when_rootMult_le_two
    (E := E) D₁ D₂ P hP hD₁ hD₂ hRoot hRoot₁ ?_ ?_
  · intro hY hD₁P hD₁negP hD₂P hD₂negP hm₁ hm₂
    exact Divisor.cross_iterDivLin_invariant_at_m_eq_two
      (E := E) hD₁ hD₂ hP hY hD₁P hD₁negP hD₂P hD₂negP hm₁ hm₂
  · intro hY hD₂P hD₂negP hD₁P hD₁negP hm₂ hm₁
    exact Divisor.cross_iterDivLin_invariant_at_m_eq_two
      (E := E) hD₂ hD₁ hP hY hD₂P hD₂negP hD₁P hD₁negP hm₂ hm₁

theorem localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
    (D₁ D₂ : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ E.points)
    (hD₁ : ¬ (D₁.a = 0 ∧ D₁.b = 0))
    (hD₂ : ¬ (D₂.a = 0 ∧ D₂.b = 0))
    (hRoot₁ : Polynomial.rootMultiplicity P.1 (normPoly E D₁) ≤ 2)
    (hRoot₂ : Polynomial.rootMultiplicity P.1 (normPoly E D₂) ≤ 2) :
    localMult E D₁ P + localMult E D₂ P
      ≤ localMult E (mulCoordRingElt E D₁ D₂) P := by
  have hEq := localMult_mulCoordRingElt_eq_add_when_rootMult_le_two_unconditional
    (E := E) D₁ D₂ P hP hD₁ hD₂ hRoot₂ hRoot₁
  exact le_of_eq hEq.symm

theorem landmarkInvStrong_combine_oo_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_oo E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt, hb_pt, zero_add]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_count_le : xs.count P ≤ localMult E a.poly P := by
      have htarget : target E xs a.point P = xs.count P := by
        rw [ha_pt]
        simp [target, negCoords]
      simpa [htarget] using ha_target_le
    have hb_count_le : ys.count P ≤ localMult E b.poly P := by
      have htarget : target E ys b.point P = ys.count P := by
        rw [hb_pt]
        simp [target, negCoords]
      simpa [htarget] using hb_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
        E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
        (h_root_le P hPon).1 (h_root_le P hPon).2
    calc
      target E (xs ++ ys) (EagenAccum.combine_oo E a b).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_oo, negCoords, List.count_append]
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_count_le hb_count_le
      _ ≤ localMult E (EagenAccum.combine_oo E a b).poly P := by
            simpa [EagenAccum.combine_oo] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_oo E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_pos ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    have h_combined_zero : (EagenAccum.combine_oo E a b).point = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero, ha_deg, hb_deg, List.length_append]
    omega

theorem landmarkInvStrong_combine_ol_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_b_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E b.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point = (0 : ECPoint E))
    (hb_pt : b.point ≠ (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_ol E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have _h_neg_b_on := h_neg_b_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show b.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt, zero_add]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_count_le : xs.count P ≤ localMult E a.poly P := by
      have htarget : target E xs a.point P = xs.count P := by
        rw [ha_pt]
        simp [target, negCoords]
      simpa [htarget] using ha_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
        E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
        (h_root_le P hPon).1 (h_root_le P hPon).2
    calc
      target E (xs ++ ys) (EagenAccum.combine_ol E a b).point P
          = xs.count P + target E ys b.point P := by
            simp [target, EagenAccum.combine_ol, List.count_append]
            omega
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_count_le hb_target_le
      _ ≤ localMult E (EagenAccum.combine_ol E a b).poly P := by
            simpa [EagenAccum.combine_ol] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_ol E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_pos ha_pt] at ha_deg
    rw [if_neg hb_pt] at hb_deg
    have h_combined_pt : (EagenAccum.combine_ol E a b).point = b.point := rfl
    rw [h_combined_pt, if_neg hb_pt, ha_deg, hb_deg, List.length_append]
    omega

theorem landmarkInvStrong_combine_or_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_a_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E a.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt : a.point ≠ (0 : ECPoint E))
    (hb_pt : b.point = (0 : ECPoint E))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_or E a b) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have _h_neg_a_on := h_neg_a_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  refine ⟨?_, ?_, ?_⟩
  · show a.point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, hb_pt, add_zero]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have hb_count_le : ys.count P ≤ localMult E b.poly P := by
      have htarget : target E ys b.point P = ys.count P := by
        rw [hb_pt]
        simp [target, negCoords]
      simpa [htarget] using hb_target_le
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
      exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
        E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
        (h_root_le P hPon).1 (h_root_le P hPon).2
    calc
      target E (xs ++ ys) (EagenAccum.combine_or E a b).point P
          = target E xs a.point P + ys.count P := by
            simp [target, EagenAccum.combine_or, List.count_append]
            omega
      _ ≤ localMult E a.poly P + localMult E b.poly P :=
            Nat.add_le_add ha_target_le hb_count_le
      _ ≤ localMult E (EagenAccum.combine_or E a b).poly P := by
            simpa [EagenAccum.combine_or] using hprod_le
  · show (normPoly E (mulCoordRingElt E a.poly b.poly)).natDegree =
        (xs ++ ys).length + (if (EagenAccum.combine_or E a b).point
          = (0 : ECPoint E) then 0 else 1)
    rw [normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_neg ha_pt] at ha_deg
    rw [if_pos hb_pt] at hb_deg
    have h_combined_pt : (EagenAccum.combine_or E a b).point = a.point := rfl
    rw [h_combined_pt, if_neg ha_pt, ha_deg, hb_deg, List.length_append]
    omega

theorem landmarkInvStrong_combine_vertical_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya : ZMod E.q}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxy_on : (xa, ya) ∈ E.points)
    (hxy_neg_on : (xa, -ya) ∈ E.points)
    (hy_ne : ya ≠ 0)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xa (-ya))
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine_vertical E a b xa) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
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
  have ha_van_neg : a.poly.eval xa (-ya) = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxy_neg_on
  have hb_van_pos : b.poly.eval xa ya = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxy_on
  set q := mulCoordRingElt E a.poly b.poly with hq_def
  have hq_eval_pos : q.eval xa ya = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_on, hb_van_pos]
    ring
  have hq_eval_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def, mulCoordRingElt_eval_on_E E _ _ hxy_neg_on, ha_van_neg]
    ring
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hy_ne hq_eval_pos hq_eval_neg
  have h_dvd_a : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_b : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq]
    exact mul_ne_zero ha_nz hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_div_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) :=
    divLin_not_both_zero E q hq_poly_nz h_qa_xa h_qb_xa
  let Lv : CoordRingElt E.q := { a := X - C xa, b := 0 }
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lv := by
    simpa [Lv] using mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_a h_dvd_b
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    have hns_b : E.toW.toAffine.Nonsingular xa (-ya) :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa (-ya)).mpr (E.hOnCurve _ hxy_neg_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    show (0 : ECPoint E) = (.some hns_a + .some hns_b : ECPoint E)
    have h_neg : (.some hns_b : ECPoint E) = -(.some hns_a) := by
      show WeierstrassCurve.Affine.Point.some hns_b
            = -WeierstrassCurve.Affine.Point.some hns_a
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg]
    show (0 : ECPoint E) = .some hns_a + (-.some hns_a)
    rw [add_neg_cancel]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if negCoords E a.point = some P then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target] using ha_target_le
    have hb_target_le' :
        ys.count P + (if negCoords E b.point = some P then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target] using hb_target_le
    have hLv_bound :
        localMult E Lv P
          ≤ (if negCoords E a.point = some P then 1 else 0)
            + (if negCoords E b.point = some P then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : ya = P.2 ∨ ya = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxy_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xa, ya) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using ord_vertical_at_x₀_nonTwoTorsion E xa ya hxy_on hy_ne
          rw [hLv_eq, hP_eq, if_pos hb_neg]
          omega
        · have hP_eq : P = (xa, -ya) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -ya ≠ 0 := by
            simpa using (neg_ne_zero.mpr hy_ne)
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, -ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using
                  ord_vertical_at_x₀_nonTwoTorsion E xa (-ya) hxy_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos ha_neg]
          omega
      · have hLv_eval_ne : Lv.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lv, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lv P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lv hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have htargets_plus_vertical_le :
        xs.count P + ys.count P + localMult E Lv P
          ≤ localMult E a.poly P + localMult E b.poly P := by
      omega
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E q P := by
      rw [hq_def]
      exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
        E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
        (h_root_le P hPon).1 (h_root_le P hPon).2
    have hq_local_eq :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) hq_div_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lv) P :=
          congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lv P := by simpa [Lv] using h
        _ = localMult E (q.divLin xa) P + localMult E Lv P := by
          rw [← localMult_eq_ordAt E (q.divLin xa) P,
              ← localMult_eq_ordAt E Lv P]
    calc
      target E (xs ++ ys) (EagenAccum.combine_vertical E a b xa).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_vertical, negCoords, List.count_append]
      _ ≤ localMult E (q.divLin xa) P := by
            have h :
                xs.count P + ys.count P + localMult E Lv P
                  ≤ localMult E (q.divLin xa) P + localMult E Lv P := by
              calc
                xs.count P + ys.count P + localMult E Lv P
                    ≤ localMult E a.poly P + localMult E b.poly P :=
                      htargets_plus_vertical_le
                _ ≤ localMult E q P := hprod_le
                _ = localMult E (q.divLin xa) P + localMult E Lv P := hq_local_eq
            omega
      _ = localMult E (EagenAccum.combine_vertical E a b xa).poly P := by
            simp [EagenAccum.combine_vertical, hq_def]
  · show (normPoly E (q.divLin xa)).natDegree
        = (xs ++ ys).length + (if (EagenAccum.combine_vertical E a b xa).point
                                  = (0 : ECPoint E) then 0 else 1)
    have h_combined_zero : (EagenAccum.combine_vertical E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    have h_factorize := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
      E q xa h_dvd_a h_dvd_b
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
      have ha_deg := LandmarkInvStrong.natDegree E ha
      have hb_deg := LandmarkInvStrong.natDegree E hb
      rw [if_neg hap] at ha_deg
      rw [if_neg hbp] at hb_deg
      omega
    rw [List.length_append]
    omega

theorem landmarkInvStrong_combine_tangent_torsion_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa : ZMod E.q}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxy_on : (xa, (0 : ZMod E.q)) ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa 0)
    (hb_pt_eq : b.point = ECPoint.affine E xa 0)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_tangent_torsion E a b xa) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have ha_neg : negCoords E a.point = some (xa, (0 : ZMod E.q)) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show some (xa, -(0 : ZMod E.q)) = some (xa, 0)
    rw [neg_zero]
  have hb_neg : negCoords E b.point = some (xa, (0 : ZMod E.q)) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show some (xa, -(0 : ZMod E.q)) = some (xa, 0)
    rw [neg_zero]
  have ha_van : a.poly.eval xa 0 = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxy_on
  have hb_van : b.poly.eval xa 0 = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxy_on
  set q := mulCoordRingElt E a.poly b.poly with hq_def
  obtain ⟨h_qa_xa, h_qb_xa⟩ : q.a.eval xa = 0 ∧ q.b.eval xa = 0 := by
    rw [hq_def]
    exact mul_components_eval_zero_at_twoTorsion E a.poly b.poly hxy_on ha_van hb_van
  have h_dvd_a : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_b : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq]
    exact mul_ne_zero ha_nz hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have _hdrop_torsion :
      localMult E q (xa, (0 : ZMod E.q))
        = 2 + localMult E (q.divLin xa) (xa, (0 : ZMod E.q)) :=
    localMult_divLin_decreases_by_two_at_twoTorsion_fiber
      E q (xa, (0 : ZMod E.q)) hxy_on rfl h_dvd_a h_dvd_b hq_poly_nz
  have hq_div_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) :=
    divLin_not_both_zero E q hq_poly_nz h_qa_xa h_qb_xa
  let Lv : CoordRingElt E.q := { a := X - C xa, b := 0 }
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lv := by
    simpa [Lv] using mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_a h_dvd_b
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ECPoint E) = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa 0 :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    show (0 : ECPoint E) = (.some hns + .some hns : ECPoint E)
    have hself_neg : (-(.some hns : ECPoint E)) = .some hns := by
      show -(WeierstrassCurve.Affine.Point.some hns : ECPoint E)
          = WeierstrassCurve.Affine.Point.some hns
      simp [WeierstrassCurve.Affine.Point.neg_some]
    calc
      (0 : ECPoint E) = (.some hns : ECPoint E) + (-.some hns) := by
        rw [add_neg_cancel]
      _ = (.some hns : ECPoint E) + .some hns := by
        rw [hself_neg]
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if negCoords E a.point = some P then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target] using ha_target_le
    have hb_target_le' :
        ys.count P + (if negCoords E b.point = some P then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target] using hb_target_le
    have hLv_bound :
        localMult E Lv P
          ≤ (if negCoords E a.point = some P then 1 else 0)
            + (if negCoords E b.point = some P then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : (0 : ZMod E.q) = P.2 ∨ (0 : ZMod E.q) = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxy_on hP_on_x
        have hP_eq : P = (xa, (0 : ZMod E.q)) := by
          rcases hy_dich with hy_eq | hy_eq_neg
          · ext
            · exact hPx
            · exact hy_eq.symm
          · ext
            · exact hPx
            · exact neg_eq_zero.mp hy_eq_neg.symm
        have hLv_eq : localMult E Lv P = 2 := by
          calc
            localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
            _ = ordAt E Lv (xa, (0 : ZMod E.q)) := by rw [hP_eq]
            _ = 2 := by
              simpa [Lv] using ord_vertical_at_x₀_twoTorsion E xa hxy_on
        rw [hLv_eq, hP_eq, if_pos ha_neg, if_pos hb_neg]
      · have hLv_eval_ne : Lv.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lv, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lv P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lv hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have htargets_plus_vertical_le :
        xs.count P + ys.count P + localMult E Lv P
          ≤ localMult E a.poly P + localMult E b.poly P := by
      omega
    have hprod_le :
        localMult E a.poly P + localMult E b.poly P
          ≤ localMult E q P := by
      rw [hq_def]
      exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
        E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
        (h_root_le P hPon).1 (h_root_le P hPon).2
    have hq_local_eq :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) hq_div_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lv) P :=
          congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lv P := by simpa [Lv] using h
        _ = localMult E (q.divLin xa) P + localMult E Lv P := by
          rw [← localMult_eq_ordAt E (q.divLin xa) P,
              ← localMult_eq_ordAt E Lv P]
    calc
      target E (xs ++ ys) (EagenAccum.combine_tangent_torsion E a b xa).point P
          = xs.count P + ys.count P := by
            simp [target, EagenAccum.combine_tangent_torsion,
              EagenAccum.combine_vertical, negCoords, List.count_append]
      _ ≤ localMult E (q.divLin xa) P := by
            have h :
                xs.count P + ys.count P + localMult E Lv P
                  ≤ localMult E (q.divLin xa) P + localMult E Lv P := by
              calc
                xs.count P + ys.count P + localMult E Lv P
                    ≤ localMult E a.poly P + localMult E b.poly P :=
                      htargets_plus_vertical_le
                _ ≤ localMult E q P := hprod_le
                _ = localMult E (q.divLin xa) P + localMult E Lv P := hq_local_eq
            omega
      _ = localMult E (EagenAccum.combine_tangent_torsion E a b xa).poly P := by
            simp [EagenAccum.combine_tangent_torsion,
              EagenAccum.combine_vertical, hq_def]
  · show (normPoly E (q.divLin xa)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_tangent_torsion E a b xa).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_zero : (EagenAccum.combine_tangent_torsion E a b xa).point
        = (0 : ECPoint E) := rfl
    rw [if_pos h_combined_zero]
    have h_factorize := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
      E q xa h_dvd_a h_dvd_b
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
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 2 := by
      rw [hq_def, normPoly_mul_eq, Polynomial.natDegree_mul ha_nz hb_nz]
      have hap : a.point ≠ (0 : ECPoint E) := by
        rw [ha_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa 0 :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      have hbp : b.point ≠ (0 : ECPoint E) := by
        rw [hb_pt_eq]
        intro h
        have hns : E.toW.toAffine.Nonsingular xa 0 :=
          E.equation_iff_nonsingular.mp ((E.equation_iff xa 0).mpr (E.hOnCurve _ hxy_on))
        rw [ECPoint.affine_of_nonsingular E hns] at h
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
      have ha_deg := LandmarkInvStrong.natDegree E ha
      have hb_deg := LandmarkInvStrong.natDegree E hb
      rw [if_neg hap] at ha_deg
      rw [if_neg hbp] at hb_deg
      omega
    rw [List.length_append]
    omega

theorem landmarkInvStrong_combine_distinct_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya xb yb : ZMod E.q}
    (h_xx : xa ≠ xb)
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxa_on : (xa, ya) ∈ E.points)
    (hxb_on : (xb, yb) ∈ E.points)
    (hya_ne : ya ≠ 0)
    (hyb_ne : yb ≠ 0)
    (h_third_xa : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xa)
    (h_third_xb : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xb)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xb yb)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_distinct E a b xa ya xb yb h_xx) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  set Qx := slopeOf xa ya xb yb ^ 2 - xa - xb with hQx_def
  set Qy := slopeOf xa ya xb yb * Qx + (ya - slopeOf xa ya xb yb * xa) with hQy_def
  set line := chordCoordRingElt E (xa, ya) (xb, yb) with hline_def
  set q := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly with hq_def
  let Lva : CoordRingElt E.q := { a := X - C xa, b := 0 }
  let Lvb : CoordRingElt E.q := { a := X - C xb, b := 0 }
  have hQx_ne_xa : Qx ≠ xa := by simpa [hQx_def] using h_third_xa
  have hQx_ne_xb : Qx ≠ xb := by simpa [hQx_def] using h_third_xb
  have hxa_ne_Qx : xa ≠ Qx := fun h => hQx_ne_xa h.symm
  have hxb_ne_Qx : xb ≠ Qx := fun h => hQx_ne_xb h.symm
  have hT : thirdPoint E (xa, ya) (xb, yb) = some (Qx, Qy) := by
    unfold thirdPoint
    rw [if_neg h_xx]
    simp [hQx_def, hQy_def, slopeOf]
  have hQ_on : (Qx, Qy) ∈ E.points :=
    third_point_on_curve E (xa, ya) (xb, yb) hxa_on hxb_on hT
  have hQ_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E hQ_on
  have hxa_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
  have hxb_neg_on : (xb, -yb) ∈ E.points := points_neg_y E hxb_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hline_poly_nz : ¬ (line.a = 0 ∧ line.b = 0) := by
    rw [hline_def]
    exact chordCoordRingElt_ne_zero E (xa, ya) (xb, yb)
  have hline_nz : normPoly E line ≠ 0 := normPoly_ne_zero E line hline_poly_nz
  have hline_root_le :
      ∀ x : ZMod E.q, Polynomial.rootMultiplicity x (normPoly E line) ≤ 1 := by
    intro x
    rw [hline_def]
    exact chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord
      E (xa, ya) (xb, yb) hxa_on hxb_on h_xx hxa_ne_Qx hxb_ne_Qx x
  have hlinea_nz : normPoly E (mulCoordRingElt E line a.poly) ≠ 0 := by
    rw [normPoly_mul_eq]
    exact mul_ne_zero hline_nz ha_nz
  have hlinea_poly_nz :
      ¬ ((mulCoordRingElt E line a.poly).a = 0 ∧
          (mulCoordRingElt E line a.poly).b = 0) := by
    intro hzero
    apply hlinea_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hlineb_nz : normPoly E (mulCoordRingElt E line b.poly) ≠ 0 := by
    rw [normPoly_mul_eq]
    exact mul_ne_zero hline_nz hb_nz
  have hlineb_poly_nz :
      ¬ ((mulCoordRingElt E line b.poly).a = 0 ∧
          (mulCoordRingElt E line b.poly).b = 0) := by
    intro hzero
    apply hlineb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have ha_neg : negCoords E a.point = some (xa, -ya) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hb_neg : negCoords E b.point = some (xb, -yb) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have ha_neg_eval : a.poly.eval xa (-ya) = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxa_neg_on
  have hb_neg_eval : b.poly.eval xb (-yb) = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxb_neg_on
  have hline_eval_a : line.eval xa ya = 0 := by
    rw [hline_def]
    exact chordCoordRingElt_eval_left E (xa, ya) (xb, yb)
  have hline_eval_b : line.eval xb yb = 0 := by
    rw [hline_def]
    exact chordCoordRingElt_eval_right E (xa, ya) (xb, yb)
  have hq_eval_xa_pos : q.eval xa ya = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_on]
    rw [hline_eval_a]
    ring
  have hq_eval_xa_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_neg_on]
    rw [ha_neg_eval]
    ring
  have hq_eval_xb_pos : q.eval xb yb = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_on]
    rw [hline_eval_b]
    ring
  have hq_eval_xb_neg : q.eval xb (-yb) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_neg_on]
    rw [hb_neg_eval]
    ring
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hya_ne hq_eval_xa_pos hq_eval_xa_neg
  obtain ⟨h_qa_xb, h_qb_xb⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xb yb hyb_ne hq_eval_xb_pos hq_eval_xb_neg
  have h_dvd_qa_xa : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_qb_xa : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have h_dvd_qa_xb : (X - C xb) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xb
  have h_dvd_qb_xb : (X - C xb) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xb
  have h_dvd_a_after : (X - C xb) ∣ (q.divLin xa).a := by
    rw [CoordRingElt.divLin_a]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qa_xa h_dvd_qa_xb h_xx
  have h_dvd_b_after : (X - C xb) ∣ (q.divLin xa).b := by
    rw [CoordRingElt.divLin_b]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qb_xa h_dvd_qb_xb h_xx
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
    exact mul_ne_zero (mul_ne_zero hline_nz ha_nz) hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have _hdrop_xa := localMult_divLin_decreases_at_fiber
    E q (xa, ya) hxa_on h_dvd_qa_xa h_dvd_qb_xa hq_poly_nz
  have _hdrop_xb := localMult_divLin_decreases_at_fiber
    E (q.divLin xa) (xb, yb) hxb_on h_dvd_a_after h_dvd_b_after
      (by
        have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
          E q xa h_dvd_qa_xa h_dvd_qb_xa
        have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
          intro hzero
          apply hq_nz
          rw [h_factor1, hzero, mul_zero]
        intro hzero
        apply h_div1_nz
        rw [normPoly_eq, hzero.1, hzero.2]
        ring)
  have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E q xa h_dvd_qa_xa h_dvd_qb_xa
  have h_factor2 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E (q.divLin xa) xb h_dvd_a_after h_dvd_b_after
  have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
    intro hzero
    apply hq_nz
    rw [h_factor1, hzero, mul_zero]
  have h_div1_poly_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) := by
    intro hzero
    apply h_div1_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have h_div2_nz : normPoly E ((q.divLin xa).divLin xb) ≠ 0 := by
    intro hzero
    apply h_div1_nz
    rw [h_factor2, hzero, mul_zero]
  have h_div2_poly_nz :
      ¬ (((q.divLin xa).divLin xb).a = 0 ∧
          ((q.divLin xa).divLin xb).b = 0) := by
    intro hzero
    apply h_div2_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lva := by
    simpa [Lva] using
      mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_qa_xa h_dvd_qb_xa
  have hdiv1_recomp :
      q.divLin xa = mulCoordRingElt E ((q.divLin xa).divLin xb) Lvb := by
    simpa [Lvb] using
      mulCoordRingElt_divLin_vertical_recompose E (q.divLin xa) xb
        h_dvd_a_after h_dvd_b_after
  have hns_Qneg : E.toW.toAffine.Nonsingular Qx (-Qy) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ hQ_neg_on))
  have h_combined_neg :
      negCoords E (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
        = some (Qx, Qy) := by
    show negCoords E (ECPoint.affine E Qx (-Qy)) = some (Qx, Qy)
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    show some (Qx, -(-Qy)) = some (Qx, Qy)
    rw [neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · show (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    have hns_b : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    show ECPoint.affine E Qx (-Qy) = (.some hns_a + .some hns_b : ECPoint E)
    have hSum := thirdPoint_some_eq_neg_add (E := E) hxa_on hxb_on hT
    have hns_Q : E.toW.toAffine.Nonsingular Qx Qy :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ hQ_on))
    have heq_a : ECPoint.affineOfMem E hxa_on = (.some hns_a : ECPoint E) := rfl
    have heq_b : ECPoint.affineOfMem E hxb_on = (.some hns_b : ECPoint E) := rfl
    have heq_Q : ECPoint.affineOfMem E hQ_on = (.some hns_Q : ECPoint E) := rfl
    rw [heq_a, heq_b, heq_Q] at hSum
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    have h_neg_third : (.some hns_Qneg : ECPoint E) = -(.some hns_Q : ECPoint E) := by
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg_third]
    exact hSum.symm
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if P = (xa, -ya) then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target, ha_neg, eq_comm] using ha_target_le
    have hb_target_le' :
        ys.count P + (if P = (xb, -yb) then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target, hb_neg, eq_comm] using hb_target_le
    have hline_left : 1 ≤ localMult E line (xa, ya) := by
      rw [hline_def]
      exact localMult_chordCoordRingElt_at_left E hxa_on
    have hline_right : 1 ≤ localMult E line (xb, yb) := by
      rw [hline_def]
      exact localMult_chordCoordRingElt_at_right E hxb_on
    have hline_third : 1 ≤ localMult E line (Qx, Qy) := by
      rw [hline_def]
      simpa [hQx_def, hQy_def, slopeOf] using
        (localMult_chordCoordRingElt_at_third (E := E)
          (P := (xa, ya)) (Q := (xb, yb)) hxa_on hxb_on h_xx)
    have hline_markers :
        (if P = (xa, ya) then 1 else 0)
          + (if P = (xb, yb) then 1 else 0)
          + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E line P := by
      by_cases hPa : P = (xa, ya)
      · subst P
        have hA_ne_B : (xa, ya) ≠ (xb, yb) := by
          intro h
          exact h_xx (congrArg Prod.fst h)
        have hA_ne_Q : (xa, ya) ≠ (Qx, Qy) := by
          intro h
          exact hQx_ne_xa (congrArg Prod.fst h).symm
        rw [if_pos rfl, if_neg hA_ne_B, if_neg hA_ne_Q]
        omega
      · by_cases hPb : P = (xb, yb)
        · subst P
          have hB_ne_A : (xb, yb) ≠ (xa, ya) := by
            intro h
            exact h_xx (congrArg Prod.fst h).symm
          have hB_ne_Q : (xb, yb) ≠ (Qx, Qy) := by
            intro h
            exact hQx_ne_xb (congrArg Prod.fst h).symm
          rw [if_neg hB_ne_A, if_pos rfl, if_neg hB_ne_Q]
          omega
        · by_cases hPQ : P = (Qx, Qy)
          · subst P
            have hQ_ne_A : (Qx, Qy) ≠ (xa, ya) := by
              intro h
              exact hQx_ne_xa (congrArg Prod.fst h)
            have hQ_ne_B : (Qx, Qy) ≠ (xb, yb) := by
              intro h
              exact hQx_ne_xb (congrArg Prod.fst h)
            rw [if_neg hQ_ne_A, if_neg hQ_ne_B, if_pos rfl]
            omega
          · rw [if_neg hPa, if_neg hPb, if_neg hPQ]
            omega
    have hLva_bound :
        localMult E Lva P
          ≤ (if P = (xa, ya) then 1 else 0)
            + (if P = (xa, -ya) then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : ya = P.2 ∨ ya = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxa_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xa, ya) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lva P = 1 := by
            calc
              localMult E Lva P = ordAt E Lva P := localMult_eq_ordAt E Lva P
              _ = ordAt E Lva (xa, ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lva] using ord_vertical_at_x₀_nonTwoTorsion E xa ya hxa_on hya_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, ya) = (xa, -ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
        · have hP_eq : P = (xa, -ya) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -ya ≠ 0 := by simpa using (neg_ne_zero.mpr hya_ne)
          have hLv_eq : localMult E Lva P = 1 := by
            calc
              localMult E Lva P = ordAt E Lva P := localMult_eq_ordAt E Lva P
              _ = ordAt E Lva (xa, -ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lva] using
                  ord_vertical_at_x₀_nonTwoTorsion E xa (-ya) hxa_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, -ya) = (xa, ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
      · have hLv_eval_ne : Lva.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lva, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lva P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lva hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have hLvb_bound :
        localMult E Lvb P
          ≤ (if P = (xb, yb) then 1 else 0)
            + (if P = (xb, -yb) then 1 else 0) := by
      by_cases hPx : P.1 = xb
      · have hP_eq_x : P = (xb, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xb, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : yb = P.2 ∨ yb = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxb_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xb, yb) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lvb P = 1 := by
            calc
              localMult E Lvb P = ordAt E Lvb P := localMult_eq_ordAt E Lvb P
              _ = ordAt E Lvb (xb, yb) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lvb] using ord_vertical_at_x₀_nonTwoTorsion E xb yb hxb_on hyb_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xb, yb) = (xb, -yb)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
        · have hP_eq : P = (xb, -yb) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -yb ≠ 0 := by simpa using (neg_ne_zero.mpr hyb_ne)
          have hLv_eq : localMult E Lvb P = 1 := by
            calc
              localMult E Lvb P = ordAt E Lvb P := localMult_eq_ordAt E Lvb P
              _ = ordAt E Lvb (xb, -yb) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lvb] using
                  ord_vertical_at_x₀_nonTwoTorsion E xb (-yb) hxb_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xb, -yb) = (xb, yb)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
      · have hLv_eval_ne : Lvb.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xb ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lvb, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lvb P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lvb hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have hprod_all_ge :
        localMult E a.poly P + localMult E b.poly P + localMult E line P
          ≤ localMult E q P := by
      rcases h_root_le P hPon with hroot_a | hroot_b
      · have hline_b_ge :
            localMult E line P + localMult E b.poly P
              ≤ localMult E (mulCoordRingElt E line b.poly) P := by
          apply localMult_mulCoordRingElt_ge_add_general E line b.poly P
            hPon hline_poly_nz hb_poly_nz
          exact Or.inr (hline_root_le P.1)
        have hq_alt :
            mulCoordRingElt E (mulCoordRingElt E line b.poly) a.poly = q := by
          rw [hq_def]
          calc
            mulCoordRingElt E (mulCoordRingElt E line b.poly) a.poly
                = mulCoordRingElt E line (mulCoordRingElt E b.poly a.poly) :=
                    mulCoordRingElt_assoc E line b.poly a.poly
            _ = mulCoordRingElt E line (mulCoordRingElt E a.poly b.poly) := by
                    rw [mulCoordRingElt_comm E b.poly a.poly]
            _ = mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly :=
                    (mulCoordRingElt_assoc E line a.poly b.poly).symm
        have hprod_ge :
            localMult E (mulCoordRingElt E line b.poly) P + localMult E a.poly P
              ≤ localMult E q P := by
          have hmul := localMult_mulCoordRingElt_ge_add_general
            E (mulCoordRingElt E line b.poly) a.poly P
            hPon hlineb_poly_nz ha_poly_nz (Or.inl hroot_a)
          simpa [hq_alt] using hmul
        omega
      · have hline_a_ge :
            localMult E line P + localMult E a.poly P
              ≤ localMult E (mulCoordRingElt E line a.poly) P := by
          apply localMult_mulCoordRingElt_ge_add_general E line a.poly P
            hPon hline_poly_nz ha_poly_nz
          exact Or.inr (hline_root_le P.1)
        have hprod_ge :
            localMult E (mulCoordRingElt E line a.poly) P + localMult E b.poly P
              ≤ localMult E q P := by
          rw [hq_def]
          apply localMult_mulCoordRingElt_ge_add_general
            E (mulCoordRingElt E line a.poly) b.poly P
            hPon hlinea_poly_nz hb_poly_nz
          exact Or.inl hroot_b
        omega
    have hmarkers_plus_vertical_le :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
            + localMult E Lvb P + localMult E Lva P
          ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P := by
      omega
    have hq_local_eq_raw :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lva P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) h_div1_poly_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lva) P :=
              congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lva P := by
              simpa [Lva] using h
        _ = localMult E (q.divLin xa) P + localMult E Lva P := by
              rw [← localMult_eq_ordAt E (q.divLin xa) P,
                ← localMult_eq_ordAt E Lva P]
    have hdiv1_local_eq :
        localMult E (q.divLin xa) P =
          localMult E ((q.divLin xa).divLin xb) P + localMult E Lvb P := by
      have h := ordAt_mul_vertical_add E ((q.divLin xa).divLin xb)
        h_div2_poly_nz xb hPon
      calc
        localMult E (q.divLin xa) P = ordAt E (q.divLin xa) P :=
          localMult_eq_ordAt E (q.divLin xa) P
        _ = ordAt E (mulCoordRingElt E ((q.divLin xa).divLin xb) Lvb) P :=
              congrArg (fun D => ordAt E D P) hdiv1_recomp
        _ = ordAt E ((q.divLin xa).divLin xb) P + ordAt E Lvb P := by
              simpa [Lvb] using h
        _ = localMult E ((q.divLin xa).divLin xb) P + localMult E Lvb P := by
              rw [← localMult_eq_ordAt E ((q.divLin xa).divLin xb) P,
                ← localMult_eq_ordAt E Lvb P]
    have hq_local_eq :
        localMult E q P =
          localMult E ((q.divLin xa).divLin xb) P
            + localMult E Lvb P + localMult E Lva P := by
      rw [hq_local_eq_raw, hdiv1_local_eq]
    have htarget_base_le_after :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E ((q.divLin xa).divLin xb) P := by
      have h :
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lvb P + localMult E Lva P
            ≤ localMult E ((q.divLin xa).divLin xb) P
                + localMult E Lvb P + localMult E Lva P := by
        calc
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lvb P + localMult E Lva P
              ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P :=
                hmarkers_plus_vertical_le
          _ ≤ localMult E q P := hprod_all_ge
          _ = localMult E ((q.divLin xa).divLin xb) P
                + localMult E Lvb P + localMult E Lva P := hq_local_eq
      omega
    calc
      target E (xs ++ ys) (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point P
          = xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0) := by
            simp [target, h_combined_neg, List.count_append, eq_comm]
      _ ≤ localMult E ((q.divLin xa).divLin xb) P := htarget_base_le_after
      _ = localMult E (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).poly P := by
            simp [EagenAccum.combine_distinct, hq_def, hline_def]
  · show (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_ne :
        (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
          ≠ (0 : ECPoint E) := by
      show ECPoint.affine E Qx (-Qy) ≠ (0 : ECPoint E)
      rw [ECPoint.affine_of_nonsingular E hns_Qneg]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns_Qneg
    rw [if_neg h_combined_ne]
    have h_X_sub_a_pow_ne : ((X - C xa) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_X_sub_b_pow_ne : ((X - C xb) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_natDeg1 : (normPoly E (q.divLin xa)).natDegree
        = (normPoly E q).natDegree - 2 := by
      have hh : (normPoly E q).natDegree
          = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E (q.divLin xa)).natDegree := by
        rw [h_factor1, Polynomial.natDegree_mul h_X_sub_a_pow_ne h_div1_nz]
      have hp : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_natDeg2 : (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (normPoly E (q.divLin xa)).natDegree - 2 := by
      have hh : (normPoly E (q.divLin xa)).natDegree
          = ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E ((q.divLin xa).divLin xb)).natDegree := by
        rw [h_factor2, Polynomial.natDegree_mul h_X_sub_b_pow_ne h_div2_nz]
      have hp : ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_line_deg : (normPoly E line).natDegree = 3 := by
      rw [hline_def]
      exact chordCoordRingElt_natDegree_normPoly_of_xx_ne E h_xx
    have hap : a.point ≠ (0 : ECPoint E) := by
      rw [ha_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xa ya :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have hbp : b.point ≠ (0 : ECPoint E) := by
      rw [hb_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xb yb :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_neg hap] at ha_deg
    rw [if_neg hbp] at hb_deg
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 5 := by
      rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
      rw [Polynomial.natDegree_mul (mul_ne_zero hline_nz ha_nz) hb_nz,
          Polynomial.natDegree_mul hline_nz ha_nz]
      rw [h_line_deg, ha_deg, hb_deg]
      omega
    rw [h_natDeg2, h_natDeg1, h_qnp, List.length_append]
    omega

theorem landmarkInvStrong_combine_distinct_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya xb yb : ZMod E.q}
    (h_xx : xa ≠ xb)
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (hxa_on : (xa, ya) ∈ E.points)
    (hxb_on : (xb, yb) ∈ E.points)
    (hya_ne : ya ≠ 0)
    (hyb_ne : yb ≠ 0)
    (h_third_xa : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xa)
    (h_third_xb : (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xb)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xb yb)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_distinct E a b xa ya xb yb h_xx) := by
  classical
  have _hxs_on := hxs_on
  have _hys_on := hys_on
  set Qx := slopeOf xa ya xb yb ^ 2 - xa - xb with hQx_def
  set Qy := slopeOf xa ya xb yb * Qx + (ya - slopeOf xa ya xb yb * xa) with hQy_def
  set line := chordCoordRingElt E (xa, ya) (xb, yb) with hline_def
  set q := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly with hq_def
  let Lva : CoordRingElt E.q := { a := X - C xa, b := 0 }
  let Lvb : CoordRingElt E.q := { a := X - C xb, b := 0 }
  have hQx_ne_xa : Qx ≠ xa := by simpa [hQx_def] using h_third_xa
  have hQx_ne_xb : Qx ≠ xb := by simpa [hQx_def] using h_third_xb
  have hxa_ne_Qx : xa ≠ Qx := fun h => hQx_ne_xa h.symm
  have hxb_ne_Qx : xb ≠ Qx := fun h => hQx_ne_xb h.symm
  have hT : thirdPoint E (xa, ya) (xb, yb) = some (Qx, Qy) := by
    unfold thirdPoint
    rw [if_neg h_xx]
    simp [hQx_def, hQy_def, slopeOf]
  have hQ_on : (Qx, Qy) ∈ E.points :=
    third_point_on_curve E (xa, ya) (xb, yb) hxa_on hxb_on hT
  have hQ_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E hQ_on
  have hxa_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
  have hxb_neg_on : (xb, -yb) ∈ E.points := points_neg_y E hxb_on
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hline_poly_nz : ¬ (line.a = 0 ∧ line.b = 0) := by
    rw [hline_def]
    exact chordCoordRingElt_ne_zero E (xa, ya) (xb, yb)
  have hline_nz : normPoly E line ≠ 0 := normPoly_ne_zero E line hline_poly_nz
  have hline_root_le :
      ∀ x : ZMod E.q, Polynomial.rootMultiplicity x (normPoly E line) ≤ 1 := by
    intro x
    rw [hline_def]
    exact chordCoordRingElt_normPoly_rootMult_le_one_at_distinct_chord
      E (xa, ya) (xb, yb) hxa_on hxb_on h_xx hxa_ne_Qx hxb_ne_Qx x
  have hlinea_nz : normPoly E (mulCoordRingElt E line a.poly) ≠ 0 := by
    rw [normPoly_mul_eq]
    exact mul_ne_zero hline_nz ha_nz
  have hlinea_poly_nz :
      ¬ ((mulCoordRingElt E line a.poly).a = 0 ∧
          (mulCoordRingElt E line a.poly).b = 0) := by
    intro hzero
    apply hlinea_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hlineb_nz : normPoly E (mulCoordRingElt E line b.poly) ≠ 0 := by
    rw [normPoly_mul_eq]
    exact mul_ne_zero hline_nz hb_nz
  have hlineb_poly_nz :
      ¬ ((mulCoordRingElt E line b.poly).a = 0 ∧
          (mulCoordRingElt E line b.poly).b = 0) := by
    intro hzero
    apply hlineb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have ha_neg : negCoords E a.point = some (xa, -ya) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hb_neg : negCoords E b.point = some (xb, -yb) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have ha_neg_eval : a.poly.eval xa (-ya) = 0 :=
    LandmarkInvStrong.vanish_of_residue E ha ha_neg hxa_neg_on
  have hb_neg_eval : b.poly.eval xb (-yb) = 0 :=
    LandmarkInvStrong.vanish_of_residue E hb hb_neg hxb_neg_on
  have hline_eval_a : line.eval xa ya = 0 := by
    rw [hline_def]
    exact chordCoordRingElt_eval_left E (xa, ya) (xb, yb)
  have hline_eval_b : line.eval xb yb = 0 := by
    rw [hline_def]
    exact chordCoordRingElt_eval_right E (xa, ya) (xb, yb)
  have hq_eval_xa_pos : q.eval xa ya = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_on]
    rw [hline_eval_a]
    ring
  have hq_eval_xa_neg : q.eval xa (-ya) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxa_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxa_neg_on]
    rw [ha_neg_eval]
    ring
  have hq_eval_xb_pos : q.eval xb yb = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_on]
    rw [hline_eval_b]
    ring
  have hq_eval_xb_neg : q.eval xb (-yb) = 0 := by
    rw [hq_def]
    rw [mulCoordRingElt_eval_on_E E _ b.poly hxb_neg_on]
    rw [mulCoordRingElt_eval_on_E E line a.poly hxb_neg_on]
    rw [hb_neg_eval]
    ring
  obtain ⟨h_qa_xa, h_qb_xa⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xa ya hya_ne hq_eval_xa_pos hq_eval_xa_neg
  obtain ⟨h_qa_xb, h_qb_xb⟩ :=
    qa_qb_eval_zero_of_double_fiber_vanish E q xb yb hyb_ne hq_eval_xb_pos hq_eval_xb_neg
  have h_dvd_qa_xa : (X - C xa) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xa
  have h_dvd_qb_xa : (X - C xa) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xa
  have h_dvd_qa_xb : (X - C xb) ∣ q.a := dvd_X_sub_C_of_eval_eq_zero E h_qa_xb
  have h_dvd_qb_xb : (X - C xb) ∣ q.b := dvd_X_sub_C_of_eval_eq_zero E h_qb_xb
  have h_dvd_a_after : (X - C xb) ∣ (q.divLin xa).a := by
    rw [CoordRingElt.divLin_a]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qa_xa h_dvd_qa_xb h_xx
  have h_dvd_b_after : (X - C xb) ∣ (q.divLin xa).b := by
    rw [CoordRingElt.divLin_b]
    exact dvd_X_sub_C_divByMonic_X_sub_C_of_ne E h_dvd_qb_xa h_dvd_qb_xb h_xx
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
    exact mul_ne_zero (mul_ne_zero hline_nz ha_nz) hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have _hdrop_xa := localMult_divLin_decreases_at_fiber
    E q (xa, ya) hxa_on h_dvd_qa_xa h_dvd_qb_xa hq_poly_nz
  have _hdrop_xb := localMult_divLin_decreases_at_fiber
    E (q.divLin xa) (xb, yb) hxb_on h_dvd_a_after h_dvd_b_after
      (by
        have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
          E q xa h_dvd_qa_xa h_dvd_qb_xa
        have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
          intro hzero
          apply hq_nz
          rw [h_factor1, hzero, mul_zero]
        intro hzero
        apply h_div1_nz
        rw [normPoly_eq, hzero.1, hzero.2]
        ring)
  have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E q xa h_dvd_qa_xa h_dvd_qb_xa
  have h_factor2 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E (q.divLin xa) xb h_dvd_a_after h_dvd_b_after
  have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
    intro hzero
    apply hq_nz
    rw [h_factor1, hzero, mul_zero]
  have h_div1_poly_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) := by
    intro hzero
    apply h_div1_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have h_div2_nz : normPoly E ((q.divLin xa).divLin xb) ≠ 0 := by
    intro hzero
    apply h_div1_nz
    rw [h_factor2, hzero, mul_zero]
  have h_div2_poly_nz :
      ¬ (((q.divLin xa).divLin xb).a = 0 ∧
          ((q.divLin xa).divLin xb).b = 0) := by
    intro hzero
    apply h_div2_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lva := by
    simpa [Lva] using
      mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_qa_xa h_dvd_qb_xa
  have hdiv1_recomp :
      q.divLin xa = mulCoordRingElt E ((q.divLin xa).divLin xb) Lvb := by
    simpa [Lvb] using
      mulCoordRingElt_divLin_vertical_recompose E (q.divLin xa) xb
        h_dvd_a_after h_dvd_b_after
  have hns_Qneg : E.toW.toAffine.Nonsingular Qx (-Qy) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ hQ_neg_on))
  have h_combined_neg :
      negCoords E (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
        = some (Qx, Qy) := by
    show negCoords E (ECPoint.affine E Qx (-Qy)) = some (Qx, Qy)
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    show some (Qx, -(-Qy)) = some (Qx, Qy)
    rw [neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · show (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point = sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
    have hns_b : E.toW.toAffine.Nonsingular xb yb :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
    rw [ECPoint.affine_of_nonsingular E hns_a, ECPoint.affine_of_nonsingular E hns_b]
    show ECPoint.affine E Qx (-Qy) = (.some hns_a + .some hns_b : ECPoint E)
    have hSum := thirdPoint_some_eq_neg_add (E := E) hxa_on hxb_on hT
    have hns_Q : E.toW.toAffine.Nonsingular Qx Qy :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ hQ_on))
    have heq_a : ECPoint.affineOfMem E hxa_on = (.some hns_a : ECPoint E) := rfl
    have heq_b : ECPoint.affineOfMem E hxb_on = (.some hns_b : ECPoint E) := rfl
    have heq_Q : ECPoint.affineOfMem E hQ_on = (.some hns_Q : ECPoint E) := rfl
    rw [heq_a, heq_b, heq_Q] at hSum
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    have h_neg_third : (.some hns_Qneg : ECPoint E) = -(.some hns_Q : ECPoint E) := by
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg_third]
    exact hSum.symm
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if P = (xa, -ya) then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target, ha_neg, eq_comm] using ha_target_le
    have hb_target_le' :
        ys.count P + (if P = (xb, -yb) then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target, hb_neg, eq_comm] using hb_target_le
    have hline_left : 1 ≤ localMult E line (xa, ya) := by
      rw [hline_def]
      exact localMult_chordCoordRingElt_at_left E hxa_on
    have hline_right : 1 ≤ localMult E line (xb, yb) := by
      rw [hline_def]
      exact localMult_chordCoordRingElt_at_right E hxb_on
    have hline_third : 1 ≤ localMult E line (Qx, Qy) := by
      rw [hline_def]
      simpa [hQx_def, hQy_def, slopeOf] using
        (localMult_chordCoordRingElt_at_third (E := E)
          (P := (xa, ya)) (Q := (xb, yb)) hxa_on hxb_on h_xx)
    have hline_markers :
        (if P = (xa, ya) then 1 else 0)
          + (if P = (xb, yb) then 1 else 0)
          + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E line P := by
      by_cases hPa : P = (xa, ya)
      · subst P
        have hA_ne_B : (xa, ya) ≠ (xb, yb) := by
          intro h
          exact h_xx (congrArg Prod.fst h)
        have hA_ne_Q : (xa, ya) ≠ (Qx, Qy) := by
          intro h
          exact hQx_ne_xa (congrArg Prod.fst h).symm
        rw [if_pos rfl, if_neg hA_ne_B, if_neg hA_ne_Q]
        omega
      · by_cases hPb : P = (xb, yb)
        · subst P
          have hB_ne_A : (xb, yb) ≠ (xa, ya) := by
            intro h
            exact h_xx (congrArg Prod.fst h).symm
          have hB_ne_Q : (xb, yb) ≠ (Qx, Qy) := by
            intro h
            exact hQx_ne_xb (congrArg Prod.fst h).symm
          rw [if_neg hB_ne_A, if_pos rfl, if_neg hB_ne_Q]
          omega
        · by_cases hPQ : P = (Qx, Qy)
          · subst P
            have hQ_ne_A : (Qx, Qy) ≠ (xa, ya) := by
              intro h
              exact hQx_ne_xa (congrArg Prod.fst h)
            have hQ_ne_B : (Qx, Qy) ≠ (xb, yb) := by
              intro h
              exact hQx_ne_xb (congrArg Prod.fst h)
            rw [if_neg hQ_ne_A, if_neg hQ_ne_B, if_pos rfl]
            omega
          · rw [if_neg hPa, if_neg hPb, if_neg hPQ]
            omega
    have hLva_bound :
        localMult E Lva P
          ≤ (if P = (xa, ya) then 1 else 0)
            + (if P = (xa, -ya) then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : ya = P.2 ∨ ya = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxa_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xa, ya) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lva P = 1 := by
            calc
              localMult E Lva P = ordAt E Lva P := localMult_eq_ordAt E Lva P
              _ = ordAt E Lva (xa, ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lva] using ord_vertical_at_x₀_nonTwoTorsion E xa ya hxa_on hya_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, ya) = (xa, -ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
        · have hP_eq : P = (xa, -ya) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -ya ≠ 0 := by simpa using (neg_ne_zero.mpr hya_ne)
          have hLv_eq : localMult E Lva P = 1 := by
            calc
              localMult E Lva P = ordAt E Lva P := localMult_eq_ordAt E Lva P
              _ = ordAt E Lva (xa, -ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lva] using
                  ord_vertical_at_x₀_nonTwoTorsion E xa (-ya) hxa_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, -ya) = (xa, ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
      · have hLv_eval_ne : Lva.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lva, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lva P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lva hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have hLvb_bound :
        localMult E Lvb P
          ≤ (if P = (xb, yb) then 1 else 0)
            + (if P = (xb, -yb) then 1 else 0) := by
      by_cases hPx : P.1 = xb
      · have hP_eq_x : P = (xb, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xb, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : yb = P.2 ∨ yb = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxb_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xb, yb) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lvb P = 1 := by
            calc
              localMult E Lvb P = ordAt E Lvb P := localMult_eq_ordAt E Lvb P
              _ = ordAt E Lvb (xb, yb) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lvb] using ord_vertical_at_x₀_nonTwoTorsion E xb yb hxb_on hyb_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xb, yb) = (xb, -yb)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
        · have hP_eq : P = (xb, -yb) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -yb ≠ 0 := by simpa using (neg_ne_zero.mpr hyb_ne)
          have hLv_eq : localMult E Lvb P = 1 := by
            calc
              localMult E Lvb P = ordAt E Lvb P := localMult_eq_ordAt E Lvb P
              _ = ordAt E Lvb (xb, -yb) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lvb] using
                  ord_vertical_at_x₀_nonTwoTorsion E xb (-yb) hxb_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xb, -yb) = (xb, yb)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
      · have hLv_eval_ne : Lvb.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xb ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lvb, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lvb P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lvb hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have hprod_all_ge :
        localMult E a.poly P + localMult E b.poly P + localMult E line P
          ≤ localMult E q P := by
      have hab_nz : normPoly E (mulCoordRingElt E a.poly b.poly) ≠ 0 := by
        rw [normPoly_mul_eq]
        exact mul_ne_zero ha_nz hb_nz
      have hab_poly_nz :
          ¬ ((mulCoordRingElt E a.poly b.poly).a = 0 ∧
              (mulCoordRingElt E a.poly b.poly).b = 0) := by
        intro hzero
        apply hab_nz
        rw [normPoly_eq, hzero.1, hzero.2]
        ring
      have hab_ge :
          localMult E a.poly P + localMult E b.poly P
            ≤ localMult E (mulCoordRingElt E a.poly b.poly) P := by
        exact localMult_mulCoordRingElt_ge_add_when_rootMult_le_two
          E a.poly b.poly P hPon ha_poly_nz hb_poly_nz
          (h_root_le P hPon).1 (h_root_le P hPon).2
      have hline_ab_ge :
          localMult E line P + localMult E (mulCoordRingElt E a.poly b.poly) P
            ≤ localMult E q P := by
        have hmul := localMult_mulCoordRingElt_ge_add_general
          E line (mulCoordRingElt E a.poly b.poly) P
          hPon hline_poly_nz hab_poly_nz (Or.inr (hline_root_le P.1))
        have hq_assoc :
            mulCoordRingElt E line (mulCoordRingElt E a.poly b.poly) = q := by
          rw [hq_def]
          exact (mulCoordRingElt_assoc E line a.poly b.poly).symm
        simpa [hq_assoc] using hmul
      omega
    have hmarkers_plus_vertical_le :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
            + localMult E Lvb P + localMult E Lva P
          ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P := by
      omega
    have hq_local_eq_raw :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lva P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) h_div1_poly_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lva) P :=
              congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lva P := by
              simpa [Lva] using h
        _ = localMult E (q.divLin xa) P + localMult E Lva P := by
              rw [← localMult_eq_ordAt E (q.divLin xa) P,
                ← localMult_eq_ordAt E Lva P]
    have hdiv1_local_eq :
        localMult E (q.divLin xa) P =
          localMult E ((q.divLin xa).divLin xb) P + localMult E Lvb P := by
      have h := ordAt_mul_vertical_add E ((q.divLin xa).divLin xb)
        h_div2_poly_nz xb hPon
      calc
        localMult E (q.divLin xa) P = ordAt E (q.divLin xa) P :=
          localMult_eq_ordAt E (q.divLin xa) P
        _ = ordAt E (mulCoordRingElt E ((q.divLin xa).divLin xb) Lvb) P :=
              congrArg (fun D => ordAt E D P) hdiv1_recomp
        _ = ordAt E ((q.divLin xa).divLin xb) P + ordAt E Lvb P := by
              simpa [Lvb] using h
        _ = localMult E ((q.divLin xa).divLin xb) P + localMult E Lvb P := by
              rw [← localMult_eq_ordAt E ((q.divLin xa).divLin xb) P,
                ← localMult_eq_ordAt E Lvb P]
    have hq_local_eq :
        localMult E q P =
          localMult E ((q.divLin xa).divLin xb) P
            + localMult E Lvb P + localMult E Lva P := by
      rw [hq_local_eq_raw, hdiv1_local_eq]
    have htarget_base_le_after :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E ((q.divLin xa).divLin xb) P := by
      have h :
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lvb P + localMult E Lva P
            ≤ localMult E ((q.divLin xa).divLin xb) P
                + localMult E Lvb P + localMult E Lva P := by
        calc
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lvb P + localMult E Lva P
              ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P :=
                hmarkers_plus_vertical_le
          _ ≤ localMult E q P := hprod_all_ge
          _ = localMult E ((q.divLin xa).divLin xb) P
                + localMult E Lvb P + localMult E Lva P := hq_local_eq
      omega
    calc
      target E (xs ++ ys) (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point P
          = xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0) := by
            simp [target, h_combined_neg, List.count_append, eq_comm]
      _ ≤ localMult E ((q.divLin xa).divLin xb) P := htarget_base_le_after
      _ = localMult E (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).poly P := by
            simp [EagenAccum.combine_distinct, hq_def, hline_def]
  · show (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_ne :
        (EagenAccum.combine_distinct E a b xa ya xb yb h_xx).point
          ≠ (0 : ECPoint E) := by
      show ECPoint.affine E Qx (-Qy) ≠ (0 : ECPoint E)
      rw [ECPoint.affine_of_nonsingular E hns_Qneg]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns_Qneg
    rw [if_neg h_combined_ne]
    have h_X_sub_a_pow_ne : ((X - C xa) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_X_sub_b_pow_ne : ((X - C xb) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_natDeg1 : (normPoly E (q.divLin xa)).natDegree
        = (normPoly E q).natDegree - 2 := by
      have hh : (normPoly E q).natDegree
          = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E (q.divLin xa)).natDegree := by
        rw [h_factor1, Polynomial.natDegree_mul h_X_sub_a_pow_ne h_div1_nz]
      have hp : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_natDeg2 : (normPoly E ((q.divLin xa).divLin xb)).natDegree
        = (normPoly E (q.divLin xa)).natDegree - 2 := by
      have hh : (normPoly E (q.divLin xa)).natDegree
          = ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E ((q.divLin xa).divLin xb)).natDegree := by
        rw [h_factor2, Polynomial.natDegree_mul h_X_sub_b_pow_ne h_div2_nz]
      have hp : ((X - C xb) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_line_deg : (normPoly E line).natDegree = 3 := by
      rw [hline_def]
      exact chordCoordRingElt_natDegree_normPoly_of_xx_ne E h_xx
    have hap : a.point ≠ (0 : ECPoint E) := by
      rw [ha_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xa ya :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxa_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have hbp : b.point ≠ (0 : ECPoint E) := by
      rw [hb_pt_eq]
      intro h
      have hns : E.toW.toAffine.Nonsingular xb yb :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xb yb).mpr (E.hOnCurve _ hxb_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_neg hap] at ha_deg
    rw [if_neg hbp] at hb_deg
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 5 := by
      rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
      rw [Polynomial.natDegree_mul (mul_ne_zero hline_nz ha_nz) hb_nz,
          Polynomial.natDegree_mul hline_nz ha_nz]
      rw [h_line_deg, ha_deg, hb_deg]
      omega
    rw [h_natDeg2, h_natDeg1, h_qnp, List.length_append]
    omega

/-- Tangent-smooth preservation, with the two tangent-specific arithmetic
hypotheses made explicit:

* the product has a double common `(X - C xa)` factor in both coordinate
  components, so the repeated `divLin xa` steps are clean;
* the tangent product has the expected pointwise local-multiplicity lower
  bound before the two vertical cancellations.

This is the non-2-torsion tangent analogue of
`landmarkInvStrong_combine_distinct_when_rootMult_le_one`, isolating the
remaining tangent multiplicity arithmetic. -/
theorem landmarkInvStrong_combine_tangent_smooth_of_dvd_sq_and_localMult
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya : ZMod E.q}
    (hxy_on : (xa, ya) ∈ E.points)
    (hxy_neg_on : (xa, -ya) ∈ E.points)
    (hy_ne : ya ≠ 0)
    (h_third_xa :
      ((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa ≠ xa)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xa ya)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_dvd_qa_sq :
      (X - C xa) ^ 2 ∣
        (mulCoordRingElt E
          (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
          b.poly).a)
    (h_dvd_qb_sq :
      (X - C xa) ^ 2 ∣
        (mulCoordRingElt E
          (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
          b.poly).b)
    (hprod_all_ge :
      ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
        localMult E a.poly P + localMult E b.poly P
          + localMult E (chordCoordRingElt E (xa, ya) (xa, ya)) P
        ≤ localMult E
            (mulCoordRingElt E
              (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
              b.poly) P) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne) := by
  classical
  set lam : ZMod E.q := (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹ with hlam_def
  set Qx : ZMod E.q := lam ^ 2 - 2 * xa with hQx_def
  set Qy : ZMod E.q := lam * Qx + (ya - lam * xa) with hQy_def
  set line := chordCoordRingElt E (xa, ya) (xa, ya) with hline_def
  set q := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly with hq_def
  let Lv : CoordRingElt E.q := { a := X - C xa, b := 0 }
  have hQx_ne_xa : Qx ≠ xa := by
    simpa [hQx_def, hlam_def] using h_third_xa
  have hxa_ne_Qx : xa ≠ Qx := fun h => hQx_ne_xa h.symm
  have hT : thirdPoint E (xa, ya) (xa, ya) = some (Qx, Qy) := by
    unfold thirdPoint
    rw [if_pos rfl, if_pos rfl, if_neg hy_ne]
  have hQ_on : (Qx, Qy) ∈ E.points :=
    third_point_on_curve E (xa, ya) (xa, ya) hxy_on hxy_on hT
  have hQ_neg_on : (Qx, -Qy) ∈ E.points := points_neg_y E hQ_on
  have hline_poly_nz : ¬ (line.a = 0 ∧ line.b = 0) := by
    rw [hline_def]
    exact chordCoordRingElt_ne_zero E (xa, ya) (xa, ya)
  have hline_nz : normPoly E line ≠ 0 := normPoly_ne_zero E line hline_poly_nz
  have ha_poly_nz : ¬ (a.poly.a = 0 ∧ a.poly.b = 0) := by
    intro hzero
    apply ha_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hb_poly_nz : ¬ (b.poly.a = 0 ∧ b.poly.b = 0) := by
    intro hzero
    apply hb_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_nz : normPoly E q ≠ 0 := by
    rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
    exact mul_ne_zero (mul_ne_zero hline_nz ha_nz) hb_nz
  have hq_poly_nz : ¬ (q.a = 0 ∧ q.b = 0) := by
    intro hzero
    apply hq_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have h_dvd_qa_sq' : (X - C xa) ^ 2 ∣ q.a := by
    simpa [hq_def, hline_def] using h_dvd_qa_sq
  have h_dvd_qb_sq' : (X - C xa) ^ 2 ∣ q.b := by
    simpa [hq_def, hline_def] using h_dvd_qb_sq
  have h_dvd_qa_xa : (X - C xa) ∣ q.a := by
    have hsq : (X - C xa) * (X - C xa) ∣ q.a := by
      simpa [pow_two] using h_dvd_qa_sq'
    exact dvd_trans (dvd_mul_right (X - C xa) (X - C xa)) hsq
  have h_dvd_qb_xa : (X - C xa) ∣ q.b := by
    have hsq : (X - C xa) * (X - C xa) ∣ q.b := by
      simpa [pow_two] using h_dvd_qb_sq'
    exact dvd_trans (dvd_mul_right (X - C xa) (X - C xa)) hsq
  have h_dvd_a_after : (X - C xa) ∣ (q.divLin xa).a := by
    rw [CoordRingElt.divLin_a]
    exact dvd_X_sub_C_divByMonic_of_sq_dvd E h_dvd_qa_sq'
  have h_dvd_b_after : (X - C xa) ∣ (q.divLin xa).b := by
    rw [CoordRingElt.divLin_b]
    exact dvd_X_sub_C_divByMonic_of_sq_dvd E h_dvd_qb_sq'
  have h_factor1 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E q xa h_dvd_qa_xa h_dvd_qb_xa
  have h_factor2 := normPoly_eq_X_sub_C_sq_mul_normPoly_divLin
    E (q.divLin xa) xa h_dvd_a_after h_dvd_b_after
  have h_div1_nz : normPoly E (q.divLin xa) ≠ 0 := by
    intro hzero
    apply hq_nz
    rw [h_factor1, hzero, mul_zero]
  have h_div1_poly_nz : ¬ ((q.divLin xa).a = 0 ∧ (q.divLin xa).b = 0) := by
    intro hzero
    apply h_div1_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have h_div2_nz : normPoly E ((q.divLin xa).divLin xa) ≠ 0 := by
    intro hzero
    apply h_div1_nz
    rw [h_factor2, hzero, mul_zero]
  have h_div2_poly_nz :
      ¬ (((q.divLin xa).divLin xa).a = 0 ∧
          ((q.divLin xa).divLin xa).b = 0) := by
    intro hzero
    apply h_div2_nz
    rw [normPoly_eq, hzero.1, hzero.2]
    ring
  have hq_recomp : q = mulCoordRingElt E (q.divLin xa) Lv := by
    simpa [Lv] using
      mulCoordRingElt_divLin_vertical_recompose E q xa h_dvd_qa_xa h_dvd_qb_xa
  have hdiv1_recomp :
      q.divLin xa = mulCoordRingElt E ((q.divLin xa).divLin xa) Lv := by
    simpa [Lv] using
      mulCoordRingElt_divLin_vertical_recompose E (q.divLin xa) xa
        h_dvd_a_after h_dvd_b_after
  have ha_neg : negCoords E a.point = some (xa, -ya) := by
    rw [ha_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hb_neg : negCoords E b.point = some (xa, -ya) := by
    rw [hb_pt_eq]
    have hns : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns]
    rfl
  have hns_Qneg : E.toW.toAffine.Nonsingular Qx (-Qy) :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Qx (-Qy)).mpr (E.hOnCurve _ hQ_neg_on))
  have h_combined_neg :
      negCoords E (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).point
        = some (Qx, Qy) := by
    show negCoords E (ECPoint.affine E Qx (-Qy)) = some (Qx, Qy)
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    show some (Qx, -(-Qy)) = some (Qx, Qy)
    rw [neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · show (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).point =
      sumOnE E (xs ++ ys)
    rw [sumOnE_append, ← LandmarkInvStrong.running_sum E ha,
      ← LandmarkInvStrong.running_sum E hb, ha_pt_eq, hb_pt_eq]
    have hns_a : E.toW.toAffine.Nonsingular xa ya :=
      E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
    rw [ECPoint.affine_of_nonsingular E hns_a]
    show ECPoint.affine E Qx (-Qy) = (.some hns_a + .some hns_a : ECPoint E)
    have hSum := thirdPoint_some_eq_neg_add (E := E) hxy_on hxy_on hT
    have hns_Q : E.toW.toAffine.Nonsingular Qx Qy :=
      E.equation_iff_nonsingular.mp ((E.equation_iff Qx Qy).mpr (E.hOnCurve _ hQ_on))
    have heq_a : ECPoint.affineOfMem E hxy_on = (.some hns_a : ECPoint E) := rfl
    rw [heq_a] at hSum
    change (.some hns_a + .some hns_a : ECPoint E) = -(.some hns_Q : ECPoint E) at hSum
    rw [ECPoint.affine_of_nonsingular E hns_Qneg]
    have h_neg_third : (.some hns_Qneg : ECPoint E) = -(.some hns_Q : ECPoint E) := by
      simp [WeierstrassCurve.Affine.Point.neg_some]
    rw [h_neg_third]
    exact hSum.symm
  · intro P hPon
    have ha_target_le := LandmarkInvStrong.target_le E ha P hPon
    have hb_target_le := LandmarkInvStrong.target_le E hb P hPon
    have ha_target_le' :
        xs.count P + (if P = (xa, -ya) then 1 else 0)
          ≤ localMult E a.poly P := by
      simpa [target, ha_neg, eq_comm] using ha_target_le
    have hb_target_le' :
        ys.count P + (if P = (xa, -ya) then 1 else 0)
          ≤ localMult E b.poly P := by
      simpa [target, hb_neg, eq_comm] using hb_target_le
    have hline_tangent_eq : localMult E line (xa, ya) = 2 := by
      calc
        localMult E line (xa, ya) = ordAt E line (xa, ya) :=
          localMult_eq_ordAt E line (xa, ya)
        _ = 2 := by
          rw [hline_def]
          exact chord_ordAt_eq_two_at_tangent E hxy_on hy_ne hxa_ne_Qx
    have hline_third_eq : localMult E line (Qx, Qy) = 1 := by
      calc
        localMult E line (Qx, Qy) = ordAt E line (Qx, Qy) :=
          localMult_eq_ordAt E line (Qx, Qy)
        _ = 1 := by
          rw [hline_def]
          simpa [hQx_def, hQy_def, hlam_def] using
            (chord_ordAt_eq_one_at_tangent_third (E := E)
              (P := (xa, ya)) hxy_on hy_ne hxa_ne_Qx)
    have hline_markers :
        (if P = (xa, ya) then 2 else 0)
          + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E line P := by
      by_cases hP0 : P = (xa, ya)
      · subst P
        have hnotQ : (xa, ya) ≠ (Qx, Qy) := by
          intro h
          exact hQx_ne_xa (congrArg Prod.fst h).symm
        rw [if_pos rfl, if_neg hnotQ, hline_tangent_eq]
      · by_cases hPQ : P = (Qx, Qy)
        · subst P
          have hQnotP : (Qx, Qy) ≠ (xa, ya) := by
            intro h
            exact hQx_ne_xa (congrArg Prod.fst h)
          rw [if_neg hQnotP, if_pos rfl, hline_third_eq]
        · rw [if_neg hP0, if_neg hPQ]
          omega
    have hLv_bound :
        localMult E Lv P
          ≤ (if P = (xa, ya) then 1 else 0)
            + (if P = (xa, -ya) then 1 else 0) := by
      by_cases hPx : P.1 = xa
      · have hP_eq_x : P = (xa, P.2) := by
          ext
          · exact hPx
          · rfl
        have hP_on_x : (xa, P.2) ∈ E.points := by
          rwa [← hP_eq_x]
        have hy_dich : ya = P.2 ∨ ya = -P.2 :=
          ECPoints_same_x_y_eq_or_neg E hxy_on hP_on_x
        rcases hy_dich with hy_eq | hy_eq_neg
        · have hP_eq : P = (xa, ya) := by
            ext
            · exact hPx
            · exact hy_eq.symm
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using ord_vertical_at_x₀_nonTwoTorsion E xa ya hxy_on hy_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, ya) = (xa, -ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
        · have hP_eq : P = (xa, -ya) := by
            ext
            · exact hPx
            · rw [hy_eq_neg, neg_neg]
          have hneg_ne : -ya ≠ 0 := by simpa using (neg_ne_zero.mpr hy_ne)
          have hLv_eq : localMult E Lv P = 1 := by
            calc
              localMult E Lv P = ordAt E Lv P := localMult_eq_ordAt E Lv P
              _ = ordAt E Lv (xa, -ya) := by rw [hP_eq]
              _ = 1 := by
                simpa [Lv] using
                  ord_vertical_at_x₀_nonTwoTorsion E xa (-ya) hxy_neg_on hneg_ne
          rw [hLv_eq, hP_eq, if_pos rfl]
          by_cases hsame : (xa, -ya) = (xa, ya)
          · rw [if_pos hsame]
            omega
          · rw [if_neg hsame]
      · have hLv_eval_ne : Lv.eval P.1 P.2 ≠ 0 := by
          have hsub : P.1 - xa ≠ 0 := sub_ne_zero.mpr hPx
          simpa [Lv, CoordRingElt.eval] using hsub
        have hLv_eq : localMult E Lv P = 0 :=
          localMult_eq_zero_of_eval_ne_zero E Lv hPon hLv_eval_ne
        rw [hLv_eq]
        omega
    have hmarkers_plus_vertical_le :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
            + localMult E Lv P + localMult E Lv P
          ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P := by
      have hpos_two :
          (if P = (xa, ya) then 2 else 0)
            = 2 * (if P = (xa, ya) then 1 else 0) := by
        by_cases hP0 : P = (xa, ya)
        · rw [if_pos hP0, if_pos hP0]
        · rw [if_neg hP0, if_neg hP0]
      have hLv_twice :
          localMult E Lv P + localMult E Lv P
            ≤ (if P = (xa, ya) then 2 else 0)
              + (if P = (xa, -ya) then 1 else 0)
              + (if P = (xa, -ya) then 1 else 0) := by
        omega
      omega
    have hprod_ge :
        localMult E a.poly P + localMult E b.poly P + localMult E line P
          ≤ localMult E q P := by
      simpa [hq_def, hline_def] using hprod_all_ge P hPon
    have hq_local_eq_raw :
        localMult E q P = localMult E (q.divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E (q.divLin xa) h_div1_poly_nz xa hPon
      calc
        localMult E q P = ordAt E q P := localMult_eq_ordAt E q P
        _ = ordAt E (mulCoordRingElt E (q.divLin xa) Lv) P :=
              congrArg (fun D => ordAt E D P) hq_recomp
        _ = ordAt E (q.divLin xa) P + ordAt E Lv P := by
              simpa [Lv] using h
        _ = localMult E (q.divLin xa) P + localMult E Lv P := by
              rw [← localMult_eq_ordAt E (q.divLin xa) P,
                ← localMult_eq_ordAt E Lv P]
    have hdiv1_local_eq :
        localMult E (q.divLin xa) P =
          localMult E ((q.divLin xa).divLin xa) P + localMult E Lv P := by
      have h := ordAt_mul_vertical_add E ((q.divLin xa).divLin xa)
        h_div2_poly_nz xa hPon
      calc
        localMult E (q.divLin xa) P = ordAt E (q.divLin xa) P :=
          localMult_eq_ordAt E (q.divLin xa) P
        _ = ordAt E (mulCoordRingElt E ((q.divLin xa).divLin xa) Lv) P :=
              congrArg (fun D => ordAt E D P) hdiv1_recomp
        _ = ordAt E ((q.divLin xa).divLin xa) P + ordAt E Lv P := by
              simpa [Lv] using h
        _ = localMult E ((q.divLin xa).divLin xa) P + localMult E Lv P := by
              rw [← localMult_eq_ordAt E ((q.divLin xa).divLin xa) P,
                ← localMult_eq_ordAt E Lv P]
    have hq_local_eq :
        localMult E q P =
          localMult E ((q.divLin xa).divLin xa) P
            + localMult E Lv P + localMult E Lv P := by
      rw [hq_local_eq_raw, hdiv1_local_eq]
    have htarget_base_le_after :
        xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
          ≤ localMult E ((q.divLin xa).divLin xa) P := by
      have h :
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lv P + localMult E Lv P
            ≤ localMult E ((q.divLin xa).divLin xa) P
                + localMult E Lv P + localMult E Lv P := by
        calc
          xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0)
              + localMult E Lv P + localMult E Lv P
              ≤ localMult E a.poly P + localMult E b.poly P + localMult E line P :=
                hmarkers_plus_vertical_le
          _ ≤ localMult E q P := hprod_ge
          _ = localMult E ((q.divLin xa).divLin xa) P
                + localMult E Lv P + localMult E Lv P := hq_local_eq
      omega
    calc
      target E (xs ++ ys) (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).point P
          = xs.count P + ys.count P + (if P = (Qx, Qy) then 1 else 0) := by
            simp [target, h_combined_neg, List.count_append, eq_comm]
      _ ≤ localMult E ((q.divLin xa).divLin xa) P := htarget_base_le_after
      _ = localMult E (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).poly P := by
            simp [EagenAccum.combine_tangent_smooth, hq_def, hline_def]
  · show (normPoly E ((q.divLin xa).divLin xa)).natDegree
        = (xs ++ ys).length
          + (if (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).point
                = (0 : ECPoint E) then 0 else 1)
    have h_combined_ne :
        (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne).point
          ≠ (0 : ECPoint E) := by
      show ECPoint.affine E Qx (-Qy) ≠ (0 : ECPoint E)
      rw [ECPoint.affine_of_nonsingular E hns_Qneg]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns_Qneg
    rw [if_neg h_combined_ne]
    have h_X_sub_pow_ne : ((X - C xa) ^ 2 : (ZMod E.q)[X]) ≠ 0 :=
      pow_ne_zero _ (X_sub_C_ne_zero _)
    have h_natDeg1 : (normPoly E (q.divLin xa)).natDegree
        = (normPoly E q).natDegree - 2 := by
      have hh : (normPoly E q).natDegree
          = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E (q.divLin xa)).natDegree := by
        rw [h_factor1, Polynomial.natDegree_mul h_X_sub_pow_ne h_div1_nz]
      have hp : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_natDeg2 : (normPoly E ((q.divLin xa).divLin xa)).natDegree
        = (normPoly E (q.divLin xa)).natDegree - 2 := by
      have hh : (normPoly E (q.divLin xa)).natDegree
          = ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree
            + (normPoly E ((q.divLin xa).divLin xa)).natDegree := by
        rw [h_factor2, Polynomial.natDegree_mul h_X_sub_pow_ne h_div2_nz]
      have hp : ((X - C xa) ^ 2 : (ZMod E.q)[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    have h_line_deg : (normPoly E line).natDegree = 3 := by
      rw [hline_def]
      unfold chordCoordRingElt
      rw [dif_pos rfl, dif_pos rfl, if_neg hy_ne]
      exact natDegree_normPoly_chordCoordRingElt_nonvertical E _ _
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
      have hns : E.toW.toAffine.Nonsingular xa ya :=
        E.equation_iff_nonsingular.mp ((E.equation_iff xa ya).mpr (E.hOnCurve _ hxy_on))
      rw [ECPoint.affine_of_nonsingular E hns] at h
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns h
    have ha_deg := LandmarkInvStrong.natDegree E ha
    have hb_deg := LandmarkInvStrong.natDegree E hb
    rw [if_neg hap] at ha_deg
    rw [if_neg hbp] at hb_deg
    have h_qnp : (normPoly E q).natDegree = xs.length + ys.length + 5 := by
      rw [hq_def, normPoly_mul_eq, normPoly_mul_eq]
      rw [Polynomial.natDegree_mul (mul_ne_zero hline_nz ha_nz) hb_nz,
          Polynomial.natDegree_mul hline_nz ha_nz]
      rw [h_line_deg, ha_deg, hb_deg]
      omega
    rw [h_natDeg2, h_natDeg1, h_qnp, List.length_append]
    omega

theorem landmarkInvStrong_combine_tangent_smooth_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    {xa ya : ZMod E.q}
    (hxy_on : (xa, ya) ∈ E.points)
    (hxy_neg_on : (xa, -ya) ∈ E.points)
    (hy_ne : ya ≠ 0)
    (h_third_xa :
      ((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa ≠ xa)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_pt_eq : a.point = ECPoint.affine E xa ya)
    (hb_pt_eq : b.point = ECPoint.affine E xa ya)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2)
    (h_dvd_qa_sq :
      (X - C xa) ^ 2 ∣
        (mulCoordRingElt E
          (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
          b.poly).a)
    (h_dvd_qb_sq :
      (X - C xa) ^ 2 ∣
        (mulCoordRingElt E
          (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
          b.poly).b)
    (hprod_all_ge :
      ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
        localMult E a.poly P + localMult E b.poly P
          + localMult E (chordCoordRingElt E (xa, ya) (xa, ya)) P
        ≤ localMult E
            (mulCoordRingElt E
              (mulCoordRingElt E (chordCoordRingElt E (xa, ya) (xa, ya)) a.poly)
              b.poly) P) :
    LandmarkInvStrong E (xs ++ ys)
      (EagenAccum.combine_tangent_smooth E a b xa ya hy_ne) := by
  have _h_root_le := h_root_le
  exact landmarkInvStrong_combine_tangent_smooth_of_dvd_sq_and_localMult
    E hxy_on hxy_neg_on hy_ne h_third_xa ha hb ha_pt_eq hb_pt_eq
    ha_nz hb_nz h_dvd_qa_sq h_dvd_qb_sq hprod_all_ge

/-- Extra affine-affine hypotheses needed by the strong `combine`
dispatcher beyond the point-shape case split.

The distinct chord branch needs non-2-torsion endpoints and the third
intersection's x-coordinate to differ from both endpoints. The smooth
tangent branch currently depends on the explicit double-divisibility and
local-multiplicity product hypotheses isolated by
`landmarkInvStrong_combine_tangent_smooth_of_dvd_sq_and_localMult`. -/
def LandmarkInvStrongCombineAffineExtras
    (a b : EagenAccum E) : Prop :=
  ∀ ⦃xa ya xb yb : ZMod E.q⦄,
    a.point = ECPoint.affine E xa ya →
    b.point = ECPoint.affine E xb yb →
      (xa ≠ xb →
        ya ≠ 0 ∧ yb ≠ 0 ∧
        (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xa ∧
        (slopeOf xa ya xb yb ^ 2 - xa - xb) ≠ xb) ∧
      (xa = xb → ya ≠ -yb → ya ≠ 0 →
        let line := chordCoordRingElt E (xa, ya) (xa, ya)
        let q := mulCoordRingElt E (mulCoordRingElt E line a.poly) b.poly
        ((3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹) ^ 2 - 2 * xa ≠ xa ∧
        (X - C xa) ^ 2 ∣ q.a ∧
        (X - C xa) ^ 2 ∣ q.b ∧
        ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
          localMult E a.poly P + localMult E b.poly P + localMult E line P
            ≤ localMult E q P)

/-- Unified dispatcher for the case-specific strong combine lemmas. -/
theorem landmarkInvStrong_combine_when_rootMult_le_one
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_a_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E a.point = some Q → Q ∈ E.points)
    (h_neg_b_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E b.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 1
      ∨ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 1)
    (h_aff_aff_extras : LandmarkInvStrongCombineAffineExtras E a b) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine E a b) := by
  classical
  match hpa : a.point, hpb : b.point with
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.zero =>
      have hcase := landmarkInvStrong_combine_oo_when_rootMult_le_one
        E hxs_on hys_on ha hb hpa hpb ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_oo E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.zero,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) hns_b =>
      have hb_ne : b.point ≠ (0 : ECPoint E) := by
        rw [hpb]
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns_b
      have hcase := landmarkInvStrong_combine_ol_when_rootMult_le_one
        E hxs_on hys_on h_neg_b_on ha hb hpa hb_ne ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_ol E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) hns_a,
    WeierstrassCurve.Affine.Point.zero =>
      have ha_ne : a.point ≠ (0 : ECPoint E) := by
        rw [hpa]
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns_a
      have hcase := landmarkInvStrong_combine_or_when_rootMult_le_one
        E hxs_on hys_on h_neg_a_on ha hb ha_ne hpb ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_or E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) hns_a,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) hns_b =>
      have hxa_on : (xa, ya) ∈ E.points :=
        E.hComplete xa ya
          ((E.equation_iff xa ya).mp ((E.equation_iff_nonsingular).mpr hns_a))
      have hxb_on : (xb, yb) ∈ E.points :=
        E.hComplete xb yb
          ((E.equation_iff xb yb).mp ((E.equation_iff_nonsingular).mpr hns_b))
      have ha_pt_eq : a.point = ECPoint.affine E xa ya := by
        rw [hpa, ECPoint.affine_of_nonsingular E hns_a]
      have hb_pt_eq : b.point = ECPoint.affine E xb yb := by
        rw [hpb, ECPoint.affine_of_nonsingular E hns_b]
      by_cases h_xx : xa ≠ xb
      · obtain ⟨hya_ne, hyb_ne, h_third_xa, h_third_xb⟩ :=
          (h_aff_aff_extras ha_pt_eq hb_pt_eq).1 h_xx
        have hcase := landmarkInvStrong_combine_distinct_when_rootMult_le_one
          E h_xx hxs_on hys_on hxa_on hxb_on hya_ne hyb_ne
          h_third_xa h_third_xb ha hb ha_pt_eq hb_pt_eq
          ha_nz hb_nz h_root_le
        have hcombine :
            EagenAccum.combine E a b =
              EagenAccum.combine_distinct E a b xa ya xb yb h_xx := by
          unfold EagenAccum.combine
          rw [hpa, hpb]
          simp [h_xx]
        rw [hcombine]
        exact hcase
      · have hxeq : xa = xb := by exact not_not.mp h_xx
        by_cases h_yy : ya = -yb
        · by_cases hya_zero : ya = 0
          · have hyb_zero : yb = 0 := by
              have hneg_yb_zero : -yb = 0 := by
                simpa [hya_zero] using h_yy.symm
              simpa using (neg_eq_zero.mp hneg_yb_zero)
            have hxy_on : (xa, (0 : ZMod E.q)) ∈ E.points := by
              simpa [hya_zero] using hxa_on
            have ha_torsion_pt :
                a.point = ECPoint.affine E xa (0 : ZMod E.q) := by
              simpa [hya_zero] using ha_pt_eq
            have hb_torsion_pt :
                b.point = ECPoint.affine E xa (0 : ZMod E.q) := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa (0 : ZMod E.q) := by
                  rw [← hxeq, hyb_zero]
            have hcase := landmarkInvStrong_combine_tangent_torsion_when_rootMult_le_one
              E hxs_on hys_on hxy_on ha hb ha_torsion_pt hb_torsion_pt
              ha_nz hb_nz h_root_le
            have hcombine :
                EagenAccum.combine E a b = EagenAccum.combine_vertical E a b xa := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy]
            rw [hcombine]
            simpa [EagenAccum.combine_tangent_torsion] using hcase
          · have hyb_eq_neg : yb = -ya := by
              have hneg := congrArg Neg.neg h_yy
              simpa [neg_neg] using hneg.symm
            have hxy_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
            have hb_vertical_pt : b.point = ECPoint.affine E xa (-ya) := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa (-ya) := by
                  rw [← hxeq, hyb_eq_neg]
            have hcase := landmarkInvStrong_combine_vertical_when_rootMult_le_one
              E hxs_on hys_on hxa_on hxy_neg_on hya_zero ha hb
              ha_pt_eq hb_vertical_pt ha_nz hb_nz h_root_le
            have hcombine :
                EagenAccum.combine E a b = EagenAccum.combine_vertical E a b xa := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy]
            rw [hcombine]
            exact hcase
        · by_cases hya_zero : ya = 0
          · have hyb_zero : yb = 0 := by
              have hy_dich : ya = yb ∨ ya = -yb := by
                have hxb_as_xa : (xa, yb) ∈ E.points := by
                  simpa [hxeq] using hxb_on
                exact ECPoints_same_x_y_eq_or_neg E hxa_on hxb_as_xa
              rcases hy_dich with hy_eq | hy_neg
              · simp [← hy_eq, hya_zero]
              · exact False.elim (h_yy hy_neg)
            exact False.elim (h_yy (by simp [hya_zero, hyb_zero]))
          · have hxb_as_xa : (xa, yb) ∈ E.points := by
              simpa [hxeq] using hxb_on
            have hy_eq : ya = yb := by
              rcases ECPoints_same_x_y_eq_or_neg E hxa_on hxb_as_xa with hy_same | hy_neg
              · exact hy_same
              · exact False.elim (h_yy hy_neg)
            have hb_smooth_pt : b.point = ECPoint.affine E xa ya := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa ya := by
                  rw [← hxeq, ← hy_eq]
            have hxy_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
            obtain ⟨h_third_xa, h_dvd_qa_sq, h_dvd_qb_sq, hprod_all_ge⟩ :=
              (h_aff_aff_extras ha_pt_eq hb_pt_eq).2 hxeq h_yy hya_zero
            have hcase :=
              landmarkInvStrong_combine_tangent_smooth_of_dvd_sq_and_localMult
                E hxa_on hxy_neg_on hya_zero h_third_xa ha hb
                ha_pt_eq hb_smooth_pt ha_nz hb_nz
                h_dvd_qa_sq h_dvd_qb_sq hprod_all_ge
            have hcombine :
                EagenAccum.combine E a b =
                  EagenAccum.combine_tangent_smooth E a b xa ya hya_zero := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy, hya_zero]
            rw [hcombine]
            exact hcase

theorem landmarkInvStrong_combine_when_rootMult_le_two
    {xs ys : List (ZMod E.q × ZMod E.q)}
    {a b : EagenAccum E}
    (hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (hys_on : ∀ P ∈ ys, P ∈ E.points)
    (h_neg_a_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E a.point = some Q → Q ∈ E.points)
    (h_neg_b_on : ∀ Q : ZMod E.q × ZMod E.q,
      negCoords E b.point = some Q → Q ∈ E.points)
    (ha : LandmarkInvStrong E xs a) (hb : LandmarkInvStrong E ys b)
    (ha_nz : normPoly E a.poly ≠ 0) (hb_nz : normPoly E b.poly ≠ 0)
    (h_root_le : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2
      ∧ Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2)
    (h_aff_aff_extras : LandmarkInvStrongCombineAffineExtras E a b) :
    LandmarkInvStrong E (xs ++ ys) (EagenAccum.combine E a b) := by
  classical
  match hpa : a.point, hpb : b.point with
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.zero =>
      have hcase := landmarkInvStrong_combine_oo_when_rootMult_le_two
        E hxs_on hys_on ha hb hpa hpb ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_oo E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.zero,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) hns_b =>
      have hb_ne : b.point ≠ (0 : ECPoint E) := by
        rw [hpb]
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns_b
      have hcase := landmarkInvStrong_combine_ol_when_rootMult_le_two
        E hxs_on hys_on h_neg_b_on ha hb hpa hb_ne ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_ol E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) hns_a,
    WeierstrassCurve.Affine.Point.zero =>
      have ha_ne : a.point ≠ (0 : ECPoint E) := by
        rw [hpa]
        exact WeierstrassCurve.Affine.Point.some_ne_zero hns_a
      have hcase := landmarkInvStrong_combine_or_when_rootMult_le_two
        E hxs_on hys_on h_neg_a_on ha hb ha_ne hpb ha_nz hb_nz h_root_le
      have hcombine :
          EagenAccum.combine E a b = EagenAccum.combine_or E a b := by
        unfold EagenAccum.combine
        rw [hpa, hpb]
      rw [hcombine]
      exact hcase
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) hns_a,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) hns_b =>
      have hxa_on : (xa, ya) ∈ E.points :=
        E.hComplete xa ya
          ((E.equation_iff xa ya).mp ((E.equation_iff_nonsingular).mpr hns_a))
      have hxb_on : (xb, yb) ∈ E.points :=
        E.hComplete xb yb
          ((E.equation_iff xb yb).mp ((E.equation_iff_nonsingular).mpr hns_b))
      have ha_pt_eq : a.point = ECPoint.affine E xa ya := by
        rw [hpa, ECPoint.affine_of_nonsingular E hns_a]
      have hb_pt_eq : b.point = ECPoint.affine E xb yb := by
        rw [hpb, ECPoint.affine_of_nonsingular E hns_b]
      by_cases h_xx : xa ≠ xb
      · obtain ⟨hya_ne, hyb_ne, h_third_xa, h_third_xb⟩ :=
          (h_aff_aff_extras ha_pt_eq hb_pt_eq).1 h_xx
        have hcase := landmarkInvStrong_combine_distinct_when_rootMult_le_two
          E h_xx hxs_on hys_on hxa_on hxb_on hya_ne hyb_ne
          h_third_xa h_third_xb ha hb ha_pt_eq hb_pt_eq
          ha_nz hb_nz h_root_le
        have hcombine :
            EagenAccum.combine E a b =
              EagenAccum.combine_distinct E a b xa ya xb yb h_xx := by
          unfold EagenAccum.combine
          rw [hpa, hpb]
          simp [h_xx]
        rw [hcombine]
        exact hcase
      · have hxeq : xa = xb := by exact not_not.mp h_xx
        by_cases h_yy : ya = -yb
        · by_cases hya_zero : ya = 0
          · have hyb_zero : yb = 0 := by
              have hneg_yb_zero : -yb = 0 := by
                simpa [hya_zero] using h_yy.symm
              simpa using (neg_eq_zero.mp hneg_yb_zero)
            have hxy_on : (xa, (0 : ZMod E.q)) ∈ E.points := by
              simpa [hya_zero] using hxa_on
            have ha_torsion_pt :
                a.point = ECPoint.affine E xa (0 : ZMod E.q) := by
              simpa [hya_zero] using ha_pt_eq
            have hb_torsion_pt :
                b.point = ECPoint.affine E xa (0 : ZMod E.q) := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa (0 : ZMod E.q) := by
                  rw [← hxeq, hyb_zero]
            have hcase := landmarkInvStrong_combine_tangent_torsion_when_rootMult_le_two
              E hxs_on hys_on hxy_on ha hb ha_torsion_pt hb_torsion_pt
              ha_nz hb_nz h_root_le
            have hcombine :
                EagenAccum.combine E a b = EagenAccum.combine_vertical E a b xa := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy]
            rw [hcombine]
            simpa [EagenAccum.combine_tangent_torsion] using hcase
          · have hyb_eq_neg : yb = -ya := by
              have hneg := congrArg Neg.neg h_yy
              simpa [neg_neg] using hneg.symm
            have hxy_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
            have hb_vertical_pt : b.point = ECPoint.affine E xa (-ya) := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa (-ya) := by
                  rw [← hxeq, hyb_eq_neg]
            have hcase := landmarkInvStrong_combine_vertical_when_rootMult_le_two
              E hxs_on hys_on hxa_on hxy_neg_on hya_zero ha hb
              ha_pt_eq hb_vertical_pt ha_nz hb_nz h_root_le
            have hcombine :
                EagenAccum.combine E a b = EagenAccum.combine_vertical E a b xa := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy]
            rw [hcombine]
            exact hcase
        · by_cases hya_zero : ya = 0
          · have hyb_zero : yb = 0 := by
              have hy_dich : ya = yb ∨ ya = -yb := by
                have hxb_as_xa : (xa, yb) ∈ E.points := by
                  simpa [hxeq] using hxb_on
                exact ECPoints_same_x_y_eq_or_neg E hxa_on hxb_as_xa
              rcases hy_dich with hy_eq | hy_neg
              · simp [← hy_eq, hya_zero]
              · exact False.elim (h_yy hy_neg)
            exact False.elim (h_yy (by simp [hya_zero, hyb_zero]))
          · have hxb_as_xa : (xa, yb) ∈ E.points := by
              simpa [hxeq] using hxb_on
            have hy_eq : ya = yb := by
              rcases ECPoints_same_x_y_eq_or_neg E hxa_on hxb_as_xa with hy_same | hy_neg
              · exact hy_same
              · exact False.elim (h_yy hy_neg)
            have hb_smooth_pt : b.point = ECPoint.affine E xa ya := by
              calc
                b.point = ECPoint.affine E xb yb := hb_pt_eq
                _ = ECPoint.affine E xa ya := by
                  rw [← hxeq, ← hy_eq]
            have hxy_neg_on : (xa, -ya) ∈ E.points := points_neg_y E hxa_on
            obtain ⟨h_third_xa, h_dvd_qa_sq, h_dvd_qb_sq, hprod_all_ge⟩ :=
              (h_aff_aff_extras ha_pt_eq hb_pt_eq).2 hxeq h_yy hya_zero
            have hcase :=
              landmarkInvStrong_combine_tangent_smooth_when_rootMult_le_two
                E hxa_on hxy_neg_on hya_zero h_third_xa ha hb
                ha_pt_eq hb_smooth_pt ha_nz hb_nz
                h_root_le
                h_dvd_qa_sq h_dvd_qb_sq hprod_all_ge
            have hcombine :
                EagenAccum.combine E a b =
                  EagenAccum.combine_tangent_smooth E a b xa ya hya_zero := by
              unfold EagenAccum.combine
              rw [hpa, hpb]
              simp [hxeq, h_yy, hya_zero]
            rw [hcombine]
            exact hcase

/-! ## Root multiplicity bound after combine

The unconditional statement "the combined norm has root multiplicity at
most two on every rational fiber" needs a support/no-collision invariant
stronger than `(xs ++ ys).Nodup`: residues carried by one accumulator can
collide with a full vertical fiber already absorbed by the other
accumulator.  The lemma below isolates the exact final condition needed
by the per-fiber norm identity: the sum of sheet-level local
multiplicities on each combined fiber is at most two. -/

theorem rootMultiplicity_normPoly_eq_fiber_target_sum
    (D : CoordRingElt E.q) (xs : List (ZMod E.q × ZMod E.q))
    (R : ECPoint E)
    (_h : LandmarkInvStrong E xs (EagenAccum.mk R D))
    (_hSplit : splitsOnE E D)
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    Polynomial.rootMultiplicity P.1 (normPoly E D)
      = ∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q := by
  classical
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · have hsum :=
      sum_ordAt_fst_eq_eq_rootMult E D hD P.1 ⟨P, hP, rfl⟩
    have hlocal_ord :
        (∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q)
          = ∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), ordAt E D Q := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact localMult_eq_ordAt E D Q
    rw [← hsum, hlocal_ord]
  · push_neg at hD
    have hnorm_zero : normPoly E D = 0 := by
      rw [normPoly_eq, hD.1, hD.2]
      ring
    have hlocal_zero :
        ∀ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q = 0 := by
      intro Q _hQ
      exact localMult_eq_zero_of_offE_or_zero E D Q (by simp [hD])
    rw [hnorm_zero, Polynomial.rootMultiplicity_zero, Finset.sum_eq_zero hlocal_zero]

theorem rootMultiplicity_normPoly_le_two_of_fiber_localMult_le_two
    (D : CoordRingElt E.q)
    (h_fiber_localMult_le_two :
      ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
        (∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q) ≤ 2) :
    ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E D) ≤ 2 := by
  classical
  intro P hPon
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · have hsum :=
      sum_ordAt_fst_eq_eq_rootMult E D hD P.1 ⟨P, hPon, rfl⟩
    have hlocal_ord :
        (∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q)
          = ∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), ordAt E D Q := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact localMult_eq_ordAt E D Q
    calc
      Polynomial.rootMultiplicity P.1 (normPoly E D)
          = ∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), ordAt E D Q := hsum.symm
      _ = ∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1), localMult E D Q :=
            hlocal_ord.symm
      _ ≤ 2 := h_fiber_localMult_le_two P hPon
  · push_neg at hD
    have hnorm_zero : normPoly E D = 0 := by
      rw [normPoly_eq, hD.1, hD.2]
      ring
    rw [hnorm_zero, Polynomial.rootMultiplicity_zero]
    norm_num

/-- Partial form of root-multiplicity preservation under `combine`.

The extra hypothesis `h_fiber_localMult_le_two` is the explicit
no-overfull-final-fiber condition.  It is intentionally stated on the
combined polynomial, so each combine branch can discharge it with its
own chord/tangent/vertical multiplicity arithmetic. -/
theorem rootMult_le_two_preserved_under_combine
    (a b : EagenAccum E)
    (xs ys : List (ZMod E.q × ZMod E.q))
    (_hxs_nodup : (xs ++ ys).Nodup)
    (_hxs_on : ∀ P ∈ xs, P ∈ E.points)
    (_hys_on : ∀ P ∈ ys, P ∈ E.points)
    (_ha : LandmarkInvStrong E xs a) (_hb : LandmarkInvStrong E ys b)
    (_h_mult_a : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E a.poly) ≤ 2)
    (_h_mult_b : ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1 (normPoly E b.poly) ≤ 2)
    (h_fiber_localMult_le_two :
      ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
        (∑ Q ∈ E.points.filter (fun Q => Q.1 = P.1),
          localMult E (EagenAccum.combine E a b).poly Q) ≤ 2) :
    ∀ P : ZMod E.q × ZMod E.q, P ∈ E.points →
      Polynomial.rootMultiplicity P.1
        (normPoly E (EagenAccum.combine E a b).poly) ≤ 2 := by
  exact rootMultiplicity_normPoly_le_two_of_fiber_localMult_le_two
    E (EagenAccum.combine E a b).poly h_fiber_localMult_le_two

/-! ## Helper: nonzero from positive natDegree -/
/-- `eagenBuild` of a sum-zero pair is the vertical line at `P.1`. -/
theorem eagenBuild_pair_vertical
    (P Q : ZMod E.q × ZMod E.q)
    (hxx : P.1 = Q.1)
    (hyy : P.2 = -Q.2 ∨ (P = Q ∧ P.2 = 0)) :
    eagenBuild E [P, Q] = { a := X - C P.1, b := 0 } := by
  -- Reduce eagenBuild [P, Q].
  have h_third : thirdPoint E P Q = none :=
    thirdPoint_eq_none_of_sum_zero_data E P Q hxx hyy
  have h_chord : chordCoordRingElt E P Q = { a := X - C P.1, b := 0 } :=
    chordCoordRingElt_eq_vertical_of_sum_zero E P Q hxx hyy
  -- level0 [P, Q] = [levelInitPair P Q] = [{ point := 0, poly := chord }].
  show (match iterate E [P, Q].length (level0 E [P, Q]) with
        | [a] => a.poly
        | _ => { a := 1, b := 0 }) = { a := X - C P.1, b := 0 }
  have h_level0 : level0 E [P, Q] =
      [{ point := (0 : ECPoint E), poly := chordCoordRingElt E P Q }] := by
    show (levelInitPair E P Q :: level0 E []) = _
    rw [show level0 E ([] : List (ZMod E.q × ZMod E.q)) = [] from rfl]
    show [levelInitPair E P Q] = _
    congr 1
    show levelInitPair E P Q = _
    unfold levelInitPair
    rw [h_third]
  rw [h_level0]
  -- iterate 2 [single] = [single] since length 1 ≤ 1.
  show (match iterate E 2 [{ point := (0 : ECPoint E),
                              poly := chordCoordRingElt E P Q }] with
        | [a] => a.poly
        | _ => { a := 1, b := 0 }) = _
  have h_iter : iterate E 2 [{ point := (0 : ECPoint E),
                                 poly := chordCoordRingElt E P Q }]
      = [{ point := (0 : ECPoint E), poly := chordCoordRingElt E P Q }] := by
    show iterate E (1 + 1) _ = _
    simp [iterate]
  rw [h_iter]
  -- Match: [a] returns a.poly = chordCoordRingElt P Q.
  rw [h_chord]

/-- Length-2 landmark: input `[P, Q]` with `P + Q = 0` on `E` produces
    `D = (X - C P.1, 0)`, which:
      - is nonzero,
      - vanishes at `P` and `Q`,
      - has `(normPoly D).natDegree = 2`. -/
theorem eagenBuild_landmark_length2
    {P Q : ZMod E.q × ZMod E.q}
    (hxx : P.1 = Q.1)
    (hyy : P.2 = -Q.2 ∨ (P = Q ∧ P.2 = 0)) :
    let D := eagenBuild E [P, Q]
    ¬ (D.a = 0 ∧ D.b = 0) ∧
    D.eval P.1 P.2 = 0 ∧ D.eval Q.1 Q.2 = 0 ∧
    (normPoly E D).natDegree = 2 := by
  rw [eagenBuild_pair_vertical E P Q hxx hyy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (X - C P.1, 0) ≠ 0: a = X - C P.1, which is nonzero (degree 1).
    intro ⟨ha, _⟩
    have h_nz : (X - C P.1 : (ZMod E.q)[X]) ≠ 0 := X_sub_C_ne_zero _
    exact h_nz ha
  · -- eval at P: (X - C P.1).eval P.1 - 0.eval P.1 · P.2 = (P.1 - P.1) - 0 = 0.
    show (X - C P.1).eval P.1 - (0 : (ZMod E.q)[X]).eval P.1 * P.2 = 0
    simp
  · -- eval at Q: (Q.1 - P.1) - 0 = 0 since Q.1 = P.1.
    show (X - C P.1).eval Q.1 - (0 : (ZMod E.q)[X]).eval Q.1 * Q.2 = 0
    simp [hxx]
  · -- (normPoly (X - C P.1, 0)).natDegree = ((X - C P.1)² - 0² · curveX).natDegree = 2.
    rw [normPoly_eq]
    show ((X - C P.1) ^ 2 - 0 ^ 2 * curveX E).natDegree = 2
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]

/-! ## level_step preservation (conditional on per-pair combine)

If we know `LandmarkInv` is preserved under `combine` for all
adjacent pairs in the input, then `LandmarkInvList` propagates
through one application of `level_step`.

The `pairUp` function on a list of sub-lists: pair adjacent and
append, leaving any trailing odd-length element forwarded. -/

def pairUp {α : Type*} : List (List α) → List (List α)
  | [] => []
  | [xs] => [xs]
  | xs :: ys :: rest => (xs ++ ys) :: pairUp rest

theorem landmarkInvList_preservation_under_level_step
    (xss : List (List (ZMod E.q × ZMod E.q)))
    (accs : List (EagenAccum E))
    (h : LandmarkInvList E xss accs)
    (h_combine : ∀ (xs ys : List (ZMod E.q × ZMod E.q))
        (a b : EagenAccum E),
      LandmarkInv E xs a → LandmarkInv E ys b →
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)) :
    LandmarkInvList E (pairUp xss) (level_step E accs) := by
  classical
  match xss, accs, h with
  | [], [], _ =>
    show LandmarkInvList E [] (level_step E [])
    show List.Forall₂ _ [] []
    exact List.Forall₂.nil
  | [xs], [a], h =>
    show LandmarkInvList E [xs] (level_step E [a])
    show List.Forall₂ _ [xs] [a]
    exact h
  | xs :: ys :: rest_xs, a :: b :: rest_acc, h =>
    obtain ⟨h_a, h_rest⟩ := List.forall₂_cons.mp h
    obtain ⟨h_b, h_rest_rest⟩ := List.forall₂_cons.mp h_rest
    show LandmarkInvList E (pairUp (xs :: ys :: rest_xs))
                              (level_step E (a :: b :: rest_acc))
    show List.Forall₂ _ ((xs ++ ys) :: pairUp rest_xs)
                          (EagenAccum.combine E a b :: level_step E rest_acc)
    refine List.Forall₂.cons ?_ ?_
    · exact h_combine xs ys a b h_a h_b
    · exact landmarkInvList_preservation_under_level_step rest_xs rest_acc h_rest_rest h_combine

/-! ## iterate preservation

If `LandmarkInvList` holds for the input and per-pair combine preserves
LandmarkInv, then iterating `level_step` `n` times preserves the
property (with the corresponding number of `pairUp` operations on
the index list). -/

def pairUpN {α : Type*} : ℕ → List (List α) → List (List α)
  | 0, xss => xss
  | n + 1, xss =>
      if xss.length ≤ 1 then xss
      else pairUpN n (pairUp xss)

private theorem iterate_succ_eq (n : ℕ) (xs : List (EagenAccum E)) :
    iterate E (n + 1) xs =
      if xs.length ≤ 1 then xs else iterate E n (level_step E xs) := rfl

private theorem pairUpN_succ_eq (n : ℕ) (xss : List (List (ZMod E.q × ZMod E.q))) :
    pairUpN (n + 1) xss =
      if xss.length ≤ 1 then xss else pairUpN n (pairUp xss) := rfl

theorem landmarkInvList_preservation_under_iterate
    (n : ℕ)
    (xss : List (List (ZMod E.q × ZMod E.q)))
    (accs : List (EagenAccum E))
    (h : LandmarkInvList E xss accs)
    (h_combine : ∀ (xs ys : List (ZMod E.q × ZMod E.q))
        (a b : EagenAccum E),
      LandmarkInv E xs a → LandmarkInv E ys b →
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)) :
    LandmarkInvList E (pairUpN n xss) (iterate E n accs) := by
  classical
  induction n generalizing xss accs with
  | zero => exact h
  | succ n ih =>
    have h_lengths : xss.length = accs.length := List.Forall₂.length_eq h
    rw [iterate_succ_eq, pairUpN_succ_eq]
    by_cases hLen : accs.length ≤ 1
    · have h_xss_len : xss.length ≤ 1 := h_lengths ▸ hLen
      rw [if_pos hLen, if_pos h_xss_len]
      exact h
    · have h_xss_len : ¬ xss.length ≤ 1 := h_lengths ▸ hLen
      rw [if_neg hLen, if_neg h_xss_len]
      have h_step : LandmarkInvList E (pairUp xss) (level_step E accs) :=
        landmarkInvList_preservation_under_level_step E xss accs h h_combine
      exact ih (pairUp xss) (level_step E accs) h_step

/-! ## Top-level driver: eagenBuild via singletons

Composes `level0_singletons` with `iterate` to produce the final
polynomial. -/

noncomputable def eagenBuild_singletons
    (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingElt E.q :=
  let initial := level0_singletons E Ps
  let final := iterate E Ps.length initial
  match final with
  | [a] => a.poly
  | _ => { a := 1, b := 0 }

/-! ## pairUp helpers: flatten and convergence

`pairUp` preserves the flattened sub-list. After enough iterations
on a non-empty list of singletons, `pairUpN` converges to a singleton
containing the full list. -/

theorem pairUp_flatten {α : Type*} (xss : List (List α)) :
    (pairUp xss).flatten = xss.flatten := by
  match xss with
  | [] => rfl
  | [xs] => rfl
  | xs :: ys :: rest =>
    show (pairUp (xs :: ys :: rest)).flatten = (xs :: ys :: rest).flatten
    rw [show pairUp (xs :: ys :: rest) = (xs ++ ys) :: pairUp rest from rfl]
    simp [List.flatten, pairUp_flatten rest]

theorem pairUpN_flatten_aux {α : Type*} (n : ℕ) (xss : List (List α)) :
    (pairUpN n xss).flatten = xss.flatten := by
  induction n generalizing xss with
  | zero => rfl
  | succ n ih =>
    by_cases h : xss.length ≤ 1
    · show (pairUpN (n + 1) xss).flatten = xss.flatten
      have heq : pairUpN (n + 1) xss = xss := by
        show (if xss.length ≤ 1 then xss else pairUpN n (pairUp xss)) = xss
        rw [if_pos h]
      rw [heq]
    · show (pairUpN (n + 1) xss).flatten = xss.flatten
      have heq : pairUpN (n + 1) xss = pairUpN n (pairUp xss) := by
        show (if xss.length ≤ 1 then xss else pairUpN n (pairUp xss))
            = pairUpN n (pairUp xss)
        rw [if_neg h]
      rw [heq, ih, pairUp_flatten]

theorem pairUpN_flatten {α : Type*} (n : ℕ) (xss : List (List α)) :
    (pairUpN n xss).flatten = xss.flatten :=
  pairUpN_flatten_aux n xss

/-! ## More pairUp helpers -/

theorem map_singleton_flatten {α : Type*} (Ps : List α) :
    (Ps.map (fun P => [P])).flatten = Ps := by
  induction Ps with
  | nil => rfl
  | cons P rest ih =>
    show ([P] :: rest.map (fun P => [P])).flatten = P :: rest
    rw [List.flatten_cons]
    rw [show ([P] : List α) = P :: [] from rfl]
    rw [List.cons_append, List.nil_append]
    rw [ih]

/-! ## Landmark theorem (conditional on per-pair combine)

Combining levelInitSingleton, level_step preservation, iterate
preservation, and the pairUp/flatten helpers:

  Given a list of points all on `E`, the iterate of level0_singletons
  produces a list of accumulators each satisfying LandmarkInv with
  its corresponding sub-list partition. -/

theorem landmarkInvList_eagenBuild_singletons
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (h_combine : ∀ (xs ys : List (ZMod E.q × ZMod E.q))
        (a b : EagenAccum E),
      LandmarkInv E xs a → LandmarkInv E ys b →
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)) :
    LandmarkInvList E (pairUpN Ps.length (Ps.map (fun P => [P])))
                       (iterate E Ps.length (level0_singletons E Ps)) := by
  classical
  have h_init : LandmarkInvList E (Ps.map (fun P => [P]))
                                  (level0_singletons E Ps) :=
    landmarkInvList_level0_singletons E Ps hPs_on
  exact landmarkInvList_preservation_under_iterate E Ps.length _ _ h_init h_combine

/-! ## Convergence of pairUpN

For sufficient fuel, `pairUpN n xss` reaches a list of length ≤ 1.
When length = 1, the single element is `xss.flatten`. -/

theorem pairUp_length_le {α : Type*} (xss : List (List α)) :
    (pairUp xss).length ≤ xss.length / 2 + 1 := by
  match xss with
  | [] => simp [pairUp]
  | [_] => simp [pairUp]
  | xs :: ys :: rest =>
    show ((xs ++ ys) :: pairUp rest).length ≤ _
    rw [List.length_cons]
    have ih := pairUp_length_le rest
    rw [show (xs :: ys :: rest).length = rest.length + 2 from rfl]
    omega

theorem pairUpN_le_of_le {α : Type*} (n : ℕ) (xss : List (List α))
    (h : xss.length ≤ 1) :
    pairUpN n xss = xss := by
  match n with
  | 0 => rfl
  | k + 1 =>
    show (if xss.length ≤ 1 then xss else pairUpN k (pairUp xss)) = xss
    rw [if_pos h]

theorem pairUpN_eq_singleton_of_len_one {α : Type*} (n : ℕ) (xss : List (List α))
    (h : (pairUpN n xss).length = 1) :
    pairUpN n xss = [xss.flatten] := by
  have hf : (pairUpN n xss).flatten = xss.flatten := pairUpN_flatten n xss
  match h_eq : pairUpN n xss with
  | [] => simp [h_eq] at h
  | [x] =>
    rw [h_eq] at hf
    show [x] = [xss.flatten]
    have : x = xss.flatten := by
      have := hf
      simp at this
      exact this
    rw [this]
  | _ :: _ :: _ => simp [h_eq] at h

/-! ## level_step length bound -/

theorem level_step_length_le (xs : List (EagenAccum E)) :
    (level_step E xs).length ≤ (xs.length + 1) / 2 := by
  match xs with
  | [] => simp [level_step]
  | [_] => simp [level_step]
  | a :: b :: rest =>
    show (EagenAccum.combine E a b :: level_step E rest).length ≤ _
    rw [List.length_cons]
    have ih := level_step_length_le rest
    rw [show (a :: b :: rest).length = rest.length + 2 from rfl]
    omega

theorem iterate_length_le_one_of_fuel_geq
    (n : ℕ) (xs : List (EagenAccum E)) (h : xs.length ≤ n) :
    (iterate E n xs).length ≤ 1 := by
  induction n generalizing xs with
  | zero =>
    show xs.length ≤ 1
    omega
  | succ k ih =>
    show (iterate E (k + 1) xs).length ≤ 1
    by_cases hLen : xs.length ≤ 1
    · show (if xs.length ≤ 1 then xs else iterate E k (level_step E xs)).length ≤ 1
      rw [if_pos hLen]; exact hLen
    · show (if xs.length ≤ 1 then xs else iterate E k (level_step E xs)).length ≤ 1
      rw [if_neg hLen]
      apply ih
      have hStep := level_step_length_le E xs
      -- xs.length ≥ 2, so (level_step xs).length ≤ (xs.length + 1) / 2 ≤ xs.length - 1 ≤ k.
      -- Specifically: xs.length ≤ k + 1 and xs.length ≥ 2, so (xs.length + 1)/2 ≤ k.
      omega

/-! ## Final landmark theorem (conditional on combine) -/

theorem eagenBuild_singletons_landmark
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hSumZero : sumOnE E Ps = 0)
    (hNonEmpty : Ps ≠ [])
    (h_combine : ∀ (xs ys : List (ZMod E.q × ZMod E.q))
        (a b : EagenAccum E),
      LandmarkInv E xs a → LandmarkInv E ys b →
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)) :
    let D := eagenBuild_singletons E Ps
    ¬ (D.a = 0 ∧ D.b = 0) ∧
    (∀ P ∈ Ps, D.eval P.1 P.2 = 0) ∧
    (normPoly E D).natDegree = Ps.length := by
  classical
  -- The iterate output has length ≤ 1 with sufficient fuel.
  have h_init_len : (level0_singletons E Ps).length = Ps.length := by
    show (Ps.map _).length = Ps.length
    exact List.length_map ..
  have h_iter_le : (iterate E Ps.length (level0_singletons E Ps)).length ≤ 1 :=
    iterate_length_le_one_of_fuel_geq E Ps.length _ (by rw [h_init_len])
  -- LandmarkInvList for the iterated.
  have h_inv_list : LandmarkInvList E
      (pairUpN Ps.length (Ps.map (fun P => [P])))
      (iterate E Ps.length (level0_singletons E Ps)) :=
    landmarkInvList_eagenBuild_singletons E Ps hPs_on h_combine
  -- Pair up partition has same length as iterate output (Forall₂).
  have h_lens : (pairUpN Ps.length (Ps.map (fun P => [P]))).length
      = (iterate E Ps.length (level0_singletons E Ps)).length :=
    List.Forall₂.length_eq h_inv_list
  -- The iterate output has length ≥ 1 (since input non-empty).
  have h_init_pos : (level0_singletons E Ps).length ≥ 1 := by
    rw [h_init_len]
    cases Ps with
    | nil => exact (hNonEmpty rfl).elim
    | cons _ _ => simp
  -- ... actually iterate doesn't preserve length ≥ 1 in general, need to handle.
  -- For Ps.length ≥ 1, after iterate the output is exactly length 1.
  -- This requires: iterate doesn't drop to 0 if input was non-empty.
  -- Skip rigorous proof of this, take from the LandmarkInvList structure:
  -- pairUpN starts with non-empty (Ps.map fun P => [P]) and pairUp preserves
  -- non-empty (when input non-empty). So pairUpN result is non-empty.
  -- Hence iterate result is non-empty (same length).
  -- Combined with h_iter_le: length is exactly 1.
  -- ...
  -- For now, use pairUpN_flatten + non-empty as a proxy.
  have h_pairUp_flatten : (pairUpN Ps.length (Ps.map (fun P => [P]))).flatten
      = Ps := by
    rw [pairUpN_flatten, map_singleton_flatten]
  -- pairUpN result has length ≥ 1 (since flatten = Ps non-empty).
  have h_pair_ne_empty : pairUpN Ps.length (Ps.map (fun P => [P])) ≠ [] := by
    intro h
    rw [h] at h_pairUp_flatten
    simp at h_pairUp_flatten
    exact hNonEmpty h_pairUp_flatten
  have h_pair_len_pos : (pairUpN Ps.length (Ps.map (fun P => [P]))).length ≥ 1 := by
    cases h_pair_eq : pairUpN Ps.length (Ps.map (fun P => [P])) with
    | nil => exact (h_pair_ne_empty h_pair_eq).elim
    | cons _ _ => simp
  -- So both lists have length 1.
  have h_pair_len_one : (pairUpN Ps.length (Ps.map (fun P => [P]))).length = 1 := by
    rw [h_lens]; omega
  -- pairUpN result = [Ps].
  have h_pair_eq_singleton :
      pairUpN Ps.length (Ps.map (fun P => [P])) = [Ps] := by
    have := pairUpN_eq_singleton_of_len_one Ps.length
              (Ps.map (fun P => [P])) h_pair_len_one
    rw [this, map_singleton_flatten]
  -- iterate result has length 1: extract the singleton.
  match h_iter_eq : iterate E Ps.length (level0_singletons E Ps) with
  | [] =>
    rw [h_iter_eq] at h_lens
    simp at h_lens
    rw [h_lens] at h_pair_len_one
    simp at h_pair_len_one
  | [final_acc] =>
    -- LandmarkInv E Ps final_acc.
    rw [h_pair_eq_singleton, h_iter_eq] at h_inv_list
    have h_inv : LandmarkInv E Ps final_acc := by
      cases h_inv_list with
      | cons h_head h_tail => exact h_head
    obtain ⟨h_pt, h_van, h_res, h_deg⟩ := h_inv
    -- final_acc.point = sumOnE Ps = 0.
    have h_pt_zero : final_acc.point = (0 : ECPoint E) := by
      rw [h_pt]; exact hSumZero
    -- D = eagenBuild_singletons Ps = final_acc.poly.
    have h_D_eq : eagenBuild_singletons E Ps = final_acc.poly := by
      show (match iterate E Ps.length (level0_singletons E Ps) with
            | [a] => a.poly
            | _ => { a := 1, b := 0 }) = final_acc.poly
      rw [h_iter_eq]
    -- Degree.
    rw [if_pos h_pt_zero] at h_deg
    -- Show all three conjuncts.
    refine ⟨?_, ?_, ?_⟩
    · -- D ≠ 0.
      intro ⟨ha, hb⟩
      rw [h_D_eq] at ha hb
      have hNorm : normPoly E final_acc.poly = 0 := by
        rw [normPoly_eq]
        rw [ha, hb]
        ring
      rw [hNorm, Polynomial.natDegree_zero] at h_deg
      have : Ps.length = 0 := by linarith
      have : Ps = [] := List.length_eq_zero_iff.mp this
      exact hNonEmpty this
    · -- D vanishes at every P ∈ Ps.
      intro P hP
      rw [h_D_eq]
      exact h_van P hP
    · -- (normPoly D).natDegree = Ps.length.
      rw [h_D_eq, h_deg]
      omega
  | _ :: _ :: _ =>
    rw [h_iter_eq] at h_iter_le
    simp at h_iter_le


/-! ## Path forward (Codex consultation)

Making eagenBuild_singletons_landmark unconditional (no h_combine
hypothesis) requires strengthening LandmarkInv with point/sheet-level
multiplicity tracking. Per Codex:

  - Define a constructive local multiplicity mult E D P : Nat for
    D : CoordRingElt, P : ZMod q x q, returning 0 if D does not
    vanish at P, otherwise matching geometric ord.
  - Strengthen LandmarkInv:
      target xs R P := xs.count P + (if negCoords R = some P then 1 else 0)
      forall P in E.points, target xs a.point P <= mult E a.poly P
      (normPoly a.poly).natDegree = sum P in E.points, target xs a.point P
  - combine_distinct becomes a multiplicity identity:
      M(xs,A) + M(ys,B) + L(A,B) - V(A) - V(B) = M(xs++ys, A+B)
    where chord/divLin contributions cancel at fiber collisions.

Estimated: ~600-1000 LOC of new infrastructure. -/


/-! ## Bridge: landmark → full divisor identity (uses splitsOnE machinery) -/

/-- Local copy of formalDivisorOfList (avoid importing EagenBuildRecursive
to keep the bridge theorem's project-axiom dependence minimal). -/
noncomputable def formalDivisorOfList
    (Ps : List (ZMod E.q × ZMod E.q)) : ECPoint E → ℤ :=
  fun R =>
    match R with
    | WeierstrassCurve.Affine.Point.zero => -((Ps.length : ℤ))
    | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
        (Ps.filter (fun P => P = (x, y))).length

private theorem filter_length_eq_count_eq {α : Type _} [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) :
    (xs.filter (fun x => x = a)).length = xs.count a := by
  induction xs with
  | nil =>
      simp [List.count]
  | cons x xs ih =>
      by_cases hx : x = a
      · simp [List.count, ih, hx]
      · simp [List.count, ih, hx]

theorem divisorOfD_eq_formalDivisorOfList_of_landmark
    (Ps : List (ZMod E.q × ZMod E.q))
    (D : CoordRingElt E.q)
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hNodup : Ps.Nodup)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hVan : ∀ P ∈ Ps, D.eval P.1 P.2 = 0)
    (hDeg : (normPoly E D).natDegree = Ps.length)
    (hSplit : splitsOnE E D) :
    ∀ R : ECPoint E,
      divisorOfD E D R = formalDivisorOfList E Ps R := by
  classical
  have h_total : (∑ Q ∈ E.points, ordAt E D Q) = Ps.length := by
    rw [sum_ordAt_eq_natDegree_under_split E D hD hSplit]
    exact hDeg
  have h_each_pos : ∀ P ∈ Ps, 1 ≤ ordAt E D P := by
    intro P hP
    have hP_on : P ∈ E.points := hPs_on P hP
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero]
    rw [ordAt_pos_iff_zero E D hD P hP_on]
    exact hVan P hP
  have h_Ps_subset : Ps.toFinset ⊆ E.points := by
    intro P hP; rw [List.mem_toFinset] at hP; exact hPs_on P hP
  have h_Ps_card : Ps.toFinset.card = Ps.length := List.toFinset_card_of_nodup hNodup
  have h_sub_lower : Ps.length ≤ ∑ P ∈ Ps.toFinset, ordAt E D P := by
    rw [← h_Ps_card]
    rw [show Ps.toFinset.card = ∑ _P ∈ Ps.toFinset, 1 from by
        rw [Finset.sum_const, Nat.smul_one_eq_cast]; rfl]
    apply Finset.sum_le_sum
    intro P hP
    rw [List.mem_toFinset] at hP
    exact h_each_pos P hP
  have h_split_sum :
      (∑ Q ∈ E.points, ordAt E D Q)
        = (∑ P ∈ Ps.toFinset, ordAt E D P)
          + (∑ Q ∈ E.points \ Ps.toFinset, ordAt E D Q) := by
    rw [← Finset.sum_sdiff h_Ps_subset]; ring
  have h_rest_zero : (∑ Q ∈ E.points \ Ps.toFinset, ordAt E D Q) = 0 := by omega
  have h_Ps_sum : (∑ P ∈ Ps.toFinset, ordAt E D P) = Ps.length := by omega
  have h_each_eq : ∀ P ∈ Ps, ordAt E D P = 1 := by
    intro P hP
    by_contra h_ne
    have hge2 : 2 ≤ ordAt E D P := by
      have h1 := h_each_pos P hP; omega
    have hP_in : P ∈ Ps.toFinset := List.mem_toFinset.mpr hP
    have h_split2 :
        (∑ Q ∈ Ps.toFinset, ordAt E D Q)
          = ordAt E D P + (∑ Q ∈ Ps.toFinset.erase P, ordAt E D Q) := by
      rw [← Finset.sum_erase_add _ _ hP_in]; ring
    have h_others_card : (Ps.toFinset.erase P).card = Ps.length - 1 := by
      rw [Finset.card_erase_of_mem hP_in, h_Ps_card]
    have h_others_lower : Ps.length - 1 ≤ ∑ Q ∈ Ps.toFinset.erase P, ordAt E D Q := by
      rw [← h_others_card]
      rw [show (Ps.toFinset.erase P).card = ∑ _Q ∈ Ps.toFinset.erase P, 1 from by
          rw [Finset.sum_const, Nat.smul_one_eq_cast]; rfl]
      apply Finset.sum_le_sum
      intro Q hQ
      rw [Finset.mem_erase, List.mem_toFinset] at hQ
      exact h_each_pos Q hQ.2
    have hPs_pos : 0 < Ps.length := by
      cases Ps with
      | nil => exact absurd hP (List.not_mem_nil)
      | cons _ _ => simp
    omega
  have h_off_zero : ∀ Q ∈ E.points \ Ps.toFinset, ordAt E D Q = 0 := by
    intro Q hQ
    by_contra h_ne
    have h_pos : 0 < ordAt E D Q := Nat.pos_of_ne_zero h_ne
    have h_sum_pos : 0 < ∑ Q ∈ E.points \ Ps.toFinset, ordAt E D Q :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨Q, hQ, h_pos⟩
    omega
  intro R
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    show -((normPoly E D).natDegree : ℤ) = -((Ps.length : ℤ))
    rw [hDeg]
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
    show (ordAt E D (x, y) : ℤ) = ((Ps.filter (fun P => P = (x, y))).length : ℤ)
    have hxy_on : (x, y) ∈ E.points := E.hComplete x y
      ((E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns))
    by_cases hxy_in : (x, y) ∈ Ps
    · have h_ord : ordAt E D (x, y) = 1 := h_each_eq _ hxy_in
      have h_count : (Ps.filter (fun P => P = (x, y))).length = 1 := by
        have h_filter_count :
            (Ps.filter (fun P => P = (x, y))).length = Ps.count (x, y) := by
          exact filter_length_eq_count_eq Ps (x, y)
        rw [h_filter_count]
        exact List.count_eq_one_of_mem hNodup hxy_in
      exact congrArg (fun n : ℕ => (n : ℤ)) (by rw [h_ord, h_count])
    · have h_ord : ordAt E D (x, y) = 0 := by
        apply h_off_zero
        rw [Finset.mem_sdiff]
        exact ⟨hxy_on, by rw [List.mem_toFinset]; exact hxy_in⟩
      have h_count : (Ps.filter (fun P => P = (x, y))).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro P hP h_eq
        simp at h_eq
        rw [← h_eq] at hxy_in
        exact hxy_in hP
      exact congrArg (fun n : ℕ => (n : ℤ)) (by rw [h_ord, h_count])

/-- Landmark data already forces `normPoly E D` to split over `F_q`, and
every root comes from the x-coordinate of one of the landmark points. -/
theorem splitsOnE_of_landmark
    (Ps : List (ZMod E.q × ZMod E.q))
    (D : CoordRingElt E.q)
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hNodup : Ps.Nodup)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hVan : ∀ P ∈ Ps, D.eval P.1 P.2 = 0)
    (hDeg : (normPoly E D).natDegree = Ps.length) :
    splitsOnE E D := by
  classical
  let c : ZMod E.q → ℕ :=
    fun α => (Ps.toFinset.filter (fun P => P.1 = α)).card
  have h_Ps_card : Ps.toFinset.card = Ps.length := List.toFinset_card_of_nodup hNodup
  have h_maps : ∀ P ∈ Ps.toFinset, P.1 ∈ (Finset.univ : Finset (ZMod E.q)) :=
    fun _ _ => Finset.mem_univ _
  have h_c_sum_card :
      Ps.toFinset.card = ∑ α : ZMod E.q, c α := by
    unfold c
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (f := fun P : ZMod E.q × ZMod E.q => P.1)
        (s := Ps.toFinset) (t := (Finset.univ : Finset (ZMod E.q))) h_maps)
  have h_c_sum : (∑ α : ZMod E.q, c α) = (normPoly E D).natDegree := by
    rw [← h_c_sum_card, h_Ps_card, ← hDeg]
  have h_c_le_rm : ∀ α : ZMod E.q,
      c α ≤ rootMultiplicity α (normPoly E D) := by
    intro α
    unfold c
    set S := Ps.toFinset.filter (fun P => P.1 = α)
    have hS_sub : S ⊆ E.points.filter (fun P => P.1 = α) := by
      intro P hP
      have hP' := Finset.mem_filter.mp hP
      rw [Finset.mem_filter]
      refine ⟨?_, hP'.2⟩
      rw [List.mem_toFinset] at hP'
      exact hPs_on P hP'.1
    have hS_card_le : S.card ≤ 2 :=
      (Finset.card_le_card hS_sub).trans (card_points_with_fst_eq_le E α)
    interval_cases hScard : S.card
    · exact Nat.zero_le _
    · rw [Finset.card_eq_one] at hScard
      obtain ⟨P, hS_eq⟩ := hScard
      have hPS : P ∈ S := by
        rw [hS_eq]
        exact Finset.mem_singleton_self P
      have hPmem : P ∈ Ps := by
        have hP' := (Finset.mem_filter.mp hPS).1
        rwa [List.mem_toFinset] at hP'
      have hPx : P.1 = α := (Finset.mem_filter.mp hPS).2
      have hRm_pos : 0 < rootMultiplicity P.1 (normPoly E D) :=
        rootMultiplicity_normPoly_pos E D (hPs_on P hPmem) (hVan P hPmem) hD
      rw [hPx] at hRm_pos
      omega
    · rw [Finset.card_eq_two] at hScard
      obtain ⟨P₁, P₂, hNeq, hS_eq⟩ := hScard
      have hP₁S : P₁ ∈ S := by
        rw [hS_eq]
        exact Finset.mem_insert_self P₁ {P₂}
      have hP₂S : P₂ ∈ S := by
        rw [hS_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self P₂)
      have hP₁mem : P₁ ∈ Ps := by
        have hP' := (Finset.mem_filter.mp hP₁S).1
        rwa [List.mem_toFinset] at hP'
      have hP₂mem : P₂ ∈ Ps := by
        have hP' := (Finset.mem_filter.mp hP₂S).1
        rwa [List.mem_toFinset] at hP'
      have hP₁x : P₁.1 = α := (Finset.mem_filter.mp hP₁S).2
      have hP₂x : P₂.1 = α := (Finset.mem_filter.mp hP₂S).2
      have hYneq : P₁.2 ≠ P₂.2 := by
        intro hY
        exact hNeq (Prod.ext (hP₁x.trans hP₂x.symm) hY)
      have hY₁sq : P₁.2 ^ 2 = P₁.1 ^ 3 + E.curveA * P₁.1 + E.curveB :=
        E.hOnCurve P₁ (hPs_on P₁ hP₁mem)
      have hY₂sq : P₂.2 ^ 2 = P₂.1 ^ 3 + E.curveA * P₂.1 + E.curveB :=
        E.hOnCurve P₂ (hPs_on P₂ hP₂mem)
      have hYsum : P₁.2 ^ 2 = P₂.2 ^ 2 := by
        rw [hY₁sq, hY₂sq, hP₁x, hP₂x]
      have hFactor : (P₁.2 - P₂.2) * (P₁.2 + P₂.2) = 0 := by
        linear_combination hYsum
      have hYneg : P₂.2 = -P₁.2 := by
        have hSumZero : P₁.2 + P₂.2 = 0 := by
          rcases mul_eq_zero.mp hFactor with h | h
          · exact absurd (sub_eq_zero.mp h) hYneq
          · exact h
        linear_combination hSumZero
      have hY₁ : P₁.2 ≠ 0 := by
        intro h
        apply hYneq
        rw [h, hYneg, h, neg_zero]
      have hZ₁ : D.eval P₁.1 P₁.2 = 0 := hVan P₁ hP₁mem
      have hZ₁neg : D.eval P₁.1 (-P₁.2) = 0 := by
        have hEval :
            D.eval P₁.1 (-P₁.2) = D.eval P₂.1 P₂.2 := by
          congr 1
          · exact hP₁x.trans hP₂x.symm
          · exact hYneg.symm
        rw [hEval, hVan P₂ hP₂mem]
      have hge2 : 2 ≤ rootMultiplicity P₁.1 (normPoly E D) :=
        rootMultiplicity_normPoly_ge_two_of_both_sheets E D hD hY₁ hZ₁ hZ₁neg
      rw [hP₁x] at hge2
      exact hge2
  have h_rm_sum_card :
      (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
        = Multiset.card (normPoly E D).roots :=
    sum_rootMultiplicity_eq_card_roots E (normPoly E D)
  have h_nat_le_rm_sum :
      (normPoly E D).natDegree ≤
        ∑ α : ZMod E.q, rootMultiplicity α (normPoly E D) := by
    rw [← h_c_sum]
    exact Finset.sum_le_sum (fun α _ => h_c_le_rm α)
  have hSplit : normPoly_splits_over_Fq E D := by
    unfold normPoly_splits_over_Fq
    have h_nat_le_card :
        (normPoly E D).natDegree ≤ Multiset.card (normPoly E D).roots := by
      rw [← h_rm_sum_card]
      exact h_nat_le_rm_sum
    exact le_antisymm (Polynomial.card_roots' (normPoly E D)) h_nat_le_card
  have h_rm_sum : (∑ α : ZMod E.q, rootMultiplicity α (normPoly E D))
      = (normPoly E D).natDegree := by
    rw [h_rm_sum_card]
    exact hSplit
  have h_c_eq_rm : ∀ α : ZMod E.q,
      c α = rootMultiplicity α (normPoly E D) := by
    intro α
    by_contra hne
    have hlt : c α < rootMultiplicity α (normPoly E D) :=
      lt_of_le_of_ne (h_c_le_rm α) hne
    have hsum_lt : (∑ x : ZMod E.q, c x)
        < ∑ x : ZMod E.q, rootMultiplicity x (normPoly E D) :=
      Finset.sum_lt_sum (fun x _ => h_c_le_rm x) ⟨α, Finset.mem_univ _, hlt⟩
    omega
  refine ⟨hSplit, ?_⟩
  intro α hα
  have hRoot_pos : 0 < rootMultiplicity α (normPoly E D) :=
    (Polynomial.rootMultiplicity_pos (normPoly_ne_zero E D hD)).mpr
      ((Polynomial.mem_roots (normPoly_ne_zero E D hD)).mp hα)
  have hc_pos : 0 < c α := by
    rw [h_c_eq_rm α]
    exact hRoot_pos
  have hS_nonempty :
      (Ps.toFinset.filter (fun P => P.1 = α)).Nonempty := by
    unfold c at hc_pos
    exact Finset.card_pos.mp hc_pos
  obtain ⟨P, hPS⟩ := hS_nonempty
  have hPmem : P ∈ Ps := by
    have hP' := (Finset.mem_filter.mp hPS).1
    rwa [List.mem_toFinset] at hP'
  have hPx : P.1 = α := (Finset.mem_filter.mp hPS).2
  exact ⟨P.2, by
    rw [← hPx]
    simpa using hPs_on P hPmem⟩

theorem eagenBuild_singletons_divisor_identity
    (Ps : List (ZMod E.q × ZMod E.q))
    (hPs_on : ∀ P ∈ Ps, P ∈ E.points)
    (hSumZero : sumOnE E Ps = 0)
    (hNonEmpty : Ps ≠ [])
    (hNodup : Ps.Nodup)
    (h_combine : ∀ (xs ys : List (ZMod E.q × ZMod E.q))
        (a b : EagenAccum E),
      LandmarkInv E xs a → LandmarkInv E ys b →
      LandmarkInv E (xs ++ ys) (EagenAccum.combine E a b)) :
    ∀ R : ECPoint E,
      divisorOfD E (eagenBuild_singletons E Ps) R
        = formalDivisorOfList E Ps R := by
  classical
  let D := eagenBuild_singletons E Ps
  have h_landmark :
      ¬ (D.a = 0 ∧ D.b = 0) ∧
      (∀ P ∈ Ps, D.eval P.1 P.2 = 0) ∧
      (normPoly E D).natDegree = Ps.length := by
    simpa [D] using
      eagenBuild_singletons_landmark E Ps hPs_on hSumZero hNonEmpty h_combine
  obtain ⟨hD, hVan, hDeg⟩ := h_landmark
  have hSplit : splitsOnE E D :=
    splitsOnE_of_landmark E Ps D hPs_on hNodup hD hVan hDeg
  simpa [D] using
    divisorOfD_eq_formalDivisorOfList_of_landmark
      E Ps D hPs_on hNodup hD hVan hDeg hSplit

end Divisor.Landmark
