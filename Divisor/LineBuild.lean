/-
  Divisor/LineBuild.lean

  The line build: Miller's construction (J. Cryptology 17(4), 2004)
  with Eagen's level-by-level schedule (ePrint 2022/596, §3.1.1).
  Adjacent accumulators are combined through the line between their
  running points, the odd one is carried up a level, and vertical
  factors are divided out. `Accum.point` is an `ECPoint`, so a running
  sum may be `O`.

  This file holds the construction (`Accum.combine`, `level_step`,
  `iterate`, `lineBuild_singletons`) and its list bookkeeping. Its
  correctness is proved in `Divisor.LineBuildExact`.
-/
import Divisor.IncrementalConstruction

open Polynomial

namespace Divisor.LineAccum

variable (E : ECSetup)

/-! ## Data model

`Accum` carries a running-sum point on `E` (admitting `O` =
infinity for sub-lists summing to zero) and the accumulated
polynomial. -/

/-- Accumulator for the LineAccum recursion. `point : ECPoint E`
admits `0 = ∞` so vertical-internal sub-sums are first-class.

The invariant `Exact.ExactInv xs a` (in `Divisor.LineBuildExact.Combine`)
ties the fields to a list of absorbed inputs `xs`. -/
structure Accum where
  point : ECPoint E
  poly : CoordRingElt E.q

/-! ## Combine helpers

The per-pair combine logic is
split into six helpers, one for each branch of the
`(a.point, b.point)` ECPoint pair. The public `combine` matches and
dispatches; invariant lemmas are proved on the helpers.

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
noncomputable def Accum.combine_oo (a b : Accum E) : Accum E :=
  { point := 0, poly := mulCoordRingElt E a.poly b.poly }

/-- `a.point = 0`, `b.point ≠ 0`: forward `b`'s residue. -/
noncomputable def Accum.combine_ol (a b : Accum E) : Accum E :=
  { point := b.point, poly := mulCoordRingElt E a.poly b.poly }

/-- `a.point ≠ 0`, `b.point = 0`: forward `a`'s residue. -/
noncomputable def Accum.combine_or (a b : Accum E) : Accum E :=
  { point := a.point, poly := mulCoordRingElt E a.poly b.poly }

/-- Both points affine with distinct x-coordinates: chord case.
    The chord through `a.point`, `b.point` meets `E` at a third
    rational point; the new running sum is its negation
    `-(a + b)` in the group law. The polynomial is
    `(line · a.poly · b.poly) / ((X - a.x)(X - b.x))`. -/
noncomputable def Accum.combine_distinct
    (a b : Accum E)
    (xa ya xb yb : ZMod E.q)
    (_h_xx : xa ≠ xb) :
    Accum E :=
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
noncomputable def Accum.combine_vertical
    (a b : Accum E) (xa : ZMod E.q) :
    Accum E :=
  let prod := mulCoordRingElt E a.poly b.poly
  { point := 0, poly := prod.divLin xa }

/-- Both points affine, equal, with `y = 0`: 2-torsion doubling.
    Tangent line is vertical `X - x_a`; new running sum = O. -/
noncomputable def Accum.combine_tangent_torsion
    (a b : Accum E) (xa : ZMod E.q) :
    Accum E :=
  -- Identical to vertical case at the data level.
  Accum.combine_vertical E a b xa

/-- Both points affine, equal, with `y ≠ 0`: tangent doubling.
    Tangent line at `(xa, ya)`. The "third intersection" is the
    point `(x₂, y₂)` with `x₂ = λ² - 2·xa`, where
    `λ = (3·xa² + curveA)/(2·ya)`. New running sum = `-(2·a)` =
    `(x₂, -y₂)`. -/
noncomputable def Accum.combine_tangent_smooth
    (a b : Accum E)
    (xa ya : ZMod E.q) (_h_y : ya ≠ 0) :
    Accum E :=
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

noncomputable def Accum.combine (a b : Accum E) : Accum E :=
  match _h_a : a.point, _h_b : b.point with
  | WeierstrassCurve.Affine.Point.zero, WeierstrassCurve.Affine.Point.zero =>
      Accum.combine_oo E a b
  | WeierstrassCurve.Affine.Point.zero,
    WeierstrassCurve.Affine.Point.some _ _ _ =>
      Accum.combine_ol E a b
  | WeierstrassCurve.Affine.Point.some _ _ _,
    WeierstrassCurve.Affine.Point.zero =>
      Accum.combine_or E a b
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) _,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) _ =>
      if h_xx : xa ≠ xb then
        Accum.combine_distinct E a b xa ya xb yb h_xx
      else if _h_yy : ya = -yb then
        -- a.point + b.point = O.
        Accum.combine_vertical E a b xa
      else
        -- Same x AND not y-flipped ⇒ ya = yb (curve dichotomy).
        if h_y0 : ya = 0 then
          Accum.combine_tangent_torsion E a b xa
        else
          Accum.combine_tangent_smooth E a b xa ya h_y0

/-! ## Driver: level_step, iterate -/

/-- One level: pair adjacent accumulators and combine each pair.
    Trailing odd element is forwarded unchanged (so `level_step`
    on odd-length input doesn't lose the residual; it converges
    in `⌈log₂ n⌉` levels). -/
noncomputable def level_step :
    List (Accum E) → List (Accum E)
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      Accum.combine E a b :: level_step rest

/-- The point projection of one `Accum.combine` dispatch.
    This skips the polynomial side and is computable. -/
def pointCombine (p q : ECPoint E) : ECPoint E :=
  match p, q with
  | WeierstrassCurve.Affine.Point.zero, _ => q
  | WeierstrassCurve.Affine.Point.some _ _ _, WeierstrassCurve.Affine.Point.zero => p
  | WeierstrassCurve.Affine.Point.some (x := xa) (y := ya) _,
    WeierstrassCurve.Affine.Point.some (x := xb) (y := yb) _ =>
      if _h_xx : xa ≠ xb then
        let lam := slopeOf xa ya xb yb
        let Qx := lam ^ 2 - xa - xb
        let Qy := lam * Qx + (ya - lam * xa)
        ECPoint.affine E Qx (-Qy)
      else if _h_yy : ya = -yb then
        0
      else if _h_y0 : ya = 0 then
        0
      else
        let lam : ZMod E.q := (3 * xa ^ 2 + E.curveA) * (2 * ya)⁻¹
        let Qx := lam ^ 2 - 2 * xa
        let Qy := lam * Qx + (ya - lam * xa)
        ECPoint.affine E Qx (-Qy)

/-- Iterate `level_step` `n` times (or until length ≤ 1). -/
noncomputable def iterate :
    ℕ → List (Accum E) → List (Accum E)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else iterate n (level_step E xs)

/-! ## Sum-on-curve helper

The running EC sum of a list of inputs, lifted to `ECPoint E`. Off
`E.points` an input contributes nothing (junk on `E.points` membership
is benign because the recursion's invariant requires all
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


/-- The "negation coordinates" of an `ECPoint`. Returns `none` for
    infinity, `some (x, -y)` for an affine `(x, y)`. Used to spell
    out residue vanishing (the polynomial vanishes at `-a.point`). -/
noncomputable def negCoords (P : ECPoint E) : Option (ZMod E.q × ZMod E.q) :=
  match P with
  | WeierstrassCurve.Affine.Point.zero => none
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ => some (x, -y)

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

/-! ## Level-0 singletons

Each input point `P` becomes the accumulator
`{ point := ECPoint.affine E P.1 P.2, poly := (X - C P.1, 0) }`;
`level_step` then handles all the pairing logic uniformly. -/

/-- The on-curve assumption is unused at the data level (Junk if off-curve
    via `ECPoint.affine`'s `dif_*` fallback to 0). The invariant requires it. -/
noncomputable def levelInitSingleton
    (P : ZMod E.q × ZMod E.q) : Accum E :=
  { point := ECPoint.affine E P.1 P.2,
    poly := { a := X - C P.1, b := 0 } }

/-- Singletonized level-0: each input becomes a vertical-line accumulator. -/
noncomputable def level0_singletons (Ps : List (ZMod E.q × ZMod E.q)) :
    List (Accum E) :=
  Ps.map (levelInitSingleton E)

/-! ## Pairing sub-lists

The `pairUp` function on a list of sub-lists: pair adjacent and
append, leaving any trailing odd-length element forwarded. -/

def pairUp {α : Type*} : List (List α) → List (List α)
  | [] => []
  | [xs] => [xs]
  | xs :: ys :: rest => (xs ++ ys) :: pairUp rest

/-! ## Point projection of `combine` -/

theorem combine_point_eq_pointCombine (a b : Accum E) :
    (Accum.combine E a b).point = pointCombine E a.point b.point := by
  rcases a with ⟨pa, Da⟩
  rcases b with ⟨pb, Db⟩
  cases pa <;> cases pb <;>
    simp [Accum.combine, pointCombine,
      Accum.combine_oo, Accum.combine_ol, Accum.combine_or,
      Accum.combine_distinct, Accum.combine_vertical,
      Accum.combine_tangent_torsion, Accum.combine_tangent_smooth]
  repeat
    first
    | split
    | simp

/-! ## Iterated pairing

`pairUpN n` mirrors `iterate E n` on the index list: each level pairs
adjacent sub-lists the way `level_step` combines adjacent
accumulators. -/

def pairUpN {α : Type*} : ℕ → List (List α) → List (List α)
  | 0, xss => xss
  | n + 1, xss =>
      if xss.length ≤ 1 then xss
      else pairUpN n (pairUp xss)

/-! ## Top-level driver: `lineBuild_singletons`

Composes `level0_singletons` with `iterate` to produce the final
polynomial. -/

noncomputable def lineBuild_singletons
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

/-! ## Convergence of pairUpN

For sufficient fuel, `pairUpN n xss` reaches a list of length ≤ 1.
When length = 1, the single element is `xss.flatten`. -/

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

theorem level_step_length_le (xs : List (Accum E)) :
    (level_step E xs).length ≤ (xs.length + 1) / 2 := by
  match xs with
  | [] => simp [level_step]
  | [_] => simp [level_step]
  | a :: b :: rest =>
    show (Accum.combine E a b :: level_step E rest).length ≤ _
    rw [List.length_cons]
    have ih := level_step_length_le rest
    rw [show (a :: b :: rest).length = rest.length + 2 from rfl]
    omega

theorem iterate_length_le_one_of_fuel_geq
    (n : ℕ) (xs : List (Accum E)) (h : xs.length ≤ n) :
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

/-! ## Formal divisor of a support list -/

/-- The formal divisor `Σ_{P ∈ Ps} (P) − |Ps|·(∞)` of a support list. -/
noncomputable def formalDivisorOfList
    (Ps : List (ZMod E.q × ZMod E.q)) : ECPoint E → ℤ :=
  fun R =>
    match R with
    | WeierstrassCurve.Affine.Point.zero => -((Ps.length : ℤ))
    | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
        (Ps.filter (fun P => P = (x, y))).length

end Divisor.LineAccum
