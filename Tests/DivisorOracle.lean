/-
  Tests/DivisorOracle.lean

  A computable divisor oracle for test runs of the prover: the local
  order of `D = a(x) − b(x)·y` at an affine point of `E`, and the exact
  check that `D` has divisor `Σ_{P ∈ S} (P) − |S|·(O)`.

  `localOrder` expands `D` in a local parameter at `Q = (x₀, y₀)` as a
  truncated power series and returns its valuation:

  * `y₀ ≠ 0`: `t = x − x₀`; `y(t)` solves `y² = f(x₀ + t)`, `y(0) = y₀`, by
    the coefficient recursion `2y₀·y_k = f_k − Σ_{0<i<k} y_i·y_{k−i}`;
  * `y₀ = 0`: `t = y`; `x(t) = x₀ + s(t)` solves `f(x₀ + s) = t²` by the
    fixed-point iteration `s ← (t² − f₂·s² − s³) / f′(x₀)`, one order per
    step (`f′(x₀) ≠ 0` by nonsingularity).

  The precision is `degE(D) + 1`, where `degE = max(2·deg a, 2·deg b + 3)`
  is the pole order at `O`; every affine order is at most `degE`, so the
  valuation is exact.

  `divisorExact E D S`: `D ≠ 0`, `S` lies on `E`, and `localOrder D Q =
  S.count Q` at every affine point `Q`. Since `D` has poles only at `O`,
  this is the full divisor.
-/
import Divisor.ProverDefs
import Tests.CurveFixtures

namespace Tests.DivisorOracle

open Divisor

variable (E : ECSetup)

/-! ## Truncated power series, precision `N` -/

private abbrev Ser := Array (ZMod E.q)

private def sConst (N : ℕ) (c : ZMod E.q) : Ser E :=
  Array.ofFn (n := N) fun i => if i.val = 0 then c else 0

private def sAdd (N : ℕ) (u v : Ser E) : Ser E :=
  Array.ofFn (n := N) fun i => u.getD i 0 + v.getD i 0

private def sSub (N : ℕ) (u v : Ser E) : Ser E :=
  Array.ofFn (n := N) fun i => u.getD i 0 - v.getD i 0

private def sSmul (c : ZMod E.q) (u : Ser E) : Ser E := u.map (c * ·)

private def sMul (N : ℕ) (u v : Ser E) : Ser E :=
  Array.ofFn (n := N) fun i =>
    (List.range (i.val + 1)).foldl (fun acc k => acc + u.getD k 0 * v.getD (i.val - k) 0) 0

/-- `p(s)` for a series `s`, by Horner. -/
private def sCompose (N : ℕ) (p : CoeffPoly E.q) (s : Ser E) : Ser E :=
  p.coeffs.foldr (fun c acc => sAdd E N (sMul E N acc s) (sConst E N c)) (sConst E N 0)

/-- Index of the first nonzero coefficient; `N` if there is none. -/
private def sVal (N : ℕ) (u : Ser E) : ℕ :=
  ((List.range N).find? fun i => u.getD i 0 != 0).getD N

/-! ## Local expansions -/

/-- Taylor coefficients of `f(x₀ + t) = (x₀ + t)³ + A·(x₀ + t) + B`. -/
private def fShift (x₀ : ZMod E.q) : ℕ → ZMod E.q
  | 0 => x₀ ^ 3 + E.curveA * x₀ + E.curveB
  | 1 => 3 * x₀ ^ 2 + E.curveA
  | 2 => 3 * x₀
  | 3 => 1
  | _ => 0

/-- `y(t)` with `y(0) = y₀`, `y² = f(x₀ + t)`; needs `y₀ ≠ 0`. -/
private def ySeries (N : ℕ) (x₀ y₀ : ZMod E.q) : Ser E :=
  (List.range N).foldl (fun ys k =>
    if k = 0 then ys.push y₀
    else
      let conv := (List.range k).foldl
        (fun acc i => if i = 0 then acc else acc + ys.getD i 0 * ys.getD (k - i) 0) 0
      ys.push ((fShift E x₀ k - conv) * (2 * y₀)⁻¹)) #[]

/-- `s(t) = x(t) − x₀` with `f(x₀ + s) = t²`; needs `f′(x₀) ≠ 0`. -/
private def sSeries (N : ℕ) (x₀ : ZMod E.q) : Ser E :=
  let t2 : Ser E := Array.ofFn (n := N) fun i => if i.val = 2 then 1 else 0
  (List.range N).foldl (fun s _ =>
    let s2 := sMul E N s s
    sSmul E (fShift E x₀ 1)⁻¹
      (sSub E N (sSub E N t2 (sSmul E (fShift E x₀ 2) s2)) (sMul E N s2 s))) (sConst E N 0)

/-- Degree plus one; `0` for the zero polynomial. -/
private def lenC (p : CoeffPoly E.q) : ℕ :=
  (p.coeffs.reverse.dropWhile (· == 0)).length

/-- `degE(D) + 1`, with `degE = max(2·deg a, 2·deg b + 3)` over the nonzero
    parts. -/
def precision (D : CoordRingEltC E.q) : ℕ :=
  let la := lenC E D.a
  let lb := lenC E D.b
  max (2 * (la - 1)) (if lb = 0 then 0 else 2 * lb + 1) + 1

/-- Order of vanishing of `D = a − b·y` at the affine point `Q ∈ E`. -/
def localOrder (D : CoordRingEltC E.q) (Q : ZMod E.q × ZMod E.q) : ℕ :=
  let N := precision E D
  let (x₀, y₀) := Q
  if y₀ ≠ 0 then
    let X : Ser E := Array.ofFn (n := N) fun i =>
      if i.val = 0 then x₀ else if i.val = 1 then 1 else 0
    sVal E N (sSub E N (sCompose E N D.a X)
      (sMul E N (sCompose E N D.b X) (ySeries E N x₀ y₀)))
  else
    let X := sAdd E N (sConst E N x₀) (sSeries E N x₀)
    let Y : Ser E := Array.ofFn (n := N) fun i => if i.val = 1 then 1 else 0
    sVal E N (sSub E N (sCompose E N D.a X) (sMul E N (sCompose E N D.b X) Y))

/-! ## The divisor check -/

/-- All affine points of `E(F_q)`. -/
def curvePts : List (ZMod E.q × ZMod E.q) :=
  ((List.range E.q).flatMap fun x =>
      (List.range E.q).map fun y => ((x : ZMod E.q), (y : ZMod E.q))).filter fun p =>
    p.2 ^ 2 == p.1 ^ 3 + E.curveA * p.1 + E.curveB

/-- `D` has divisor exactly `Σ_{P ∈ S} (P) − |S|·(O)`: `D ≠ 0`, `S ⊆ E`, and
    the order of `D` at every affine point `Q` is the count of `Q` in `S`. -/
def divisorExact (D : CoordRingEltC E.q) (S : List (ZMod E.q × ZMod E.q)) : Bool :=
  let pts := curvePts E
  (lenC E D.a != 0 || lenC E D.b != 0) &&
    S.all (fun P => P ∈ pts) && pts.all fun Q => localOrder E D Q == S.count Q

/-- `divisorExact` on a prover output; `false` on `none`. -/
def msgExact {k : ℕ} (out : Option (MsgC E.q k)) (S : List (ZMod E.q × ZMod E.q)) : Bool :=
  match out with
  | some o => divisorExact E ⟨o.a, o.b⟩ S
  | none => false

/-! ## Sanity checks on `y² = x³ − x` over `F₂₃` -/

private abbrev E23 : ECSetup := Tests.CurveFixtures.E23

private abbrev F := ZMod E23.q

private def D (a b : List F) : CoordRingEltC E23.q := ⟨⟨a⟩, ⟨b⟩⟩

-- A nonzero constant: order `0` everywhere, divisor `0`.
#guard (curvePts E23).all fun Q => localOrder E23 (D [5] []) Q == 0
#guard divisorExact E23 (D [5] []) []
-- The zero element is rejected.
#guard !divisorExact E23 (D [0] [0]) []

-- Vertical line `x − 2` at `±(2, 11)`: order `1` each.
#guard localOrder E23 (D [-2, 1] []) (2, 11) = 1
#guard localOrder E23 (D [-2, 1] []) (2, 12) = 1
#guard divisorExact E23 (D [-2, 1] []) [(2, 11), (2, 12)]
-- Vertical line `x` at the 2-torsion point `(0, 0)`: order `2`.
#guard localOrder E23 (D [0, 1] []) (0, 0) = 2
#guard divisorExact E23 (D [0, 1] []) [(0, 0), (0, 0)]
-- `y` vanishes simply at the three 2-torsion points.
#guard divisorExact E23 (D [] [-1]) [(0, 0), (1, 0), (22, 0)]

-- Tangent `y − 1` at `(10, 1)` (slope `0`): order `2` there, `1` at `(3, 1)`.
#guard localOrder E23 (D [-1] [-1]) (10, 1) = 2
#guard divisorExact E23 (D [-1] [-1]) [(10, 1), (10, 1), (3, 1)]
-- Tangent `y − 10x + 8` at `(3, 22)`: order `2` there, `1` at `(2, 12)`.
#guard localOrder E23 (D [8, -10] [-1]) (3, 22) = 2
#guard divisorExact E23 (D [8, -10] [-1]) [(3, 22), (3, 22), (2, 12)]
-- Flex tangent `y − 12x + 13` at `(2, 11)`: order `3`.
#guard localOrder E23 (D [13, -12] [-1]) (2, 11) = 3
#guard divisorExact E23 (D [13, -12] [-1]) [(2, 11), (2, 11), (2, 11)]

/-- `(x − 2)·(y − 12x + 13)`: divisor `4·(2, 11) + (2, 12) − 5·(O)`. -/
private def vertTimesFlex : CoordRingEltC E23.q :=
  CoordRingEltC.mul E23.curveA E23.curveB (D [-2, 1] []) (D [13, -12] [-1])

-- Multiplicity across `±P` is seen: the swapped support fails.
#guard localOrder E23 vertTimesFlex (2, 11) = 4
#guard localOrder E23 vertTimesFlex (2, 12) = 1
#guard divisorExact E23 vertTimesFlex [(2, 11), (2, 11), (2, 11), (2, 11), (2, 12)]
#guard !divisorExact E23 vertTimesFlex [(2, 11), (2, 12), (2, 12), (2, 12), (2, 12)]

end Tests.DivisorOracle
