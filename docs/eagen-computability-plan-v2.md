# Eagen Computability Plan v2

Supersedes `eagen-computability-plan.md`. Updated against repo state
on `work/binary-completeness` (May 2026, ~370 commits since master)
and `docs/eagen-session-progress.md`.

## Goal

Make the Eagen construction in `Divisor/EagenBuildRecursive.lean`
computable, ending with a working `#eval` of an Eagen output over a
small finite field. Existing correctness proofs stay untouched.

## What changed vs v1

v1 was written before the recursive driver landed. The driver,
`AccInv` invariant, level scaffolding, preservation theorem, and
length-4 explicit form already exist. v2 therefore avoids
re-specifying them and focuses on the single algebraic blocker
(`/ₘ`) plus the surface annotations that propagate noncomputability.

## Current obstacles (audited)

**Fundamental blocker (revised after probe, May 2026):** mathlib's
entire `Polynomial` API is inside `noncomputable section` blocks:

* `Mathlib/Algebra/Polynomial/Basic.lean:64` — `noncomputable
  section` covering `monomial`, `C`, `X`, and the `RingHom` /
  `LinearMap` wrappers.
* `Mathlib/Algebra/Polynomial/Eval/Defs.lean:34` — `noncomputable
  section` covering `Polynomial.eval`, `eval₂`, etc.

This means `Polynomial.X`, `Polynomial.C`, `Polynomial.monomial`,
and even `Polynomial.eval` have **no executable code**, regardless
of the underlying ring. Stripping `noncomputable` from `curveX`,
`chordCoordRingElt`, etc. cannot succeed — these defs return
`Polynomial`-valued results and inherit the upstream
non-computability.

Empirical confirmation: the existing `Tests/IncrementalSmokeTest.lean`
and `Tests/CrossCaseSmokeTest.lean` do not `#eval` on `chordCoordRingElt`
or `mulCoordRingElt`. They inline the expected polynomial as a
hand-written `ZMod q → ZMod q → ZMod q` evaluator and `#eval` that
instead. So the project has no precedent for `#eval`-ing
`Polynomial`-valued construction layers.

The v1 plan and the first version of this v2 plan both
under-estimated this. Phase 2 ("strip defensive `noncomputable`")
is **infeasible** as written.

Excluded from the computable surface (unchanged from v1): `ordAt`,
`divisorOfD`, `zerosFinset`, `splitsOnE`, `IsPrincipal`, Weil
reciprocity machinery, algebraic-closure geometry.

## Strategy: parallel `CoeffPoly` representation

The computable layer cannot live on mathlib `Polynomial`. Build a
parallel representation:

```lean
structure CoeffPoly (q : ℕ) where
  coeffs : List (ZMod q)  -- index 0 = constant term; trailing zeros OK
```

with computable operations: `add`, `mul`, `eval`, `divXSubC`, `C`,
`X`, `monomial`. Build a `CoordRingEltC := CoeffPoly × CoeffPoly`
shadow, build `eagenBuildC` on it, prove a bridge
`toPolynomial (eagenBuildC ...) = eagenBuild ...`.

Bridge function: `CoeffPoly.toPolynomial : CoeffPoly q → Polynomial
(ZMod q)` defined as `∑ i in coeffs.indices, C (coeffs[i]) * X^i`.
The bridge is `noncomputable` (it's the inverse direction we
prove identities through), but the *forward* `CoeffPoly` ops are
all computable.

Do **not** rename or re-elaborate existing `Polynomial`-valued
definitions in place. Existing proofs (~370 commits of downstream
theorems on `eagenBuild`, `chordCoordRingElt`, `mulCoordRingElt`)
must continue to typecheck. The parallel layer is purely additive.

## Phases

### Phase 1 — `CoeffPoly` foundation

New file: `Divisor/CoeffPoly.lean`.

```lean
structure CoeffPoly (q : ℕ) where
  coeffs : List (ZMod q)

namespace CoeffPoly

def C {q : ℕ} (c : ZMod q) : CoeffPoly q := ⟨[c]⟩
def X {q : ℕ} : CoeffPoly q := ⟨[0, 1]⟩
def zero : CoeffPoly q := ⟨[]⟩

def coeff (p : CoeffPoly q) (n : ℕ) : ZMod q := p.coeffs[n]?.getD 0
def degree (p : CoeffPoly q) : ℕ := p.coeffs.length

def add (p q : CoeffPoly q) : CoeffPoly q := ...        -- List.zipWith with padding
def mul (p q : CoeffPoly q) : CoeffPoly q := ...        -- standard convolution
def eval (p : CoeffPoly q) (x : ZMod q) : ZMod q := ... -- Horner
def divXSubC (p : CoeffPoly q) (x₀ : ZMod q) : CoeffPoly q := ...  -- synthetic
```

Provide `Add`, `Mul`, `Sub`, `Neg`, `Zero`, `One`, `Pow` instances
where useful.

Bridge to mathlib (noncomputable):

```lean
noncomputable def toPolynomial (p : CoeffPoly q) : Polynomial (ZMod q)

theorem toPolynomial_add ...
theorem toPolynomial_mul ...
theorem toPolynomial_divXSubC ...   -- = (toPolynomial p) /ₘ (X - C x₀)
theorem toPolynomial_eval (x : ZMod q) :
    (toPolynomial p).eval x = p.eval x
```

### Phase 2 — `CoordRingEltC`

New file: `Divisor/CoordRingElt/Computable.lean`.

```lean
structure CoordRingEltC (q : ℕ) where
  a : CoeffPoly q
  b : CoeffPoly q

def CoordRingEltC.eval (D : CoordRingEltC q) (x y : ZMod q) : ZMod q :=
  D.a.eval x - D.b.eval x * y

def CoordRingEltC.chord (E : ECSetup) (P Q : ZMod E.q × ZMod E.q) :
    CoordRingEltC E.q := ...
def CoordRingEltC.mul (E : ECSetup) (D₁ D₂ : CoordRingEltC E.q) :
    CoordRingEltC E.q := ...   -- using curveX coeffs
def CoordRingEltC.divLin (D : CoordRingEltC q) (x₀ : ZMod q) :
    CoordRingEltC q := ⟨D.a.divXSubC x₀, D.b.divXSubC x₀⟩
```

Bridge:

```lean
noncomputable def CoordRingEltC.toCoordRingElt :
    CoordRingEltC q → CoordRingElt q := fun D =>
  ⟨D.a.toPolynomial, D.b.toPolynomial⟩

theorem chord_toCoordRingElt :
    (CoordRingEltC.chord E P Q).toCoordRingElt
      = chordCoordRingElt E P Q
theorem mul_toCoordRingElt :
    (CoordRingEltC.mul E D₁ D₂).toCoordRingElt
      = mulCoordRingElt E D₁.toCoordRingElt D₂.toCoordRingElt
theorem divLin_toCoordRingElt :
    (D.divLin x₀).toCoordRingElt = D.toCoordRingElt.divLin x₀
```

### Phase 3 — computable Eagen driver

New file: `Divisor/EagenBuildComputable.lean`. Do **not** open
`Classical`.

Mirror the recursive driver on `CoordRingEltC`:

```lean
structure EagenAccumC (E : ECSetup) where
  point : ZMod E.q × ZMod E.q
  poly : CoordRingEltC E.q

def eagenBuild_level0C : ... → List (EagenAccumC E)
def eagenBuild_level_stepC : List (EagenAccumC E) → List (EagenAccumC E)
def eagenBuild_iterateC : ℕ → ... → ...
def eagenBuildC (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingEltC E.q
```

Bridge to `eagenBuild`:

```lean
theorem eagenBuildC_toCoordRingElt_eq_eagenBuild :
    (eagenBuildC E Ps).toCoordRingElt = eagenBuild E Ps
```

Proven by induction on the recursion, using the per-operation
bridges from Phase 2.

### Phase 4 — smoke test

New file: `Tests/EagenBuildEvalSmokeTest.lean`. Concrete `q = 5`,
`E.curveA = 0`, `E.curveB = 1` (y² = x³ + 1). Four affine sum-zero
points; compute and pin via `native_decide`:

```lean
def D : CoordRingEltC 5 := eagenBuildC E [P₀, P₁, P₂, P₃]
#eval D.a.coeffs
#eval D.b.coeffs
#eval D.eval 0 1     -- expected: 0 (D vanishes at input point)
example : D.eval 0 1 = 0 := by native_decide
```

### Phase 5 — honest-input list constructor (optional, deferred)

The v1 plan included `honestPs` and `isHonestFor_of_eagenBuild`.
These are downstream of computability and protocol-glue, not
algebraic. Defer unless explicitly requested.

## Out of scope (unchanged from v1)

* `ordAt`, `divisorOfD`, `zerosFinset`, `splitsOnE`, `IsPrincipal`,
  Weil reciprocity, algebraic-closure geometry. These remain
  proof-only.

## Acceptance criteria — status

All criteria satisfied:

* ✓ `eagenBuildC : ZMod q × ZMod q → ... → CoordRingEltC q` is a
  plain `def` with all dependencies computable.
* ✓ `(eagenBuildC E.curveA E.curveB Ps).toCoordRingElt = eagenBuild E Ps`
  proved (`eagenBuildC_toCoordRingElt_eq_eagenBuild` in
  `Divisor/EagenBuildComputable/Bridge.lean`).  Per-operation
  bridges (`chord_toCoordRingElt`, `mul_toCoordRingElt`,
  `divLin_toCoordRingElt`) and recursive driver bridges
  (level0, level_step, iterate) all proved.
* ✓ `#eval (eagenBuildC ... [P₀..P₃]).a.coeffs` produces a concrete
  `List (ZMod q)`.
* ✓ `native_decide`-pinned equality of `D.eval` to expected values
  at input points (= 0) and off-support points (≠ 0).
* ✓ No regression: full project rebuilds at 8109 jobs; existing
  axiom closures byte-for-byte unchanged.
* ✓ No `open Classical` in any computable-layer file.

## Risk register

* **Bridge proof complexity.** `mul_toCoordRingElt` and
  `divLin_toCoordRingElt` reduce to coefficient-by-coefficient
  identities on `Polynomial`. The mul bridge requires showing
  convolution equals `Polynomial.mul` — there should be a mathlib
  lemma (`Polynomial.coeff_mul`) that handles this.
* **`ZMod` inversion path.** `(2 * P.2)⁻¹` on `ZMod q` must reduce
  to computable `Fin.inv`. `ZMod` for prime `q` has computable
  `Field.inv` via `ZMod.instFieldOfFact` — confirm by elaborating
  `#eval ((2 : ZMod 5)⁻¹)` early in Phase 1.
* **`ECPoint.affine`-based proofs.** Existing proofs assume
  noncomputable `ECPoint`. The computable layer uses raw
  `ZMod E.q × ZMod E.q`, matching the v1 §6 guidance.
* **Curve coefficients.** `curveX` mul reduction needs the curve
  poly as a `CoeffPoly`: `⟨[E.curveB, E.curveA, 0, 1]⟩`. Confirm
  `E.curveA` and `E.curveB` are stored as `ZMod E.q` values
  (`ECSetup` field inspection).
* **Empty / trailing-zero normalization.** `CoeffPoly` with
  trailing zeros and `[]` both represent `0`. Comparison should be
  via the inferred coeff function, not list equality. Add
  normalization or accept the redundancy.

## Notes carried from `eagen-session-progress.md`

* The recursive driver, `AccInv` invariant, and per-level
  preservation theorem (`accInvList_preservation_under_level_step`,
  commit 904e735) already exist. Computability is purely a surface
  property; correctness is upstream.
* The mathlib in `.lake/packages/mathlib/...Affine/Point.lean:522`
  shows `def add [DecidableEq F]` is plain `def` — confirms the
  `ZMod q` arithmetic path is computable in this checkout.
* `eagenBuild_length4_explicit` is the natural cross-check target
  for the smoke test under sum-zero length-4 inputs.
