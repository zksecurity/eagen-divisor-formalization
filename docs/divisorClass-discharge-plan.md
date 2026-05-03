# Discharge plan for `divisorClass_isPrincipal_of_not_const_unit`

The headline target is

```lean
axiom CoordRingElt.divisorClass_isPrincipal_of_not_const_unit
    (D : CoordRingElt E.q) (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hSplit : splitsOnE E D)
    (_hNotConstUnit :
      ¬ ∃ c : ZMod E.q, c ≠ 0 ∧ D.a = Polynomial.C c ∧ D.b = 0) :
    ∃ I : (FractionalIdeal _ _)ˣ, I.val.IsPrincipal ∧
      Additive.toMul (divisorClass E (divisorOfD E D) _) = ClassGroup.mk I
```

## Stage 1 (landed in `Divisor/CoordinateRingBridge.lean`)

Bridge between the project's `CoordRingElt` and mathlib's affine
`CoordinateRing`:

* `CoordRingElt.toBivar D : (ZMod q)[X][Y] := C D.a − C D.b · Y`
* `CoordRingElt.toCoordinateRing E D : E.toW.toAffine.CoordinateRing
   := CoordinateRing.mk E.toW.toAffine D.toBivar`
* `D.toBivar.evalEval x y = D.eval x y`
* `D.toCoordinateRing E ≠ 0` whenever `(D.a, D.b) ≠ (0, 0)`
* `D.toCoordinateRing E ∈ XYIdeal x (C y) ↔ D.eval x y = 0` for
  `(x, y) ∈ E.points`

These give the algebraic-geometry side of the project's vanishing
condition.

## Stage 2 (next): local-order ↔ recursive `ordAt`

The project's `ordAt E D P` (recursive: 2-torsion closed-form,
non-2-torsion lone/twin trichotomy) must agree with the localization
valuation of `D.toCoordinateRing` at the prime `XYIdeal x y`.

Lemmas to land:

1. **Non-vanishing case** (easiest):
   ```lean
   theorem ordAt_eq_zero_of_eval_ne_zero
       (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
       (hP : P ∈ E.points) (hD : D.eval P.1 P.2 ≠ 0) :
       ordAt E D P = 0
   ```
   On the project side this reduces to definition. On the
   algebraic-geometry side it follows from
   `toCoordinateRing_mem_XYIdeal_iff` plus the unit-iff-not-in-ideal
   characterisation of localizations at prime ideals.

2. **2-torsion closed form**: for `P = (x₀, 0)` with `y₀ = 0`,
   `ordAt = min(2 · rootMult x₀ a, 2 · rootMult x₀ b + 1)`.
   The local uniformizer is `Y`; the matching is via
   `(X − x₀) = Y² · u(x)` in the local ring (Silverman AEC II.1).

3. **Non-2-torsion lone**: norm identity
   `ord_P(D) + ord_{P^σ}(D) = rootMult x₀ (normPoly E D)`.
   When `D(P^σ) ≠ 0`, this collapses to
   `ord_P(D) = rootMult x₀ (normPoly E D)`.

4. **Non-2-torsion twin**: recursive step. If `D(P) = D(P^σ) = 0`
   then `(X − x₀)` divides both `a` and `b`, so
   `D = (X − x₀) · D'` and `ord_P(D) = 1 + ord_P(D')`. Recurse.

## Stage 3 (next): pole at infinity

Identify the project's `−natDegree(normPoly E D)` slot at infinity
with the standard pole order. Use the norm relation
`(D.toCoordinateRing) · (D̄.toCoordinateRing) = normPoly E D` in the
coordinate ring (where `D̄ = a + b·Y`), plus the rank-2 freeness over
`F_q[X]` to read off the pole order from `natDegree(normPoly)`.

## Stage 4: principal-class conclusion

Construct the principal fractional ideal
`(D.toCoordinateRing E) ∈ FractionalIdeal _ _` (nonzero by Stage 1's
`toCoordinateRing_ne_zero`). Show its class equals
`divisorClass E (divisorOfD E D)` using Stages 2-3 plus
`Point.toClass`'s additivity.

Mathlib API expected to slot in:

* `FractionalIdeal.spanSingleton`
* `ClassGroup.mk_eq_one_iff` (principal ↔ class = 1)
* `Point.toClass`, `Point.toClass_eq_zero` (already used in
  `Divisor/OrdP/PrincipalClass.lean`)

## Notes

* The `splitsOnE` hypothesis ensures every root of `normPoly E D` has
  both sheets `(x, y)` and `(x, -y)` over `F_q` — i.e., no
  fiber-irrational points contribute. This is required for the
  rationality of the geometric divisor.
* The `not_const_unit` hypothesis excludes the trivial case
  `D = C c` (already a separate theorem). In that case
  `divisorOfD E D = 0` and the existential is satisfied with
  `I = 1`.
* The recursive `ordAt` is well-founded by the strict drop in
  `(D.a.natDegree, D.b.natDegree)` when twin-divided by `(X − C x₀)`;
  this matches the local-ring induction on the uniformizer.
