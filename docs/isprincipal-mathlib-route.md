# `IsPrincipal` mathlib-native route

Investigation of replacing the `ordAt_divisor_isPrincipal` /
`principal_divisor_iff` axiom pair with concrete content. Branch:
`worker-4/isprincipal-investigation`.

## What the two axioms produce, jointly

The codebase consumes the pair through a single endpoint:
`Divisor.ordAt_group_sum_zero_under_split` in
`Divisor/OrdP/LocalRing.lean` (~line 1004), which feeds clause (v) of
`exists_divisor_multiplicity_proved`. That endpoint says: under
`splitsOnE E D`,

```
ECPoint.weightedSum E E.points
  (fun P => ECPoint.nsmul E (ordAt E D P) (ECPoint.affine E P.1 P.2)) = 0
```

The current proof chain is:

1. `ordAt_divisor_isPrincipal E D _ _ : IsPrincipal E (divisorOfD E D)`
   (axiom — opaque target).
2. `(principal_divisor_iff E (divisorOfD E D) hFinSup).mp` extracts
   `(∑ coeffs = 0) ∧ (weightedSum = 0)`.
3. Take the second conjunct.

The whole point of the two-axiom dance is to expose a single
group-sum-zero fact about `divisorOfD E D` to `ordAt`'s downstream
clients. `IsPrincipal` is opaque (`Divisor/DefsPre.lean:275`) and only
mentioned via the `iff`.

## Two key facts that change the picture

### (a) `ECPoint E` *is* mathlib's `WeierstrassCurve.Affine.Point`

```lean
abbrev ECPoint (E : ECSetup) : Type := E.toW.toAffine.Point
-- Divisor/DefsPre.lean:194
```

There is no quotient, type wrapper, or transport between the project's
group-law type and mathlib's. The project also defines
`ECPoint.zsmul / nsmul / weightedSum` as defeq aliases for mathlib's
`n • p` and `Finset.sum` (`Divisor/Defs.lean:24,68,72`).

### (b) Mathlib already has the divisor-class injection

`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` (line ~592)
defines

```lean
noncomputable def toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)
```

with `toClass 0 = 0`, `toClass (some h) = ClassGroup.mk (XYIdeal' h)`,
and proves

* `toClass_injective` (line ~635)
* `toClass_eq_zero P : toClass P = 0 ↔ P = 0`

Specialised at `W = E.toW.toAffine`, this is precisely the
addition-preserving injection `ECPoint E ↪ Pic(F_q[E])` — i.e. the
algebraic-geometry side of Silverman III.3.4 / III.3.5 already
formalised in mathlib for `Pic` of the affine coordinate ring.

## The mathlib-native replacement

### Concrete `IsPrincipal`

Define, replacing the opaque:

```lean
/-- Sum of `coeffs P • toClass P` in `Pic(F_q[E])`. -/
noncomputable def divisorClass
    (E : ECSetup) (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs)) :
    Additive (ClassGroup E.toW.toAffine.CoordinateRing) :=
  ∑ P ∈ h.toFinset, (coeffs P) • toClass P

/-- A divisor is principal iff its class in `Pic(F_q[E])` is trivial. -/
def IsPrincipal' (E : ECSetup) (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs)) : Prop :=
  divisorClass E coeffs h = 0
```

This is *honest*: `Pic(F_q[E])` of the affine coordinate ring is the
divisor class group of `E \ {O}`, which (classically) is `Pic⁰(E)`
quotiented by the basepoint, and equals zero on a divisor iff the
divisor is `div(f)` for some `f ∈ F_q(E)^×`. (For finite fields the
class group is finite but generally non-trivial; the concrete
group law is exactly the Silverman III.3.4 `Pic⁰(E) ≅ E` isomorphism.)

### Recovering `principal_divisor_iff` as a theorem

For finite-support `coeffs : ECPoint E → ℤ`,

```lean
theorem principal_divisor_iff'
    (E : ECSetup) (coeffs : ECPoint E → ℤ)
    (h : Set.Finite (Function.support coeffs)) :
    IsPrincipal' E coeffs h ↔
      (∑ P ∈ h.toFinset, coeffs P = 0) ∧
      (ECPoint.weightedSum E h.toFinset
        (fun P => ECPoint.zsmul E (coeffs P) P) = 0)
```

is **plumbing only**: the (←) direction goes by computing
`divisorClass = 0` using `toClass`'s additivity plus the fact that
`toClass 0 = 0` (so the basepoint contribution disappears) plus
`toClass_injective` to translate the `weightedSum` condition. The
(→) direction uses the same translation in reverse, with the degree
condition recovered from `Pic(F_q[E])` carrying a degree map
(degree-zero-on-affine forces the `coeffs(0)` contribution to balance
the rest). All of this is straightforward AddMonoidHom algebra.

### What `ordAt_divisor_isPrincipal` becomes

The remaining content is the single algebraic-geometry fact:

> For `D ∈ F_q[E]^×` (i.e. `CoordRingElt E.q` with `¬ (D.a = 0 ∧ D.b = 0)`)
> with `splitsOnE E D`, the divisor `divisorOfD E D` has trivial class
> in `ClassGroup E.toW.toAffine.CoordinateRing`.

Equivalently (via the iff above): `ordAt`'s group sum is zero on
`E.points`. So the *axiomatic surface* hasn't shrunk — but the iff
becomes a theorem and the remaining axiom is now phrased in fully
concrete mathlib language (a `Finset.sum` in
`Additive (ClassGroup _)`).

## Plumbing vs. genuine algebraic-geometry work

### Pure plumbing (a few hundred LOC)

* Concrete `IsPrincipal'` definition via `toClass`.
* `principal_divisor_iff'` as a theorem from `toClass_injective` +
  `AddMonoidHom.map_sum`. The basepoint-degree handling is the only
  non-trivial step; the rest is `simp`-grade rewriting.
* Replumbing `Divisor/DivisorPrincipal.lean` to use `IsPrincipal'`
  (its consumer already extracts the two conjuncts; switching to the
  concrete iff is a near-rename).
* `Divisor/OrdP/LocalRing.lean §7` adapted: `divisorOfD E D` becomes
  the class in `ClassGroup _`, and `ordAt_group_sum_zero_under_split`
  is the unwrapping of a `divisorClass = 0` hypothesis.

### Genuine algebraic-geometry formalisation (~2-3 weeks, see comment block in `Divisor/OrdP/LocalRing.lean:864`)

* The replacement axiom `ordAt_divisor_classZero E D ... : divisorClass E (divisorOfD E D) _ = 0`
  is **the mathematical content**. Discharging it as a theorem
  requires:
  1. Showing the project's recursive `ordAt` (defined via
     `ordAt_twoTorsion` / `ordAt_nonTwoTorsion` in
     `Divisor/OrdP/Uniformizer.lean`) agrees with the standard
     localization-based ord_P at the prime `XYIdeal x y`. This is
     where Silverman AEC II §1's uniformizer construction would land
     in Lean. This step is the bulk of the work — it's a per-prime
     calculation matching the recursive recipe to mathlib's
     `IsLocalization.AtPrime` / `Submodule.IsPrincipal` machinery.
  2. The principal-ideal lemma:
     `ClassGroup.mk (Ideal.span {algebraMap _ _ D}) = 0` for any
     `D ≠ 0` in `CoordinateRing`. This is `ClassGroup.mk_principal`
     and should be quotable from mathlib.
  3. Connecting `divisorClass (divisorOfD E D)` to
     `ClassGroup.mk (Ideal.span {D})`. This is a finite-support sum
     decomposition: by step 1, the divisor of the principal ideal is
     `Σ ord_P(D) (P) − natDeg(N(D)) (O)`, which is `divisorOfD E D`
     under `splitsOnE`.

  Step 1 is the genuine algebraic-geometry seam. Steps 2 and 3 are
  bridge lemmas — non-trivial but mathlib-quotable.

* Without `splitsOnE`, mathlib's class lives over `K̄`, and the
  F_q-rational restriction needs the Galois-descent argument cited
  in `Divisor/Axioms/AxiomPrincipalDivisorIff.lean`. Confining the
  whole replacement to the `splitsOnE` branch (which is the only
  branch the headline theorems consume) avoids that detour.

## Sufficiency for `ma_extractable` / `ip_knowledge_sound`

The headline path consumes `ordAt_divisor_isPrincipal` and
`principal_divisor_iff` exclusively through
`ordAt_group_sum_zero_under_split` (clause (v) of
`exists_divisor_multiplicity_proved`). The replacement
`ordAt_divisor_classZero` plus the iff-theorem produces the same
conclusion via the same chain; no headline-theorem statement changes.

`Divisor/DivisorPrincipal.lean`'s use of `principal_divisor_iff.mpr`
in `IsPrincipal_dCoeffs_of_β` becomes an `Iff.mpr` of the proved
biconditional and is mechanical to update.

## Recommendation

Two-stage plan:

**Stage A — plumbing (1-3 days).**  Land the concrete `IsPrincipal'`
+ the iff-theorem in a side module
(`Divisor/OrdP/IsPrincipalSkeleton.lean`, see the companion file in
this branch). Keep the existing `IsPrincipal` opaque and the two
axioms in place; gate the new path behind a short bridge so consumers
can opt in. The skeleton in this branch already factors the iff
through mathlib's `toClass` directly — no new axioms needed for that
half.

**Stage B — algebraic-geometry seam (~2-3 weeks).**  Discharge the
single remaining `ordAt_divisor_classZero` axiom by formalising the
recursive-ord ↔ localization-ord agreement. This is the genuine
algebraic-geometry work; the rest is bookkeeping. Once it lands,
`IsPrincipal` becomes fully theorem-backed, both axioms come out of
the closure, and the headline theorems' axiom list drops two entries.

The risk surface in Stage A is essentially zero (it's a refactor
behind an Iff). Stage B is bounded — the per-prime `ordAt`
calculation is finite and explicit; mathlib has all the surrounding
infrastructure (`CoordinateRing`, `XYIdeal`, `ClassGroup`,
`PicardGroup`); the only missing piece is the bridge.

## Files referenced

* `Divisor/DefsPre.lean:194,275` — `ECPoint`, opaque `IsPrincipal`.
* `Divisor/Axioms/AxiomPrincipalDivisorIff.lean:48` — the iff axiom.
* `Divisor/OrdP/LocalRing.lean:785-1035` — Section 7 (the consumers).
* `Divisor/OrdP/Uniformizer.lean:92-160` — recursive `ordAt`.
* `Divisor/DivisorPrincipal.lean` — the wrapper consumer.
* `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:585-640` —
  `toClass`, `toClass_injective`, `toClass_eq_zero`.
* `Mathlib/RingTheory/PicardGroup.lean:850` — `ClassGroup.equivPic`.
