# Concrete `chord_fiber_product`: prototype + assessment

Branch: `geom-polyG-skeleton`
Sketch file: `Divisor/Sketch/ChordFiberProductConcrete.lean`

## Current state

`chord_fiber_product` is declared as

```lean
noncomputable opaque chord_fiber_product
    (E : ECSetup) (lam : ZMod E.q) (D : CoordRingElt E.q) : (ZMod E.q)[X]
```

(in `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`) and pinned by
three axioms:

| Axiom | Where | What it gives |
| --- | --- | --- |
| `chord_fiber_product_eq_normZ_under_split` | `AxiomChordFiberProductEqNormZUnderSplit.lean` | `c · normZ` proportionality on splitting |
| `chord_fiber_product_bar_eq_geom_prod` | `AxiomChordFiberProductBarFactored.lean` | bar-level factored form |
| `chord_sum_eq_chord_fiber_product_logDeriv` | `AxiomChordSumEqChordFiberProductLogDeriv.lean` | trace-of-log-derivative identity |

Downstream consumers (`ChordLogDerivProof.lean`, `GeometricSoundness.lean`,
`WeilReciprocityDescent.lean`) only ever interact with the polynomial through
these three axioms (plus `Polynomial.eval`, `Polynomial.derivative`, and base
change to `Fqbar`).

## Candidate concrete definition (resultant)

The mathematics: `chord_fiber_product` is the function-field norm of `D` for the
extension `F_q(E) / F_q(zLambda lam)`. Concretely, it is the **resultant in the
chord x-variable** of the chord cubic against the D-on-line lift.

Define in `(ZMod E.q)[Z][X]`:
* `chordCubicBiv lam = X³ − λ² X² + (A − 2λZ) X + (B − Z²)`  — outer monic cubic in `X` with coefficients in `(ZMod E.q)[Z]`;
* `DLineBiv lam D    = D.a(X) − D.b(X) (λX + Z)`              — outer poly in `X` of `X`-degree `≤ max(deg a, deg b + 1)`;
* `chord_fiber_product_concrete lam D := Polynomial.resultant chordCubicBiv DLineBiv ∈ (ZMod E.q)[Z]`.

The output ring `(ZMod E.q)[Z]` is the same as `(ZMod E.q)[X]` up to renaming
the indeterminate; `Z` here represents the chord intercept `μ`.

`Polynomial.resultant` lives in `Mathlib.RingTheory.Polynomial.Resultant.Basic`
(in mathlib's tree). Key supporting lemmas:
* `Polynomial.resultant_eq_prod_eval [IsDomain R] (f g : R[X]) (n : ℕ) (hg : g.natDegree ≤ n) (hf : f.Splits) : resultant f g f.natDegree n = f.leadingCoeff ^ n * (f.roots.map g.eval).prod`
* `Polynomial.resultant_map_map` for reducing to a base-change.

This gives, on evaluation at `μ`:
`chord_fiber_product_concrete.eval μ = ∏_{i=0,1,2} D.eval(x_i, λ x_i + μ)`
when the chord cubic at `μ` splits — exactly the fibre-product reading.

## The obligations against the candidate

The sketch file states each obligation as a `theorem … := by sorry`.

| # | Obligation | Difficulty | Notes |
| --- | --- | --- | --- |
| 1 | `chord_fiber_product_concrete_eval` | **Plumbing** | `resultant_map_map` for the eval homomorphism `Polynomial.X ↦ μ`. ~30 LOC of normalisation. |
| 2 | `chord_fiber_product_concrete_eval_eq_prod_split` | **Plumbing** | Direct `Polynomial.resultant_eq_prod_eval`; chord cubic is monic (LC = 1). Requires the `Splits` hypothesis. |
| 3a | `chord_fiber_product_concrete_bar_eval` | **Plumbing** | Base-change the resultant to `Fqbar`, then specialise the intercept `μ`. This is two `resultant_map_map` applications. |
| 3b | `chord_fiber_product_concrete_bar_eval_eq_prod` | **Plumbing** | Same as 2 over `Fqbar`, where `Splits` is automatic, using 3a as the input. |
| 4 | `chord_fiber_product_concrete_ne_zero` | **Done** | Proved by evaluating over `Fqbar`, choosing an intercept outside the finite set `gd.support.image (zLambdaBar E lam)`, and using the resultant product formula. |
| 5 | `chord_fiber_product_concrete_bar_eq_geom_prod` | **Hard math (deepest)** | The divisor-of-norm identity `div(N(D)) = π_*(div D)` for the chord projection. Needs the link `mult_at_μ (resultant) = ∑_{Q : zLambdaBar Q = μ} gd.mult Q`, i.e., per-place inertial degree of the chord cover. Project's existing `geomLocalOrder` and `IsGeometricZeroMultiplicity` give one direction; the multiplicity-summing direction needs new machinery. **No mathlib analogue.** |
| 6 | `chord_fiber_product_concrete_eq_normZ_under_split` | **Plumbing** | Once obligation 5 is in hand, this is a "match factored forms over `Fqbar`, scalar descends to `ZMod E.q`" argument. |
| 7 | `chord_fiber_product_concrete_logDeriv` | **Medium math** | Logarithmic derivative of `∏_i D(x_i(μ), λx_i(μ) + μ)` via product rule + implicit-function differentiation of the chord cubic. The cancellation that produces the `logDerivTerm` formula is the substantive step; `hDen` rules out the cusp where the implicit-function argument fails. Mathlib has `Polynomial.derivative_*` and `aeval` machinery for the formal-derivative side; the chain rule is `Polynomial.derivative_comp` plus algebra. |

## Plumbing / math split

**Pure plumbing (would land within a session each, given the right mathlib
identifiers):** 1, 2, 3a, 3b, 6.

**Medium math (sketchable in 1–2 days, with care):** 7.

**Hard math (the actual proof obligation, needs new infra):** 5.

Obligation 5 is the **only** one whose hardness comes from genuinely new
mathematics that has no mathlib analogue. Specifically: the divisor-of-norm
formula relates the `μ`-multiplicity of `chord_fiber_product` at `μ_0` to the
sum of `D`'s geometric multiplicities `gd.mult Q` over geometric points `Q`
with `zLambdaBar Q = μ_0`. The argument breaks into two halves:

* **Lower bound** (`mult_at μ_0 ≥ ∑ Q gd.mult Q`): for each geometric `Q` with
  `zLambdaBar Q = μ_0`, every chord through `Q` (one for each `μ` near `μ_0`)
  hits `Q` with the prescribed local order; by `geomLocalOrder` and the
  resultant's `mult_root` semantics, the contribution of `Q` to the `μ`-root
  multiplicity is at least `gd.mult Q`. The "for each μ near μ_0" step is
  delicate but reduces to standard residue-disc bookkeeping.

* **Upper bound** (`mult_at μ_0 ≤ ∑ Q gd.mult Q`): the `μ`-multiplicity is
  bounded by the algebraic-degree contribution from the resultant, which after
  Hasse + the `gd` accounting (`accounting_le_degE`) matches the lower bound.
  The accounting is already in the project; the multiplicity-counting step
  reduces to the Sylvester-matrix expansion of the resultant.

Both halves use only finite-field algebraic geometry; nothing transcendental.

## Replacement plan, if undertaken

1. Land the sketch file `Divisor/Sketch/ChordFiberProductConcrete.lean` (compiles
   with the remaining sketch sorries — ~90 minutes of mathlib-API alignment).
2. Discharge obligations 1, 2, 3a, 3b (plumbing only; resultant_map_map +
   resultant_eq_prod_eval) — **done**.
3. Discharge obligation 4 via `bar_eval_eq_prod` at a generic `μ` — **done**.
4. Discharge obligation 7 via product-rule + implicit-function chain — **1–2
   days** (with care around the cusp / non-degeneracy).
5. Discharge obligation 5 — **3–5 days** (the new infra: per-place
   multiplicity-summing for the resultant of `chord cubic` against
   `D-on-line`).
6. Discharge obligation 6 (Fqbar-factored-forms-match descent) — **half a day**.
7. Replace the `opaque` declaration of `chord_fiber_product` by the concrete
   definition; replace each axiom invocation by the now-proven theorem; remove
   the three axiom files.

Total: roughly **1 working week** of focused Lean for one practitioner. The bulk
sits in step 5.

## Counter-suggestion: keep the axiom, narrow it

Obligation 5 is the only genuine math, and its content (`div(N(D)) = π_*(div D)`)
is a textbook fact (Stichtenoth Prop 3.1.9 + Thm 3.7.1, exactly as the existing
axiom citation reads). The question is whether the project wants to *carry*
this proof inside Lean or *cite* it as an axiom.

A mid-point: define `chord_fiber_product` concretely (the resultant), prove
obligations 1–4, 6, 7 by construction, and leave a single narrower axiom

```lean
axiom chord_fiber_product_concrete_bar_eq_geom_prod  -- (formerly 5)
```

This is **strictly weaker** than the current `chord_fiber_product_bar_eq_geom_prod`
(it talks about a concrete polynomial, not an opaque one) and removes the
proportionality / log-derivative axioms entirely. The dependency graph
collapses from "three axioms + opaque" to "one axiom + concrete definition".

## Sketch file build status

`lake build Divisor.Sketch.ChordFiberProductConcrete` **passes**.

Discharge progress:
* **Obligation 1 (`chord_fiber_product_concrete_eval`): DONE.** Discharge via
  two helper lemmas (`chordCubicBiv_map_evalRingHom`,
  `DLineBiv_map_evalRingHom`) on top of `Polynomial.resultant_map_map`. About
  60 LOC, no `sorry`s.
* **Obligation 2 (`chord_fiber_product_concrete_eval_eq_prod_split`): DONE.**
  Discharge via `Polynomial.resultant_eq_prod_eval`, plus monicity/degree
  facts for `intersectionPoly`.
* **Obligation 3a (`chord_fiber_product_concrete_bar_eval`): DONE.**
  Discharge by mapping the resultant to `Fqbar` and then specialising `μ`,
  both via `Polynomial.resultant_map_map`.
* **Obligation 3b (`chord_fiber_product_concrete_bar_eval_eq_prod`): DONE.**
  Discharge via `Polynomial.resultant_eq_prod_eval` over `Fqbar E`, using
  `IsAlgClosed.splits` plus degree/leading-coefficient lemmas for
  `chordCubicBar`.
* **Obligation 4 (`chord_fiber_product_concrete_ne_zero`): DONE.**
  Discharged by the finite-bad-intercept argument over `Fqbar E`, using
  `exists_geometric_zero_support`, `exists_geometricDivisorData_of_support`,
  `Infinite.exists_notMem_finset`, and
  `chord_fiber_product_concrete_bar_eval_eq_prod`.
* Obligations 5, 6, 7: still `sorry`.

Next planned: support-level zero-locus bridge for obligation 5, then obligation
6 (factored-forms-match descent — depends on 5).

## Summary for codex

* Concrete candidate: **resultant of chord cubic against D-on-line lift**
  (well-posed, mathlib-friendly).
* 7 top-level obligations are stated, with obligation 3 split into two
  plumbing lemmas; only obligations 5, 6, and 7 remain. Obligation 5 is the
  genuine new mathematics (`bar_eq_geom_prod`).
* If the project keeps the new mathematics axiomatic, the construction
  collapses to **one axiom + concrete definition** (vs the current three
  axioms + opaque), which is a clean reduction in surface area.
