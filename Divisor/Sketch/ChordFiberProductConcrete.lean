/-
  Divisor/Sketch/ChordFiberProductConcrete.lean

  PROTOTYPE / HISTORICAL SANDBOX — concrete candidate for
  `chord_fiber_product`.

  This file predates the production discharge of the chord-fiber
  bridge. Today, `chord_fiber_product` is a plain `noncomputable def`
  (equal to the resultant candidate `chord_fiber_product_concrete`;
  see `Divisor/Bridges/ChordFiberProductNormZ.lean`),
  and the statements this sandbox sketches are theorem-backed on the
  production side (`Divisor/Bridges/ChordFiberProductEqNormZUnderSplit.lean`
  and `Divisor/Bridges/ChordSumEqChordFiberProductLogDeriv.lean`),
  resting only on the named axioms pinned in
  `Tests/AxiomClosurePin.lean`.

  Sorry-free delegations to production theorems, kept as
  documentation of the proof plan. The geometric lemmas consumed by
  production live downstream in
  `Divisor/Sketch/ChordFiberGeometry.lean`. -/
import Divisor.Bridges.ChordFiberProductBarFactored
import Divisor.ChordFiberMultiplicativity

open Polynomial

namespace Divisor.Sketch

variable (E : ECSetup)

/-! ## Obligation sketches against the concrete candidate

Each `theorem` below mirrors a downstream consumer of
`chord_fiber_product`, delegating to the production theorems; the
surrounding comments record the mathematical plan. -/

/-- **Narrow hard lemma: chord-projection multiplicity accounting.**

This is the citable mathematical core of the bar-factorisation statement:
the multiplicity of a chord intercept `z` as a root of the concrete
resultant equals the sum of the local multiplicities of the geometric
`D`-zeros in the fibre `zLambdaBar = z`.

Mathematically this is the divisor-of-norm identity
`div(N_{F_qbar(E)/F_qbar(z)} D) = π_*(div D)` for the chord projection
`π = zLambdaBar`, with the right-hand side written fibrewise. The direct
pushforward citation is Stacks 02RS; Stichtenoth Prop. 3.1.9 and
Thm. 3.1.11 provide supporting function-field divisor accounting. -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q :=
  -- Discharged via the production theorem in
  -- `AxiomChordFiberProductBarFactored.lean`, using divisibility plus
  -- weighted-Sylvester natDegree.
  Divisor.chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber E D lam hD gd

/-! ### Discharge plan via the multiplicity squeeze helper

The above multiplicity equality can be discharged from two strictly
weaker pieces using `Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`:

1. **Fibrewise divisibility** (the local divisor-of-norm content):
   for each `z` in the fibre image, `(X − C z)^(fibre sum) ∣ p`.

2. **Global natDegree bound**: `p.natDegree ≤ (normPoly E D).natDegree`,
   which by `GeometricDivisorData.mult_sum_eq_normPoly_natDegree`
   transports to `p.natDegree ≤ ∑ Q ∈ gd.support, gd.mult Q` (the
   shape required by the helper).

Combined with the existing root-set theorem
`chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image`, the
helper's squeeze argument forces multiplicity equality at every fibre.
The two stubbed pieces capture *exactly* what's substantive: a local
divisor-of-norm intersection statement (the divisibility), and a
degree count for the chord-projection norm polynomial against the
X-projection norm polynomial.

The natDegree bound has substantial inductive infrastructure already
landed in `Divisor/ChordFiberMultiplicativity.lean`:

* Linear-factor `divLin` recursion via
  `chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step`
  (each twin step adds 2 to both `chord_fiber_product.natDegree` and
  `normPoly.natDegree`).
* General-monic factor extraction via
  `chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_general`
  (taking the resultant natDegree formula
  `Res(chordCubic, p.map C, 3, p.natDegree).natDegree = 2 · p.natDegree`
  as a hypothesis).
* The resultant natDegree formula for any monic `p` is a theorem
  (`resultant_chordCubicBiv_pmap_C_natDegree_of_monic`) via the
  `SplittingField p` lift, so the inductive structure is fully closed
  modulo the gcd-1 base case.
* Inequality form
  `chord_fiber_product_concrete_natDegree_le_normPoly_natDegree_step_monic`
  reduces the bound `(chord_fiber_product D).natDegree ≤ (normPoly D).natDegree`
  to the same statement on `D'` after extracting any monic common
  divisor of `D.a, D.b`.

The remaining substantive gap is the **gcd(D.a, D.b) = 1 base case**
of the natDegree inequality. The recommended Lean route is a
weighted-Sylvester degree bound with `wt(x)=2`, `wt(Z)=3`: each
Sylvester-determinant monomial picks `n = deg_x DLineBiv` entries from
DLine rows and 3 entries from chord-cubic rows, and the weight identity
forces `degZ ≤ w` where `w = max(2 deg a, 2 deg b + 3) = (normPoly).natDegree`.
This avoids any deep function-field theorem and uses only mathlib's
`Matrix.det_apply` + `natDegree_sum_le` + `natDegree_prod_le`. -/

/-- **Stub 1**: fibrewise divisibility for the chord-fibre product.

The `(X - C z)^1` case (equivalently the per-Q `(X - C (zLambdaBar Q))^1`
case for `Q ∈ gd.support`) is covered by the theorem in
`Divisor/ChordFiberProductConcrete.lean` —
`chord_fiber_product_concrete_bar_X_sub_C_pow_one_dvd_of_mem_support_image`
and `chord_fiber_product_concrete_bar_X_sub_C_zLambda_pow_one_dvd_of_mem_support`.
Both follow directly from the existing root-set theorem
`chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image`.

The remaining substantive content is exactly the higher exponents:
when the per-fibre multiplicity sum exceeds 1, the local order of `D` at
each `Q` in the fibre must propagate to the chord-projection norm. This
is the local divisor-of-norm / local-intersection content. -/
theorem chord_fiber_product_concrete_bar_zfiber_pow_dvd
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.X - Polynomial.C z) ^
      (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      ∣ (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E)) :=
  -- Delegates to the production theorem
  -- `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`
  -- (`Divisor/Bridges/ChordFiberDivisibility.lean`).
  Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd E D lam hD gd z

/-! **Stub 2a**: natDegree bound for the chord-fibre product against the
norm polynomial's natDegree.

Mathematically this should be an *equality*, not just `≤`: both
`chord_fiber_product_concrete` and `normPoly` are affine principal-divisor
polynomials of the function `D = a - b·y` under different finite
projections `E → P^1` (chord-projection `z = y - λx` and X-projection),
and both have natDegree equal to the total zero multiplicity of `D` on
the affine part of `E`. Since `D` is regular away from infinity, this
total equals `∑ Q ∈ gd.support, gd.mult Q`, hence
`(normPoly).natDegree` by `mult_sum_eq_normPoly_natDegree`.

Reference: Stacks Project, [Lemma 42.18.1 (Principal divisors and
pushforward)](https://stacks.math.columbia.edu/tag/02RS).

Substantial inductive infrastructure for the equality form is already
landed in `Divisor/ChordFiberMultiplicativity.lean`:

- `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_one` — `p = 1`.
- `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C` — `p = X − C x₀`.
- `resultant_chordCubicBiv_pmap_C_natDegree_of_eq_X_sub_C_pow` — `p = (X − C x₀)^k`.
- `resultant_chordCubicBiv_pmap_C_natDegree_of_splits` — any monic `p`
  splitting over `ZMod E.q` (multiset induction on `p.roots`).

Plus inductive-step combinators
(`chord_fiber_product_concrete_natDegree_eq_normPoly_natDegree_step_*`)
that compose these closed-form results with normPoly's recurrence to
derive `chord_fiber_product.natDegree = normPoly.natDegree` for any D
whose gcd-factor splits over `ZMod E.q`.

Two Lean-tractable proof routes for the *general* (non-splitting) p:
1. Cite the general norm/divisor pushforward as an axiom and
   instantiate it for both projections.
2. Lift the existing splits theorem to `Polynomial.SplittingField p`
   over `ZMod E.q` via `Polynomial.resultant_map_map` and the injective
   algebraMap natDegree preservation. This requires a generic version
   of the splits theorem parametrised over `f : R[X][X]` (not specific
   to `chordCubicBiv`) and a parameterised chord cubic over arbitrary
   commutative ring R.
3. Direct weighted-leading-term resultant analysis with weights
   `wt(T) = 3`, `wt(X) = 2`. Under those weights, the leading part of
   `chordCubicBiv` is `X³ - T²` (weight 6) and the leading part of
   `DLineBiv` matches `normPoly`'s leading-coefficient structure.

Stated as `≤` (rather than `=`) because that is the form the squeeze
helper consumes; the equality itself is not needed for the discharge.

**Discharge plan** (gcd-extraction reduction):

* The mapped natDegree is preserved by `algebraMap (ZMod E.q) (Fqbar E)`'s
  injectivity, so the bound is equivalent to
  `(chord_fiber_product_concrete E lam D).natDegree ≤ (normPoly E D).natDegree`.
* The general-D case reduces in one step to the coprime case via
  `chord_fiber_product_concrete_natDegree_le_normPoly_natDegree_of_coprime_base`
  in `Divisor/ChordFiberMultiplicativity.lean`.
* The remaining substantive content is the coprime base case
  `chord_fiber_product_concrete_natDegree_le_of_coprime` below. -/


/-- **Stub 2a-coprime**: gcd-1 base case for the natDegree bound.
This is the only remaining substantive content for stub 2 after the
gcd-extraction reduction has been applied.

Recommended Lean route: weighted-Sylvester degree bound with
`wt(x)=2`, `wt(Z)=3`. -/
theorem chord_fiber_product_concrete_natDegree_le_of_coprime
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hcop : IsCoprime D.a D.b) :
    (chord_fiber_product_concrete E lam D).natDegree
      ≤ (normPoly E D).natDegree :=
  -- The weighted-Sylvester proof (`Divisor/ChordFiberWeightedDegree.lean`) is
  -- unconditional: it works for any D with `¬(D.a = 0 ∧ D.b = 0)`, with no
  -- coprime hypothesis needed.
  chord_fiber_product_concrete_natDegree_le_normPoly_natDegree E lam D hD

theorem chord_fiber_product_concrete_bar_natDegree_le_normPoly
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((chord_fiber_product_concrete E lam D).map
        (algebraMap (ZMod E.q) (Fqbar E))).natDegree
      ≤ (normPoly E D).natDegree := by
  classical
  -- Strip off the algebraMap (ZMod E.q) → (Fqbar E) lift via injective natDegree preservation.
  rw [Polynomial.natDegree_map_eq_of_injective
        (algebraMap (ZMod E.q) (Fqbar E)).injective
        (chord_fiber_product_concrete E lam D)]
  -- Reduce to the coprime base case via gcd extraction.
  exact chord_fiber_product_concrete_natDegree_le_normPoly_natDegree_of_coprime_base
    E lam D hD
    (fun D' hD' hcop =>
      chord_fiber_product_concrete_natDegree_le_of_coprime E lam D' hD' hcop)

/-- **Stub 2b**: natDegree bound restated against `∑ Q gd.mult Q`, using
the `mult_sum_eq_normPoly_natDegree` identity from
`Divisor/GeomLocalOrder.lean`. -/
theorem chord_fiber_product_concrete_bar_natDegree_le
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ((chord_fiber_product_concrete E lam D).map
        (algebraMap (ZMod E.q) (Fqbar E))).natDegree
      ≤ ∑ Q ∈ gd.support, gd.mult Q := by
  rw [GeometricDivisorData.mult_sum_eq_normPoly_natDegree E D hD gd]
  exact chord_fiber_product_concrete_bar_natDegree_le_normPoly E lam D hD

/-- **Discharge sketch**: the multiplicity equality follows from the two
stubs via the helper. -/
theorem chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber_via_squeeze
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hroots :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image
      E lam D hD gd
  have hdvd : ∀ z ∈ gd.support.image (zLambdaBar E lam),
      (Polynomial.X - Polynomial.C z) ^
        (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
        ∣ p :=
    fun z _ =>
      chord_fiber_product_concrete_bar_zfiber_pow_dvd E lam D hD gd z
  have hdeg : p.natDegree ≤ ∑ Q ∈ gd.support, gd.mult Q :=
    chord_fiber_product_concrete_bar_natDegree_le E lam D hD gd
  exact Divisor.rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le
    p gd.support (zLambdaBar E lam) gd.mult hpne hroots hdvd hdeg

/-- **Plumbing from multiplicity accounting to factored form.**

Once the root set is known (`ChordFiberProductConcrete` proves it) and every
root multiplicity is the sum over the corresponding geometric fibre, the
usual `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C` factorisation over
the algebraically closed field `Fqbar E` gives the factored form. -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity
    [DecidableEq (Fqbar E)]
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D)
    (hZ : ∀ z : Fqbar E,
      (Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
        (chord_fiber_product_concrete E lam D)).rootMultiplicity z =
        ∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = Polynomial.C c * ∏ Q ∈ gd.support,
            (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  set p := (chord_fiber_product_concrete E lam D).map
    (algebraMap (ZMod E.q) (Fqbar E)) with hp_def
  have hpne : p ≠ 0 :=
    Polynomial.map_ne_zero
      (chord_fiber_product_concrete_ne_zero E lam D hD)
  have hpsplit : p.Splits := IsAlgClosed.splits _
  have hcard : p.roots.card = p.natDegree := hpsplit.natDegree_eq_card_roots.symm
  refine ⟨p.leadingCoeff, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hfac :
      Polynomial.C p.leadingCoeff *
        (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod = p :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hrootSet :
      p.roots.toFinset = gd.support.image (zLambdaBar E lam) :=
    chord_fiber_product_concrete_bar_roots_toFinset_eq_support_image E lam D hD gd
  have hMaps : ∀ Q ∈ gd.support, zLambdaBar E lam Q ∈
      gd.support.image (zLambdaBar E lam) :=
    fun Q hQ => Finset.mem_image.mpr ⟨Q, hQ, rfl⟩
  have hprod :
      (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod =
        ∏ Q ∈ gd.support,
          (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
    rw [Finset.prod_multiset_map_count]
    rw [hrootSet]
    have hcount_eq : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (Polynomial.X - Polynomial.C z) ^ (p.roots.count z) =
        (Polynomial.X - Polynomial.C z) ^
          (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
            gd.mult Q) := by
      intro z _
      rw [Polynomial.count_roots, hZ]
    rw [Finset.prod_congr rfl hcount_eq]
    rw [Finset.prod_congr rfl
      (fun z _ => (Finset.prod_pow_eq_pow_sum
        (gd.support.filter (fun Q => zLambdaBar E lam Q = z))
        gd.mult (Polynomial.X - Polynomial.C z)).symm)]
    have hZreplace : ∀ z ∈ gd.support.image (zLambdaBar E lam),
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (Polynomial.X - Polynomial.C z) ^ (gd.mult Q)) =
        (∏ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z),
          (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q)) := by
      intro z _
      refine Finset.prod_congr rfl ?_
      intro Q hQ
      rw [(Finset.mem_filter.mp hQ).2]
    rw [Finset.prod_congr rfl hZreplace]
    exact Finset.prod_fiberwise_of_maps_to hMaps
      (fun Q => (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q))
  conv_lhs => rw [← hfac]
  rw [hprod]

/-- **Bar-level factored form** (replacement of
`chord_fiber_product_bar_eq_geom_prod`).

*Math (deepest)*: combine `bar_eval_eq_prod` (resultant ↦ ∏ chord-root
evaluations) with the geometric divisor data: each `D`-zero `Q` in
`gd.support` contributes `gd.mult Q` factors of `(X − zLambdaBar Q)`,
because for `μ` near `zLambdaBar Q` the chord-line `y = λx + μ` passes
through `Q` (with the prescribed local order). The leading coefficient
matches `(normPoly E D).leadingCoeff` after passing through Hasse +
geom-divisor accounting. This is the divisor-of-norm formula
`div(N(D)) = π_*(div D)` for the cover
`F_qbar(E) / F_qbar(zLambdaBar lam)` (Stacks 02RS, with Stichtenoth
Prop 3.1.9 and Thm 3.1.11 as supporting function-field accounting).
Provable in mathlib once we have:
  (a) the inertial-degree / ramification computation for the chord
      projection (already encoded by `gd.mult` via the local-order
      machinery in `GeomLocalOrder`);
  (b) a finite product expansion for the resultant.
The hardest sub-step is (a): linking `gd.mult Q` to the multiplicity of
`zLambdaBar Q` as a root of the resultant. -/
theorem chord_fiber_product_concrete_bar_eq_geom_prod
    (lam : ZMod E.q) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) :
    ∃ c : Fqbar E, c ≠ 0 ∧
      Polynomial.map (algebraMap (ZMod E.q) (Fqbar E))
          (chord_fiber_product_concrete E lam D)
        = Polynomial.C c * ∏ Q ∈ gd.support,
            (Polynomial.X - Polynomial.C (zLambdaBar E lam Q)) ^ (gd.mult Q) := by
  classical
  exact chord_fiber_product_concrete_bar_eq_geom_prod_of_rootMultiplicity E lam D hD gd
    (chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber E lam D hD gd)

end Divisor.Sketch
