# Axiom: `chord_fiber_product_concrete_bar_zfiber_pow_dvd`

## Statement

```lean
axiom chord_fiber_product_concrete_bar_zfiber_pow_dvd
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.X - Polynomial.C z) ^
      (∑ Q ∈ gd.support.filter (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      ∣ (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E))
```

In words: for each chord-intercept `z : F_qbar`, the chord-fibre product
(the concrete resultant), as a polynomial over `F_qbar`, is divisible by
`(X − C z)^(fibre_sum)` where `fibre_sum` is the sum of geometric
multiplicities at the points `Q ∈ gd.support` projecting to `z` under
`zLambdaBar lam`.

This is the **lower-bound (≥) half** of the divisor-of-norm pushforward
identity for the chord projection `π = y - λx : E → ℙ¹`, written
coefficientwise.

## Citation

* **Stacks Project**, [Lemma 42.18.1 (Principal divisors and pushforward)](https://stacks.math.columbia.edu/tag/02RS).
  The statement here is the lower-bound coefficient form of the
  pushforward identity `div(N(D)) = π_* div(D)` at the place `(z)` of
  `F_qbar(zLambdaBar lam)`.

* **Stichtenoth**, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.):
  - Proposition 3.1.9 (conorm of a principal divisor is principal)
  - Theorem 3.7.1 (Hasse-Arf-style ramification for cyclic extensions).

  The norm pushforward at unramified places gives equality; at
  ramified places the local ramification index controls the difference.

## Why this remains an axiom

Mathlib v4.28.0 supplies polynomial and resultant infrastructure but
**not** the local-intersection / order-of-vanishing API for the affine
coordinate ring of an elliptic curve. Specifically:

* The k=1 case is a theorem
  (`chord_fiber_product_concrete_bar_X_sub_C_zLambda_pow_one_dvd_of_mem_support`);
  it follows from the existing root-set bridge.

* The k≥2 case requires either:
  1. Direct local-intersection theory: a notion of "order of vanishing
     of D along a moving chord" formalised on the affine coordinate
     ring of E.
  2. Axiomatising a textbook function-field theorem (e.g. Stacks 02RS
     in its full divisor-pushforward form) and instantiating.

Mathlib lacks both routes for this specific setting; the present axiom
is the narrowest packaging of the local content.

## Why the matching upper bound is *not* an axiom

The opposite-direction inequality

```
((chord_fiber_product_concrete E lam D).natDegree
  ≤ (normPoly E D).natDegree)
```

is now a complete coordinate-native theorem in
`Divisor/ChordFiberWeightedDegree.lean`:

```lean
theorem chord_fiber_product_concrete_natDegree_le_normPoly_natDegree
    (lam : ZMod E.q) (D : CoordRingElt E.q)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    (chord_fiber_product_concrete E lam D).natDegree
      ≤ (normPoly E D).natDegree
```

Proof (weighted-Sylvester analysis):

1. **Lemma A**: per-coefficient weight bound for `chordCubicBiv`:
   `3·natDegree(chordCubicBiv.coeff k) + 2k ≤ 6` for `k ≤ 3`.
2. **Lemma B**: per-coefficient weight bound for `DLineBiv`:
   `3·natDegree(DLineBiv.coeff k) + 2k ≤ (normPoly).natDegree` for
   `k ≤ DLineBiv.natDegree`.
3. **Sylvester index-sum identity**:
   `Σ_j ((σ j).val − sylvesterOff j) = 3·n` for any permutation `σ`
   with full support (n = `DLineBiv.natDegree`).
4. **Per-permutation bound**: for each `σ`, the product
   `∏ j, M[σ j, j]` either vanishes (some entry zero) or its natDegree
   is bounded by w via the weighted sum:
   `3·Σ natDeg + 2·3n ≤ 3·w + 6·n`, yielding `Σ natDeg ≤ w`.
5. **Determinant bound**: `Matrix.det_apply` + sign-of-permutation
   handling + `natDegree_sum_le_of_forall_le`.

This is the upper-bound half of the divisor-of-norm identity, derived
without any function-field / local-intersection machinery.

## Discharge plan

Combined with the upper-bound theorem, the divisibility axiom plus the
squeeze argument (`rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le`)
proves the unrestricted `chord_fiber_product_concrete_bar_rootMultiplicity_eq_zfiber`
identity (currently a theorem in
`Divisor/Axioms/AxiomChordFiberProductBarFactored.lean`).

To eliminate this axiom entirely, the project would need to formalise:

1. The local-ring-divisor-multiplicity API for the affine coordinate
   ring of E (linking `gd.mult Q` to the maximal-ideal valuation),
   then prove the local pushforward at each closed point of `ℙ¹`.

2. Or: a textbook-form `principalDivisor_norm_eq_pushForward` axiom
   over function fields, and a bridge from the project's concrete
   chord-projection setting to that abstract framework. This would
   replace the axiom with a more textbook-shaped one, but would not
   necessarily reduce axiom count.

The k=1 case is closed; the k≥2 case is the genuine local content.
