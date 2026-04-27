# `CoordRingElt.exists_divisor_multiplicity`

- **Lean source**: `Divisor/Axioms/AxiomExistsDivisorMultiplicity.lean`

```lean
axiom CoordRingElt.exists_divisor_multiplicity
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (normPoly_splits_over_Fq E D →
        (∑ P ∈ E.points, β P) = (normPoly E D).natDegree) ∧
      (normPoly_splits_over_Fq E D →
        ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0)
```

Existence of the canonical "true divisor multiplicity" function
`β = ord_P(D)` for `D = a − b·y ∈ F_q[E]^×`, with the four divisor
properties:

1. **Support**: `β` is supported only on F_q-rational affine zeros of `D` on `E`.
2. **Coverage**: every F_q-rational affine zero of `D` is in `β`'s support.
3. **Total-degree bound** (unconditional): `Σ β ≤ D.degE`.
4. Under `normPoly_splits_over_Fq E D`:
   - **Pole-at-∞ accounting**: `Σ β = natDegree (normPoly E D)`.
   - **Abel's group-sum-zero**: `Σ [β(P)]·P = O` in the group law.

## Why this exists (and the previous axiom did not)

This axiom replaces the now-retired
[`CoordRingElt.divisor_group_sum_zero`](coordringelt_divisor_group_sum_zero.md),
which had hard-coded `β = betaConstructive E D`. That binding was
provably false (counterexample over `F_5`); see the retired-axiom
provenance file for details.

The fix: existential rather than constructive. The witness is the
true local order `ord_P(D)`, which lives in Silverman AEC II §1
(local discrete valuation at a smooth point) and gives the full
group-sum content of Cor III.3.5 (specialised under splitting).

## Citation

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106):

* **§II.1** (p. 21–24): local rings, uniformizers, and the discrete
  valuation `ord_P` at a smooth point of an algebraic curve.
* **Corollary III.3.5**, p. 63: principal-divisor characterisation
  via degree zero + group-sum zero.

Combined: the local order `ord_P(D)` at affine F_q-points of `E`
provides a multiplicity function whose F_q-sum (under splitting)
matches Cor III.3.5's full geometric sum, hence the four divisor
properties.

## Verbatim (Cor III.3.5)

> Corollary 3.5. Let E be an elliptic curve and let
> D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
>
> Σ_{P ∈ E} n_P = 0     and     Σ_{P ∈ E} [n_P] P = O.

![Silverman Cor III.3.5](snippets/silverman-cor-III.3.5-principal-divisor-081.png)

## Discharge plan

The axiom is intended to be discharged in Phase 1 of the trust-
closure plan:

1. Mechanise `ord_P` from local uniformizers (`Divisor/OrdP/Uniformizer.lean`):
   - Non-2-torsion `P = (x₀, y₀)` with `y₀ ≠ 0`: uniformizer = `x − x₀`.
   - 2-torsion `P = (x₀, 0)`: uniformizer = `y`.
2. Prove the four divisor properties for `ord_P` in
   `Divisor/OrdP/LocalRing.lean` (currently sorry'd skeleton).
3. Apply `principal_divisor_iff.mp` to obtain the group-sum-zero
   property under splitting.
4. Replace the axiom with the proven theorem
   `Divisor.exists_divisor_multiplicity_proved` in
   `Divisor/OrdP/LocalRing.lean`.

## Notes

The splitting hypothesis is essential for (4) and (5). Without
splitting, conjugate orbits `{P, P^φ}` in `E(F_{q^r}) \ E(F_q)`
contribute to the geometric sum but are invisible to the
F_q-restricted sum, so the F_q-only group sum is in general nonzero
even though the geometric one is `O`. Splitting forces every
geometric zero of `D` to be F_q-rational, recovering the full sum.
