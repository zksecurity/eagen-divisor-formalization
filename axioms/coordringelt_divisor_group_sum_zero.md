# `CoordRingElt.divisor_group_sum_zero` — RETIRED (was unsound)

This axiom was retired in commit `04d2c6e` after a high-severity audit
found it provably false as stated.

## What it was

```lean
axiom CoordRingElt.divisor_group_sum_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : normPoly_splits_over_Fq E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (betaConstructive E D P)
                    (ECPoint.affine P.1 P.2)) = 0
```

The axiom hard-coded `betaConstructive E D` as the multiplicity
function. Despite citing Silverman AEC Cor III.3.5, this is **not**
the F_q-restricted form of Cor III.3.5: `betaConstructive`'s
twin-sheet Nat-division surrogate is provably non-faithful to the
true ord_P at twin sheets with asymmetric orders.

## Concrete counterexample

* Curve: `E : y² = x³ + 1` over `F_5`.
* Element: `D = (x²+1) − (1+2x)·y`.
* `normPoly E D = x · (x−2)⁴` — splits over `F_5`, `natDeg = 5`.
* `E.points = {(0,1), (0,4), (2,2), (2,3), (4,0)}`.
* `D`-zeros: `{(0,1), (2,2), (2,3)}`.
* True `ord_P(D)`: `1` at `(0,1)`, `3` at `(2,2)`, `1` at `(2,3)`.
  True-multiplicity group sum: `1·(0,1) + 3·(2,2) + 1·(2,3) = O` ✓
* `betaConstructive` values: `1` at `(0,1)`, `2` at `(2,2)`, `2` at `(2,3)`
  (twin Nat-division at `x = 2`). β-weighted sum:
  `1·(0,1) + 2·(2,2) + 2·(2,3) = (0,1) ≠ O`. ✗

The axiom is therefore **provably false** as stated.

## Replacement

Replaced by the existential axiom
[`CoordRingElt.exists_divisor_multiplicity`](exists_divisor_multiplicity.md),
which does not bind to `betaConstructive`: it asserts the *existence*
of a faithful divisor multiplicity (the true `ord_P`) satisfying all
four divisor properties. The classical witness is Silverman AEC
III Cor 3.5 + II §1 (local order at smooth points).

## Provenance retained for context

Silverman, *The Arithmetic of Elliptic Curves* (GTM 106),
**Corollary III.3.5**, p. 63 (the textbook content the original
axiom *intended* to encode, before the `betaConstructive` hard-coding
broke faithfulness).

> Corollary 3.5. Let E be an elliptic curve and let
> D = Σ n_P (P) ∈ Div(E). Then D is a principal divisor if and only if
>
> Σ_{P ∈ E} n_P = 0     and     Σ_{P ∈ E} [n_P] P = O.

![Silverman Cor III.3.5](snippets/silverman-cor-III.3.5-principal-divisor-081.png)
