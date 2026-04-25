# `bivariate_poly_zeros_on_ExE_le` (10th axiom — corrected)

- **Lean source**: `Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`
- **Support file**: `Divisor/FourVarPoly.lean` (`total_degree_le` predicate + helpers)

```lean
axiom bivariate_poly_zeros_on_ExE_le
    (f : FourVarPoly E.q) (D : ℕ)
    (hDeg : total_degree_le E f D)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 9 * D * E.q
```

**Representation**: `FourVarPoly q := MvPolynomial (Fin 4) (ZMod q)` with variable assignment `0 = X₀, 1 = Y₀, 2 = X₁, 3 = Y₁`. The `total_degree_le E f D` predicate unfolds to `f.totalDegree ≤ D` — Mathlib's `MvPolynomial.totalDegree`.

**Non-vanishing hypothesis**: stated as "∃ an F_q-point of E × E where `f` is non-zero" — equivalent to "f is not identically zero on the F_q-points of E × E".

## Citations

### DKL'14 Claim 7.2 (primary)

Dvir, Kollar, Lovett, *"Variety Evasive Sets"*,
Computational Complexity **23** (2014), pp. 1–32 — **Claim 7.2**, p. 10.

PDF archived: `axioms/papers/DvirKollarLovett14.pdf`.

Verbatim:

> Let V ∈ V_{n,d,k}. Then |V ∩ F^n| ≤ d · |F|^k.

(`V_{n,d,k}` denotes varieties in `F̄^n` of dimension `k` and degree `d` defined over `F`.)

### Hartshorne I.7.7 (Bezout, primary)

Hartshorne, *Algebraic Geometry*, GTM 52 — **Theorem I.7.7** (Bezout).

Verbatim:

> Let Y, Z be distinct curves in P², having degrees d, e respectively. Then `Y · Z = ∑_P i(Y, Z; P) = de`.

The hypersurface-meets-surface generalisation in `P^N` follows by standard intersection theory (Hartshorne I.7).

### EOT'10 Lemma A.3 (alternative)

Ellenberg, Oberlin, Tao, *"The Kakeya set and maximal conjectures for algebraic varieties over finite fields"*,
Mathematika **56** (2010), pp. 1–25 — **Lemma A.3**, p. 23.

PDF archived: `axioms/papers/EllenbergOberlinTao10.pdf`.

Verbatim:

> Let V ⊂ ℙ^N be a projective variety of dimension n and degree d. Then |V(F)| ≤ d(|F|+1)^n.

This is an alternative path (with a slightly weaker constant) to the same conclusion.

## Derivation chain

Let `V := {f = 0} ∩ (E × E)`.

1. **Hypersurface degree.** A 4-variate polynomial `f` of total degree `≤ D` defines a hypersurface `H_f ⊂ A⁴` of degree `≤ D` (Hartshorne I.7).
2. **Surface degree.** `E × E ⊂ P² × P²` is a surface (dimension 2) of degree `9` under the Segre embedding into `P⁸` (each `E ⊂ P²` has degree 3 as a smooth Weierstrass cubic; degrees multiply for products).
3. **Bezout intersection.** By Hartshorne I.7.7 (hypersurface-meets-surface form), the intersection `V = H_f ∩ (E × E)` has dimension `≤ 1` and degree at most `9 · D`.
4. **DKL point count.** By DKL'14 Claim 7.2 with `(n, d, k) = (8, 9D, 1)`, `|V(F_q)| ≤ 9D · |F_q|^1 = 9D · q`.

(Equivalently via EOT'10 Lemma A.3 with `n = 1`, `d ≤ 9D`: `|V(F_q)| ≤ 9D·(q+1)`. For `q ≥ 5` this is within a small constant of the DKL bound; we use the cleaner DKL form `9·D·q`.)

## Old axiom (unsound — replaced)

The previous axiom claimed `2·(dX + dY)·|E|` from `bi_x_degree_le`. This was **falsified** by Sage:

| f | q | curve | bound (old axiom) | actual count |
|---|---|---|---|---|
| `Y₀ + Y₁` | 5 | y²=x³+1 | 0 (since dX = dY = 0) | 5 |
| `Y₀ + Y₁` | 11 | y²=x³+x+3 | 0 | 41 |
| `Y₀·Y₁` | 5 | y²=x³+1 | 0 | 9 |

**Cause**: bi-x-degree `(0, 0)` predicts `2·(0+0)·|E| = 0` zeros, but the polynomial vanishes on a non-trivial subvariety because the `Y`-degree contribution was not bounded. Total degree captures both.

## New axiom on the same counterexamples

| f | totalDeg `D` | q | bound (new axiom) `9·D·q` | actual count | OK? |
|---|---|---|---|---|---|
| `Y₀ + Y₁` | 1 | 5 | 45 | 5 | ✓ |
| `Y₀ + Y₁` | 1 | 11 | 99 | 41 | ✓ |
| `Y₀·Y₁` | 2 | 5 | 90 | 9 | ✓ |

All three counterexamples to the old axiom are within the new axiom's bound, with substantial slack — consistent with the claimed `9·D·q` upper bound.

## Cross-check (Lean statement vs. derivation)

**Sanity checks**:
* `f = X₀ - X₀` (zero polynomial) — but excluded by `hNonzero`.
* `f = X₀ - c` for some constant `c`: `D = 1`, hypersurface is the line `X₀ = c`. Intersection with `E × E` is `{(c, ±√(c³+Ac+B))} × E`, of size `≤ 2 · |E| ≤ 2 · (q + 2√q + 1) ≤ 9·1·q` for `q ≥ 5`. ✓
* `f = Y₀ - Y₁`: `D = 1`, zeros are `{(A₀, A₀) : A₀ ∈ E} ∪ {(A, A') : A.2 = A'.2 ≠ 0, A.1 ≠ A'.1}`. Approximately `≤ 3·|E|` (at most 3 collisions in y-coordinate per point), well within `9 · 1 · q`. ✓
* `f` of total degree `D`: hypersurface degree `D`, intersection degree `≤ 9D`, point count `≤ 9D·q`. ✓

## Status

Declared in Lean (`Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`). DKL'14 and EOT'10 PDFs archived (`axioms/papers/`). `#print axioms` for any downstream `ma_extractable` invocation lists `bivariate_poly_zeros_on_ExE_le` alongside the existing 9 axioms.

This corrected axiom replaces an unsound prior version (which only bounded by `2·(dX + dY)·|E|`). The shift from bi-x-degree to total degree is the key correction; the multiplicative constant changes from `2·(dX + dY)` to `9·D` in line with the standard DKL+Bezout derivation.
