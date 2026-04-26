# `bivariate_poly_zeros_on_ExE_le`

- **Status**: theorem (no longer an axiom)
- **Lean source**: `Divisor/BivariateZerosOnExE.lean`
- **Support file**: `Divisor/CurveEvalZerosHelper.lean` (per-curve zero count via norm polynomial)

```lean
theorem bivariate_poly_zeros_on_ExE_le
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

## Proof route (Lang–Weil-style, Hasse-only)

The Lean proof uses elementary fiber counting plus Hasse-Weil's `2·|E| ≤ 3q + 3` rather than DKL+Bezout intersection theory. The only project-level axiom in the dependency chain is `Divisor.hasse_weil`.

1. **Per-curve reduction.** For a bivariate `g(X, Y)` of total degree `≤ d`, reduce mod `Y² = X³ + AX + B` to canonical form `g ≡ α(X) + β(X)·Y` with `max(2·deg α, 3 + 2·deg β) ≤ 3d`.
2. **Per-curve count.** On `E(F_q)`, zeros of `α(X) − β(X)·Y` are bounded by `degE := max(2·deg α, 3 + 2·deg β)` via the norm polynomial `α² − β²·c(X)` plus a `rootMultiplicity ≥ 2` argument at common roots of `α, β`. Hence `≤ 3d` zeros per fiber.
3. **4-variate lift.** Specialise one coordinate of `f`. Bad fibers (those where `f` vanishes identically on `E` for that fixed coord) are bounded by `3D` by symmetric application. Good fibers contribute `≤ 3D` each.
4. **Hasse close-out.** Sum: `total ≤ bad·|E| + (|E| − bad)·3D ≤ 6D·|E| − 9D²`. With Hasse-Weil's `2·|E| ≤ 3q + 3` (valid for `q ≥ 5`), `total ≤ 9Dq + 9D − 9D² ≤ 9Dq` for `D ≥ 1`. Boundary cases (`D = 0`, `|E| ≤ 3D`) handled directly.

## Citations (provenance, retained for documentation)

### DKL'14 Claim 7.2

Dvir, Kollar, Lovett, *"Variety Evasive Sets"*,
Computational Complexity **23** (2014), pp. 1–32 — **Claim 7.2**, p. 10.

PDF archived: `axioms/papers/DvirKollarLovett14.pdf`.

Verbatim:

> Let V ∈ V_{n,d,k}. Then |V ∩ F^n| ≤ d · |F|^k.

(`V_{n,d,k}` denotes varieties in `F̄^n` of dimension `k` and degree `d` defined over `F`.)

### Hartshorne I.7.7 (Bezout)

Hartshorne, *Algebraic Geometry*, GTM 52 — **Theorem I.7.7** (Bezout).

Verbatim:

> Let Y, Z be distinct curves in P², having degrees d, e respectively. Then `Y · Z = ∑_P i(Y, Z; P) = de`.

The hypersurface-meets-surface generalisation in `P^N` follows by standard intersection theory (Hartshorne I.7).

### EOT'10 Lemma A.3

Ellenberg, Oberlin, Tao, *"The Kakeya set and maximal conjectures for algebraic varieties over finite fields"*,
Mathematika **56** (2010), pp. 1–25 — **Lemma A.3**, p. 23.

PDF archived: `axioms/papers/EllenbergOberlinTao10.pdf`.

Verbatim:

> Let V ⊂ ℙ^N be a projective variety of dimension n and degree d. Then |V(F)| ≤ d(|F|+1)^n.

This is an alternative path to the same linear-in-`q` shape, with a weaker constant.

## Sanity checks

* `f = X₀ - c` for some constant `c`: `D = 1`, the hypersurface is the line `X₀ = c`. Intersection with `E × E` is `{(c, ±√(c³+Ac+B))} × E`, of size `≤ 2 · |E| ≤ 2 · (q + 2√q + 1) ≤ 9·1·q` for `q ≥ 5`. ✓
* `f = Y₀ - Y₁`: `D = 1`, zeros are `{(A₀, A₀) : A₀ ∈ E} ∪ {(A, A') : A.2 = A'.2 ≠ 0, A.1 ≠ A'.1}`. At most `3·|E|` (at most 3 collisions per y-coordinate), well within `9 · 1 · q`. ✓
* General `f` of total degree `D`: Bezout intersection-theoretic bound is `9D` on the surface degree; point count `≤ 9D·q` matches. ✓
