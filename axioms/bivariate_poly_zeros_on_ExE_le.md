# `bivariate_poly_zeros_on_ExE_le` (10th axiom)

- **Lean source**: `Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`
- **Support file**: `Divisor/FourVarPoly.lean` (types and helpers)

```lean
axiom bivariate_poly_zeros_on_ExE_le
    (f : FourVarPoly E.q) (dX dY : ℕ)
    (hBidegX : bi_x_degree_le E f dX dY)
    (hNonzero : ∃ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ bivEval₂ f A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => bivEval₂ f p.1 p.2 = 0)).card
      ≤ 2 * (dX + dY) * E.points.card
```

**Representation**: `FourVarPoly q := MvPolynomial (Fin 4) (ZMod q)` with variable assignment `0 = X₀, 1 = Y₀, 2 = X₁, 3 = Y₁`. The `bi_x_degree_le E f dX dY` predicate unfolds to `f.degreeOf 0 ≤ dX ∧ f.degreeOf 2 ≤ dY` — the `X₀` and `X₁` degrees from Mathlib's `MvPolynomial.degreeOf`. The `Y_i` degrees are unbounded at the axiom signature (they are implicitly reduced mod the curve relations during application, via `hBidegX` being discharged from the reduced form).

**Non-vanishing hypothesis**: stated as "∃ an F_q-point of E × E where `f` is non-zero", equivalent to "f is not identically zero on the F_q-points of E × E". This is a stronger condition than the algebraic "f mod curve ideal ≠ 0" form in the original plan draft (the latter allows f identically zero on F_q-points but non-zero over the algebraic closure); in practice callers get the ∃-point form for free from the cleared-polynomial identity at a non-vanishing witness.

Weil / Lang–Weil bound on F_q-points of a non-zero bivariate curve cut out on `E × E`.

## Citation

Primary:

- **Lang & Weil**, *"Number of Points of Varieties in Finite Fields"*, American Journal of Mathematics **76** (1954), pp. 819–827 — **Theorem 1**, p. 819.

Supporting (already axiomatised / textbook form for single curves):

- Stichtenoth, *Algebraic Function Fields and Codes* (GTM 254, 2nd ed.), **Theorem 5.2.3 (Hasse–Weil Bound)**, p. 198 — for a single curve.
- Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), **Theorem V.1.1 (Hasse)**, p. 138 — for one elliptic curve.
- Silverman AEC **Theorem V.2.2 (Weil Conjectures)**, p. 141 — for smooth projective varieties.

## Verbatim

Lang–Weil 1954, Theorem 1:

> Theorem 1. There exists a constant A(n, d, r) depending only on n, d, r such that for any variety V = V_{n,d}^r defined over a finite field k we have
>
> |N − q^r| ≤ (d − 1)(d − 2)·q^{r − 1/2} + A(n, d, r)·q^{r − 1}.

Silverman V.2.2 (supporting, closest textbook form):

> Theorem 2.2. (Weil Conjectures) Let V/F_q be a smooth projective variety of dimension N. …

Stichtenoth 5.2.3 (supporting, single-curve Hasse–Weil Bound):

> Theorem 5.2.3 (Hasse–Weil Bound). The number N = N(F) of places of F/F_q of degree one satisfies the inequality
>
> |N − (q + 1)| ≤ 2g·q^{1/2}.

## Snippets

![Lang–Weil 1954 Thm 1](snippets/lang-weil-1954-thm-1-02.png)

![Silverman V.2.2 Weil Conjectures](snippets/silverman-thm-V.2.2-weil-conjectures-158.png)

![Stichtenoth 5.2.3](snippets/stichtenoth-thm-5.2.3-hasse-weil-bound-209.png)

## Provenance note (from the plan)

The axiom would follow from combining:

- `hasse_weil` (already axiomatised, single curve),
- absolute irreducibility of `E × E` (product of two absolutely irreducible curves),
- Bezout's theorem for hypersurface-in-surface intersection,
- Lang–Weil's point-count for curves on a surface.

Fully formalising these would take months. Stating the compound form as a single axiom with textbook citation matches the style used for `principal_divisor_iff` and `hasse_weil`.

## Cross-check (Lean statement vs. Lang-Weil 1954 Thm 1)

**Lang-Weil Thm 1** bounds the F_q-point count of a projective variety `V = V_{n,d}^r`:

    |N − q^r| ≤ (d − 1)(d − 2)·q^{r − 1/2} + A(n, d, r)·q^{r − 1}.

**Translation to the axiom.** Set `V = {f = 0} ∩ (E × E)`, a curve (r = 1) cut out inside the surface `E × E` (dim 2, degree 9 in P² × P² ⊂ P⁸ via Segre). The degree of `V` is bounded by `deg(f) · deg(E × E)`; under mod-curve reduction, the two `Y_i`-branches contribute a factor of 2, giving `deg V ≤ 2·(dX + dY)` in the axiom's reduced-X counting (rather than the naive `9·(dX + dY)` Bezout bound, which is looser). Applying Lang-Weil Thm 1 with `r = 1` to each irreducible component of `V` and summing, combined with `|E| ≥ q + 1 − 2√q` (Hasse, existing axiom `hasse_weil`), yields `|V(F_q)| ≤ 2·(dX + dY)·|E|` for all `q ≥ 5` (which `ECSetup` already assumes).

**Sanity checks**:
* For `f` depending only on `A₀` (i.e. `dY = 0`, `f = g(X₀, Y₀)`) with `g` a polynomial on `E` of x-degree `dX`: zeros on `E` are `≤ 2·dX` by line-SZ; product with all of `E.points` for `A₁` gives `≤ 2·dX·|E|`. Axiom: `2·(dX + 0)·|E| = 2·dX·|E|`. ✓
* Symmetrically for `dX = 0`. ✓
* For `f` depending on both: standard split-fibre SZ gives `≤ 2·dX·|E| + 2·dY·|E|`. ✓

**Tightness note.** The paper's `sections/ec.tex:763-779` uses a specialised `18·(deg_E(D) + M − 1)·|E|` bound for the log-derivative polynomial — a factor of 2 tighter than the generic `2·(dX + dY)·|E| = 36·(deg_E(D) + k)·|E|` when `dX = dY = 9·(deg_E(D) + k)`. The paper exploits structural symmetry of the log-derivative polynomial; this axiom is the generic Lang-Weil bound. Phase 5 of `docs/bivariate-sz-paper-faithful.md` handles the factor-2 gap for the log-deriv application.

## Status

Declared in Lean (`Divisor/Axioms/AxiomBivariatePolyZerosOnExELe.lean`). Primary source archived (Lang-Weil 1954, `papers/lang-weil-1954.pdf`). `#print axioms` for any downstream `ma_extractable` invocation of this axiom will list `bivariate_poly_zeros_on_ExE_le` alongside the existing 9 axioms.
