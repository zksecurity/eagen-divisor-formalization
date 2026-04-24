# divisors

Lean 4 mechanization of an elliptic-curve-based dlog knowledge-sound IP.

## Build

```
lake build
```

Requires elan + Lean 4 toolchain (see `lean-toolchain`).

## Theorem surface

The headline theorems live in `Divisor/ExtractorBridge.lean` and `Divisor/Soundness.lean`:

- `Divisor.ma_extractable` — knowledge soundness of the MA protocol.
- `Divisor.ip_knowledge_sound` — knowledge soundness of the IP protocol.
- `Divisor.ma_completeness` — completeness of the MA protocol.

### `Divisor.ma_extractable` (MA knowledge soundness)

Fix a statement `stmt` over the finite field `F_q`: bases `B_1, ..., B_k` in `E(F_q)`, a target `T` in `E(F_q)`, and a degree bound `d`. Fix a prover first-round message `msg` encoding a divisor representative `D = a(x) - b(x) y` in `F_q[E]` together with scalars `m_1, ..., m_k`, such that the `E`-degree of `D` is at most `d`.

**Hypotheses** (`Divisor/ExtractorBridge.lean:3374`):

- smoothness of `E`: `4 a_E^3 + 27 b_E^2 ≠ 0`
- `normPoly(D)` splits over `F_q` (every geometric zero of `D` is `F_q`-rational)
- accounting: the `beta`-weights add up to the degree of `normPoly(D)`:

$$\sum_{P \in E(F_q)} \beta(P) = \deg(\mathrm{normPoly}(D))$$

- denominator non-vanishing on `A_0` outside `zerosFinset(D)` and avoiding `distinctR`
- size condition on the number of points of `E`:

$$|E(F_q)| > 2\bigl(5(\deg_E D + k + 2) + 3\bigr) + 21(\deg_E D + k + 2) + 72.$$

**Conclusion.** One of the two branches holds.

1. *Witness branch.* There exists a witness `w` such that `maExtractor(stmt, msg) = some w` and

$$T = \sum_{i=1}^{k} [n_i]\, B_i \qquad \text{in } E(F_q),$$

where `n_i = w.scalars(i)` in `Z` with `|n_i| < d`.

2. *Small-accept-set branch.* The set of challenges `(A_0, A_1)` in `validPairs` on which the verifier accepts has cardinality at most `B(d, k, q)`, where

$$B(d, k, q) = \bigl(72(d+k+6) + 4\bigr) \cdot |E(F_q)| + 6q \cdot \bigl((d+k+1) + (d+k+1)(d+k)\bigr).$$

### `Divisor.ip_knowledge_sound` (IP knowledge soundness)

The same disjunction as `ma_extractable`, conjoined with *uniqueness of the third-round response*: for every challenge and intercept `A_2` with `D` non-vanishing at `A_0, A_1, A_2` and the chord line `L(A_0, A_1)` non-vanishing at `-T`, any two third-round messages `msg3, msg3'` both accepted by the IP verifier must be equal.

### `Divisor.ma_completeness`

For an honest prover message `msg` witnessing `(stmt, wit)` with `degE(D) ≤ d` and `(a, b) ∈ admSet`, the rejecting-challenge set is bounded:

$$\bigl| \{ (A_0, A_1) \in E \times E : V \text{ rejects} \} \bigr| \le  (3N + 1) \cdot |E_{\mathrm{aff}}|,$$

where `N = numZeros(D)` and `E_aff` is the set of affine `F_q`-points of `E`. Proof uses Weil reciprocity plus Lemma 2 (`support_disjointness`).

## Axiom surface

`#print axioms Divisor.ma_extractable` (same for `Divisor.ip_knowledge_sound`):

```
propext, Classical.choice, Quot.sound,
Divisor.ECPoint.add_comm, Divisor.ECPoint.add_assoc, Divisor.ECPoint.neg_add_cancel,
Divisor.CoordRingElt.divisor_group_sum_zero,
Divisor.chord_fiber_product_eq_normZ_under_split,
Divisor.chord_sum_eq_chord_fiber_product_logDeriv
```

`#print axioms Divisor.ma_completeness`:

```
propext, Classical.choice, Quot.sound,
Divisor.ECPoint.add_comm, Divisor.ECPoint.add_assoc, Divisor.ECPoint.neg_add_cancel,
Divisor.weil_reciprocity_honest
```

### Textbook axioms — human-readable statements

Each project-defined axiom cites a textbook result; the PDFs are in the repo root. See `docs/axiom-textbook-crosscheck.md` for the detailed cross-check.

#### `ECPoint.add_comm` — Silverman AEC III Prop 2.2(c), p. 51

Commutativity of the chord-and-tangent group law on `E`:

$$P \oplus Q = Q \oplus P \qquad \text{for all } P, Q \in E.$$

#### `ECPoint.add_assoc` — Silverman AEC III Prop 2.2(e), p. 51

Associativity:

$$(P \oplus Q) \oplus R = P \oplus (Q \oplus R) \qquad \text{for all } P, Q, R \in E.$$

#### `ECPoint.neg_add_cancel` — Silverman AEC III Prop 2.2(d), p. 51

Existence of inverses (specialized to the concrete negation defined in `Divisor/Defs.lean`):

$$P \oplus (\ominus P) = O \qquad \text{for all } P \in E.$$

#### `CoordRingElt.divisor_group_sum_zero` — Silverman AEC III Cor 3.5, p. 63 (forward direction)

Abel's theorem on `E`. For the nonzero rational function `D = a(x) - b(x) y` in `F_q[E]`, under the splitting hypothesis `normPoly(D)` splits over `F_q` — so every geometric zero of `D` is `F_q`-rational — the `beta`-weighted group sum vanishes:

$$\sum_{P \in E(F_q)} [\beta(P)]\, P = O \qquad \text{in } (E, \oplus).$$

Textbook statement: a divisor

$$D = \sum_P n_P (P) \in  \mathrm{Div}(E)$$

is principal iff

$$\sum_P n_P = 0 \qquad \text{and} \qquad \sum_P [n_P] P = O.$$

The axiom uses the forward direction.

#### `chord_fiber_product_eq_normZ_under_split` — Stichtenoth Prop 3.1.9, p. 73 + Thm 3.7.1, p. 121

Function-field norm identity for the degree-3 extension `F_q(E) / F_q(z)` where `z = y - λ x`. Let `A_0, A_1, A_2` be the three chord-fiber sheets of the chord with slope `λ`. Then there exists a nonzero constant `c` in `F_q` with

$$\prod_{i=0}^{2} D\bigl(A_i(z)\bigr) = c \cdot N_D(z) \qquad \text{in } F_q[z],$$

where the left side is the Galois norm from `F_q(E)` to `F_q(z)` applied to `D`, and `N_D(z) = normZ(z)` is the `z`-coordinate norm polynomial. Stichtenoth 3.1.9 gives the conorm identity `Con(div(x)) = div(x)`; Thm 3.7.1 gives Galois-transitive action on place extensions.

#### `chord_sum_eq_chord_fiber_product_logDeriv` — Lang *Algebra* §VI.5, p. 285 + §VIII.5, p. 370

Trace-of-log-derivative identity, specialized to `L/K = F_q(E)/F_q(z)` and evaluated at the chord intercept `μ = z_λ(A_0)`:

$$\sum_{i=0}^{2} \frac{dD}{D}\bigl(A_i\bigr) = \frac{d\,N(D)}{N(D)}(\mu).$$

Equivalently, in general extensions `L/K`:

$$\mathrm{Tr}_{L/K}\bigl(dg/g\bigr) = \frac{d\bigl(N_{L/K}(g)\bigr)}{N_{L/K}(g)}.$$

Follows from differentiating the product-of-embeddings formula `N(g) = ∏_σ σ(g)` (Lang VI.5 Thm 5.1) with the derivation uniquely extended to the Galois closure (Lang VIII.5 Thm 5.1 Case 1).

#### `weil_reciprocity_honest` — Silverman AEC II Exercise 2.11, p. 39

Weil reciprocity specialized to the honest-prover setting. Classical statement: for nonzero rational functions `f, g` on a smooth curve `C` with `div(f)` and `div(g)` of disjoint support,

$$f\bigl(\mathrm{div}(g)\bigr) = g\bigl(\mathrm{div}(f)\bigr),$$

where by convention

$$f(D) = \prod_P f(P)^{n_P} \qquad \text{for } D = \sum_P n_P (P).$$

The axiom concludes the project-specific log-derivative consequence: for an honest divisor `D` and every challenge `(A_0, A_1)` off the bad set, `logDerivCheckFn(D, target, k, bases, m, A_0, A_1) = 0`. This packages Weil reciprocity applied to the rational function `D / L^m` (where `L` is the chord line) plus residue/differential arithmetic not stated in Exercise 2.11.

#### `hasse_weil` — Silverman AEC V Thm 1.1, p. 138

Classical Hasse bound on the number of `F_q`-points of `E`. Stated in `Divisor/Axioms.lean` in the equivalent integer-squared form

$$\bigl(|E(F_q)| - q - 1\bigr)^2 \le  4q,$$

which is equivalent to

$$\bigl| |E(F_q)| - q - 1 \bigr| \le  2\sqrt{q}.$$

## Outstanding work

- **Eliminate `chord_fiber_product_eq_normZ_under_split`**: prove the function-field norm identity in Lean, using conorm + Galois-transitive norm machinery.
- **Eliminate `chord_sum_eq_chord_fiber_product_logDeriv`**: prove the trace-of-log-derivative identity `Tr(dg/g) = d(Ng)/Ng` in Lean, using norm multiplicativity + unique derivation extension.
- **Downgrade `weil_reciprocity_honest`**: split into (i) a verbatim Weil reciprocity axiom matching Exercise II.2.11 and (ii) a proved residue/differential reduction to `logDerivCheckFn`.
- **Mechanize `CoordRingElt.divisor_group_sum_zero`** (Silverman III Cor 3.5 forward direction) — requires function-field infrastructure.

## Plan

See `docs/axiom-elimination-plan.md` for the full history of axiom-elimination work, and `docs/axiom-textbook-crosscheck.md` for the textbook cross-check underlying this README.
