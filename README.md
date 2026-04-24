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

For a statement `stmt` over $\mathbb{F}_q$ (target point, base points $B_1,\ldots,B_k$, degree bound $d$) and a prover first-round message `msg` carrying a divisor representative $D$ with $\deg_E(D) \le d$, under:
- smoothness $4a^3 + 27b^2 \neq 0$,
- splitting of $\mathrm{normPoly}(D)$ over $\mathbb{F}_q$,
- degree accounting $\sum_{P \in E(\mathbb{F}_q)} \beta(P) = \deg(\mathrm{normPoly}(D))$,
- a denominator non-vanishing condition on $A_0$,
- size condition $|E(\mathbb{F}_q)| > 2(5(\deg_E D + k + 2) + 3) + 21(\deg_E D + k + 2) + 72$,

one of the two branches holds:

$$
\bigl(\exists\, w.\; \mathrm{maExtractor}(\mathrm{stmt}, \mathrm{msg}) = \mathrm{some}\,w \;\wedge\; \mathrm{dlogHolds}(\mathrm{stmt}, w)\bigr)
\;\lor\;
\bigl|\{\, (A_0,A_1) \in \mathrm{validPairs} : V \text{ accepts}\,\}\bigr| \le B(d,k,q),
$$

with
$$B(d,k,q) = (72(d+k+6)+4)\cdot|E(\mathbb{F}_q)| + 6q\bigl((d+k+1) + (d+k+1)(d+k)\bigr).$$

### `Divisor.ip_knowledge_sound` (IP knowledge soundness)

Same extractor-or-small-accept-set disjunction as `ma_extractable`, plus uniqueness of the third-round response:
for every challenge `chal` and intercept $A_2$ with $D$ non-vanishing at $A_0, A_1, A_2$ and $L_{A_0,A_1}$ non-vanishing at $-\mathrm{target}$, any two accepting third-round messages are equal:
$$\mathrm{ipAccepts}(\mathrm{msg}_3) \wedge \mathrm{ipAccepts}(\mathrm{msg}_3') \implies \mathrm{msg}_3 = \mathrm{msg}_3'.$$

### `Divisor.ma_completeness`

For an honest prover message `msg` witnessing `stmt`/`wit` with $\deg_E(D) \le d$ and admissible $(polyA, polyB)$, the rejecting-challenge set is bounded via Weil reciprocity and Lemma 2 (`support_disjointness`):
$$\bigl|\{(A_0,A_1) \in E \times E : V \text{ rejects}\,\}\bigr| \;\le\; (3N + 1) \cdot |E_{\mathrm{aff}}|,$$
where $N = \mathrm{numZeros}(D)$.

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

Commutativity of the chord-and-tangent group law on $E$:
$$P \oplus Q = Q \oplus P \qquad \text{for all } P, Q \in E.$$

#### `ECPoint.add_assoc` — Silverman AEC III Prop 2.2(e), p. 51

Associativity of the group law:
$$(P \oplus Q) \oplus R = P \oplus (Q \oplus R) \qquad \text{for all } P, Q, R \in E.$$

#### `ECPoint.neg_add_cancel` — Silverman AEC III Prop 2.2(d), p. 51

Existence of inverses (specialized to the concrete negation defined in `Divisor/Defs.lean`):
$$P \oplus (\ominus P) = O \qquad \text{for all } P \in E.$$

#### `CoordRingElt.divisor_group_sum_zero` — Silverman AEC III Cor 3.5, p. 63 (forward direction)

Abel's theorem on $E$. For the nonzero rational function $D = a(x) - b(x) y \in \mathbb{F}_q[E]^\times$, under the splitting hypothesis $\mathrm{normPoly}_{\mathbb{F}_q}(D)$ splits over $\mathbb{F}_q$, every geometric zero of $D$ is $\mathbb{F}_q$-rational, and the $\beta$-weighted group sum vanishes:
$$\sum_{P \in E(\mathbb{F}_q)} [\beta(P)]\, P \;=\; O \qquad \text{in } (E, \oplus).$$

Textbook: $D = \sum_P n_P(P) \in \mathrm{Div}(E)$ is principal iff $\sum_P n_P = 0$ and $\sum_P [n_P] P = O$; the axiom uses the $(\Rightarrow)$ direction.

#### `chord_fiber_product_eq_normZ_under_split` — Stichtenoth Prop 3.1.9, p. 73 + Thm 3.7.1, p. 121

Function-field norm identity for the degree-3 extension $\mathbb{F}_q(E) / \mathbb{F}_q(z)$ where $z = y - \lambda x$. Let $A_0, A_1, A_2$ be the three chord-fiber sheets of the chord with slope $\lambda$. Then there exists $c \in \mathbb{F}_q^\times$ with
$$\prod_{i=0}^{2} D\bigl(A_i(z)\bigr) \;=\; c \cdot N_D(z) \qquad \text{in } \mathbb{F}_q[z],$$
where the left side is the Galois norm $N_{\mathbb{F}_q(E)/\mathbb{F}_q(z)}(D)$ and $N_D(z) = \mathrm{normZ}(z)$ is the $z$-coordinate norm polynomial. Stichtenoth 3.1.9 gives $\mathrm{Con}_{F'/F}(\mathrm{div}(x)) = \mathrm{div}_{F'}(x)$; Thm 3.7.1 gives Galois-transitive action on place extensions.

#### `chord_sum_eq_chord_fiber_product_logDeriv` — Lang *Algebra* §VI.5, p. 285 + §VIII.5, p. 370

Trace-of-log-derivative identity, specialized to $L/K = \mathbb{F}_q(E)/\mathbb{F}_q(z)$ and evaluated at the chord intercept $\mu = z_\lambda(A_0)$:
$$\sum_{i=0}^{2} \frac{dD}{D}\bigl(A_i\bigr) \;=\; \frac{d\,N(D)}{N(D)}\,(\mu).$$
Equivalently, $\mathrm{Tr}_{L/K}(dg/g) = d\bigl(N_{L/K}(g)\bigr) / N_{L/K}(g)$. Follows from differentiating the product-of-embeddings formula $N(g) = \prod_\sigma \sigma(g)$ (Lang VI.5 Thm 5.1) with the derivation uniquely extended to the Galois closure (Lang VIII.5 Thm 5.1 Case 1).

#### `weil_reciprocity_honest` — Silverman AEC II Exercise 2.11, p. 39

Weil reciprocity specialized to the honest-prover setting. Classical statement: for $f, g \in \bar K(C)^\times$ with $\mathrm{div}(f)$ and $\mathrm{div}(g)$ of disjoint support on a smooth curve $C$,
$$f\bigl(\mathrm{div}(g)\bigr) \;=\; g\bigl(\mathrm{div}(f)\bigr),$$
where $f(D) = \prod_P f(P)^{n_P}$ for $D = \sum_P n_P(P)$. The axiom concludes the project-specific log-derivative consequence: for honest $D$ and every challenge $(A_0, A_1)$ off the bad set,
$$\mathrm{logDerivCheckFn}(D, \mathrm{target}, k, \mathrm{bases}, m, A_0, A_1) \;=\; 0.$$
This packages Weil reciprocity applied to $D / L^m$ (where $L$ is the chord line) plus residue/differential arithmetic not stated in Exercise 2.11.

### Auxiliary axiom (not on current soundness/completeness path)

#### `hasse_weil` — Silverman AEC V Thm 1.1, p. 138

The classical Hasse bound on $\#E(\mathbb{F}_q)$. Stated in `Divisor/Axioms.lean` in the equivalent integer-squared form
$$\bigl(\#E(\mathbb{F}_q) - q - 1\bigr)^2 \;\le\; 4q,$$
which is equivalent to
$$\bigl|\#E(\mathbb{F}_q) - q - 1\bigr| \;\le\; 2\sqrt{q}.$$
Kept for future use (e.g. converting bounds stated in $|E(\mathbb{F}_q)|$ into bounds in $q$), but not currently consumed by `ma_extractable`, `ip_knowledge_sound`, or `ma_completeness`.

## Outstanding work

- **Eliminate `chord_fiber_product_eq_normZ_under_split`**: prove the function-field norm identity $\prod_i D(A_i(z)) = c \cdot N_D(z)$ in Lean, using conorm + Galois-transitive norm machinery.
- **Eliminate `chord_sum_eq_chord_fiber_product_logDeriv`**: prove the trace-of-log-derivative identity $\mathrm{Tr}(dg/g) = d(Ng)/Ng$ in Lean, using norm multiplicativity + unique derivation extension.
- **Downgrade `weil_reciprocity_honest`**: split into (i) a verbatim Weil reciprocity axiom matching Exercise II.2.11 and (ii) a proved residue/differential reduction to `logDerivCheckFn`.
- **Mechanize `CoordRingElt.divisor_group_sum_zero`** (Silverman III Cor 3.5 forward direction) — requires function-field infrastructure.

## Plan

See `docs/axiom-elimination-plan.md` for the full history of axiom-elimination work, and `docs/axiom-textbook-crosscheck.md` for the textbook cross-check underlying this README.
