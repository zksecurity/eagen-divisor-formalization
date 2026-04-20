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

## Axiom surface

`Divisor.ma_extractable` and `Divisor.ip_knowledge_sound` depend on:

| Axiom | Source |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | Lean core |
| `ECPoint.add_assoc`, `add_comm`, `neg_add_cancel` | Silverman III §2 (group law) |
| `principal_divisor_iff` | Silverman III Cor 3.5 |
| `CoordRingElt.divisor_degree_eq` | Silverman III Prop 3.4 (pole order at infinity) |
| `CoordRingElt.divisor_group_sum_zero` | Silverman III Prop 3.4 (Abel's theorem on E) |
| `polyG_zero_of_logDerivCheck_identically_zero` | Residue identity — **UNSOUND** (see below) |

`Divisor.ma_completeness` depends on the Lean core + group-law axioms + `weil_reciprocity_honest` (Silverman III §X).

Hasse-Weil bounds (`hasse_weil_upper`, `hasse_weil_lower`) are project-wide axioms but are not on the current soundness dependency path.

### Soundness flag (Session 37 finding)

The transient axiom `polyG_zero_of_logDerivCheck_identically_zero` is **provably false** under Lean's current `logDerivTerm` definition (`Divisor/LogDeriv.lean:128`). A concrete Lean-verified counterexample lives at `docs/counterexamples/axiom_false_witness.lean`:

- `E : y² = x³ + 1 over F_7`, `D = y` (i.e. `a=0, b=-1`), `P = (0, 1)`, `B₀ = -P`, `m₀ = -1`.
- All axiom hypotheses satisfied at `A₀ = (2, 3)`, `A₁ = (4, 3)`.
- But `polyG ... = 5 ≠ 0`.

Root cause: Lean's `logDerivTerm` implements only the formal `x`-partial `(∂D/∂x)/D · dx/dz`, omitting the `(∂D/∂y)·(dy/dz)/D = -b(x)·(3x²+A)/((3x²+A-2λy)·D)` on-curve chain-rule contribution present in the paper's Lemma 6 integrand (§ec.tex:557-579). The downstream `ma_extractable` theorem avoids this specific witness only because it routes through the `-P ∈ {B_j}` special branch, but the axiom as stated is classically inconsistent.

**Reference**: Silverman, J.H. *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106.

## Outstanding work

- **Fix `logDerivTerm` to paper-faithful form**: Session 37 identified that Lean's `logDerivTerm` is mathematically incorrect. Fixing requires cascade-rewriting `logDerivTerm` + `logDerivCheckFn` to include the missing y-chain-rule term, then re-proving all downstream consumers (~400-2000 LOC cascade, mostly mechanical). After the cascade, the classical residue identity applies and the axiom is eliminable via Lemma 6 mechanization (~1500 LOC additional).
- **Residue identity mechanization**: `polyG_zero_of_logDerivCheck_identically_zero` encodes the classical log-derivative + norm-decomposition identity for rational functions on E. Fully mechanizing Lemma 6 requires a function-field model of `F_q(E)` with local uniformizers and Weierstrass preparation. Queue 3 (sessions Q3.0-Q3.4, see `docs/axiom-elimination-plan.md`) landed partial scaffolding: partial-fraction infrastructure, norm-decomposition helper (`betaConstructive`), bivariate denominator-cleared log-derivative identity, `polyGPoly` definition + degree bounds, and Vieta/chord-sum reductions.
- **Silverman III Prop 3.4 mechanization**: the two narrow `CoordRingElt.divisor_*` axioms each cite a single specific fact from Silverman III Prop 3.4. Mechanizing these (like the residue identity) requires function-field infrastructure.

## Plan

See `docs/axiom-elimination-plan.md` for the full history of axiom-elimination work, including per-session commit logs for Queues 1 and 2.
