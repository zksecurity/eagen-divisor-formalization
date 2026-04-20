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
| `polyG_zero_of_logDerivCheck_identically_zero` | Residue identity — transient (see outstanding work) |

`Divisor.ma_completeness` depends on the Lean core + group-law axioms + `weil_reciprocity_honest` (Silverman III §X).

Hasse-Weil bounds (`hasse_weil_upper`, `hasse_weil_lower`) are project-wide axioms but are not on the current soundness dependency path.

**Reference**: Silverman, J.H. *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106.

## Outstanding work

- **Residue identity mechanization**: `polyG_zero_of_logDerivCheck_identically_zero` encodes the classical log-derivative + norm-decomposition identity for rational functions on E. Fully mechanizing it requires a function-field model of `F_q(E)` with local uniformizers and Weierstrass preparation (~1100-1400 LOC of new infrastructure). Queue 3 (sessions Q3.0-Q3.4, see `docs/axiom-elimination-plan.md`) landed partial scaffolding: partial-fraction infrastructure, norm-decomposition helper (`betaConstructive`), bivariate denominator-cleared log-derivative identity, `polyGPoly` definition + degree bounds, and Vieta/chord-sum reductions. The remaining per-sheet fiber decomposition step (Lemma 6) requires function-field theory; Q3 closed out with the axiom preserved as transient. Session 35 documents the Path-B honest close-out.
- **Silverman III Prop 3.4 mechanization**: the two narrow `CoordRingElt.divisor_*` axioms each cite a single specific fact from Silverman III Prop 3.4. Mechanizing these (like the residue identity) requires function-field infrastructure.

## Plan

See `docs/axiom-elimination-plan.md` for the full history of axiom-elimination work, including per-session commit logs for Queues 1 and 2.
