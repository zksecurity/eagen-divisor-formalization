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

`Divisor.ma_extractable` and `Divisor.ip_knowledge_sound` depend on 8 axioms:

| Axiom | Source |
|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | Lean core |
| `ECPoint.add_assoc`, `add_comm`, `neg_add_cancel` | Silverman III §2 (group law) |
| `CoordRingElt.divisor_group_sum_zero` | Silverman III Prop 3.4 (Abel's theorem on E) |
| `polyG_zero_trace_formula` | Silverman III Prop 3.4 (function-field trace-of-log-derivative identity) + density extension |

The former transient axiom `polyG_zero_of_logDerivCheck_identically_zero` was eliminated in Phase 4; the Phase-4 hypothesis `hPolyGZero` has been replaced by the classical axiom `polyG_zero_trace_formula` (Silverman III Prop 3.4 applied to the degree-3 extension `F_q(E)/F_q(z)`, `z = y − λ x`, plus a polynomial-degree density extension on `polyGPoly`). See "Phase 4 narrowing" below.

`Divisor.ma_completeness` depends on the Lean core + group-law axioms + `weil_reciprocity_honest` (Silverman III §X).

Hasse-Weil bounds (`hasse_weil_upper`, `hasse_weil_lower`) are project-wide axioms but are not on the current soundness dependency path.

### Phase 4 narrowing — residue-identity hypothesis

The former transient axiom `polyG_zero_of_logDerivCheck_identically_zero` has been converted to a theorem that takes a hypothesis `hPolyGZero`, threaded through the consumer chain (`distinctSigma_exists` → `extractor_succeeds_and_isPrincipal` → `extractorSucceeds_of_logDerivCheck_identically_zero_general` → `extracted_scalars_valid` → `ma_extractable` / `ip_knowledge_sound`). The hypothesis states, schematically:

> For every principal-divisor candidate `β_fun` satisfying the Silverman III.3.5 support/coverage/degree-sum conditions, `polyG E (zerosAt msg.toD) (multAt β_fun msg.toD) (distinctR) (distinctM')` vanishes on every non-vertical pair on `E × E`.

The hypothesis packages two classical function-field facts:

1. **Lemma 6** (paper's `lem:log-deriv-norm`, `sections/ec.tex:557-579`): the chord-sum identity `Σᵢ logDerivTerm(Aᵢ, λ) = -Σ_k β_k · L_Q(Q_k)⁻¹`. Phase 3 (`Divisor/Lemma6.lean`) reduces Lemma 6 to a scalar log-derivative-match hypothesis `chordLogDerivMatchesNormZ E D A₀ A₁`; discharging it unconditionally requires the function-field norm identity `N(D)(z) = lc(D)^3 · ∏_k (z - z(Q_k))^{β_k}` as a polynomial equality in `F_q[z]`. Phase 6 (`Divisor/ChordLogDerivProof.lean`) further narrows the remaining gap to the scalar identity `chord_sum_eq_residue_sum`.
2. **Density extension** from defined non-vertical pairs to all non-vertical pairs, using the polynomial form `polyGPoly` (`Divisor/PolyGBridge.lean`) + degree bounds + `card_zeros_on_E_le` (`Divisor/CubicIntersection.lean`).

At the `ma_extractable` / `ip_knowledge_sound` boundary the `hPolyGZero` hypothesis is discharged by the classical axiom `polyG_zero_trace_formula` (cited as Silverman III Prop 3.4 + density; see `Divisor/ExtractorBridge.lean`). The intermediate theorems in the chain still take `hPolyGZero` as a hypothesis for compositional convenience. The scalar bridge at a defined non-vertical pair (Step-5 `polyG ⇔ paperResidueDivided` equivalence) is already mechanized in `Divisor/ResidueIdentity.lean` (`polyG_eq_zero_iff_paperResidue`).

## Outstanding work

- **Mechanize `polyG_zero_trace_formula`**: the new classical axiom citing Silverman III Prop 3.4 + density. Two sub-tasks:
  - **Function-field norm identity** (Lemma 6): prove `N(D)(z) = lc(D)^3 · ∏_k (z - z(Q_k))^{β_k}` as a polynomial equality in `F_q[z]`. Phase 6 localizes this to `chord_sum_eq_residue_sum` in `Divisor/ChordLogDerivProof.lean`.
  - **Density argument**: polynomial-degree bound on `polyGPoly` + `card_zeros_on_E_le` on E × E extends vanishing from defined pairs to all non-vertical pairs.
- **Silverman III Prop 3.4 mechanization**: the narrow `CoordRingElt.divisor_group_sum_zero` axiom cites Abel's theorem on E from Silverman III Prop 3.4. Mechanizing it requires function-field infrastructure.

## Plan

See `docs/axiom-elimination-plan.md` for the full history of axiom-elimination work, including per-session commit logs for Queues 1 and 2.
