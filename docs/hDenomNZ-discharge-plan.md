# Discharge plan for `hDenomNZ`

## Status: **COMPLETE**

The `hDenomNZ` precondition has been fully internalised. Public
`ma_extractable`, `ip_knowledge_sound`, and the `_paper` / `_clean`
/ `_witness_of_excess_*` variants no longer expose it.

**Final discharge route** (deviates from the original plan in §6):
the obstruction is absorbed inside `sigma_data_of_gd_support_rational`
via the *full* `denomScaledPoly` bad set `badDenomA0` (not just the
`DAtA₂Scaled` factor `badA₂Mod` originally planned). Internal proof
threads `A₀ ∉ badDenomA0` through `h_card_nondef` / `h_card_def_lb`
/ `h_nonspec`, with `h_spec` extended via the swap argument to also
handle `A₀ ∈ badDenomA0`. See:

- `Divisor/HDenomNZBound.lean` — `badDenomA0`,
  `badDenomA0_card_mul_card_sub_two_le`, `badDenomA0_card_le_linear_relax`,
  `exists_A0_outside_bad`.
- `Divisor/GeometricSoundness.lean` — refactored
  `card_logDerivCheckFnDefined_complement_le` (per-A₀ hypothesis) and
  `sigma_data_of_gd_support_rational` (drops `_hDenomNZ` parameter).
- `Divisor/ExtractorBridgeTheorems.lean` — public theorems no longer
  carry `hDenomNZ`.

Axiom closure: unchanged. No new axioms, no `sorryAx`. The
`badA₂Mod_card_mul_card_sub_two_le` lemma is preserved as a
narrower-but-cheaper alternative; `badDenomA0_card_mul_card_sub_two_le`
generalises it across the full denominator factorisation.

The remainder of this document is preserved as historical record of
the original plan.

---

## Original status (before discharge)

`hDenomNZ` was a hypothesis on `Divisor.ma_extractable`
(at `Divisor/ExtractorBridgeTheorems.lean:60`). The theorem was
**conditional** on this — it proved "extraction holds when
`hDenomNZ` holds", not unconditional knowledge soundness.

This corresponded to the paper's `event_deg`-not-occurring
precondition (`~/paper/divisor-org/sections/ip.tex:396-398`). The
paper's stated bounds **include** `Pr[event_deg]` explicitly; the
Lean version had to absorb it into the count to be unconditional.

## Existing Lean infrastructure

The factor structure of `denomScaledPoly` is:

```
denomScaledPoly D P k B A₀
  = DAllScaled D A₀ * dxdzAllScaled A₀ * linesProductScaled P k B A₀
```

with elementary sub-factors:

| Sub-factor | natDegree (outer Y) | Non-vanishing source |
|------------|---------------------|----------------------|
| `DAtA₀Poly` | 0 | always (scalar) |
| `DAtA₁Poly` | < 2 (theorem `DAtA₁Poly_natDegree_lt_two`) | `D ≠ 0` from `hD` |
| `DAtA₂Scaled` | ≤ `D.degE` (CAN exceed 2) | per-`A₀` structural |
| `dxdzDenA₀Scaled` | < 2 (theorem `dxdzDenA₀Scaled_natDegree_lt_two`) | `hSmooth` + `A₀ ∈ E.points` |
| `dxdzDenA₁Scaled` | < 2 | `hSmooth` |
| `dxdzDenA₂Scaled` | < 2 | `hSmooth` |
| `lineEvalNumAt` (per j) | < 2 (theorem `lineEvalNumAt_natDegree_lt_two`) | `A₀ ≠ distinctR_j` |

By `not_curveEqPoly_dvd_of_natDegree_lt`, the natDeg<2 factors are not
divisible by `curveEqPoly`. By `curveEqPoly_dvd_mul` (primality), the
product mod `curveEqPoly` ≠ 0 iff every factor is.

## The blocker: `DAtA₂Scaled`

`DAtA₂Scaled` has natDeg up to `D.degE`, which CAN be ≥ 2. So the
simple natDeg<2 argument fails.

But `bivEval (DAtA₂Scaled D A₀) A₁ = (A₁.1 − A₀.1)^D.degE · D.eval(chordX₂ A₀ A₁) (chordY₂ A₀ A₁)`
on the non-vertical cone. So `DAtA₂Scaled mod curveEqPoly = 0` (the
"bad A₀" event) implies `D` vanishes at the chord-third of every
non-vertical `A₁`.

## Existing infrastructure (key finding)

`Divisor/ClearedPolyForm.lean:2241` proves:

```lean
theorem DAtA₂_zero_pairs_card_le (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p => D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0)).card
    ≤ (D.degE + 2) * E.points.card
```

This bounds the **joint** count of `(A₀, A₁)` pairs where `D` vanishes
at the chord-third.

## Discharge strategy (codex-validated)

1. **Define** `badA₂Mod := E.points.filter fun A₀ => DAtA₂Scaled D A₀ %ₘ curveEqPoly E = 0`.

2. **Lemma**: for `A₀ ∈ badA₂Mod` and non-vertical `A₁ ∈ E.points`,
   `D.eval (chordX₂ A₀ A₁) (chordY₂ A₀ A₁) = 0`. Proof via
   `bivEval_eq_modByMonic_on_E E _ hA₁` + the explicit form
   `bivEval_DAtA₂Scaled_eq` + `pow_ne_zero` for the prefactor.

3. **Marginal bound**: by fiber argument
   (`Finset.card_filter_add_card_filter_not` + `card_points_with_fst_eq_le`):
   ```
   badA₂Mod.card * (E.points.card − 2)
     ≤ (D.degE + 2) * E.points.card
   ```
   Solved by `omega` under the existing `hLargeQ` regime.

4. **For all other elementary factors**: their non-vanishing follows
   from the existing preconditions (`hD`, `hSmooth`, `A₀ ∈ E.points`,
   `A₀ ∉ distinctR`) plus their natDeg-<-2 theorems +
   `not_curveEqPoly_dvd_of_natDegree_lt`.

5. **Composite**: by `curveEqPoly_dvd_mul` primality applied
   recursively, `denomScaledPoly D P k B A₀ %ₘ curveEqPoly E ≠ 0` for
   any `A₀ ∈ E.points \ (zerosFinset(D) ∪ distinctR ∪ badA₂Mod)`.

6. **Theorem statement update**: drop `hDenomNZ` from
   `ma_extractable`. The existing accept-count bound proof handles
   non-`badA₂Mod` `A₀` (per existing infrastructure). For
   `A₀ ∈ badA₂Mod`, count contribution ≤ `badA₂Mod.card * E.points.card`
   ≤ `(D.degE + 2) * E.points.card / (1 − 2/|E|)` (via step 3),
   absorbable into the existing `(3·d + 9·k + 71)·|E|` term.

## Estimated work

Substantial — codex's earlier 150 LOC estimate was low because it
underestimated the per-factor non-vanishing proofs (each elementary
factor needs explicit nonzero arguments). Realistic estimate: 300-500
LOC, including the new helper lemma + theorem-statement update +
proof-structure changes.

This is **not polish** but is a real next-priority task that closes
the headline theorem's conditional-vs-unconditional gap.
