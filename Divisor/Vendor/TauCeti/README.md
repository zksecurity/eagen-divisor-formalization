# Vendored Tau Ceti core

Seven files vendored from the Tau Ceti library:

- Repository: https://github.com/TauCetiProject/TauCeti
- Commit: `076ae23499c00fc000838bec23b0082649b838a4` (2026-08-21)
- License: Apache-2.0 (original copyright headers retained in each file)

| File here | Original path under `TauCeti/` | Provides |
|---|---|---|
| `SeparableDegree.lean` | `FieldTheory/SeparableDegree.lean` | helper |
| `FieldRange.lean` | `FieldTheory/IntermediateField/FieldRange.lean` | helper |
| `Finrank.lean` | `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Finrank.lean` | `finrank_functionField` (F(W) quadratic over F(x)) |
| `Eval.lean` | `AlgebraicGeometry/EllipticCurve/Affine/Eval.lean` | evaluation helpers |
| `CoordinateRing.lean` | `AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean` | `conj`, `mul_conj`, `isIntegrallyClosed_coordinateRing`, `isDedekindDomain_coordinateRing` |
| `XYIdealMaximal.lean` | `AlgebraicGeometry/EllipticCurve/Affine/XYIdealMaximal.lean` | `XYIdeal_isMaximal`, `XYIdeal_ne_bot`, `XYIdeal_eq_iff`, `finrank_quotient_eq_one_iff` |
| `LocalRing.lean` | `AlgebraicGeometry/EllipticCurve/Affine/LocalRing.lean` | DVR at point ideals |

Why vendored rather than a lake dependency: upstream has no release
tags, tracks Lean `v4.34.0-rc1` with a mathlib *master* pin, and uses
the `module` / `public import` system throughout; this repository is on
stable Lean/mathlib v4.33.1. These files supply the Dedekind-domain
and valuation infrastructure behind `Divisor/OrdP/`.

Local adaptations, uniformly applied and marked `-- [vendor]` where
nontrivial:

- `module` header removed; `public import` → `import`;
  `public section` → `section`.
- Internal `TauCeti.*` imports repointed to `Divisor.Vendor.TauCeti.*`.
- API adjustments for mathlib v4.33 where upstream targets v4.34/master.

The Lean namespaces (`TauCeti.*`) are kept as upstream to minimize the
diff against the source, so upstream syncs are a re-run of the vendoring
transform plus a diff review.
