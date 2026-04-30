# Aristotle Job Ledger

This file tracks only Aristotle jobs submitted by this Codex session for
this repository. The Aristotle queue is shared, so jobs observed via
`uv run aristotle list` are not assumed to be ours unless they appear here.

## Active Jobs

- `65b53e80-0427-413e-b18c-ff86e7d6dd0a`
  - Submitted: 2026-04-30
  - Targets: `chord_fiber_product_ne_zero` and
    `chord_fiber_product_bar_rootMultiplicity_eq_zfiber` in
    `Divisor.GeometricSoundness`.
  - Prompt summary: discharge the two sharp residuals of the bar
    fiber-accounting bundle; rational non-vanishing of the opaque
    chord-fiber product, and per-`z` push-forward identity for its
    base change. Constraint: no broad new axiom; sharper sub-`sorry`s
    are acceptable.
  - Expected useful output: complete proofs if possible, otherwise a
    cleaner decomposition with the smallest residual sub-sorries and
    a derivation of the two targets from them.
  - Status: submitted, not yet checked.

## Historical Context

- `43872498-d8b8-4837-9cb2-4d0a31a68fe8` completed on 2026-04-30.
  - Target: `Divisor.GeometricSoundness.gd_support_rational_of_hAllZero`.
  - Result: did not fully discharge. Aristotle output snapshotted an older
    revision of the file (missing the local Frobenius-helpers block at lines
    318-374) and produced a proof skeleton that delegates to several new
    helpers, of which at least lines 1588 / 1610 / 1640 / 1805 still carry
    `sorry`. Decomposition is reasonable but cannot be cleanly merged onto
    the current `master`/`job2` snapshot without manual reconciliation.
- `edf1eaa2-0cd8-4bec-be91-ba8e5c1e7c82` completed on 2026-04-30.
  - Target: `Divisor.GeometricSoundness.chord_fiber_product_bar_factorisation`
  - Result: did not fully discharge the theorem from existing project facts.
    It reduced the theorem to a sharper missing statement,
    `chord_fiber_product_bar_z_fiber_accounting`, asserting nonvanishing of
    the base-changed chord-fiber product and equality between its root
    multiplicities at `z` and the sum of `gd.mult` over the `zLambdaBar`
    fiber. On 2026-04-30 (commit `f475ff3`) this single bundle was further
    split locally into two sharper named obligations:
    - `chord_fiber_product_ne_zero` (rational non-vanishing),
    - `chord_fiber_product_bar_rootMultiplicity_eq_zfiber` (per-`z`
      push-forward identity),
    with the original `chord_fiber_product_bar_z_fiber_accounting` bundle
    now derived from these via `Polynomial.map_ne_zero`.
- `8aef918d-d611-4ee2-9abf-87b50bec8ca8` was observed as `IN_PROGRESS`
  after the latest work-branch check, but this Codex session did not submit it.
  Treat it as external unless later evidence ties it to this session.
- Earlier Aristotle jobs visible in the global queue predate this ledger. Their
  ownership is not recorded here unless a local submit action is performed and
  the resulting job ID is appended.

## Update Rule

When this Codex session submits a job, immediately append:

- job ID
- submission time
- target theorem/file
- prompt summary
- expected useful output
- final status/result once checked
