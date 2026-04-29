# Aristotle Job Ledger

This file tracks only Aristotle jobs submitted by this Codex session for
this repository. The Aristotle queue is shared, so jobs observed via
`uv run aristotle list` are not assumed to be ours unless they appear here.

## Active Jobs

- `edf1eaa2-0cd8-4bec-be91-ba8e5c1e7c82`
  - Submitted: 2026-04-29
  - Target: `Divisor.GeometricSoundness.chord_fiber_product_bar_factorisation`
  - Prompt summary: prove the geometric divisor-of-norm factorisation over
    `F_qbar` without adding axioms; if blocked, isolate the smallest missing
    function-field/local-algebra lemma.
  - Expected useful output: either a proof replacing the theorem's `sorry`, or
    a precise missing lemma statement for the divisor-of-norm bridge.
  - Status: submitted, not yet checked.

## Historical Context

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
