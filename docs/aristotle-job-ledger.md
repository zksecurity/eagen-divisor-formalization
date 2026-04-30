# Aristotle Job Ledger

This file tracks only Aristotle jobs submitted by this Codex session for
this repository. The Aristotle queue is shared, so jobs observed via
`uv run aristotle list` are not assumed to be ours unless they appear here.

## Active Jobs

- `2330e1ea-1086-4711-9e82-76835ccae3cc`
  - Submitted: 2026-04-30
  - Target: geometric divisor-of-norm bridge plumbing in
    `Divisor.GeometricSoundness`
  - Prompt summary: add a narrow `Fqbar` geometric norm-factorisation bridge
    axiom, then derive `chord_fiber_product_ne_zero`,
    `chord_fiber_product_bar_rootMultiplicity_eq_zfiber`, and the existing
    z-fiber accounting theorem from it.
  - Expected useful output: a clean proof/axiom boundary for the two chord
    residual sorries, avoiding the old `splitsOnE`-gated axiom.
  - Status: submitted, not yet checked.
- `dbe4c0c9-30f5-4eef-ae28-5c5f2ebf24ea`
  - Submitted: 2026-04-30
  - Target: `Divisor.GeometricSoundness.chord_fiber_product_ne_zero`
  - Prompt summary: fill only the rational non-vanishing sorry for
    `chord_fiber_product E lam D`; do not alter statements or collapse the
    proof boundary.
  - Expected useful output: a proof from the existing norm/function-field API,
    or a precise explanation of the missing non-vanishing lemma.
  - Status: COMPLETE; inspected 2026-04-30. No proof produced.
    Aristotle reported the statement is not provable from the current API
    because `chord_fiber_product` is opaque and the only connecting axiom,
    `chord_fiber_product_eq_normZ_under_split`, requires `splitsOnE E D`.
    Useful conclusion: we need a dedicated norm non-vanishing bridge or a
    geometric divisor-of-norm statement.
- `0ae3f8d9-c506-48f3-b920-c3eedad49a0d`
  - Submitted: 2026-04-30
  - Target:
    `Divisor.GeometricSoundness.chord_fiber_product_bar_rootMultiplicity_eq_zfiber`
  - Prompt summary: fill only the per-`z` root-multiplicity push-forward sorry;
    do not restore the broader bundled axiom.
  - Expected useful output: a proof of the divisor-of-norm fiber accounting
    statement, or a precise missing lemma if the API is insufficient.
  - Status: COMPLETE_WITH_ERRORS; inspected 2026-04-30. No proof produced.
    Aristotle identified the exact missing bridge as a geometric
    divisor-of-norm factorisation over `Fqbar`, e.g.
    `chord_fiber_product_bar_eq_geom_prod`, from which the per-`z`
    root-multiplicity equality should be derived.
- `4912fc36-585f-4956-abbe-0c59755e87bb`
  - Submitted: 2026-04-30
  - Target: `Divisor.GeometricSoundness.gd_support_rational_of_hAllZero`
  - Prompt summary: attempt the Frobenius descent/rational support proof using
    the current geometric residue infrastructure; if blocked, isolate small
    helper lemmas rather than adding an axiom.
  - Expected useful output: a complete proof if possible, otherwise a sharper
    decomposition of the rationality/Frobenius-orbit obstruction.
  - Status: COMPLETE_WITH_ERRORS; inspected 2026-04-30. Useful helper output
    was ported in commit `b7f9312`: `Divisor.FrobDescentHelpers` proves
    abstract partial-fraction uniqueness and slope choice; `Divisor.SlopeChoice`
    instantiates slope choice for `GeomPoint`. The broad rational-support sorry
    is now reduced to `frob_descent_mult_zero_of_not_fixed`.
- `22cf9f49-19da-4e4a-83b0-6a6b6ef441f4`
  - Submitted: 2026-04-30
  - Target: `Divisor.GeometricSoundness.frob_descent_mult_zero_of_not_fixed`
  - Prompt summary: focus only on the narrowed Frobenius-descent core; use the
    newly integrated slope-choice and partial-fraction helpers; do not touch
    `WeilReciprocityDescent` and do not add axioms.
  - Expected useful output: a complete proof of the narrowed theorem, or a
    smaller missing bridge connecting the bar-level residue identity to the
    one-variable partial-fraction form.
  - Status: QUEUED when checked 2026-04-30.
- `43872498-d8b8-4837-9cb2-4d0a31a68fe8`
  - Submitted: 2026-04-30
  - Target: `Divisor.GeometricSoundness.gd_support_rational_of_hAllZero`
  - Prompt summary: attempt the hard Frobenius/residue-specialization proof
    that `hAllZero` forces every geometric support point to be `F_q`-rational;
    if too large, decompose to minimal named missing lemmas without adding
    axioms.
  - Expected useful output: a complete proof if possible, otherwise a sharper
    decomposition of the rationality/Frobenius-orbit obstruction.
  - Status: COMPLETE; inspected 2026-04-30. Not a drop-in patch for the
    current branch. It proved the target by introducing three new helper
    sorries (`geomPolyGFull_identically_zero_on_ExE`,
    `geomPolyGFullBar_vanishes_on_Ebar_of_vanish_on_E`, and
    `support_rational_of_residues_vanish`) plus a proved helper
    `gd_mult_natCast_ne_zero`. Treat as proof-plan material, not code to
    merge directly.

## Historical Context

- `edf1eaa2-0cd8-4bec-be91-ba8e5c1e7c82` completed on 2026-04-30.
  - Target: `Divisor.GeometricSoundness.chord_fiber_product_bar_factorisation`
  - Result: did not fully discharge the theorem from existing project facts.
    It reduced the theorem to a sharper missing statement,
    `chord_fiber_product_bar_z_fiber_accounting`, asserting nonvanishing of
    the base-changed chord-fiber product and equality between its root
    multiplicities at `z` and the sum of `gd.mult` over the `zLambdaBar`
    fiber. This is the exact function-field norm push-forward lemma needed to
    replace the broad chord-factorisation axiom.
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
