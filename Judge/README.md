# Judge — independent verification of the headline theorems

This directory configures [`leanprover/comparator`](https://github.com/leanprover/comparator),
a trustworthy judge for Lean proofs, to verify the library's headline
theorems against the frozen statements in `Challenge.lean` (repo root).
CI runs it on every push (`.github/workflows/ci.yml`), together with the
toolchain's built-in `leanchecker`.

## What each layer guarantees

| Check | Catches |
|---|---|
| `lake build Tests` (axiom-closure pins) | Any drift in a headline theorem's kernel-level axiom closure: a revived `sorryAx`, `Lean.ofReduceBool` (`native_decide`), or a new axiom |
| `lake env leanchecker <module>`, per library module | Environment hacking: declarations added to a `.olean` without passing the kernel. CI replays every module of this library; dependency oleans come from the mathlib cache, which mathlib's own CI leanchecks |
| Comparator, `Judge/headline.json` / `Judge/hasse.json` | A proved theorem whose **statement** differs from the frozen challenge — including smuggled hypotheses (`theorem foo (h : P) : P`), which no axiom or kernel check can see — plus an axiom allowlist and an independent kernel replay of the full export |

Comparator builds challenge and solution inside a
[`landrun`](https://github.com/Zouuup/landrun) sandbox, exports both
with [`lean4export`](https://github.com/leanprover/lean4export), checks
that every judged theorem's exported type is identical between the two,
checks the solution's axiom closure against `permitted_axioms`, and
replays the whole solution export through a fresh kernel.

## The two configurations

* `headline.json` — the axiom-free headliners (`ma_extractable`,
  `ip_extractable`, `ma_completeness`, `ma_completeness_q`,
  `ip_completeness`, `ip_completeness_q`,
  `ma_completeness_binary_any_length`,
  `ma_completeness_binary_any_length_cert`), permitted axioms exactly
  `propext`, `Quot.sound`, `Classical.choice`.
* `hasse.json` — the Hasse–Weil-priced variants
  (`ma_extractable_hasse`, `ip_extractable_hasse`), additionally
  permitting `Divisor.hasse_weil_textbook`. Because permitted axioms
  are themselves compared between challenge and solution, the judge
  also pins the *statement* of that axiom.

## Trust base

To trust a green judge run you must trust: `Challenge.lean` and its
transitive imports (`Divisor.Soundness` for the protocol/extractor
definitions and `Divisor.SafeSupportDefs` for the binary-support and
general-position definitions; nothing that proves a judged theorem),
this project's `lakefile.toml`, the Lean kernel, and the sandbox.
**Review changes to `Challenge.lean` with the same care as an
axiom**: it is the statement of record. The definitions it imports
are part of that statement.

## Running locally

Build the three binaries (once):

```bash
# landrun (Go)
git clone https://github.com/Zouuup/landrun && cd landrun
go build -o ~/bin/landrun ./cmd/landrun

# lean4export, at the tag matching this project's toolchain,
# built WITH this project's toolchain
git clone https://github.com/leanprover/lean4export && cd lean4export
git checkout v4.33.0
cp /path/to/lean-divisors/lean-toolchain lean-toolchain
lake build

# comparator (its own toolchain)
git clone https://github.com/leanprover/comparator && cd comparator
lake build
```

Then, from the repository root:

```bash
export COMPARATOR_LANDRUN=~/bin/landrun
export COMPARATOR_LEAN4EXPORT=/path/to/lean4export/.lake/build/bin/lean4export
lake env /path/to/comparator/.lake/build/bin/comparator Judge/headline.json
lake env /path/to/comparator/.lake/build/bin/comparator Judge/hasse.json
```

Success prints `Your solution is okay!`. On a machine where you also
distrust `landrun` itself, wrap the invocation in `systemd-run` as
described in comparator's README.
