# Plan: probabilistic challenge statements via VCV-io

Status: exploration/planning only — no code changes yet.

Goal: restate the headline "counting of accepting challenges" bounds
(`ma_extractable`, `ma_completeness`, `ip_*`, and their `_q`/`_hasse`
forms) as genuine probability statements — "for a uniformly random
challenge, the verifier accepts with probability ≤ ε" — using
[VCV-io](https://github.com/Verified-zkEVM/VCVio) as the probability
framework.

TL;DR of the exploration: **this is a near-perfect fit and a thin
layer.** VCVio's `probEvent_uniformSelectFinset` lemma says
`Pr[p | $ s] = {x ∈ s | p x}.card / s.card`, and our accept/reject sets
are *definitionally* `Finset.filter` of the verifier predicate over the
challenge Finset. So each probabilistic headline is a two-step
corollary of the existing counting theorem: rewrite the probability to
a cardinality ratio, then apply the existing numerator bound and the
existing denominator lower bound via `ENNReal.div_le_div`. Toolchains
match exactly (both this repo and VCVio pin `leanprover/lean4:v4.33.1`
and mathlib commit `0df444a360`, tag `v4.33.1`), so the dependency can
be added with no version friction.

## 1. What we have today (the counting layer)

All in `Divisor/`:

- `validPairs E : Finset ((ZMod q × ZMod q) × (ZMod q × ZMod q))` —
  the soundness challenge space (`BassaMonic.lean:280`), with
  `card_validPairs_lb : n·n − 3·n ≤ |validPairs E|` (`n = E.points.card`).
- `maVerifierAccepts E stmt msg chal hkm : Prop`
  (`Protocol.lean:245`) — note: a `Prop`, not decidable in general,
  because `stmt.admSet` is an arbitrary predicate
  (`Protocol.lean:32`). Everything downstream already lives under
  `open Classical`.
- `maAcceptSet E stmt msg hkm = (validPairs E).filter (fun p =>
  maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)` — *by `rfl`*
  (`Soundness.lean:373`, unfolding lemma `maAcceptSet_eq`).
- `maRejectSet` — same shape over `E.points ×ˢ E.points` with the
  negated predicate (`Soundness.lean:396`).
- Headlines (`Headlines.lean`): `ma_extractable` gives
  `|maAcceptSet| ≤ 24(d+k+3)·n` (or a witness is extracted);
  `ma_completeness` gives `|maRejectSet| ≤ (3d+4)·n`; IP variants add
  `IPUniqueThirdRound`.
- `ma_soundness_probability` (`Headlines.lean:305`) is already a
  "probability" statement *in multiplied nat form*
  (`|accept|·(n²−3n) ≤ 24(d+k+3)·n·|validPairs|`), deliberately
  avoiding division. The VCVio layer would supersede this with the real
  quotient form, over an actual sampling semantics.

## 2. What VCV-io provides (survey of current `main`)

Checked out at exploration time; VCVio has been substantially
modernized (it now uses Lean's module system — `module` +
`public import` + `@[expose] public section` — and `Pr[…]` notation).

Compatibility:

| | this repo | VCVio `main` |
|---|---|---|
| toolchain | `leanprover/lean4:v4.33.1` | `leanprover/lean4:v4.33.1` |
| mathlib | `0df444a360` (`v4.33.1`) | `0df444a360` (`v4.33.1`) |
| extra deps | — | `PolyFun`, `loom2` (+ transitive `cslib`), no binary cache for these |

Relevant API (all names verified against source):

- `ProbComp α := OracleComp unifSpec α` — computations with a uniform
  randomness oracle (`VCVio/OracleComp/ProbComp.lean`).
- Probabilities are `ℝ≥0∞`: `probOutput` / `probEvent` /
  `probFailure`, notation `Pr[= x | mx]`, `Pr[p | mx]`, `Pr[⊥ | mx]`
  (`VCVio/EvalDist/Defs/Basic.lean`).
- **Uniform selection from a `Finset`** (`hasUniformSelectFinset`,
  noncomputable): `$ s : OptionT ProbComp α`, with

  ```lean
  @[simp] lemma probEvent_uniformSelectFinset (p : α → Prop) [DecidablePred p] :
      Pr[ p | $ s] = {x ∈ s | p x}.card / s.card

  @[simp] lemma probFailure_uniformSelectFinset :
      Pr[⊥ | $ s] = if s.Nonempty then 0 else 1
  ```

  `{x ∈ s | p x}` is mathlib notation for `s.filter p` — i.e. the
  right-hand side is *literally* `|maAcceptSet| / |validPairs|` when
  `s := validPairs E` and `p` is the accept predicate.
- **Uniform selection from a type**: `SampleableType β` with `$ᵗ β`,
  `probEvent_uniformSample : Pr[p | $ᵗ α] =
  (Finset.univ.filter p).card / Fintype.card α`, never fails, and a
  noncomputable bridge `SampleableType.ofFintype` for any nonempty
  `Fintype` — usable for the subtype `↥(validPairs E)` via
  `Fintype.card_coe`.
- **Protocol framework** (`VCVio/CryptoFoundations/SigmaProtocol.lean`):
  `ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel` — a
  commit–challenge–respond protocol with a uniformly drawn challenge
  (`$ᵗ Chal`), deterministic `verify : … → Bool`; properties
  `PerfectlyComplete`, `UniqueResponses`, `HVZK`, `realTranscript`.
  `SigmaProtocol` extends it with `sim` and
  `extract (chal₁ resp₁ chal₂ resp₂) : ProbComp Wit` plus
  `SpeciallySound`.

## 3. The bridge, precisely

The entire counting→probability conversion is this observation:

```
Pr[ accept | $ (validPairs E) ]
    = |(validPairs E).filter accept| / |validPairs E|      -- probEvent_uniformSelectFinset
    = |maAcceptSet E stmt msg hkm| / |validPairs E|        -- maAcceptSet_eq (rfl) + filter_congr_decidable
    ≤ 24(d+k+3)·n / (n² − 3n)                              -- ENNReal.div_le_div
                                                           --   (ma_extractable numerator bound)
                                                           --   (card_validPairs_lb denominator bound)
```

`ENNReal.div_le_div : a ≤ b → d ≤ c → a / c ≤ b / d` does the last
step in one move — numerator up, denominator down — with no
nonzeroness side conditions (`ℝ≥0∞` handles `0` and `∞` benignly; the
hypotheses `hLargeQ`/`hSample` in fact make both denominators positive,
so the bound is also non-vacuous).

Two details, both benign:

- *Decidability*: `probEvent_uniformSelectFinset` wants
  `[DecidablePred p]` and `maVerifierAccepts` is undecidable in
  general (arbitrary `admSet`). The repo is already classical
  everywhere (`maAcceptSet` is `noncomputable`, files `open
  Classical`); two `filter`s under different `Decidable` instances are
  identified by `Finset.filter_congr_decidable`.
- *Failure*: `$ (s : Finset α)` lives in `OptionT ProbComp` and fails
  iff `s = ∅`. Under `hSample` (`… + 1 ≤ |validPairs|`) the challenge
  space is nonempty, so `Pr[⊥] = 0`; for completeness,
  `E.points ×ˢ E.points` nonemptiness is immaterial because the
  statement stays true degenerately (see §4.2).

## 4. Proposed statements (target shapes)

New file(s), additive only — nothing existing moves. Sketches below
type-check "on paper" against the verified API; exact casts to be
settled in implementation.

### 4.1 MA soundness, probabilistic dichotomy

```lean
open scoped ENNReal

/-- **MA knowledge soundness, probabilistic form.** Either the
straight-line extractor produces a valid witness, or a uniformly
random valid challenge pair is accepted with probability at most
`24(d+k+3)·n / (n² − 3n)`. -/
theorem ma_soundness_vcv (stmt : DlogStatement E.q) …same hypotheses as ma_extractable… :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    Pr[ (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm) | $ (validPairs E) ]
      ≤ (24 * (stmt.degBound + stmt.k + 3) * E.points.card : ℝ≥0∞) /
        ((E.points.card * E.points.card - 3 * E.points.card : ℕ) : ℝ≥0∞)
```

Proof: `rcases ma_extractable …`; on the counting branch,
`rw [probEvent_uniformSelectFinset]`, identify the filter with
`maAcceptSet`, finish with `ENNReal.div_le_div` +
`card_validPairs_lb`. An *exact-denominator* variant
(`≤ …/(validPairs E).card`) is even shorter and arguably the more
faithful statement; we can state both.

### 4.2 MA completeness, probabilistic form

```lean
/-- **MA completeness, probabilistic form.** The honest prover's
message is rejected on a uniformly random challenge pair with
probability at most `(3d+4)/n`. -/
theorem ma_completeness_vcv …same hypotheses as ma_completeness… :
    Pr[ (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)
        | $ (E.points ×ˢ E.points) ]
      ≤ (3 * stmt.degBound + 4 : ℝ≥0∞) / E.points.card
```

Here `Pr = |maRejectSet| / n²` and the counting bound gives
`≤ (3d+4)·n / n²`; cancel one `n` (`ENNReal.mul_div_mul_right`-style;
the `n = 0` corner is fine since `x/0 = ∞` for `x ≠ 0` in `ℝ≥0∞`, and
the probability over an empty finset is `0`). Optionally also the
positive form `1 - (3d+4)/n ≤ Pr[accept]` via
`probEvent_not` / total-mass lemmas (truncated subtraction in `ℝ≥0∞`
makes this true even when the bound exceeds 1).

### 4.3 IP variants and `_hasse` variants

- `ip_soundness_vcv`: the §4.1 dichotomy conjoined with
  `IPUniqueThirdRound` (unchanged — uniqueness is not probabilistic).
- `ip_completeness_vcv`: `Pr[¬∃ msg3, ipVerifierAccepts … | $ (E.points ×ˢ E.points)]
  ≤ (3d′ + 9k + 71)/n`, from `ip_completeness`.
- `_hasse` forms in `Divisor/Hasse.lean`'s style: from
  `ma_soundness_probability_hasse`'s numerator/denominator pair, get
  `Pr[accept] ≤ 36(d+k+4)·q / ((q−3)(q−9))` (q-only currency, priced
  by the Hasse–Weil axiom, so these live in the terminal
  probabilistic-Hasse module).

### 4.4 Optional: game-shaped and framework-shaped versions

Two further layers, in increasing order of ambition; both optional on
top of 4.1–4.3:

1. **Game form.** Package the challenge round as a computation, which
   is the idiom VCVio's crypto developments use:

   ```lean
   noncomputable def maGame (stmt) (msg) (hkm) : OptionT ProbComp Bool := do
     let p ← $ (validPairs E)
     return decide (maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)  -- classical decide

   theorem ma_soundness_game : … ∨ Pr[= true | maGame E stmt msg hkm] ≤ ε
   ```

2. **`ChallengeVerifyProtocol` instantiation** for the 3-round IP:
   `Stmt := DlogStatement E.q ×' side conditions`, `Wit :=
   DlogWitness E.q`, `Commit := MAProverMsg E.q`, `Chal :=
   ↥(validPairs E)` (needs a `SampleableType` instance via
   `SampleableType.ofFintype` + nonemptiness from `hSample` — a
   hypothesis, so the instance is per-theorem `haveI`, not global),
   `Resp := IPProverMsg3 E.q`. Findings from the fit check:
   - `verify` must be `Bool`: wrap the `Prop` verifier with classical
     `decide` (noncomputable structure fields are fine).
   - `PerfectlyComplete` does **not** fit — our completeness is
     statistical. We'd state our own
     `Pr[…] ≥ 1 − ε` on `realTranscript`; VCVio currently has no
     statistical-completeness definition for this structure (worth an
     upstream issue/PR).
   - `UniqueResponses` almost matches `IPUniqueThirdRound`, but ours
     holds only under nonvanishing side conditions, so only a
     restricted/conditional instantiation is possible.
   - `SigmaProtocol.extract` takes `(chal₁, resp₁, chal₂, resp₂)`
     only — no statement and no commitment — so our *straight-line*
     extractor (`maExtractor E stmt msg …`, which reads the
     commitment and never needs a challenge, let alone two) is
     **strictly stronger but not expressible** in that field's
     signature. Recommendation: stay on `ChallengeVerifyProtocol`
     (which has no extractor field) and state straight-line
     extractability ourselves; mention upstream that an
     `extract` with `Stmt → Commit → …` access would fit
     divisor-style protocols.

   Related: ArkLib (Verified-zkEVM's proof-system library on top of
   VCVio) has round-indexed reductions with explicit
   knowledge-soundness errors; if the goal is eventual integration
   into that ecosystem, layer 4.1–4.3 is exactly the lemma shape its
   extractors consume, and this repo would not need ArkLib as a
   dependency to be consumable from it.

## 5. Engineering plan

Dependency and layout — designed so the existing surface (and the
Comparator-judge independence of `Challenge.lean`) is untouched:

1. `lakefile.toml`: add `[[require]] name = "VCVio", git =
   "https://github.com/Verified-zkEVM/VCVio", rev = "<pinned commit>"`.
   Pin a commit, not `main`: VCVio is under active development
   (deprecations dated days ago) and API churn is the main external
   risk. Same mathlib pin, so the manifest update is clean.
2. New lean_lib `DivisorProb` (root `DivisorProb.lean` +
   `DivisorProb/` dir), the only code importing VCVio. The core
   `Divisor` lib, `Challenge` lib, and the judge pipeline are
   unchanged; the new theorems are additive corollaries importing
   `Divisor.Headlines` (and `Divisor.Hasse` for the priced forms in a
   separate terminal module, mirroring the existing axiom hygiene).
3. Imports needed are small: `VCVio.OracleComp.ProbComp` covers
   §4.1–4.3 (Finset selection + `Pr` lemmas); only §4.4 layer 2 pulls
   `VCVio.OracleComp.Constructions.SampleableType` /
   `VCVio.CryptoFoundations.SigmaProtocol`. Lake builds only the
   transitively imported modules, which keeps the build-cost increase
   well below "all of VCVio".
4. Module-system interop: VCVio files are `module`s with
   `@[expose] public section`, this repo's files are plain. A plain
   file importing a module sees its public scope, which is where all
   the needed lemmas live. Verify with the M0 smoke build below before
   committing to anything.
5. Build cost: mathlib comes from cache as today; VCVio + PolyFun +
   loom2 (+ cslib) build from source with no binary cache. Mitigate by
   caching `.lake` in CI and by the minimal-import discipline of (3).

Milestones:

- **M0 — smoke test** (small): add the `require`, one file importing
  `VCVio.OracleComp.ProbComp` next to `Divisor.Soundness`, `lake
  build DivisorProb`. Validates module interop, measures real build
  cost, surfaces any diamond/universe surprises. Go/no-go gate.
- **M1 — bridge lemmas** (small): `Pr[p | $ (validPairs E)] =
  (validPairs E).filter p |>.card / (validPairs E).card` specialized
  cast-ready helpers; `Pr[⊥] = 0` under `hSample`;
  filter-instance-identification helpers.
- **M2 — headline corollaries** (medium): §4.1, §4.2, §4.3 (six-ish
  theorems), README section documenting the probabilistic surface and
  its exact relation to the counting surface.
- **M3 — game/framework layer** (optional, medium):
  §4.4(1) games; §4.4(2) restricted `ChallengeVerifyProtocol`
  instantiation for IP; upstream issues to VCVio (statistical
  completeness; extractor signature).

Fallback if the dependency is rejected at M0: mathlib-only statement
via `PMF.uniformOfFinset (validPairs E) h` — the same
cardinality-ratio equality exists there, at the cost of losing the
`ProbComp`/game framing and the connection to the VCVio ecosystem. The
theorem *shapes* in §4 survive that swap nearly verbatim, which also
means committing to M1/M2 does not lock us in.

## 6. Open questions

1. Pinning: which VCVio commit? (Suggest: current `main` at
   implementation time; re-pin deliberately thereafter.)
2. Statement currency: exact `…/|validPairs|` vs closed-form
   `…/(n²−3n)` — propose stating both, mirroring how the repo already
   layers point-count vs field-size forms.
3. Should the probabilistic forms join the frozen `Challenge.lean`
   judge surface eventually, or remain a convenience layer? (Freezing
   them would make the judge depend on VCVio — recommend against, at
   least initially.)
4. Upstream appetite in VCVio for (a) statistical completeness on
   `ChallengeVerifyProtocol`, (b) a statement/commitment-aware
   `extract` — worth filing issues during M3.
