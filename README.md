# Formal Proofs for Eagen/Bassa/Parker Divisor Techniques

Lean 4 formalization of divisor-based techniques for elliptic-curve
inner-product and discrete-log protocols, including Eagen-style divisor
construction, Bassa-style norm/resultant arguments, Parker admissibility
variants, and the MA/IP soundness and completeness theorems.

## Build

```
lake build
```

Requires elan + Lean 4 toolchain (see `lean-toolchain`).

## Theorem Surface

Every axiom-free headline theorem lives in `Divisor/Headlines.lean`;
the Hasse–Weil-priced field-size forms live in `Divisor/Hasse.lean`.
The surface below is the axiom-free point-count surface: every bound
is stated in the currency
`n = |E(F_q)|` (`E.points.card`). Naming convention: a short name is
the point-count form (axiom-free); a `_q` suffix is the field-size form
obtained by the trivial fiber bound `n ≤ 2q` (still axiom-free;
completeness only); a `_hasse` suffix is the field-size form priced by
the Hasse–Weil axiom, and lives in the terminal module
`Divisor/Hasse.lean`.

### Soundness

The soundness theorems analyze the MA protocol and its interactive
variant IP for the discrete-log relation. The shared objects:

- `DlogStatement E.q`: the public statement: an arity `k`, basis
  coordinate pairs `bases : Fin k → ZMod q × ZMod q`, a `target`
  coordinate pair, a degree bound `degBound`, and an admissible-set
  predicate `admSet`. On-curve-ness of the bases and target is not part
  of the structure; it is supplied separately as theorem hypotheses.
- `DlogWitness E.q`: the witness data: an arity `k`, integer scalars
  `n_i`, a witness degree bound, and proofs `|n_i| < degBound`. The
  separate proposition `relDlog E stmt wit` asserts the witness is
  valid: `target = Σ_i [n_i]·bases_i` in the group `E(F_q)`.
- `MAProverMsg E.q`: the prover's first-round message: a residue vector
  `m` and two polynomials `polyA`, `polyB` that form the divisor
  `msg.toD = polyA(x) − polyB(x)·y`.
- `maExtractor`: the extraction algorithm; on a message it either
  returns a candidate witness or fails.
- `maVerifierAccepts`: the verifier's accept predicate on a challenge.
- `maAcceptSet E stmt msg hkm`: the challenge pairs in `validPairs E`
  on which the verifier accepts `msg` (the set the soundness theorems
  bound). Unfolding lemmas: `maAcceptSet_eq`, `mem_maAcceptSet`.
- `maRejectSet E stmt msg hkm`: the challenge pairs in
  `E.points ×ˢ E.points` on which the verifier rejects `msg` (the set
  the completeness theorems bound). Unfolding lemmas:
  `maRejectSet_eq`, `mem_maRejectSet`.
- `IPUniqueThirdRound E stmt msg1`: the third-round-uniqueness clause
  of the IP theorems (at most one accepted `msg3` per challenge, under
  the nonvanishing side conditions); holds unconditionally
  (`ipUniqueThirdRound_holds`).

The soundness theorems share the same first-round hypotheses; they are
enumerated in full for `ma_extractable` and referenced thereafter.

#### `Divisor.ma_extractable`

> **Theorem (MA knowledge soundness).** Let $`E`$ be an elliptic curve over
> $`\mathbb{F}_q`$, and let `stmt` be a discrete-log
> statement of arity $`k`$ and degree bound $`d`$ with $`2 \le d \le q - 1`$,
> whose target and $`k`$ basis points all lie on $`E`$. Fix a first-round
> prover message `msg` of matching arity, and assume the curve is large
> enough for the counting argument: $`|E(\mathbb{F}_q)|`$ exceeds
> $`2(5(d'+k+2)+3) + 21(d'+k+2) + 72`$ and the challenge space satisfies
> $`18(d'+k+1)q < |\mathrm{validPairs}|`$, where $`d'`$ is the degree of the
> message divisor. Then one of two things holds; either
> the extractor `maExtractor` returns a witness `wit` satisfying the
> relation `relDlog(stmt, wit)`, or `msg` is accepted on at most
> $`24(d+k+3)\,|E(\mathbb{F}_q)|`$ challenges. The content is the
> contrapositive: a `msg` accepted on more challenges is one from which
> `maExtractor` recovers a valid witness. The field-size form
> ($`\le 36(d+k+4)q`$, with both largeness hypotheses replaced by one
> threshold on $`q`$) is `ma_extractable_hasse` in `Divisor/Hasse.lean`.

Lean:
```lean
theorem ma_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    (maAcceptSet E stmt msg hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card
```

Hypotheses:

- `stmt : DlogStatement E.q`: the discrete-log relation to extract a
  witness for.
- `hd : stmt.degBound < E.q`: the degree bound is below the field size.
- `hd2 : 2 ≤ stmt.degBound`: the degree bound is at least 2.
- `msg : MAProverMsg E.q`: the prover's first-round message.
- `hkm : stmt.k = msg.k`: the message arity matches the statement arity.
- `hTargetOnE : stmt.target ∈ E.points`: the target is a curve point.
- `hBasesOnE : ∀ j, stmt.bases j ∈ E.points`: every basis point is on the curve.
- `hLargeQ : ...`: the large-curve condition needed by the counting
  argument (a lower bound on the point count).
- `hSample : ...`: the challenge sample space is large enough for the
  Frobenius slope-sampling pigeonhole. Both largeness hypotheses follow
  from the single field-size threshold `72·(d'+k+4) ≤ q` under the
  Hasse–Weil axiom (`Divisor/Hasse.lean`).

Conclusion: for every first-round message, either the extractor returns
`some wit` and `wit` is a valid discrete-log witness for `stmt`, or the
accepting challenge set has cardinality at most
`24·(d+k+3)·|E(F_q)|`.

#### `Divisor.ip_extractable`

> **Theorem (IP knowledge soundness; uniqueness of the third response).**
> Assume the hypotheses of `ma_extractable`: an elliptic curve $`E`$ over
> $`\mathbb{F}_q`$, a statement `stmt` of arity $`k`$ and
> degree bound $`d`$ with $`2 \le d \le q - 1`$, target and bases on $`E`$,
> and the same largeness bounds; write the first message as `msg1`. Then
> two statements hold at once. The first is the extraction dichotomy of
> `ma_extractable`: either `maExtractor` recovers a witness, or `msg1` is
> accepted on at most $`24(d+k+3)\,|E(\mathbb{F}_q)|`$ challenges. The
> second is uniqueness of
> the third-round response: fix a challenge with points $`A_0, A_1`$, a
> second-round point $`A_2`$, and two third responses `msg3`, `msg3'`. If
> `msg1.toD` is nonzero at $`A_0`$, $`A_1`$ and $`A_2`$, the line through
> $`A_0, A_1`$ does not vanish at the negated target, and the IP verifier
> accepts both `msg3` and `msg3'`, then `msg3 = msg3'`.

Lean:
```lean
theorem ip_extractable
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hSample : 18 * (msg1.toD.degE + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     (maAcceptSet E stmt msg1 hkm).card
      ≤ 24 * (stmt.degBound + stmt.k + 3) * E.points.card)
    ∧ IPUniqueThirdRound E stmt msg1
```

Hypotheses: identical to `ma_extractable`, with the first-round message
named `msg1`.

Conclusion: a conjunction of two parts.

1. The same witness-or-small-accept-set guarantee as `ma_extractable`.
2. Uniqueness of the third-round response: for any accepted third-message
   pair `msg3`, `msg3'`, the two messages are equal when the non-vanishing
   side conditions hold.

### Completeness

The completeness theorems analyze the *honest* prover: given a real
witness, the verifier rejects only on a small set of challenges. The
extra object here is the honest-message predicate `isHonestFor`, which
pins the prover's polynomials to the witness.

#### `Divisor.ma_completeness`

> **Theorem (MA completeness).** Let $`E`$ be an elliptic curve over
> $`\mathbb{F}_q`$, let `wit` be a witness satisfying the
> discrete-log relation for a statement `stmt` of matching arity, and let
> `msg` be the *honest* first-round message for `(stmt, wit)`, i.e.
> `msg.isHonestFor E stmt wit`. Assume the message divisor `msg.toD` is
> nonzero, its degree is within both the witness and statement bounds $`d`$,
> and its polynomials `(msg.polyA, msg.polyB)` lie in the admissible set.
> Then the honest prover is rejected on few challenges: the number of pairs
> $`(P_1, P_2) \in E \times E`$ on which the verifier does not accept is at
> most $`(3d+4)\,|E(\mathbb{F}_q)|`$. The field-size form
> ($`\le (6(d+1)+6)q`$, via the trivial fiber bound — no axiom) is
> `ma_completeness_q`.

Lean:
```lean
theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    (maRejectSet E stmt msg hkm).card
      ≤ (3 * stmt.degBound + 4) * E.points.card
```

Hypotheses:

- `stmt : DlogStatement E.q`, `wit : DlogWitness E.q`: a statement and a
  candidate witness.
- `hk : stmt.k = wit.k`: statement and witness arities match.
- `hValid : relDlog E stmt wit`: `wit` genuinely satisfies the
  discrete-log relation for `stmt`.
- `msg : MAProverMsg E.q`, `hkm : stmt.k = msg.k`: the prover's
  first-round message and its arity match.
- `hDeg : msg.toD.degE ≤ wit.degBound`: the message divisor's degree is
  within the witness degree bound.
- `hDegK : msg.toD.degE ≤ stmt.degBound`: the message divisor degree is
  also within the statement degree bound.
- `hAdm : stmt.admSet (msg.polyA, msg.polyB)`: the message polynomials
  lie in the admissible set.
- `hHonestDivisor : msg.isHonestFor E stmt wit hk hkm`: `msg` is the
  honest message for `(stmt, wit)`.
- `hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)`: the message divisor is
  nonzero (stated directly, rather than via `admSet`).

Conclusion: the verifier rejects the honest prover on at most
`(3d+4)·|E(F_q)|` challenge pairs (equivalently at most `(6(d+1)+6)·q`
via `ma_completeness_q`, still axiom-free).

#### `Divisor.ip_completeness`

> **Theorem (IP completeness).** Let `msg` be a first-round message
> with nonzero divisor whose degree $`d'`$ is within the statement
> bound. Then an accepted third-round response exists for every
> challenge pair outside a set of at most
> $`(3d' + 9k + 71)\,|E(\mathbb{F}_q)|`$ pairs. The field-size form
> ($`\le 18(d+k+12)q`$, via the trivial fiber bound — no axiom) is
> `ip_completeness_q`.

Lean:
```lean
theorem ip_completeness
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ ∃ msg3 : IPProverMsg3 E.q,
                  ipVerifierAccepts E stmt msg ⟨p.1, p.2⟩
                       (computeA₂ ⟨p.1, p.2⟩) msg3)).card
      ≤ (3 * msg.toD.degE + 9 * stmt.k + 71) * E.points.card
```

Unlike the MA side, no honesty predicate is needed: for *any*
first-round message meeting the degree and nonzero-divisor
hypotheses, the honest third-round response (the log-derivative
values and the line coefficient) exists and is accepted off the bad
set; `IPUniqueThirdRound` makes it the only accepted response
wherever its nonvanishing side conditions hold.

#### Any-length constructive completeness

`ma_completeness` is conditional on the honesty predicate
`isHonestFor`; the constructive supply (an explicit honest message,
built by the Eagen chord accumulation `eagenBuild_singletons`) is the
`ma_completeness_binary*` family. Its chain certificate — every
chord-combine in the accumulation is non-degenerate — comes two ways:
once-and-for-all for the structured support shapes (lengths 2 and 4,
and the chord families at 4/6/8), and at **any support length**
through the `SafePairs` machinery of `Divisor/SafeSupport.lean`:
`Divisor.ma_completeness_binary_any_length` derives the full chain
certificate from a single semantic general-position hypothesis,
`SafePairs` — for every nonempty split `xs ++ ys` of every sublist of
the support, the pair of elliptic-curve subset sums `(Σ xs, Σ ys)` is
chord-safe. Degenerate supports genuinely exist (2-torsion points in
the support; block sums related by `B = −2A`), so some such exclusion
is necessary; `SafePairs` is decidable per instance
(`SafePairsCert`, `decide`/`native_decide`-friendly via the
computable point skeleton). The enabling bridge is
`Landmark.pointCombine_eq_add`: the computable point-skeleton combine
agrees with mathlib's elliptic-curve group law on every pair of
points, so skeleton blocks are genuine subset sums. Axiom-free, like
the whole completeness side.

## Axiom Surface

The project has exactly **one** named axiom: the Hasse–Weil point-count
bound. Everything else in every headline theorem's closure is fully
machine-checked down to Lean/mathlib core (`propext`,
`Classical.choice`, `Quot.sound`); there is no `sorry` anywhere in the
closure. The exact closures are pinned by `#guard_msgs`-wrapped
`#print axioms` commands in `Tests/AxiomClosurePin.lean` (and
`Tests/F5RegressionAxiomClosure.lean`), so any closure drift fails the
build.

Beyond the pins, CI independently verifies the headline theorems with
[`leanprover/comparator`](https://github.com/leanprover/comparator)
against the frozen statements in `Challenge.lean` — statement identity
(so a proof cannot drift from the stated theorem or smuggle the
conclusion in as a hypothesis), an axiom allowlist, and a kernel replay
of the full export — and replays every module of this library through
the toolchain's built-in `leanchecker` to rule out environment hacking
(dependency oleans come from the mathlib cache, which mathlib's own CI
leanchecks). See `Judge/README.md`.

**Every primary headline theorem is axiom-free** — the closure of
every theorem in `Divisor/Headlines.lean` (`ma_extractable`,
`ip_extractable`, the four completeness bounds, the binary
completeness chain `ma_completeness_binary*`, and the
probability/contrapositive forms) is the Lean core three only. This is enforced *by import structure*: the axiom
file `Divisor/Axioms/AxiomHasseWeil.lean` is imported by exactly one
module, the terminal leaf `Divisor/Hasse.lean`, which sits above the
whole library and below nothing. All internal bounds are carried in the
point-count currency `n = |E(F_q)|`; `n` is bounded as a function of
`q` exactly once, in the leaf. The Hasse bound enters the development
in exactly one of two ways:

* On the completeness side it is not needed at all: the field-size
  forms (`ma_completeness_q`, `ip_completeness_q`) use the trivial
  `|E| ≤ 2q` fiber count (`points_card_le_two_q`), an axiom-free
  upper bound.
* On the extractability side the conversion needs the Hasse *lower*
  bound `q ≤ 2·|E| + 3` — the direction no fiber count can give — to
  discharge the two point-count largeness hypotheses (`hLargeQ`,
  `hSample`) from a single field-size threshold `72·(d'+k+4) ≤ q` and
  to recover the paper constant. The `_hasse` variants in
  `Divisor/Hasse.lean` (`ma_extractable_hasse`, `ip_extractable_hasse`,
  `ma_extractable_base_hasse`, `ip_extractable_base_hasse`,
  `ma_soundness_probability_hasse`, the witness-of-excess
  contrapositives, and the point-count conversion lemmas
  `hasse_points_bound` / `hasse_points_bound_lb`) are the **only**
  theorems whose closure contains

  ```text
  Divisor.hasse_weil_textbook
  ```

  Each field-size final also has an axiom-free `_of_count` flavor
  (e.g. `ma_extractable_of_count`) taking the two linear count bounds
  `2n ≤ 3q + 3` and `q ≤ 2n + 3` as explicit hypotheses — checkable
  arithmetic for any concrete curve, so fully machine-checked
  field-size instances need no axiom at all.

The one axiom is a piece of mathematical infrastructure — a point
count. It does not mention the protocol, the extractor, or the
verifier. The protocol-specific reasoning is entirely in the
machine-checked part; the axiom is an upstream fact, not the conclusion
in disguise.

### Lean Axiom Inventory

The axiom is documented below with its formal Lean statement, an
enumeration of its hypotheses, and an intuition; the two
divisor-theoretic theorems that carry the reduction to the coordinate
ring's Dedekind-domain structure are documented under "Bridge
theorems".

#### `Divisor.hasse_weil_textbook`

> **Axiom (Hasse-Weil bound).** Let $`E`$ be an elliptic curve over
> $`\mathbb{F}_q`$, and write $`N = |E(\mathbb{F}_q)|`$ for its number of
> rational points. Then $`N`$ stays within $`2\sqrt{q}`$ of $`q + 1`$:
> $`-2\sqrt{q} \le N - q - 1 \le 2\sqrt{q}`$. This is the classical Hasse
> bound (Hasse, 1936); there are no proof-side hypotheses, it is taken as
> given. The project consumes it through the equivalent integer form
> $`(N - q - 1)^2 \le 4q`$, which collapses a point-count-dependent bound
> into a bound purely in $`q`$.

Formal statement:
```lean
axiom hasse_weil_textbook (E : ECSetup) :
  |(((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)| ≤ 2 * Real.sqrt (E.q : ℝ)
```

Hypotheses:

- `E : ECSetup`: an elliptic curve over `F_q`. There are no proof-side
  hypotheses.

Intuition: the number of `F_q`-rational points on the curve cannot
stray far from `q + 1`: it lies within `2√q` of it. The project
consumes this through the derived theorem `Divisor.hasse_weil`, the
equivalent integer form `(#E − q − 1)² ≤ 4q`, which is what collapses a
point-count-dependent bound into a bound purely in `q`.

Lean source: `Divisor/Axioms/AxiomHasseWeil.lean`.

### Bridge theorems

Two divisor-theoretic theorems carry the reduction from the protocol
statements to the Dedekind-domain structure of the curve's coordinate
ring (see "Vendored code" below); both are machine-checked in the
build, in the bridge layer `Divisor/Bridges/` and `Divisor/OrdP/`.

#### `Divisor.CoordRingElt.divisorClass_eq_zero_of_splitsOnE`

> **Theorem (principal-divisor triviality).** Let $`E`$ be an elliptic curve
> over $`\mathbb{F}_q`$, and let $`D = a(x) - b(x) y`$ be a nonzero
> coordinate-ring element.
> Assume `splitsOnE E D`: every zero of $`D`$ is visible over
> $`\mathbb{F}_q`$, meaning the norm polynomial of $`D`$ splits into linear
> factors over $`\mathbb{F}_q`$ and each root has an $`\mathbb{F}_q`$-rational
> fibre on the curve. Then the divisor of $`D`$, assembled from the local
> orders `ordAt` at the affine points together with the pole at infinity,
> is principal; hence its class in the coordinate-ring class group vanishes,
> $`[\mathrm{div}(D)] = 0`$.

Formal statement:
```lean
theorem CoordRingElt.divisorClass_eq_zero_of_splitsOnE
    (E : ECSetup) (D : CoordRingElt E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D) :
    divisorClass E (divisorOfD E D)
      (divisorOfD_finiteSupport E D) = 0
```

Hypotheses:

- `E : ECSetup`, `D : CoordRingElt E.q`: a curve, and a coordinate-ring
  element `D = a(x) − b(x)·y`, i.e. a rational function on the curve.
- `hD : ¬ (D.a = 0 ∧ D.b = 0)`: `D` is not the zero function.
- `hSplit : splitsOnE E D`: every zero of `D` is visible over `F_q`:
  the norm polynomial of `D` splits into linear factors over `F_q`, and
  each root has an `F_q`-rational fibre on the curve. Without this, `D`
  could have zeros only over an extension field, and the project's
  divisor would miss that mass.

Intuition: the divisor of a rational function (its formal sum of zeros
minus poles, counted with multiplicity) is principal, so its class in
the curve's divisor class group is zero. The hypotheses ensure the
project's combinatorial divisor `divisorOfD E D` (assembled from the
local orders `ordAt` at each affine point, together with the pole at
infinity) genuinely captures the full zero/pole data of `D`. The
soundness path uses this as a general divisor-class triviality fact for
any nonzero `D` meeting the hypotheses.

How it is proved: the valuation bridge `Divisor/OrdP/ValuationBridge*`
identifies the project's combinatorial local order `ordAt` with the
`HeightOneSpectrum` valuation at the point's maximal ideal
(`v_P(D) = exp(−ordAt E D P)`); `Divisor/OrdP/SupportClassification.lean`
classifies the primes containing `D` and factors
`span {D} = ∏_P XYIdeal(P)^(ordAt P)`; the class-group computation in
`Divisor/OrdP/LocalRing.lean` then collapses the divisor class to the
class of a principal fractional ideal.

Lean source: `Divisor/OrdP/LocalRing.lean`.

#### `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`

> **Theorem (divisor-of-norm, lower bound).** Let $`E`$ be an elliptic curve
> over $`\mathbb{F}_q`$, let $`D`$ be a nonzero coordinate-ring element, and
> let $`\lambda \in \mathbb{F}_q`$ fix the chord projection
> $`\pi_\lambda(x, y) = y - \lambda x`$. Let `gd` be the geometric divisor
> data of $`D`$ over the algebraic closure $`\overline{\mathbb{F}_q}`$: its
> zero set, each zero $`Q`$ carrying its certified local multiplicity
> $`\mathrm{mult}_Q(D)`$. The chord-fibre product is the resultant, in the
> chord variable, of the chord cubic with the polynomial cutting out $`D`$
> on the line $`y = \lambda x + z`$; its roots are the chord intercepts of
> the zeros of $`D`$. Recall that the order of vanishing in the fibre over
> an intercept $`z`$ should be the summed multiplicity
> $`m = \sum_{Q} \mathrm{mult}_Q(D)`$ over the zeros $`Q`$ with
> $`\pi_\lambda(Q) = z`$. The theorem asserts the lower-bound half: for every
> $`z \in \overline{\mathbb{F}_q}`$, the base-changed resultant is divisible
> by $`(X - z)^m`$, that is
> $`(X - z)^m \mid \overline{\mathrm{Res}_X(\mathrm{chord}_\lambda, D_\lambda)}`$.
> The matching upper bound is a degree inequality, already a theorem; hence
> together they pin the multiplicity exactly.

Formal statement:
```lean
theorem chord_fiber_product_concrete_bar_zfiber_pow_dvd
    (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
    [DecidableEq (Fqbar E)]
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (gd : GeometricDivisorData E D) (z : Fqbar E) :
    (Polynomial.X - Polynomial.C z) ^
      (∑ Q ∈ gd.support.filter
         (fun Q => zLambdaBar E lam Q = z), gd.mult Q)
      ∣ (chord_fiber_product_concrete E lam D).map
          (algebraMap (ZMod E.q) (Fqbar E))
```

Hypotheses:

- `E : ECSetup`, `D : CoordRingElt E.q`: a curve and a rational
  function on it.
- `lam : ZMod E.q`: the slope of the chord projection
  `π_λ : (x, y) ↦ y − λx`.
- `[DecidableEq (Fqbar E)]`: decidable equality on the algebraic
  closure; a technical instance with no mathematical content.
- `hD : ¬ (D.a = 0 ∧ D.b = 0)`: `D` is nonzero.
- `gd : GeometricDivisorData E D`: the geometric divisor of `D`: its
  zeros over the algebraic closure, with local multiplicities. This is
  *not* free data: the structure carries proof fields forcing
  `gd.mult` to equal the true local order of `D` at each point, and
  `gd.support` to be exactly the zero set.
- `z : Fqbar E`: a candidate chord-intercept value in the algebraic
  closure.

Intuition: `chord_fiber_product_concrete E lam D` is the norm of `D`
along the chord projection: a univariate polynomial whose roots are the
chord intercepts of `D`'s zeros. The theorem says each zero `Q` of `D`
contributes its full local multiplicity to that polynomial at the
intercept `π_λ(Q)`, and zeros sharing an intercept add their
multiplicities: `(X − z)` raised to the multiplicity summed over the
fibre of `z` divides the base-changed norm polynomial. This is the
lower-bound (`≥`) half of the norm-pushforward identity; the matching
upper bound (a degree inequality) is already a theorem in the project,
so together they pin the multiplicity exactly.

How it is proved: the chord algebra `F̄[Z] → R̄` (adjoining the curve
along `Z = y − λx`) is realised in `Divisor/OrdP/ChordAlgebra.lean` as
`AdjoinRoot` of the chord cubic, a rank-3 free extension.
`Divisor/OrdP/ChordNorm.lean` shows `D̄` lies in the `mult Q`-th power
of the maximal ideal at each geometric zero `Q` (via the geometric
valuation bridge `Divisor/OrdP/GeomValuationBridge.lean`), and pushes
that through `Ideal.relNorm` to get
`(Z − z)^m ∣ intNorm F̄[Z] R̄ D̄`. Finally
`Divisor/OrdP/ChordFraction.lean` + `Divisor/OrdP/ChordResultant.lean`
identify that integral norm with the base-changed chord-fibre
resultant, by comparing the product over field embeddings (the norm)
with the product over the roots of the chord cubic (the resultant).

Lean source: `Divisor/Bridges/ChordFiberDivisibility.lean` (the
statement, with the two-line assembly), proved on
`Divisor/OrdP/ChordAlgebra.lean`, `Divisor/OrdP/ChordNorm.lean`,
`Divisor/OrdP/ChordFraction.lean`, `Divisor/OrdP/ChordResultant.lean`.

## Vendored code

`Divisor/Vendor/TauCeti/` contains seven files (~1,300 lines) vendored
from the [Tau Ceti library](https://github.com/TauCetiProject/TauCeti)
(commit `076ae234`, 2026-08-21, Apache-2.0; original copyright headers
retained). They provide the Dedekind-domain structure of an elliptic
curve's affine coordinate ring (`isDedekindDomain_coordinateRing`,
`XYIdeal` maximality and the `XYIdeal_eq_iff` point/ideal dictionary),
which underpins the proofs of both bridge theorems above.
They are vendored rather than taken as a lake dependency because
upstream has no release tags and tracks a pre-release toolchain with a
mathlib master pin. See `Divisor/Vendor/TauCeti/README.md` for
provenance, the file-by-file inventory, and the (mechanical, marked)
local adaptations.
