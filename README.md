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

The headline theorems live in `Divisor/ExtractorBridgeTheorems.lean` and
`Divisor/Soundness.lean`.

### Soundness

The soundness theorems analyze the MA protocol — and its interactive
variant IP — for the discrete-log relation. The shared objects:

- `DlogStatement E.q` — the public statement: an arity `k`, basis
  coordinate pairs `bases : Fin k → ZMod q × ZMod q`, a `target`
  coordinate pair, a degree bound `degBound`, and an admissible-set
  predicate `admSet`. On-curve-ness of the bases and target is not part
  of the structure — it is supplied separately as theorem hypotheses.
- `DlogWitness E.q` — the witness data: an arity `k`, integer scalars
  `n_i`, a witness degree bound, and proofs `|n_i| < degBound`. The
  separate proposition `relDlog E stmt wit` asserts the witness is
  valid: `target = Σ_i [n_i]·bases_i` in the group `E(F_q)`.
- `MAProverMsg E.q` — the prover's first-round message: a residue vector
  `m` and two polynomials `polyA`, `polyB` that form the divisor
  `msg.toD = polyA(x) − polyB(x)·y`.
- `maExtractor` — the extraction algorithm; on a message it either
  returns a candidate witness or fails.
- `maVerifierAccepts` — the verifier's accept predicate on a challenge.

The soundness theorems all share the same hypotheses; they are
enumerated in full for `ma_extractable` and referenced thereafter.

#### `Divisor.ma_extractable`

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
        21 * (msg.toD.degE + stmt.k + 2) + 72) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k
```

Hypotheses:

- `stmt : DlogStatement E.q` — the discrete-log statement under attack.
- `hd : stmt.degBound < E.q` — the degree bound is below the field size.
- `hd2 : 2 ≤ stmt.degBound` — the degree bound is at least 2.
- `msg : MAProverMsg E.q` — the (possibly cheating) prover's first-round
  message.
- `hkm : stmt.k = msg.k` — the message arity matches the statement
  arity.
- `hTargetOnE : stmt.target ∈ E.points` — the target is a curve point.
- `hBasesOnE : ∀ j, stmt.bases j ∈ E.points` — every basis is a curve
  point.
- `hLargeQ : ...` — a large-field condition: the affine point count
  `E.points.card` exceeds
  `2·(5·(degE+k+2)+3) + 21·(degE+k+2) + 72`, where `degE = msg.toD.degE`
  and `k = stmt.k`, so the counting argument has room. (The full point
  count including infinity is `E.numPoints = E.points.card + 1`.)

Conclusion: for *every* first-round message — honest or adversarial —
one of two things holds:

1. the extractor `maExtractor` run on `msg` returns `some wit`, and that
   `wit` is a genuine discrete-log witness for `stmt` (`relDlog`); or
2. the set of challenges the verifier accepts is small — bounded by
   `eventNotEqBound + eventDegBound`, the defined-zero discrepancy bound
   plus the undefined-denominator bound.

In words: a prover who cannot be extracted from is accepted only
negligibly often.

Human form: either `msg` yields an extracted witness $w$ with
$$
T = \sum_i [w_i] B_i,
$$
or its accepting challenges are bounded by
$$
\left|\operatorname{AcceptingChallenges}(\mathrm{msg})\right|
\le 18(d+k)q + (3d+9k+71)\left|E(\mathbb{F}_q)\right|.
$$

#### `Divisor.ma_extractable_clean`

Lean:
```lean
theorem ma_extractable_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg.toD.degE + stmt.k + 2) + 3) +
        21 * (msg.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    (∃ wit : DlogWitness E.q,
        maExtractor E stmt msg stmt.degBound hd hkm = some wit
        ∧ relDlog E stmt wit) ∨
    ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q
```

Hypotheses: identical to `ma_extractable`, plus

- `hQ : 5 ≤ E.q` — the field has at least 5 elements, needed to fold the
  two-term bound through the Hasse point count into a single `q`-term.

Conclusion: the same extractability disjunction, with the accept-set
bound consolidated to `36·(d+k+4)·q`.

Human form: either `msg` yields an extracted witness, or
$$
\left|\operatorname{AcceptingChallenges}(\mathrm{msg})\right|
\le 36(d+k+4)q.
$$

#### `Divisor.ip_knowledge_sound`

Lean:
```lean
theorem ip_knowledge_sound
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ eventNotEqBound E stmt.degBound stmt.k +
        eventDegBound E stmt.degBound stmt.k)
    ∧ ∀ (chal : MAChallenge E.q) (A₂ : ZMod E.q × ZMod E.q)
        (msg3 msg3' : IPProverMsg3 E.q),
        msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0 →
        msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0 →
        msg1.toD.eval A₂.1 A₂.2 ≠ 0 →
        (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
            stmt.target.1 (-stmt.target.2) ≠ 0 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3' →
        msg3 = msg3'
```

Hypotheses: identical to `ma_extractable` (with the first-round message
named `msg1`).

Conclusion: a conjunction of two parts.

1. The same witness-or-small-accept-set guarantee as `ma_extractable`.
2. *Uniqueness of the third-round response*: for any challenge `chal`,
   any point `A₂`, and any third-message pair `msg3`, `msg3'` that the
   IP verifier both accepts, `msg3 = msg3'` — provided the side
   conditions hold: `msg1.toD` is non-vanishing at `chal.A₀`,
   `chal.A₁`, and `A₂`, and the chord line through `A₀, A₁` does not
   pass through `−target`.

Human form:
$$
\text{IP soundness}
= \text{MA extractability}
\land \text{uniqueness of any accepted third-round response}.
$$

#### `Divisor.ip_knowledge_sound_clean`

Lean:
```lean
theorem ip_knowledge_sound_clean
    (stmt : DlogStatement E.q) (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg1 : MAProverMsg E.q)
    (hkm : stmt.k = msg1.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (msg1.toD.degE + stmt.k + 2) + 3) +
        21 * (msg1.toD.degE + stmt.k + 2) + 72)
    (hQ : 5 ≤ E.q) :
    ((∃ wit : DlogWitness E.q,
         maExtractor E stmt msg1 stmt.degBound hd hkm = some wit
         ∧ relDlog E stmt wit) ∨
     ((validPairs E).filter
        (fun p => maVerifierAccepts E stmt msg1 ⟨p.1, p.2⟩ hkm)).card
      ≤ 36 * (stmt.degBound + stmt.k + 4) * E.q)
    ∧ ∀ (chal : MAChallenge E.q) (A₂ : ZMod E.q × ZMod E.q)
        (msg3 msg3' : IPProverMsg3 E.q),
        msg1.toD.eval chal.A₀.1 chal.A₀.2 ≠ 0 →
        msg1.toD.eval chal.A₁.1 chal.A₁.2 ≠ 0 →
        msg1.toD.eval A₂.1 A₂.2 ≠ 0 →
        (lineThrough chal.A₀.1 chal.A₀.2 chal.A₁.1 chal.A₁.2).eval
            stmt.target.1 (-stmt.target.2) ≠ 0 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3 →
        ipVerifierAccepts E stmt msg1 chal A₂ msg3' →
        msg3 = msg3'
```

Hypotheses: identical to `ip_knowledge_sound`, plus `hQ : 5 ≤ E.q`.

Conclusion: the same conjunction, with the accept-set bound consolidated
to `36·(d+k+4)·q` (as in `ma_extractable_clean`).

Human form:
$$
\text{IP clean soundness}
= \text{MA clean extractability}
\land \text{uniqueness of any accepted third-round response}.
$$

### Completeness

The completeness theorems analyze the *honest* prover: given a real
witness, the verifier rejects only on a small set of challenges. The
extra object here is the honest-message predicate `isHonestFor`, which
pins the prover's polynomials to the witness.

#### `Divisor.ma_completeness`

Lean:
```lean
theorem ma_completeness
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine
```

Hypotheses:

- `stmt : DlogStatement E.q`, `wit : DlogWitness E.q` — a statement and a
  candidate witness.
- `hk : stmt.k = wit.k` — statement and witness arities match.
- `hValid : relDlog E stmt wit` — `wit` genuinely satisfies the
  discrete-log relation for `stmt`.
- `msg : MAProverMsg E.q`, `hkm : stmt.k = msg.k` — the prover's
  first-round message and its arity match.
- `hDeg : msg.toD.degE ≤ wit.degBound` — the message divisor's degree is
  within the witness degree bound.
- `hDegK : msg.toD.degE ≤ stmt.degBound` — and within the statement
  degree bound.
- `hAdm : stmt.admSet (msg.polyA, msg.polyB)` — the message polynomials
  lie in the admissible set; in particular `msg.toD` is nonzero.
- `hHonestDivisor : msg.isHonestFor E stmt wit hk hkm` — `msg` is the
  honest message for `(stmt, wit)`. This is the conjunction of: the
  residue vector `m` reduces to `wit.scalars` mod `q`; `splitsOnE E
  msg.toD` (the norm polynomial of `msg.toD` splits over `F_q` and every
  root has an `F_q`-rational fibre); the divisor of `msg.toD` matches
  the honest target divisor `(−P) + Σ_i n_i·(B_i) − degE·(∞)` at every
  point; `(−target)` is a curve point; and every basis `bases i` is a
  curve point.

Conclusion: the set of challenge pairs on which the verifier rejects is
bounded by `(3·numZeros(msg.toD) + 4)·|E_aff(F_q)|`, where
`numZeros(msg.toD)` is the number of affine zeros of the message
divisor.

Human form:
$$
\left|\operatorname{RejectingChallenges}(\mathrm{msg})\right|
\le \left(3\,\operatorname{numZeros}(D)+4\right)
   \left|E_{\mathrm{aff}}(\mathbb{F}_q)\right|.
$$

#### `Divisor.ma_completeness_clean`

Lean:
```lean
theorem ma_completeness_clean
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hValid : relDlog E stmt wit)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (hDeg : msg.toD.degE ≤ wit.degBound)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hHonestDivisor : msg.isHonestFor E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hQ : 5 ≤ E.q) :
    ((E.points ×ˢ E.points).filter
        (fun p => ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (6 * (stmt.degBound + 1) + 6) * E.q
```

Hypotheses: identical to `ma_completeness`, plus

- `hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)` — the message divisor is
  nonzero (stated directly, rather than via `admSet`).
- `hQ : 5 ≤ E.q` — the field has at least 5 elements.

Conclusion: the same reject-set bound, with the affine point count and
zero count folded — through the Hasse point count — into a single
expression in `q` and the statement degree bound.

Human form:
$$
\left|\operatorname{RejectingChallenges}(\mathrm{msg})\right|
\le (6(d+1)+6)q.
$$

## Axiom Surface

The headline theorems are *conditional*: their proofs are fully
machine-checked — there is no `sorry` anywhere in the closure — but they
rest on four named axioms, in addition to Lean/mathlib core
(`propext`, `Classical.choice`, `Quot.sound`). The exact closures are
pinned by `#print axioms` in `Tests/AxiomClosurePin.lean`.

`Divisor.ma_extractable` and `Divisor.ip_knowledge_sound` depend on:

```text
Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd
Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
Divisor.hasse_weil_textbook
Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero
```

`Divisor.ma_completeness` depends on:

```text
Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd
Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
```

`Divisor.ma_completeness_clean` additionally uses
`Divisor.hasse_weil_textbook`.

All four axioms are dependencies of the headline theorems. Each is a
piece of mathematical infrastructure — a point count, a resultant
identity, two divisor facts — and none of them mentions the protocol,
the extractor, or the verifier. The protocol-specific reasoning is
entirely in the machine-checked part; the axioms are upstream lemmas,
not the conclusion in disguise.

### Lean Axiom Inventory

Each axiom is documented below with its formal Lean statement, an
enumeration of its hypotheses, and an intuition.

#### `Divisor.hasse_weil_textbook`

Formal statement:
```lean
axiom hasse_weil_textbook (E : ECSetup) :
  |(((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)| ≤ 2 * Real.sqrt (E.q : ℝ)
```

Hypotheses:

- `E : ECSetup` — an elliptic curve over `F_q`. There are no proof-side
  hypotheses.

Intuition: the number of `F_q`-rational points on the curve cannot
stray far from `q + 1` — it lies within `2√q` of it. The project
consumes this through the derived theorem `Divisor.hasse_weil`, the
equivalent integer form `(#E − q − 1)² ≤ 4q`, which is what collapses a
point-count-dependent bound into a bound purely in `q` (the `_clean`
theorems).

Lean source: `Divisor/Axioms/AxiomHasseWeil.lean`.

#### `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero`

Formal statement:
```lean
axiom CoordRingElt.divisorClass_eq_zero_of_b_ne_zero
    (E : ECSetup) (D : CoordRingElt E.q)
    (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hSplit : splitsOnE E D) (_hbNZ : D.b ≠ 0) :
    divisorClass E (divisorOfD E D)
      (divisorOfD_finiteSupport E D) = 0
```

Hypotheses:

- `E : ECSetup`, `D : CoordRingElt E.q` — a curve, and a coordinate-ring
  element `D = a(x) − b(x)·y`, i.e. a rational function on the curve.
- `_hD : ¬ (D.a = 0 ∧ D.b = 0)` — `D` is not the zero function.
- `_hSplit : splitsOnE E D` — every zero of `D` is visible over `F_q`:
  the norm polynomial of `D` splits into linear factors over `F_q`, and
  each root has an `F_q`-rational fibre on the curve. Without this, `D`
  could have zeros only over an extension field, and the project's
  divisor would miss that mass.
- `_hbNZ : D.b ≠ 0` — `D` genuinely involves `y` (it is not a polynomial
  in `x` alone). The `D.b = 0` case is a separate, already-proved
  theorem.

Intuition: the divisor of a rational function — its formal sum of zeros
minus poles, counted with multiplicity — is principal, so its class in
the curve's divisor class group is zero. The hypotheses ensure the
project's combinatorial divisor `divisorOfD E D` (assembled from the
local orders `ordAt` at each affine point, together with the pole at
infinity) genuinely captures the full zero/pole data of `D`. The
soundness path uses this as a general divisor-class triviality fact for
any nonzero `D` meeting the hypotheses.

Lean source: `Divisor/OrdP/LocalRing.lean`.

#### `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`

Formal statement:
```lean
axiom chord_fiber_product_concrete_bar_zfiber_pow_dvd
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

- `E : ECSetup`, `D : CoordRingElt E.q` — a curve and a rational
  function on it.
- `lam : ZMod E.q` — the slope of the chord projection
  `π_λ : (x, y) ↦ y − λx`.
- `[DecidableEq (Fqbar E)]` — decidable equality on the algebraic
  closure; a technical instance with no mathematical content.
- `hD : ¬ (D.a = 0 ∧ D.b = 0)` — `D` is nonzero.
- `gd : GeometricDivisorData E D` — the geometric divisor of `D`: its
  zeros over the algebraic closure, with local multiplicities. This is
  *not* free data — the structure carries proof fields forcing
  `gd.mult` to equal the true local order of `D` at each point, and
  `gd.support` to be exactly the zero set.
- `z : Fqbar E` — a candidate chord-intercept value in the algebraic
  closure.

Intuition: `chord_fiber_product_concrete E lam D` is the norm of `D`
along the chord projection — a univariate polynomial whose roots are the
chord intercepts of `D`'s zeros. The axiom says each zero `Q` of `D`
contributes its full local multiplicity to that polynomial at the
intercept `π_λ(Q)`, and zeros sharing an intercept add their
multiplicities: `(X − z)` raised to the multiplicity summed over the
fibre of `z` divides the base-changed norm polynomial. This is the
lower-bound (`≥`) half of the norm-pushforward identity; the matching
upper bound (a degree inequality) is already a theorem in the project,
so together they pin the multiplicity exactly.

Lean source: `Divisor/Axioms/AxiomChordFiberDivisibility.lean`.

#### `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`

Formal statement:
```lean
axiom resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hf_two_le : 2 ≤ f.natDegree)
    (hg_pos : 0 < g.natDegree)
    (hF_ne : (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ ≠ 0)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
  resultantLogDerivConclusion f g t₀
```

Hypotheses:

- `K : Type*` `[Field K]`, `f g : K[X][X]` — two bivariate polynomials.
  The outer variable `X` is the resultant variable; the inner variable
  is the specialization parameter `T`.
- `t₀ : K` — the value at which the parameter `T` is specialized.
- `hMonic : f.Monic` — `f` is monic in the outer variable. Without it,
  the resultant carries a leading-coefficient factor and the formula
  acquires an extra term.
- `hf_two_le : 2 ≤ f.natDegree` — `f` has outer degree at least 2. The
  degree-0 and degree-1 cases are separate, already-proved theorems.
- `hg_pos : 0 < g.natDegree` — `g` has positive outer degree. The
  degree-0 case is a separate, already-proved theorem.
- `hF_ne : ...` — the resultant `F(T) := Res_X(f, g)` does not vanish at
  `t₀`, so its logarithmic derivative is defined there.
- `hSplit : ...` — the specialized polynomial `f(X, t₀)` splits into
  linear factors over `K`.
- `hg_def : ...` — `g` does not vanish at any root of `f(X, t₀)`; the
  root sets of `f` and `g` are disjoint at `t₀`.
- `hf_X_def : ...` — the outer derivative of `f(X, t₀)` is nonzero at
  each of its roots, i.e. those roots are simple (no double roots).

Intuition: write `F(T) = Res_X(f, g)`, a univariate polynomial in `T`.
The axiom computes its logarithmic derivative `F'(t₀)/F(t₀)` as a sum
over the roots `x` of `f(X, t₀)`:
$$
\frac{F'(t_0)}{F(t_0)}
= \sum_{x\,:\,f(x,t_0)=0}
  \frac{g_T f_X - g_X f_T}{f_X\, g}\Big|_{(x,t_0)}.
$$
Each summand is the implicit-function chain rule for
`d/dT [g(x(T), T)]`, where `x(T)` tracks a root of `f` as `T` varies.
The conclusion is packaged as the abbreviation
`resultantLogDerivConclusion f g t₀`, defined in the source file.

Lean source: `Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean`.

### Theorem-backed declarations near the axiom surface

- `Divisor.hasse_weil` — the integer-squared form `(#E − q − 1)² ≤ 4q`;
  a theorem derived from `Divisor.hasse_weil_textbook`, kept for
  downstream compatibility.
- `Divisor.chord_fiber_product_eq_normZ_under_split` — that the
  chord-fibre product is a nonzero scalar multiple of `normZ` under
  splitting; declared in
  `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean` and
  proved (no longer an axiom) via the bridge file
  `Divisor/Bridges/ChordFiberProductEqNormZUnderSplit.lean`.
- `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
  — the Galois trace-of-logarithmic-derivative identity; a theorem
  proved from mathlib.
- `CoordRingElt.exists_divisor_multiplicity` — a theorem proved from
  `ordAt` and `divisorClass_eq_zero_of_b_ne_zero`.
- `bivariate_poly_zeros_on_ExE_le` — a theorem whose project-axiom
  dependency is `Divisor.hasse_weil_textbook`.
