# Formalization of Eagen's ECIP Proof

This repository formalizes the divisor techniques behind the
Eagen/Bassa/Parker protocols in Lean 4. The primary references are Liam
Eagen's [*Zero Knowledge Proofs of Elliptic Curve Inner Products from
Principal Divisors and Weil Reciprocity*](https://eprint.iacr.org/2022/596),
IACR ePrint 2022/596, and Mathias Hall-Andersen and Diego F. Aranha's
[*Notes and Proofs for Divisor
Techniques*](https://blog.zksecurity.xyz/posts/divisor-notes/divisor-techniques.pdf).
The Lean proof differs slightly from the notes; in particular, `ma_soundness`
uses explicit point-count hypotheses and does not rely on Hasse's theorem.

> `ma_soundness` is kernel-checked in Lean 4 using only Lean's standard
> classical foundation: `propext`, `Classical.choice`, and `Quot.sound`.

The headline result is a soundness theorem for the Merlin-Arthur discrete-log
protocol:

> Fix an elliptic curve `E`, a public statement `stmt`, and *any* Merlin
> message `msg` of matching arity. If the statement is well formed, the
> explicit counting hypotheses hold, and Arthur accepts `msg` with
> probability greater than the knowledge error, then `maExtractor E stmt msg`
> returns a witness which is valid for `stmt`.

The word *any* matters. `msg` does not have to come from the honest prover; it
does not have to come from a witness at all. Soundness is precisely the claim
that a malicious message cannot be accepted too often unless the fixed
recovery function turns it into a valid witness.

## The Statement, Message, and Relation

`DlogStatement E.q` contains the public data:

- `k`: the number of bases;
- `degBound`: the public witness and message degree bound;
- `bases : Fin k → ZMod q × ZMod q`;
- `target : ZMod q × ZMod q`;
- `admSet`: the admissible set used by the verifier;
- `admSet_excludes_zero`: the zero divisor is not admissible.

Write `P = stmt.target` and `B_i = stmt.bases i`. The theorem also takes
proofs about this data. `hd` and `hd2` say
`2 ≤ stmt.degBound < E.q`; `hkm` says that the independently supplied message
has the same arity. The point hypotheses `hTargetOnE` and `hBasesOnE` say, for
every index `i`:

$$
P, B_i \in \mathbb{E}(\mathbb{F}_q)
$$

Thus `d` is not another input hidden beside `stmt`: it is shorthand for
`stmt.degBound`. These proof arguments certify the public instance; none says
that the prover is honest.

The structure does not define a language by itself. A `DlogWitness` separately
bundles its scalars with their range proof. The relation `relDlog E stmt wit`
then says that `(stmt, wit)` has matching arity and satisfies the following
group equation:

$$
P = \sum_{i=0}^{k-1} [n_i] \cdot B_i
$$

Here the `n_i` are signed integers. This is deliberate: the extractor's
special case uses the scalar `-1`.

`MAProverMsg E.q` is just prover-controlled data:

- an arity `k`;
- residues `m : Fin k → ZMod q`;
- polynomials `polyA` and `polyB`, representing the coordinate-ring element
  `msg.toD`.

There is no honesty field in this structure. The soundness theorem quantifies
over all of it.

## The Recovery Function

The public recovery interface is:

```lean
def maExtractor (E : ECSetup)
    (stmt : DlogStatement E.q)
    (msg : MAProverMsg E.q) : Option (DlogWitness E.q)
```

It is a total, executable function. It first checks `stmt.k = msg.k`; this is
only the dependent-type plumbing needed to compare the two inputs. The
mismatch branch returns `none`. Soundness does not assume that this branch, or
any other branch of the extractor, is reasonable. It proves that the exact
function above works whenever the theorem's acceptance hypothesis holds.

For matching arities, the extractor groups equal bases. On the general branch
it sums the residues `msg.m` in each group, stores the canonical integer lift
at the least index, and sets the remaining indices to zero. There is one
necessary special case: if some base is `-target`, the extractor returns `-1`
at the least such index and zero elsewhere. This already gives:

$$
[-1] \cdot (-P) = P
$$

The final finite check verifies `|n_i| < stmt.degBound` for every extracted
scalar. The current direct implementation takes quadratic time in `msg.k`;
the message polynomials are not inspected. `Tests/MAExtractorExec.lean`
compiles the function to native code and evaluates the special branch to
`some (1, -1)`.

## Arthur's Experiment

Arthur samples uniformly from `validPairs E`: pairs of affine curve points
which are distinct and do not form a vertical chord. Write `V = validPairs E`,
`s = stmt`, `m = msg`, and let `A(E,s,m,A₀,A₁)` mean that the MA verifier
accepts. For fixed `stmt` and `msg`, VCVio defines the acceptance probability
`p_A` as:

$$
p_A = \Pr_{(A_0,A_1)\leftarrow V}[A(E,s,m,A_0,A_1)]
$$

The formal bridge `maAcceptanceProbability_eq_card_div` proves that this is
exactly the finite ratio below, where `S_A = maAcceptSet E stmt msg hkm`:

$$
p_A = \frac{|S_A|}{|V|}
$$

Write `d = stmt.degBound`, `k = stmt.k`, and
`n = E.points.card`. The advertised knowledge error is:

$$
\varepsilon(E,s) = \frac{24 \cdot (d + k + 3) \cdot n}{|V|}
$$

Observe that the error depends on the public statement and the curve, not on
the prover's claimed message degree.

## The Headline Theorem

The named predicate is intentionally boring: it says that the *exact* output
of `maExtractor`, rather than some unrelated existential witness, is valid.

```lean
def maExtractorValid (E : ECSetup)
    (stmt : DlogStatement E.q) (msg : MAProverMsg E.q) : Prop :=
  match maExtractor E stmt msg with
  | some wit => relDlog E stmt wit
  | none => False

theorem ma_soundness
    (E : ECSetup)
    (stmt : DlogStatement E.q)
    (hd : stmt.degBound < E.q)
    (hd2 : 2 ≤ stmt.degBound)
    (msg : MAProverMsg E.q)
    (hkm : stmt.k = msg.k)
    (hTargetOnE : stmt.target ∈ E.points)
    (hBasesOnE : ∀ j, stmt.bases j ∈ E.points)
    (hLargeQ : E.points.card >
        2 * (5 * (stmt.degBound + stmt.k + 2) + 3) +
        21 * (stmt.degBound + stmt.k + 2) + 72)
    (hSample : 18 * (stmt.degBound + stmt.k + 1) * E.q + 1 ≤
        (validPairs E).card)
    (hAccept : maSoundnessError E stmt <
        maAcceptanceProbability E stmt msg hkm) :
    maExtractorValid E stmt msg
```

In words: for a curve `E`, a statement `stmt`, and an arbitrary matching-arity
message `msg`, if:

1. `2 ≤ stmt.degBound < E.q`;
2. $P, B_i \in \mathbb{E}(\mathbb{F}_q)$ for every index `i`;
3. the curve has enough affine points for the polynomial-identity argument;
4. `validPairs E` is large enough for the Frobenius sampling argument; and
5. Arthur accepts `msg` with probability strictly greater than the explicit
   error `ε(E, stmt)`;

then `maExtractor E stmt msg = some wit` for a witness satisfying
`relDlog E stmt wit`.

The first four items are statement and curve conditions. The fifth is the
only condition involving the behaviour of the prover's message. There is no
premise saying that `msg` is honest, admissible, nonzero, split over the base
field, or within the degree bound. Those checks are internal to the verifier
or are derived from acceptance:

- If `msg.toD.degE > stmt.degBound`, the verifier rejects at every point.
- If `(msg.polyA, msg.polyB)` is outside `stmt.admSet`, the verifier rejects at
  every point.
- If the verifier accepts, admissibility and the statement's
  `admSet_excludes_zero` field imply that `msg.toD` is nonzero.
- Rational splitting is not assumed. The proof handles zeros geometrically
  and descends the resulting identity back to the base field.

Hence a malicious message cannot manufacture the theorem's antecedent by
failing a side condition; failure gives acceptance probability zero.

## What the Proof Does

The proof is a short probabilistic wrapper around a long counting argument:

1. `ma_soundness_count_bound` proves a dichotomy for every message. Either the
   extractor returns a valid witness, or the message accepts on at most
   $24 \cdot (d + k + 3) \cdot n$ valid challenge pairs.
2. `maAcceptanceProbability_eq_card_div` turns the VCVio experiment into the
   corresponding cardinality ratio.
3. If `p_acc > ε`, the small-accept-set branch is impossible. Hence the exact
   extractor output is a valid witness.

The internal proof separates two cases. If the log-derivative discrepancy is
nonzero, a Schwartz-Zippel style count bounds the accepting pairs. If it
vanishes on enough defined pairs, the divisor argument recovers the group
equation and proves the extracted scalars valid. A message whose degree check
fails is handled before either case: its accept set is empty.

## MA Completeness

Soundness quantifies over malicious messages. Completeness is the opposite
direction and therefore has an honesty premise. `ma_completeness` starts from
a valid witness and a message satisfying `MAProverMsg.isHonestFor`; it bounds
the number of rejected challenge pairs by:

$$
(3 \cdot d + 4) \cdot n
$$

The constructive `ma_completeness_binary_any_length` family verifies messages
built with `LineAccum.lineBuild_singletons` for binary witnesses under the
decidable `SafePairs` general-position condition. These results are separate
from soundness; no honesty predicate is used by `ma_soundness` or its proof
chain.

## Build

The repository pins Lean and all dependencies. Fetch the matching Mathlib
cache, then build:

```bash
lake exe cache get
lake build
```

The executable extractor smoke test can be run directly:

```bash
lake build Tests.MAExtractorExec
```
