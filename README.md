# MA soundness for divisor protocols

This repository formalizes the divisor techniques behind the
Eagen/Bassa/Parker protocols in Lean 4. The headline result is a soundness
theorem for the Merlin-Arthur discrete-log protocol:

> Fix an elliptic curve `E`, a public statement `stmt`, and *any* Merlin
> message `msg` of matching arity. If the statement is well formed, the
> explicit counting hypotheses hold, and Arthur accepts `msg` with
> probability greater than the knowledge error, then `maExtractor E stmt msg`
> returns a witness which is valid for `stmt`.

The word *any* matters. `msg` does not have to come from the honest prover; it
does not have to come from a witness at all. Soundness is precisely the claim
that a malicious message cannot be accepted too often unless the fixed
recovery function turns it into a valid witness.

## The statement, message, and relation

`DlogStatement E.q` contains the public data:

- `k`: the number of bases;
- `degBound`: the public witness and message degree bound;
- `bases : Fin k → ZMod q × ZMod q`;
- `target : ZMod q × ZMod q`;
- `admSet`: the admissible set used by the verifier;
- `admSet_excludes_zero`: the zero divisor is not admissible.

The theorem also takes proofs about this data. `hd` and `hd2` say
`2 ≤ stmt.degBound < E.q`; `hkm` says that the independently supplied message
has the same arity; `hTargetOnE` and `hBasesOnE` say that the coordinate pairs
really are points of `E`. Thus `d` is not another input hidden beside `stmt`:
it is shorthand for `stmt.degBound`. These proof arguments certify the public
instance; none says that the prover is honest.

The structure does not define a language by itself. A `DlogWitness` separately
bundles its scalars with their range proof. The relation `relDlog E stmt wit`
then says that `(stmt, wit)` has matching arity and satisfies the following
group equation:

$$
\operatorname{target} = \sum_{i=0}^{k-1} [n_i]\operatorname{bases}_i
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

## The recovery function

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
[-1](-\operatorname{target}) = \operatorname{target}
$$

The final finite check verifies `|n_i| < stmt.degBound` for every extracted
scalar. The current direct implementation takes quadratic time in `msg.k`;
the message polynomials are not inspected. `Tests/MAExtractorExec.lean`
compiles the function to native code and evaluates the special branch to
`some (1, -1)`.

## Arthur's experiment

Arthur samples uniformly from `validPairs E`: pairs of affine curve points
which are distinct and do not form a vertical chord. For fixed `stmt` and
`msg`, VCVio defines the acceptance probability as:

$$
p_{\mathrm{acc}} =
\Pr_{(A_0,A_1)\leftarrow\operatorname{validPairs}(E)}
[\operatorname{maVerifierAccepts}(E,\operatorname{stmt},\operatorname{msg},A_0,A_1)]
$$

The formal bridge `maAcceptanceProbability_eq_card_div` proves that this is
exactly the finite ratio:

$$
p_{\mathrm{acc}} =
\frac{|\operatorname{maAcceptSet}(E,\operatorname{stmt},\operatorname{msg})|}
{|\operatorname{validPairs}(E)|}
$$

Write `d = stmt.degBound`, `k = stmt.k`, and
`n = E.points.card`. The advertised knowledge error is:

$$
\varepsilon(E,\operatorname{stmt}) =
\frac{24(d+k+3)n}{|\operatorname{validPairs}(E)|}
$$

Observe that the error depends on the public statement and the curve, not on
the prover's claimed message degree.

## The headline theorem

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
2. the target and every base are affine points of `E`;
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

## Why the implication is non-vacuous

The implication points in the useful direction:

$$
\varepsilon(E,\operatorname{stmt}) < p_{\mathrm{acc}}
\quad\Longrightarrow\quad
\operatorname{maExtractorValid}(E,\operatorname{stmt},\operatorname{msg})
$$

The antecedent is not a reformulation of the conclusion, nor does it assume
that recovery already succeeded. It is an observable property of the
verifier experiment.

The theorem `maSoundnessError_lt_one_of_large` proves that the headline's
`hLargeQ` hypothesis already forces `ε < 1`; this uses the lower bound
`|validPairs E| ≥ n² - 3n`. Thus the advertised error is nontrivial before we
look at `msg` or assume `hAccept`. We also prove the exact arithmetic
criterion, provided `validPairs E` is nonempty:

$$
\varepsilon(E,\operatorname{stmt}) < 1
\quad\Longleftrightarrow\quad
24(d+k+3)n < |\operatorname{validPairs}(E)|
$$

Finally, `maSoundnessError_lt_one_of_accept` records the independent sanity
check that any instance of the strict acceptance hypothesis forces `ε < 1`,
since every VCVio event probability is at most one. These facts are kept
separate from `ma_soundness`; adding `ε < 1` as another premise would merely
repeat a proved consequence of `hLargeQ`.

## What the proof does

The proof is a short probabilistic wrapper around a long counting argument:

1. `ma_soundness_count_bound` proves a dichotomy for every message. Either the
   extractor returns a valid witness, or the message accepts on at most
   `24(d+k+3)n` valid challenge pairs.
2. `maAcceptanceProbability_eq_card_div` turns the VCVio experiment into the
   corresponding cardinality ratio.
3. If `p_acc > ε`, the small-accept-set branch is impossible. Hence the exact
   extractor output is a valid witness.

The internal proof separates two cases. If the log-derivative discrepancy is
nonzero, a Schwartz-Zippel style count bounds the accepting pairs. If it
vanishes on enough defined pairs, the divisor argument recovers the group
equation and proves the extracted scalars valid. A message whose degree check
fails is handled before either case: its accept set is empty.

This is why `ma_soundness` is the right name. The extractor is just a fixed
algorithm; the theorem says that frequent acceptance makes its output valid.

## MA completeness

Soundness quantifies over malicious messages. Completeness is the opposite
direction and therefore has an honesty premise. `ma_completeness` starts from
a valid witness and a message satisfying `MAProverMsg.isHonestFor`; it bounds
the number of rejected challenge pairs by:

$$
(3d+4)n
$$

The constructive `ma_completeness_binary_any_length` family verifies messages
built with `LineAccum.lineBuild_singletons` for binary witnesses under the
decidable `SafePairs` general-position condition. These results are separate
from soundness; no honesty predicate is used by `ma_soundness` or its proof
chain.

## Axiom surface and independent checking

The axiom-free headlines live in `Divisor/Headlines.lean`. Their closures are
the Lean/mathlib core three: `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry` in the library proof chain.

The project has one named mathematical axiom,
`Divisor.hasse_weil_textbook`, in
`Divisor/Axioms/AxiomHasseWeil.lean`. It is the classical Hasse-Weil point
count:

```lean
axiom hasse_weil_textbook (E : ECSetup) :
  |(((E.numPoints : ℤ) - E.q - 1 : ℤ) : ℝ)| ≤
    2 * Real.sqrt (E.q : ℝ)
```

Within the library, only `Divisor/Hasse.lean` imports this axiom;
`Challenge.lean` also imports it so the independent judge can pin its exact
statement. The main theorem above is in the point-count currency and does not
depend on it. The Hasse-priced corollaries replace explicit point-count
hypotheses by bounds in `q`; their names end in `_hasse`. Corresponding
`_of_count` theorems accept two checkable integer point-count bounds instead
and remain axiom-free.

`Tests/AxiomClosurePin.lean` and `Tests/F5RegressionAxiomClosure.lean` pin the
exact axiom closure of the headlines. CI also compares their exported types
against `Challenge.lean`, checks the axiom allowlist, and replays the export
through a fresh Lean kernel. The details are in `Judge/README.md`.

## Build

The repository pins Lean and all dependencies:

```bash
lake build
```

The executable extractor smoke test can be run directly:

```bash
lake build Tests.MAExtractorExec
```
