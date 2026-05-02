/-
  Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean

  Logarithmic derivative of a bivariate resultant at a split
  specialization point.

  This is the temporary generic narrowing of the chord-fiber
  log-derivative identity. The chord-specific theorem
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace`
  in `Divisor/Axioms/AxiomChordSumEqChordFiberProductLogDeriv.lean` is
  derived from this axiom plus chord-cubic-specific algebra.

  This statement is still a composed resultant/specialisation bridge.
  The intended final proof should derive it from the proved Galois
  norm/trace/log-derivative theorem in `AxiomTraceLogDeriv.lean` plus
  resultant and specialisation algebra.

  Reference: Lang, *Algebra* (3rd ed., GTM 211), §VI.5 Theorem 5.1
  (p. 285) + §VIII.5 Theorem 5.1 Case 1 (p. 370). See
  `axioms/resultant_logDeriv_at_split.md`.
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Divisor.Axioms.AxiomTraceLogDeriv

namespace Polynomial

/-! ## Logarithmic derivative of a bivariate resultant at a split point

For `f, g : K[T][X]` with the *outer* `Polynomial.X` playing the
resultant variable and the *inner* `Polynomial.X` the specialization
parameter `T`, set `F(T) := Res_X(f, g) ∈ K[T]`. At any `t₀ : K`
where the inner-specialised polynomial `f.map (evalRingHom t₀) ∈ K[X]`
splits over `K` with simple roots, each well-separated from `g`'s
vanishing locus, the formal logarithmic derivative `F'(t₀) / F(t₀)` is
the multiset sum of per-chord-root contributions.

Mathematically this is the trace-of-log-derivative formula
`Tr_{L/K}(dα/α) = d N_{L/K}(α)/N_{L/K}(α)` specialised to the
polynomial/resultant setting. The Galois case of that formula is proved
in `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`;
what remains here is the resultant and specialisation plumbing.

Discharge plan in mathlib (the infrastructure exists modulo plumbing):
1. Construct a splitting field of `f` over `K(T)` via
   `Polynomial.SplittingField`; the roots `ξᵢ ∈ L` lift the chord
   roots in `K`.
2. Extend the formal `T`-derivation on `K[T]` to `L` via
   `Differential.deriv_aeval_eq_implicitDeriv` (the implicit-function
   formula `ξ′ = -f^D(ξ)/f'(ξ)`).
3. Apply `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv_of_isGalois`
   to `g(ξ)` and identify the norm with `Res_X(f, g)` and the trace with the
   root sum.
4. Specialise both sides at `T = t₀`. The roots of `f` over `K(T)`
   that are separable specialise to the chord roots in `K`, giving
   the stated multiset sum.

The mathlib pieces (`Differential.mapCoeffs`, `implicitDeriv`,
`logDeriv_multisetProd`) live in `Mathlib.RingTheory.Derivation.MapCoeffs`
and `Mathlib.FieldTheory.Differential.Basic`. The bridge between the
`Polynomial.derivative` map on `K[T]` and the `Differential` instance
on the splitting field is the only missing ingredient. -/

/-! ### Conclusion abbrev (used by both axiom and trivial-case theorem) -/

/-- The conclusion of the resultant-log-derivative identity, factored
out so the axiom and its trivial-case theorem do not duplicate the
long expression. Marked `abbrev` so it transparently reduces at the
existing call site in
`AxiomChordSumEqChordFiberProductLogDeriv.lean`. -/
private abbrev resultantLogDerivConclusion
    {K : Type*} [Field K] (f g : K[X][X]) (t₀ : K) : Prop :=
  Polynomial.eval t₀
      (Polynomial.derivative
        (Polynomial.resultant f g f.natDegree g.natDegree))
    / (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀
  =
    ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
      let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
      let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
      let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
      let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
      let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
      (g_T * f_X - g_X * f_T) / (f_X * g_val))).sum

/-- **Trivial case** (degree zero): when `f` is monic of degree zero,
`f = 1`, so `Res_X(f, g) = 1` (mathlib's `Polynomial.resultant_one_left`
specialised to `m = 0`), the LHS is `0/1 = 0`, and the RHS sum is empty.
This case is provable from polynomial identities and does not need the
generic resultant log-derivative axiom. -/
theorem resultant_logDeriv_at_split_specialization_of_natDegree_eq_zero
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic) (hfdeg : f.natDegree = 0) :
    resultantLogDerivConclusion f g t₀ := by
  have hf : f = 1 := hMonic.natDegree_eq_zero.mp hfdeg
  subst hf
  simp [resultantLogDerivConclusion]

/-- **Logarithmic derivative of a bivariate resultant at a split
specialization** — narrowed to `0 < f.natDegree`.

The `f.natDegree = 0` case is handled separately by the theorem
`resultant_logDeriv_at_split_specialization_of_natDegree_eq_zero` above.
The unrestricted form is recovered as a theorem via case split:
see `resultant_logDeriv_at_split_specialization` below.

Setup: `f, g : K[X][X]` (i.e. polynomials in the outer `Polynomial.X`
with coefficients in `K[X]` for the inner `Polynomial.X`); `t₀ : K` the
inner specialization point. Write `F := Res_X(f, g) ∈ K[T]`, where
`T = Polynomial.X : K[X]` is the inner variable.

Hypotheses:
* `hMonic` — `f` is monic in the outer variable. Without monicity the
  resultant carries an extra `lc(f)^{deg g}` factor (cf. mathlib's
  `Polynomial.resultant_eq_prod_eval`), and the per-chord-root sum
  picks up the corresponding logarithmic derivative
  `d/dT log(lc(f)^{deg g})` term. The project-side caller
  (`chordCubicBiv`) is monic, so we keep the simpler statement.
* `hf_pos` — `0 < f.natDegree`. The degree-zero case is provable from
  polynomial identities (see the theorem above) and is handled by the
  unrestricted re-export.
* `hF_ne` — the resultant evaluation `F(t₀) ≠ 0`.
* `hSplit` — the inner-specialised polynomial `f(X, t₀)` splits
  over `K`.
* `hg_def` — `g(x, t₀) ≠ 0` for every chord root `x` of
  `f(X, t₀)`.
* `hf_X_def` — `f_X(x, t₀) ≠ 0` for every chord root `x` (i.e. the
  outer X-derivative does not vanish; rules out double roots).

Conclusion (per-chord-root form):
```
F'(t₀) / F(t₀) = ∑_{x ∈ f(X, t₀).roots}
  (g_T(x, t₀) · f_X(x, t₀) - g_X(x, t₀) · f_T(x, t₀)) /
  (f_X(x, t₀) · g(x, t₀)),
```
where the partial derivatives are encoded directly via mathlib's
`Polynomial.derivative` and `Polynomial.eval`:
* `f_X(x, t₀) := ((f.map (evalRingHom t₀)).derivative).eval x`,
* `f_T(x, t₀) := ((f.eval (C x)).derivative).eval t₀`,
* `g_X(x, t₀) := ((g.map (evalRingHom t₀)).derivative).eval x`,
* `g_T(x, t₀) := ((g.eval (C x)).derivative).eval t₀`,
* `g(x, t₀) := (g.map (evalRingHom t₀)).eval x`.

The numerator `g_T · f_X - g_X · f_T` is the standard implicit-
function chain-rule combination for `d/dt [g(x(t), t)]` along a
moving chord root `x(t)` defined by `f(x(t), t) = 0`.

Reference: Lang, *Algebra* GTM 211, §VI.5 Theorem 5.1
(product-of-embeddings / norm-trace) + §VIII.5 Theorem 5.1 Case 1
(extension of derivations to separable algebraic extensions). -/
axiom resultant_logDeriv_at_split_specialization_of_pos_natDegree
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hf_pos : 0 < f.natDegree)
    (hF_ne : (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ ≠ 0)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
  resultantLogDerivConclusion f g t₀

/-- **Re-export — the unrestricted resultant log-derivative identity**,
now a theorem derived from the narrowed `0 < f.natDegree` axiom plus
the trivial degree-zero theorem above.

This is the form that downstream consumers
(`chord_fiber_product_logDeriv_eq_logDerivTerm_trace` in
`AxiomChordSumEqChordFiberProductLogDeriv.lean`) actually use; the
call site is unchanged. -/
theorem resultant_logDeriv_at_split_specialization
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hF_ne : (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ ≠ 0)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
    resultantLogDerivConclusion f g t₀ := by
  by_cases hd : f.natDegree = 0
  · exact resultant_logDeriv_at_split_specialization_of_natDegree_eq_zero
      f g t₀ hMonic hd
  · exact resultant_logDeriv_at_split_specialization_of_pos_natDegree
      f g t₀ hMonic (Nat.pos_of_ne_zero hd) hF_ne hSplit hg_def hf_X_def

end Polynomial
