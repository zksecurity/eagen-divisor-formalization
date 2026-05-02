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

/-- **Logarithmic derivative of a bivariate resultant at a split
specialization.**

Setup: `f, g : K[X][X]` (i.e. polynomials in the outer `Polynomial.X`
with coefficients in `K[X]` for the inner `Polynomial.X`); `t₀ : K` the
inner specialization point. Write `F := Res_X(f, g) ∈ K[T]`, where
`T = Polynomial.X : K[X]` is the inner variable.

Hypotheses:
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
axiom resultant_logDeriv_at_split_specialization
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hF_ne : (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ ≠ 0)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
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

end Polynomial
