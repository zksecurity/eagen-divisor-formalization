/-
  Divisor/Bridges/ResultantLogDerivAtSplit.lean

  Logarithmic derivative of a bivariate resultant at a split
  specialization point — the generic core of the chord-fiber
  log-derivative identity. The chord-specific theorem
  `chord_fiber_product_logDeriv_eq_logDerivTerm_trace` in
  `Divisor/Bridges/ChordSumEqChordFiberProductLogDeriv.lean` is
  derived from the theorems here plus chord-cubic-specific algebra.

  Route: prove the dual-number product formula for resultants at a
  split specialization, take the `ε` coefficient for the derivative
  product formula, and divide by the nonzero resultant value for the
  logarithmic-derivative form.
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.DualNumber
import Divisor.Bridges.TraceLogDeriv
import Divisor.PolynomialDifferential

namespace Polynomial

/-! ## Logarithmic derivative of a bivariate resultant at a split point

For `f, g : K[T][X]` with the *outer* `Polynomial.X` playing the
resultant variable and the *inner* `Polynomial.X` the specialization
parameter `T`, set `F(T) := Res_X(f, g) ∈ K[T]`. At any `t₀ : K`
where the inner-specialised polynomial `f.map (evalRingHom t₀) ∈ K[X]`
splits over `K` with simple roots, each well-separated from `g`'s
vanishing locus, the formal logarithmic derivative `F'(t₀) / F(t₀)` is
the multiset sum of per-chord-root contributions.

Mathematically this is a first-order form of the trace-of-log-derivative formula
`Tr_{L/K}(dα/α) = d N_{L/K}(α)/N_{L/K}(α)` specialised to the
polynomial/resultant setting. The proof below avoids a splitting-field
detour: after applying the first-order jet `T ↦ t₀ + ε`, the specialized
polynomial has exactly the lifted simple roots, so the usual product
formula for resultants gives the dual-number identity directly. -/

/-! ### Conclusion abbrev (used by the residual and trivial-case theorems) -/

/-- The conclusion of the resultant-log-derivative identity, factored
out so the residual and trivial-case theorems do not duplicate the
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

/-! ### Resultant collapse when `g` is constant in the outer variable

Reusable helper: when `g.natDegree = 0` (g is constant in the outer
resultant variable), `g = Polynomial.C (g.coeff 0)` and the resultant
collapses to `(g.coeff 0) ^ f.natDegree`. This is a thin wrapper around
mathlib's `Polynomial.resultant_zero_right_deg`. -/

/-- When `g.natDegree = 0`, the bivariate resultant
`Res_X(f, g, m, 0)` equals `(g.coeff 0) ^ m`. -/
theorem resultant_eq_pow_of_g_natDegree_eq_zero
    {K : Type*} [Field K]
    (f g : K[X][X]) (hg_zero : g.natDegree = 0) :
    Polynomial.resultant f g f.natDegree g.natDegree
      = (g.coeff 0) ^ f.natDegree := by
  rw [hg_zero, Polynomial.resultant_zero_right_deg]

/-- **Partial discharge** of the resultant log-derivative identity for
the case where `g` is constant in the outer (resultant) variable.

For `g` with `g.natDegree = 0`, write `h := g.coeff 0`. Then the LHS
equals `m · h'(t₀)/h(t₀)` (logarithmic derivative of `h^m`), and each
RHS summand collapses to the constant `h'(t₀)/h(t₀)`, summed over
`m = f.natDegree` chord roots. -/
theorem resultant_logDeriv_at_split_specialization_of_g_natDegree_eq_zero
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hg_zero : g.natDegree = 0)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hh_ne : (g.coeff 0).eval t₀ ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
    resultantLogDerivConclusion f g t₀ := by
  classical
  -- Setup: h = g.coeff 0; g = C h; F = h^m.
  set h : K[X] := g.coeff 0 with hh_def
  have hg_eq : g = Polynomial.C h := by
    rw [hh_def]; exact Polynomial.eq_C_of_natDegree_eq_zero hg_zero
  -- Roots-card identity (for monic f, splits + natDegree_map_monic).
  have hf_mapNatDeg : (f.map (Polynomial.evalRingHom t₀)).natDegree = f.natDegree :=
    hMonic.natDegree_map _
  have hroots_card :
      (f.map (Polynomial.evalRingHom t₀)).roots.card = f.natDegree := by
    rw [← hf_mapNatDeg, ← Polynomial.Splits.natDegree_eq_card_roots hSplit]
  -- Define the constant summand value.
  set ν : K := h.derivative.eval t₀ / h.eval t₀ with hν_def
  -- Show RHS multiset equals constant ν repeated, then sum.
  have hsum_const : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
      (let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
       let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
       let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
       let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
       let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
       (g_T * f_X - g_X * f_T) / (f_X * g_val)) = ν := by
    intro x hx
    simp only [hg_eq, Polynomial.map_C, Polynomial.derivative_C,
               Polynomial.eval_C, Polynomial.eval_zero, zero_mul, sub_zero]
    have hfX := hf_X_def x hx
    rw [hν_def]
    rw [show (Polynomial.evalRingHom t₀) h = h.eval t₀ from rfl]
    field_simp
  -- Compute the LHS via resultant_eq_pow_of_g_natDegree_eq_zero.
  unfold resultantLogDerivConclusion
  rw [resultant_eq_pow_of_g_natDegree_eq_zero f g hg_zero, ← hh_def]
  -- The RHS multiset map is constant on the support; rewrite.
  rw [show ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
        let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
        let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
        let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
        (g_T * f_X - g_X * f_T) / (f_X * g_val)))
        = (f.map (Polynomial.evalRingHom t₀)).roots.map (fun _ => ν) from
    Multiset.map_congr rfl hsum_const]
  rw [Multiset.map_const', Multiset.sum_replicate, hroots_card]
  -- Goal: F'(t₀)/F(t₀) = (f.natDegree : K) • ν.
  -- Compute F = h^m and its derivative.
  rw [Polynomial.derivative_pow, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_pow]
  rcases Nat.eq_zero_or_pos f.natDegree with hm0 | hmpos
  · simp [hm0, hν_def]
  · rw [show f.natDegree = (f.natDegree - 1) + 1 from
        (Nat.succ_pred_eq_of_pos hmpos).symm,
      pow_succ, hν_def, nsmul_eq_mul]
    field_simp
    have : f.natDegree - 1 + 1 - 1 = f.natDegree - 1 := by omega
    rw [this]
    ring

/-! ### Partial discharge: `f.natDegree = 1` (monic linear)

When `f` is monic of degree 1, `f = X - C α` for some `α : K[X]`, and
mathlib's `Polynomial.resultant_X_sub_C_left` collapses
`Res_X(f, g, 1, n)` to `g.eval α`. The log-derivative identity at
`t₀ : K` reduces to the chain rule for `g.eval α` along the moving
chord-root `α(T)`. The chain rule comes from
`Differential.deriv_aeval_eq` applied to the polynomial-as-derivation
`Polynomial.derivative` on `K[T]` (instance from
`Divisor.PolynomialDifferential`). -/

/-- "Eval-then-eval = map-then-eval" for bivariate polynomials at a
specialization point. For `p : K[X][X]`, `α : K[X]`, `t₀ : K`:
`(p.eval α).eval t₀ = (p.map (evalRingHom t₀)).eval (α.eval t₀)`.
This is the standard `eval₂_at_apply` route through the inner-coeff
ring hom `evalRingHom t₀ : K[X] → K`. -/
private lemma eval_eval_eq_map_eval
    {K : Type*} [Field K] (p : K[X][X]) (α : K[X]) (t₀ : K) :
    (p.eval α).eval t₀
      = (p.map (Polynomial.evalRingHom t₀)).eval (α.eval t₀) := by
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (Polynomial.evalRingHom t₀) α).symm

/-- Inner derivative of `g` evaluated at a constant `C t : K[X]`
equals `Differential.mapCoeffs g` evaluated at the same constant.

Reason: when `t : K` is a scalar (so `(C t)^n = C (t^n)` is constant
in the inner variable `T`), the only non-vanishing contribution to
the inner derivative of `(monomial n a).eval (C t) = a * (C t)^n` is
the coefficient derivative `a.derivative * (C t)^n`. This matches
`(monomial n a.derivative).eval (C t)` term-by-term via polynomial
induction. -/
private lemma derivative_eval_C_const_eq_mapCoeffs_eval_C
    {K : Type*} [Field K] (g : K[X][X]) (t : K) :
    (g.eval (Polynomial.C t)).derivative
      = (Differential.mapCoeffs g).eval (Polynomial.C t) := by
  induction g using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.eval_add, ihp, ihq, map_add]
  | monomial n a =>
    simp only [Polynomial.eval_monomial, Polynomial.derivative_mul,
               Polynomial.derivative_pow, Polynomial.derivative_C, mul_zero,
               add_zero, Differential.mapCoeffs_monomial,
               Polynomial.deriv_eq_derivative]

/-- Chain rule for the outer evaluation `g.eval α` of a bivariate
polynomial `g : K[X][X]` along a moving curve `α : K[X]`, expressed
as the inner formal derivative of `g.eval α : K[X]`. Derived from
`Differential.deriv_aeval_eq` instantiated at the trivial algebra
`K[X] / K[X]` with `Differential` instance from
`Divisor.PolynomialDifferential`. -/
private lemma derivative_eval_chain
    {K : Type*} [Field K] (g : K[X][X]) (α : K[X]) :
    (g.eval α).derivative
      = (Differential.mapCoeffs g).eval α
        + (g.derivative).eval α * α.derivative := by
  have h_ae : ∀ p : K[X][X], Polynomial.aeval (R := K[X]) α p = p.eval α := by
    intro p
    show (Polynomial.aeval α : K[X][X] → K[X]) p = _
    rw [Polynomial.coe_aeval_eq_eval]
  have hkey :=
    Differential.deriv_aeval_eq (R := K[X]) (A := K[X]) α g
  rw [h_ae g, h_ae (Differential.mapCoeffs g), h_ae g.derivative] at hkey
  exact hkey

/-- **Eval-then-derivative chain rule** in the form used by the
log-derivative identity: the inner derivative of `g.eval α`
evaluated at `t₀` decomposes as
`g_T(α(t₀), t₀) + g_X(α(t₀), t₀) * α'(t₀)`. -/
private lemma derivative_eval_at_chain
    {K : Type*} [Field K] (g : K[X][X]) (α : K[X]) (t₀ : K) :
    ((g.eval α).derivative).eval t₀
      = ((g.eval (Polynomial.C (α.eval t₀))).derivative).eval t₀
        + ((g.map (Polynomial.evalRingHom t₀)).derivative).eval (α.eval t₀)
            * α.derivative.eval t₀ := by
  rw [derivative_eval_chain g α, Polynomial.eval_add, Polynomial.eval_mul]
  have hgT : ((Differential.mapCoeffs g).eval α).eval t₀
      = ((g.eval (Polynomial.C (α.eval t₀))).derivative).eval t₀ := by
    rw [eval_eval_eq_map_eval, derivative_eval_C_const_eq_mapCoeffs_eval_C,
        eval_eval_eq_map_eval, Polynomial.eval_C]
  have hgX : ((g.derivative).eval α).eval t₀
      = ((g.map (Polynomial.evalRingHom t₀)).derivative).eval (α.eval t₀) := by
    rw [eval_eval_eq_map_eval, Polynomial.derivative_map]
  rw [hgT, hgX]

/-! ### Dual-number first-order specialization bridge

The remaining generic resultant bridge is most naturally expressed as a
dual-number identity.  The ring hom `jet t₀` sends a univariate
polynomial `p(T)` to `p(t₀) + p'(t₀) ε`; taking the `ε` coefficient then
recovers the desired derivative at `t₀`. -/

/-- First-order Taylor specialization `p(T) ↦ p(t₀) + p'(t₀) ε`. -/
noncomputable def jet {K : Type*} [Field K] (t₀ : K) : K[X] →+* DualNumber K :=
  Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom K K)
    (TrivSqZeroExt.inl t₀ + DualNumber.eps)

@[simp] theorem fst_jet {K : Type*} [Field K] (t₀ : K) (p : K[X]) :
    TrivSqZeroExt.fst (jet t₀ p) = p.eval t₀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
      simp [jet, Polynomial.eval₂RingHom, Polynomial.eval₂AddMonoidHom]

@[simp] theorem snd_jet {K : Type*} [Field K] (t₀ : K) (p : K[X]) :
    TrivSqZeroExt.snd (jet t₀ p) = p.derivative.eval t₀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
      simp [jet, Polynomial.eval₂RingHom, Polynomial.eval₂AddMonoidHom,
        Polynomial.derivative_monomial]
      ring

/-- Resultant of an explicit product of monic linear factors, over any
nontrivial commutative ring.  This is the commutative-ring replacement
for the domain-only split-resultant product formula when working over
dual numbers. -/
theorem resultant_finset_prod_X_sub_C_left
    {R ι : Type*} [CommRing R] [Nontrivial R] (s : Finset ι) (r : ι → R)
    (g : R[X]) (n : ℕ) (hn : g.natDegree ≤ n) :
    Polynomial.resultant (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))) g
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (r i))).natDegree n
      = ∏ i ∈ s, Polynomial.eval (r i) g := by
  rw [Polynomial.resultant_prod_left]
  · apply Finset.prod_congr rfl
    intro i _hi
    simpa [Polynomial.natDegree_X_sub_C] using
      (Polynomial.resultant_X_sub_C_left (g := g) (n := n) (r := r i) hn)
  · simp
  · exact hn

@[simp] theorem fst_eval_map_jet_at_lift
    {K : Type*} [Field K] (p : K[X][X]) (t₀ x v : K) :
    TrivSqZeroExt.fst
      ((p.map (jet t₀)).eval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v))
      = (p.map (Polynomial.evalRingHom t₀)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        TrivSqZeroExt.fst
            (((p + q).map (jet t₀)).eval
              (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v))
            =
            TrivSqZeroExt.fst
              ((p.map (jet t₀)).eval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v))
              +
            TrivSqZeroExt.fst
              ((q.map (jet t₀)).eval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v)) := by
              simp [Polynomial.map_add, Polynomial.eval_add, TrivSqZeroExt.fst_add]
        _ = (p.map (Polynomial.evalRingHom t₀)).eval x
              + (q.map (Polynomial.evalRingHom t₀)).eval x := by
              rw [hp, hq]
        _ = ((p + q).map (Polynomial.evalRingHom t₀)).eval x := by
              simp [Polynomial.map_add, Polynomial.eval_add]
  | monomial n a =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial]

/-- Dual-number chain rule for bivariate polynomial evaluation:
evaluating `p.map (jet t₀)` at `x + v ε` has `ε` coefficient
`p_T(x,t₀) + p_X(x,t₀) v`. -/
theorem snd_eval_map_jet_at_lift
    {K : Type*} [Field K] (p : K[X][X]) (t₀ x v : K) :
    TrivSqZeroExt.snd
      ((p.map (jet t₀)).eval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v))
      =
        ((p.eval (Polynomial.C x)).derivative).eval t₀
          + ((p.map (Polynomial.evalRingHom t₀)).derivative).eval x * v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add,
        TrivSqZeroExt.snd_add, hp, hq]
      simp [Polynomial.derivative_add, Polynomial.eval_add, add_assoc, add_left_comm]
      ring
  | monomial n a =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_C, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.derivative_monomial]
      ring

/-- Logarithmic derivative of a finite product in dual-number form. -/
theorem snd_multiset_prod_eq_fst_prod_mul_sum
    {K ι : Type*} [Field K] (s : Multiset ι) (a : ι → DualNumber K)
    (ha : ∀ i ∈ s, TrivSqZeroExt.fst (a i) ≠ 0) :
    TrivSqZeroExt.snd ((s.map a).prod)
      =
        TrivSqZeroExt.fst ((s.map a).prod)
          * (s.map (fun i => TrivSqZeroExt.snd (a i) / TrivSqZeroExt.fst (a i))).sum := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons i s ih =>
      have ha_i : TrivSqZeroExt.fst (a i) ≠ 0 := ha i (by simp)
      have ha_s : ∀ j ∈ s, TrivSqZeroExt.fst (a j) ≠ 0 := by
        intro j hj
        exact ha j (by simp [hj])
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, ih ha_s]
      simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      field_simp [ha_i]
      ring

/-- The residual derivative/product formula follows from the
dual-number product identity for the resultant. -/
theorem resultant_derivative_at_split_specialization_product_formula_of_jet_product
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0)
    (hJetProd :
      let liftEval : K → DualNumber K := fun x =>
        (g.map (jet t₀)).eval
          (TrivSqZeroExt.inl x
            + TrivSqZeroExt.inr
                (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
                  / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x)))
      jet t₀ (Polynomial.resultant f g f.natDegree g.natDegree)
        = (((f.map (Polynomial.evalRingHom t₀)).roots.map liftEval).prod)) :
  Polynomial.eval t₀
      (Polynomial.derivative
        (Polynomial.resultant f g f.natDegree g.natDegree))
    =
    (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ *
      ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
        let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
        let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
        let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
        (g_T * f_X - g_X * f_T) / (f_X * g_val))).sum := by
  classical
  let rts := (f.map (Polynomial.evalRingHom t₀)).roots
  let liftEval : K → DualNumber K := fun x =>
    (g.map (jet t₀)).eval
      (TrivSqZeroExt.inl x
        + TrivSqZeroExt.inr
            (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
              / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x)))
  have hfst_ne : ∀ x ∈ rts, TrivSqZeroExt.fst (liftEval x) ≠ 0 := by
    intro x hx
    dsimp [liftEval]
    rw [fst_eval_map_jet_at_lift]
    exact hg_def x hx
  have hprod_snd := snd_multiset_prod_eq_fst_prod_mul_sum rts liftEval hfst_ne
  have hprod_fst :
      TrivSqZeroExt.fst ((rts.map liftEval).prod)
        = (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ := by
    rw [← hJetProd]
    exact fst_jet t₀ (Polynomial.resultant f g f.natDegree g.natDegree)
  have hsum :
      (rts.map (fun i => TrivSqZeroExt.snd (liftEval i) / TrivSqZeroExt.fst (liftEval i))).sum
        =
      ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
        let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
        let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
        let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
        (g_T * f_X - g_X * f_T) / (f_X * g_val))).sum := by
    dsimp [rts]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    dsimp [liftEval]
    rw [fst_eval_map_jet_at_lift, snd_eval_map_jet_at_lift]
    have hfX := hf_X_def x hx
    have hgx := hg_def x hx
    field_simp [hfX, hgx]
    ring
  calc
    Polynomial.eval t₀
        (Polynomial.derivative
          (Polynomial.resultant f g f.natDegree g.natDegree))
        =
        TrivSqZeroExt.snd ((rts.map liftEval).prod) := by
          rw [← hJetProd]
          exact (snd_jet t₀ (Polynomial.resultant f g f.natDegree g.natDegree)).symm
    _ =
        TrivSqZeroExt.fst ((rts.map liftEval).prod)
          * (rts.map (fun i => TrivSqZeroExt.snd (liftEval i) / TrivSqZeroExt.fst (liftEval i))).sum := hprod_snd
    _ =
        (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ *
          ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
            let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
            let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
            let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
            let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
            let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
            (g_T * f_X - g_X * f_T) / (f_X * g_val))).sum := by
          rw [hprod_fst, hsum]

/-- **Partial discharge** of the resultant log-derivative identity for
the case `f.natDegree = 1` (with `f.Monic`).

Set `α := -f.coeff 0`; then `f = X - C α` and
`Res_X(f, g, 1, n) = g.eval α` by mathlib's `resultant_X_sub_C_left`.
The chord-root multiset is `{α.eval t₀}` (singleton), so the RHS
collapses to a single summand. The chain-rule identity
`(g.eval α)'(t₀) = g_T(α(t₀), t₀) + g_X(α(t₀), t₀) * α'(t₀)` matches
the RHS numerator after simplifying `f_X = 1` and
`f_T = -α'(t₀)`. -/
theorem resultant_logDeriv_at_split_specialization_of_f_natDegree_eq_one
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hf_one : f.natDegree = 1)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0) :
    resultantLogDerivConclusion f g t₀ := by
  classical
  -- f = X - C α with α := -f.coeff 0.
  set α : K[X] := -f.coeff 0 with hα_def
  have hf_eq : f = Polynomial.X - Polynomial.C α := by
    rw [hα_def, map_neg, sub_neg_eq_add]
    exact hMonic.eq_X_add_C hf_one
  -- f.map (evalRingHom t₀) = X - C (α.eval t₀).
  have hf_map :
      f.map (Polynomial.evalRingHom t₀)
        = Polynomial.X - Polynomial.C (α.eval t₀) := by
    rw [hf_eq, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  -- Roots: singleton {α.eval t₀}.
  have hroots :
      (f.map (Polynomial.evalRingHom t₀)).roots = {α.eval t₀} := by
    rw [hf_map, Polynomial.roots_X_sub_C]
  have ht_mem : α.eval t₀ ∈ (f.map (Polynomial.evalRingHom t₀)).roots := by
    rw [hroots]; exact Multiset.mem_singleton.mpr rfl
  have hg_t :
      (g.map (Polynomial.evalRingHom t₀)).eval (α.eval t₀) ≠ 0 :=
    hg_def _ ht_mem
  -- F = Res(f, g, 1, n) = g.eval α.
  have hF_eq : Polynomial.resultant f g f.natDegree g.natDegree = g.eval α := by
    rw [hf_one, hf_eq]
    exact Polynomial.resultant_X_sub_C_left g g.natDegree α le_rfl
  -- f_X = 1; f_T = -α.derivative.eval t₀.
  have hf_X_val :
      ((f.map (Polynomial.evalRingHom t₀)).derivative).eval (α.eval t₀) = 1 := by
    rw [hf_map, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, Polynomial.eval_one]
  have hf_T_val :
      ((f.eval (Polynomial.C (α.eval t₀))).derivative).eval t₀
        = -α.derivative.eval t₀ := by
    rw [hf_eq, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.derivative_sub, Polynomial.derivative_C, zero_sub,
        Polynomial.eval_neg]
  -- Chain rule.
  have h_chain := derivative_eval_at_chain g α t₀
  -- Expand the conclusion.
  unfold resultantLogDerivConclusion
  rw [hF_eq, hroots, Multiset.map_singleton, Multiset.sum_singleton]
  rw [eval_eval_eq_map_eval g α t₀, h_chain]
  simp only [hf_X_val, hf_T_val]
  field_simp
  ring

/-- A root whose derivative is nonzero occurs with multiplicity one in
the root multiset. -/
private lemma rootMultiplicity_eq_one_of_mem_roots_of_derivative_ne_zero
    {K : Type*} [Field K] {p : K[X]} {x : K}
    (hx : x ∈ p.roots) (hp' : p.derivative.eval x ≠ 0) :
    p.rootMultiplicity x = 1 := by
  have hp0 : p ≠ 0 := Polynomial.ne_zero_of_mem_roots hx
  have hpos : 0 < p.rootMultiplicity x := by
    rw [Polynomial.rootMultiplicity_pos hp0]
    exact Polynomial.isRoot_of_mem_roots hx
  have hle : p.rootMultiplicity x ≤ 1 := by
    by_contra hnot
    have hlt : 1 < p.rootMultiplicity x := Nat.lt_of_not_ge hnot
    have hiff := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := p) (t := x) hp0).mp hlt
    exact hp' hiff.2
  omega

/-- If every root has nonzero derivative, then the root multiset has no
duplicates. -/
private lemma roots_nodup_of_derivative_ne_zero
    {K : Type*} [Field K] {p : K[X]}
    (hp' : ∀ x ∈ p.roots, p.derivative.eval x ≠ 0) :
    p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  by_cases hx : x ∈ p.roots
  · rw [Polynomial.count_roots]
    exact (rootMultiplicity_eq_one_of_mem_roots_of_derivative_ne_zero hx (hp' x hx)).le
  · rw [Multiset.count_eq_zero.mpr hx]
    exact Nat.zero_le 1

/-- The implicit-function first-order lift of a simple root of
`f(X,t₀)` is a root of `f(X,t₀ + ε)`. -/
private lemma lifted_root_isRoot_map_jet
    {K : Type*} [Field K]
    (f : K[X][X]) (t₀ x : K)
    (hx : x ∈ (f.map (Polynomial.evalRingHom t₀)).roots)
    (hf_X : ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
    (f.map (jet t₀)).IsRoot
      (TrivSqZeroExt.inl x
        + TrivSqZeroExt.inr
            (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
              / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x))) := by
  rw [Polynomial.IsRoot.def]
  apply TrivSqZeroExt.ext
  · rw [fst_eval_map_jet_at_lift]
    exact Polynomial.IsRoot.def.mp (Polynomial.isRoot_of_mem_roots hx)
  · rw [snd_eval_map_jet_at_lift]
    rw [TrivSqZeroExt.snd_zero]
    field_simp [hf_X]
    ring

set_option maxHeartbeats 800000 in
/-- First-order factorisation of `f` after applying the dual-number jet. -/
theorem map_jet_eq_multiset_prod_lifted_roots
    {K : Type*} [Field K]
    (f : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
    f.map (jet t₀)
      =
      ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
        Polynomial.X - Polynomial.C
          (TrivSqZeroExt.inl x
            + TrivSqZeroExt.inr
                (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
                  / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x))))).prod := by
  classical
  let p0 : K[X] := f.map (Polynomial.evalRingHom t₀)
  let lift : K → DualNumber K := fun x =>
    TrivSqZeroExt.inl x
      + TrivSqZeroExt.inr
          (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
            / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x))
  let prodP : (DualNumber K)[X] := (p0.roots.map fun x => Polynomial.X - Polynomial.C (lift x)).prod
  have hnodup : p0.roots.Nodup := by
    dsimp [p0]
    exact roots_nodup_of_derivative_ne_zero hf_X_def
  have hprod_eq_finset :
      prodP = ∏ x ∈ p0.roots.toFinset, (Polynomial.X - Polynomial.C (lift x)) := by
    dsimp [prodP]
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Multiset.count_eq_one_of_mem hnodup (by simpa using hx), pow_one]
  have hdvd_each :
      ∀ x ∈ p0.roots.toFinset,
        Polynomial.X - Polynomial.C (lift x) ∣ f.map (jet t₀) := by
    intro x hx
    rw [Polynomial.dvd_iff_isRoot]
    exact lifted_root_isRoot_map_jet f t₀ x (by simpa [p0] using hx) (hf_X_def x (by simpa [p0] using hx))
  have hpair :
      (p0.roots.toFinset : Set K).Pairwise
        (fun x y => IsCoprime (Polynomial.X - Polynomial.C (lift x))
          (Polynomial.X - Polynomial.C (lift y))) := by
    intro x _hx y _hy hxy
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
    simpa [lift] using hxy0.isUnit
  have hdvd_finset :
      (∏ x ∈ p0.roots.toFinset, (Polynomial.X - Polynomial.C (lift x))) ∣ f.map (jet t₀) :=
    Finset.prod_dvd_of_coprime hpair hdvd_each
  have hdvd : prodP ∣ f.map (jet t₀) := by
    rwa [hprod_eq_finset]
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le ?hprodMonic ?hfMonic hdvd ?hdeg
  · change prodP.Monic
    dsimp [prodP]
    simpa [Multiset.map_map, Function.comp_def] using
      (Polynomial.monic_multisetProd_X_sub_C (p0.roots.map lift))
  · exact hMonic.map (jet t₀)
  · change (f.map (jet t₀)).natDegree ≤ prodP.natDegree
    rw [hMonic.natDegree_map (jet t₀)]
    dsimp [prodP]
    have hdegprod :
        (Multiset.map (fun x => Polynomial.X - Polynomial.C (lift x)) p0.roots).prod.natDegree
          = p0.roots.card := by
      simpa [Multiset.map_map, Function.comp_def] using
        (Polynomial.natDegree_multiset_prod_X_sub_C_eq_card (p0.roots.map lift))
    rw [hdegprod, ← hSplit.natDegree_eq_card_roots]
    exact le_of_eq (hMonic.natDegree_map (Polynomial.evalRingHom t₀)).symm

/-- **Residual dual-number product bridge for a bivariate resultant at a
split specialization** — narrowed to `2 ≤ f.natDegree` and
`0 < g.natDegree`.

This is the remaining citable bridge.  It is lower-level than the
derivative/product formula: after first-order specialization
`T ↦ t₀ + ε`, the resultant is the product of `g` evaluated at the
first-order lifted roots of `f`.  The lifted root velocity is the
implicit-function value `x' = -f_T/f_X`.

The derivative/product theorem below is proved from this statement by
taking the `ε` coefficient and applying the dual-number product rule. -/
theorem resultant_jet_product_at_split_specialization
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (_hf_two_le : 2 ≤ f.natDegree)
    (_hg_pos : 0 < g.natDegree)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (_hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
  let liftEval : K → DualNumber K := fun x =>
    (g.map (jet t₀)).eval
      (TrivSqZeroExt.inl x
        + TrivSqZeroExt.inr
            (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
              / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x)))
  jet t₀ (Polynomial.resultant f g f.natDegree g.natDegree)
    = (((f.map (Polynomial.evalRingHom t₀)).roots.map liftEval).prod) := by
  classical
  let p0 : K[X] := f.map (Polynomial.evalRingHom t₀)
  let lift : K → DualNumber K := fun x =>
    TrivSqZeroExt.inl x
      + TrivSqZeroExt.inr
          (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
            / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x))
  let liftEval : K → DualNumber K := fun x =>
    (g.map (jet t₀)).eval (lift x)
  let prodP : (DualNumber K)[X] :=
    (p0.roots.map fun x => Polynomial.X - Polynomial.C (lift x)).prod
  have hnodup : p0.roots.Nodup := by
    dsimp [p0]
    exact roots_nodup_of_derivative_ne_zero hf_X_def
  have hprod_eq_finset :
      prodP = ∏ x ∈ p0.roots.toFinset, (Polynomial.X - Polynomial.C (lift x)) := by
    dsimp [prodP]
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Multiset.count_eq_one_of_mem hnodup (by simpa using hx), pow_one]
  have hrhs_eq_finset :
      (p0.roots.map liftEval).prod = ∏ x ∈ p0.roots.toFinset, liftEval x := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_congr rfl
    intro x hx
    rw [Multiset.count_eq_one_of_mem hnodup (by simpa using hx), pow_one]
  have hdegProd : prodP.natDegree = f.natDegree := by
    dsimp [prodP]
    have hdegprod :
        (Multiset.map (fun x => Polynomial.X - Polynomial.C (lift x)) p0.roots).prod.natDegree
          = p0.roots.card := by
      simpa [Multiset.map_map, Function.comp_def] using
        (Polynomial.natDegree_multiset_prod_X_sub_C_eq_card (p0.roots.map lift))
    rw [hdegprod, ← hSplit.natDegree_eq_card_roots]
    exact hMonic.natDegree_map (Polynomial.evalRingHom t₀)
  have hfac : f.map (jet t₀) = prodP := by
    dsimp [prodP, p0, lift]
    exact map_jet_eq_multiset_prod_lifted_roots f t₀ hMonic hSplit hf_X_def
  calc
    jet t₀ (Polynomial.resultant f g f.natDegree g.natDegree)
        =
        Polynomial.resultant (f.map (jet t₀)) (g.map (jet t₀))
          f.natDegree g.natDegree := by
          rw [Polynomial.resultant_map_map]
    _ =
        Polynomial.resultant prodP (g.map (jet t₀)) prodP.natDegree g.natDegree := by
          rw [hfac, hdegProd]
    _ =
        ∏ x ∈ p0.roots.toFinset, Polynomial.eval (lift x) (g.map (jet t₀)) := by
          rw [hprod_eq_finset]
          exact resultant_finset_prod_X_sub_C_left
            p0.roots.toFinset lift (g.map (jet t₀)) g.natDegree
            (Polynomial.natDegree_map_le)
    _ =
        (((f.map (Polynomial.evalRingHom t₀)).roots.map
          (fun x =>
            (g.map (jet t₀)).eval
              (TrivSqZeroExt.inl x
                + TrivSqZeroExt.inr
                    (-(((f.eval (Polynomial.C x)).derivative).eval t₀)
                      / (((f.map (Polynomial.evalRingHom t₀)).derivative).eval x))))).prod) := by
          rw [← hrhs_eq_finset]

/-- **Residual derivative/product bridge for a bivariate resultant at a
split specialization** — theorem derived from the dual-number product
bridge above. -/
theorem resultant_derivative_at_split_specialization_product_formula
    {K : Type*} [Field K]
    (f g : K[X][X]) (t₀ : K)
    (hMonic : f.Monic)
    (hf_two_le : 2 ≤ f.natDegree)
    (hg_pos : 0 < g.natDegree)
    (hSplit : (f.map (Polynomial.evalRingHom t₀)).Splits)
    (hg_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        (g.map (Polynomial.evalRingHom t₀)).eval x ≠ 0)
    (hf_X_def : ∀ x ∈ (f.map (Polynomial.evalRingHom t₀)).roots,
        ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x ≠ 0) :
  Polynomial.eval t₀
      (Polynomial.derivative
        (Polynomial.resultant f g f.natDegree g.natDegree))
    =
    (Polynomial.resultant f g f.natDegree g.natDegree).eval t₀ *
      ((f.map (Polynomial.evalRingHom t₀)).roots.map (fun x =>
        let f_X := ((f.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let f_T := ((f.eval (Polynomial.C x)).derivative).eval t₀
        let g_X := ((g.map (Polynomial.evalRingHom t₀)).derivative).eval x
        let g_T := ((g.eval (Polynomial.C x)).derivative).eval t₀
        let g_val := (g.map (Polynomial.evalRingHom t₀)).eval x
        (g_T * f_X - g_X * f_T) / (f_X * g_val))).sum :=
  resultant_derivative_at_split_specialization_product_formula_of_jet_product
    f g t₀ hg_def hf_X_def
    (resultant_jet_product_at_split_specialization
      f g t₀ hMonic hf_two_le hg_pos hSplit hg_def hf_X_def)

/-- **Logarithmic derivative of a bivariate resultant at a split
specialization** — theorem derived from the residual product-form bridge.

This declaration keeps the old downstream API stable while removing the
logarithmic division itself from the axiom surface.

Three sub-cases are handled by separate theorems and excluded from the
residual bridge:
* `f.natDegree = 0`:
  `resultant_logDeriv_at_split_specialization_of_natDegree_eq_zero`.
* `g.natDegree = 0`:
  `resultant_logDeriv_at_split_specialization_of_g_natDegree_eq_zero`.
* `f.natDegree = 1`:
  `resultant_logDeriv_at_split_specialization_of_f_natDegree_eq_one`.

The unrestricted form (`resultant_logDeriv_at_split_specialization`)
is a theorem that case-splits on `f.natDegree` and `g.natDegree` and
dispatches to the appropriate trivial-case theorem or to this
narrowed theorem.

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
* `hf_two_le` — `2 ≤ f.natDegree`. The cases `f.natDegree = 0` and
  `f.natDegree = 1` are handled by separate theorems above (the
  degree-1 case via `resultant_X_sub_C_left` and the chain rule for
  `g.eval α`).
* `hg_pos` — `0 < g.natDegree`. The degree-zero case for `g` is
  proved from `derivative_pow` plus the fact that the constant
  `g.coeff 0`'s logarithmic derivative is constant on the chord-root
  multiset (see `_of_g_natDegree_eq_zero` above).
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

Human-readable version: for `F(T) = Res_X(f(X,T), g(X,T))`, if
`f(X,t0)` splits into simple roots and `g` does not vanish at those
roots, then the logarithmic derivative `F'(t0)/F(t0)` is the sum over
the roots of the logarithmic derivative of `g` along the corresponding
moving root of `f`. -/
theorem resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
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
  resultantLogDerivConclusion f g t₀ := by
  have hProd :=
    resultant_derivative_at_split_specialization_product_formula
      f g t₀ hMonic hf_two_le hg_pos hSplit hg_def hf_X_def
  unfold resultantLogDerivConclusion
  rw [hProd]
  field_simp [hF_ne]

/-- **Re-export — the unrestricted resultant log-derivative identity**,
a theorem derived from the narrowed `_of_two_le_natDegree_pos_g`
theorem plus the three trivial-case theorems above.

Cases:
* `f.natDegree = 0`: `_of_natDegree_eq_zero`.
* `f.natDegree = 1`: `_of_f_natDegree_eq_one` (via the
  `resultant_X_sub_C_left` collapse and the chain rule for
  `g.eval α`).
* `2 ≤ f.natDegree, g.natDegree = 0`: `_of_g_natDegree_eq_zero`. The
  hypothesis `(g.coeff 0).eval t₀ ≠ 0` follows from `hg_def` applied to
  any chord root; such a root exists because `0 < f.natDegree` and
  `Splits` together force at least one root.
* `2 ≤ f.natDegree, 0 < g.natDegree`: the narrowed theorem backed by
  the residual product-form axiom.

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
  classical
  rcases Nat.lt_or_ge f.natDegree 2 with hf_lt | hf_two_le
  · -- `f.natDegree ∈ {0, 1}`: dispatch to the trivial-case or linear theorem.
    have h_or : f.natDegree = 0 ∨ f.natDegree = 1 := by omega
    rcases h_or with hf_zero | hf_one
    · exact resultant_logDeriv_at_split_specialization_of_natDegree_eq_zero
        f g t₀ hMonic hf_zero
    · exact resultant_logDeriv_at_split_specialization_of_f_natDegree_eq_one
        f g t₀ hMonic hf_one hg_def
  rcases Nat.eq_zero_or_pos g.natDegree with hg_zero | hg_pos
  · -- `g.natDegree = 0`: g is constant. The hypothesis
    -- `(g.coeff 0).eval t₀ ≠ 0` follows from `hg_def` applied to any
    -- chord root; such a root exists because `0 < f.natDegree` and
    -- `Splits` give `roots.card = f.natDegree > 0`.
    have hf_pos : 0 < f.natDegree := lt_of_lt_of_le (by decide) hf_two_le
    have hf_map_natDeg : (f.map (Polynomial.evalRingHom t₀)).natDegree
        = f.natDegree := hMonic.natDegree_map _
    have hroot_card_pos : 0 < (f.map (Polynomial.evalRingHom t₀)).roots.card := by
      rw [← Polynomial.Splits.natDegree_eq_card_roots hSplit, hf_map_natDeg]
      exact hf_pos
    obtain ⟨x, hx⟩ :=
      Multiset.card_pos_iff_exists_mem.mp hroot_card_pos
    have hg_eq : g = Polynomial.C (g.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hg_zero
    have hh_ne : (g.coeff 0).eval t₀ ≠ 0 := by
      have := hg_def x hx
      rw [hg_eq, Polynomial.map_C, Polynomial.eval_C] at this
      exact this
    exact resultant_logDeriv_at_split_specialization_of_g_natDegree_eq_zero
      f g t₀ hMonic hg_zero hSplit hh_ne hf_X_def
  · exact resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
      f g t₀ hMonic hf_two_le hg_pos hF_ne hSplit hg_def hf_X_def

end Polynomial
