# divisors

Lean 4 mechanization of an elliptic-curve-based dlog knowledge-sound IP.

## Build

```
lake build
```

Requires elan + Lean 4 toolchain (see `lean-toolchain`).

## Theorem surface

The headline theorems live in `Divisor/ExtractorBridgeTheorems.lean` and `Divisor/Soundness.lean`:

- `Divisor.ma_extractable` — knowledge soundness of the MA protocol.
- `Divisor.ip_knowledge_sound` — knowledge soundness of the IP protocol.
- `Divisor.ma_completeness` — completeness of the MA protocol.

### `Divisor.ma_extractable` (MA knowledge soundness)

Fix a statement `stmt` over the finite field `F_q`: bases `B_1, ..., B_k` in `E(F_q)`, a target `T` in `E(F_q)`, and a degree bound `d`. Fix a prover first-round message `msg` encoding a divisor representative `D = a(x) - b(x) y` in `F_q[E]` together with scalars `m_1, ..., m_k`, such that the `E`-degree of `D` is at most `d`.

**Hypotheses** (`Divisor/ExtractorBridgeTheorems.lean`):

- smoothness of `E`: `4 a_E^3 + 27 b_E^2 ≠ 0`
- denominator non-vanishing on `A_0` outside `zerosFinset(D)` and avoiding `distinctR`
- size condition on the number of points of `E`:

$$|E(F_q)| > 2\bigl(5(\deg_E D + k + 2) + 3\bigr) + 21(\deg_E D + k + 2) + 72.$$

**Conclusion.** One of the two branches holds.

1. *Witness branch.* There exists a witness `w` such that `maExtractor(stmt, msg) = some w` and

$$T = \sum_{i=1}^{k} [n_i]\, B_i \qquad \text{in } E(F_q),$$

where `n_i = w.scalars(i)` in `Z` with `|n_i| < d`.

2. *Small-accept-set branch.* The set of challenges `(A_0, A_1)` in `validPairs` on which the verifier accepts has cardinality at most `B(d, k, q)`, where

$$B(d, k, q) = 18(d+k)q + (3d+9k+71)|E(F_q)|.$$

The active soundness path uses the geometric-zero skeleton in
`Divisor/GeometricSoundness.lean`: zeros of `D` are represented over
`F_qbar`, the cleared numerator is required to descend to `F_q`, and
the headline theorem no longer assumes `splitsOnE E D`. The shared
base-change model is factored into `Divisor/GeomBase.lean`; the true
local-order/fiber-accounting obligation is isolated in
`Divisor/GeomLocalOrder.lean`.

### `Divisor.ip_knowledge_sound` (IP knowledge soundness)

The same disjunction as `ma_extractable`, conjoined with *uniqueness of the third-round response*: for every challenge and intercept `A_2` with `D` non-vanishing at `A_0, A_1, A_2` and the chord line `L(A_0, A_1)` non-vanishing at `-T`, any two third-round messages `msg3, msg3'` both accepted by the IP verifier must be equal.

### `Divisor.ma_completeness`

For an honest prover message `msg` witnessing `(stmt, wit)` with `degE(D) ≤ d` and `(a, b) ∈ admSet`, the rejecting-challenge set is bounded:

$$\bigl| \{ (A_0, A_1) \in E \times E : V \text{ rejects} \} \bigr| \le  (3N + 1) \cdot |E_{\mathrm{aff}}|,$$

where `N = numZeros(D)` and `E_aff` is the set of affine `F_q`-points of `E`. Proof uses Weil reciprocity plus Lemma 2 (`support_disjointness`).

## Axiom Surface

The pinned theorem closures are checked by `#print axioms` in
`Tests/AxiomClosurePin.lean`.

`Divisor.ma_extractable` and `Divisor.ip_knowledge_sound` depend on the
following project axioms, in addition to Lean/mathlib infrastructure
(`propext`, `Classical.choice`, `Quot.sound`):

```text
Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd
Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
Divisor.hasse_weil
Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero
```

`Divisor.ma_completeness` depends on:

```text
Divisor.chord_fiber_product_eq_normZ_under_split
Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g
```

`Divisor.ma_completeness_clean` additionally uses:

```text
Divisor.hasse_weil
```

### Lean Axiom Inventory

These are the project-level `axiom` declarations. Some are headline
dependencies; others are lower-level textbook targets or compatibility
surfaces.

1. `Divisor.hasse_weil`

   Lean:
   ```lean
   axiom hasse_weil (E : ECSetup) :
     ((E.numPoints : ℤ) - E.q - 1)^2 ≤ 4 * E.q
   ```

   Source statement: Silverman, *The Arithmetic of Elliptic Curves*,
   Theorem V.1.1 states the Hasse bound
   `|#E(F_q) - q - 1| ≤ 2√q`.

   Lean specialization: the equivalent integer-squared form
   `(#E(F_q) - q - 1)^2 ≤ 4q`.

   Citation: `axioms/hasse_weil.md`,
   `axioms/snippets/silverman-thm-V.1.1-hasse-155.png`, and
   `Divisor/Axioms/AxiomHasseWeil.lean`.

2. `Divisor.principal_divisor_iff`

   Lean:
   ```lean
   axiom principal_divisor_iff
       (E : ECSetup) (coeffs : ECPoint E → ℤ)
       (hFinSupp : Set.Finite (Function.support coeffs)) :
       IsPrincipal E coeffs ↔
         (∑ P ∈ hFinSupp.toFinset, coeffs P = 0) ∧
         (ECPoint.weightedSum E hFinSupp.toFinset
             (fun P => ECPoint.zsmul E (coeffs P) P) = 0)
   ```

   Source statement: Silverman, *The Arithmetic of Elliptic Curves*,
   Corollary III.3.5 states that a divisor `D = Σ_P n_P(P)` on an
   elliptic curve is principal iff `Σ_P n_P = 0` and
   `Σ_P [n_P]P = O_E`.

   Lean specialization: the coefficient function
   `coeffs : ECPoint E → ℤ` is principal exactly when its finite support
   has integer sum zero and group-law weighted sum zero.

   Citation: `axioms/principal_divisor_iff.md`,
   `axioms/snippets/silverman-cor-III.3.5-principal-divisor-081.png`, and
   `Divisor/Axioms/AxiomPrincipalDivisorIff.lean`.

3. `Divisor.CoordRingElt.divisorClass_eq_zero_of_b_ne_zero`

   Lean:
   ```lean
   axiom CoordRingElt.divisorClass_eq_zero_of_b_ne_zero
       (E : ECSetup) (D : CoordRingElt E.q)
       (_hD : ¬ (D.a = 0 ∧ D.b = 0))
       (_hSplit : splitsOnE E D) (_hbNZ : D.b ≠ 0) :
       divisorClass E (divisorOfD E D)
         (divisorOfD_finiteSupport E D) = 0
   ```

   Source statement: Silverman II.3 defines the divisor of a rational
   function by local orders, Stichtenoth Def. 1.4.2 names such divisors
   principal, and Silverman Corollary III.3.5 characterizes principal
   divisors on elliptic curves by degree and group-law sum.

   Lean specialization: for nonzero `D = a(x) - b(x)y` with `b ≠ 0`,
   if `splitsOnE E D` exposes the relevant divisor mass over `F_q`, then
   the class of `divisorOfD E D` is zero.

   Citation: `axioms/divisorClass_isPrincipal.md`,
   `axioms/snippets/silverman-II.3-divisors-027.png`,
   `axioms/snippets/stichtenoth-def-1.4.2-principal-divisor-016.png`,
   `axioms/snippets/silverman-cor-III.3.5-principal-divisor-081.png`, and
   `Divisor/OrdP/LocalRing.lean`.

4. `Divisor.chord_fiber_product_concrete_bar_zfiber_pow_dvd`

   Lean:
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

   Source statement: Stacks Project tag 02RS gives the norm pushforward
   identity `p_* div(f) = div(Nm(f))`. Stichtenoth Prop. 3.1.9 supplies
   the supporting principal-divisor conorm statement.

   Lean specialization: for the chord projection `π_λ`, the
   base-changed chord-fiber resultant has at least the pushed-forward
   zero-divisor multiplicity at each `z`:
   `(X - z)^{Σ_{Q: π_λ(Q)=z} mult_Q(D)}` divides `N_{π_λ}(D)(X)`.

   Citation: `axioms/chord_fiber_product_concrete_bar_zfiber_pow_dvd.md`,
   `axioms/papers/stacks-02RS.html`,
   `axioms/snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png`,
   and `Divisor/Axioms/AxiomChordFiberDivisibility.lean`.

5. `Divisor.chord_fiber_product_eq_normZ_under_split`

   Lean:
   ```lean
   axiom chord_fiber_product_eq_normZ_under_split
       (E : ECSetup) (D : CoordRingElt E.q) (lam : ZMod E.q)
       (hD : ¬ (D.a = 0 ∧ D.b = 0))
       (hSplitOnE : splitsOnE E D)
       (β_fun : ZMod E.q × ZMod E.q → ℕ)
       (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
       (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
       (hAccount : (∑ P ∈ E.points, β_fun P) =
                     (normPoly E D).natDegree)
       (hβtrue : ∀ P, β_fun P = betaTrue E D hD P) :
       ∃ c : ZMod E.q, c ≠ 0 ∧
         chord_fiber_product E lam D = C c * normZ E lam D β_fun
   ```

   Source statement: Stacks Project tag 02RS gives
   `p_* div(f) = div(Nm(f))`; Stichtenoth Thm. 3.1.11 gives the finite
   extension place-accounting equality `Σ_i e_i f_i = [F' : F]`.

   Lean specialization: under `splitsOnE` and pointwise true
   multiplicity accounting, the chord-fiber product is a nonzero scalar
   multiple of `normZ E lam D β_fun`.

   Citation: `axioms/chord_fiber_product_eq_normZ_under_split.md`,
   `axioms/papers/stacks-02RS.html`,
   `axioms/snippets/stichtenoth-prop-3.1.9-conorm-principal-084.png`,
   `axioms/snippets/stichtenoth-thm-3.1.11-fundamental-equality-074.png`,
   and `Divisor/Axioms/AxiomChordFiberProductEqNormZUnderSplit.lean`.

6. `Polynomial.resultant_logDeriv_at_split_specialization_of_two_le_natDegree_pos_g`

   Lean:
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

   Source statement: Lang IV.8 identifies resultants as products over
   roots, Lang VI.5 gives norm and trace as products and sums over
   embeddings, and Lang VIII.5 gives the separable algebraic
   derivative formula `ξ' = -f^D(ξ)/f'(ξ)`.

   Lean specialization: for `F(T) = Res_X(f(X,T), g(X,T))` with `f`
   monic, `deg_X f ≥ 2`, `deg_X g > 0`, and `f(X,t₀)` split with simple
   roots where `g` is nonzero,
   `F'(t₀)/F(t₀) = Σ_{x : f(x,t₀)=0}
   (g_T f_X - g_X f_T)/(f_X g)(x,t₀)`.

   Citation: `axioms/resultant_logDeriv_at_split.md`,
   `axioms/snippets/lang-IV.8-prop-8.1-8.3-resultant-202.png`,
   `axioms/snippets/lang-VI.5-thm-5.1-norm-trace-300.png`,
   `axioms/snippets/lang-VIII.5-thm-5.1-derivations-385.png`, and
   `Divisor/Axioms/AxiomResultantLogDerivAtSplit.lean`.

7. `Differential.logDeriv_algebraNorm_eq_algebraTrace_logDeriv`

   Lean:
   ```lean
   axiom logDeriv_algebraNorm_eq_algebraTrace_logDeriv
       {F K : Type*} [Field F] [Field K]
       [Differential F] [Differential K]
       [Algebra F K] [DifferentialAlgebra F K]
       [FiniteDimensional F K] [Algebra.IsSeparable F K]
       (α : K) (hα : α ≠ 0) :
     Differential.logDeriv (Algebra.norm F α)
       = Algebra.trace F K (Differential.logDeriv α)
   ```

   Source statement: Lang VI.5 gives
   `N^E_k(α) = ∏_σ σ(α)` and `Tr^E_k(α) = Σ_σ σ(α)` for a separable
   extension, while Lang VIII.5 gives the compatible extension of
   derivations to separable algebraic extensions.

   Lean specialization: for a finite separable differential field
   extension `K/F` and `α ∈ K^×`,
   `d(N_{K/F} α)/(N_{K/F} α) = Tr_{K/F}(dα/α)`.

   Citation: `axioms/trace_logDeriv.md`,
   `axioms/snippets/lang-VI.5-thm-5.1-norm-trace-300.png`,
   `axioms/snippets/lang-VIII.5-thm-5.1-derivations-385.png`, and
   `Divisor/Axioms/AxiomTraceLogDeriv.lean`.

8. `Divisor.weil_reciprocity_textbook`

   Lean:
   ```lean
   axiom weil_reciprocity_textbook
       (E : ECSetup) (f g : CoordRingElt E.q)
       (hf : ¬ (f.a = 0 ∧ f.b = 0))
       (hg : ¬ (g.a = 0 ∧ g.b = 0))
       (hDisjointSupport :
         ∀ P ∈ E.points,
           (f.eval P.1 P.2 = 0 → g.eval P.1 P.2 ≠ 0) ∧
           (g.eval P.1 P.2 = 0 → f.eval P.1 P.2 ≠ 0)) :
       ∏ P ∈ E.points.filter (fun P => g.eval P.1 P.2 = 0),
         f.eval P.1 P.2
       =
       ∏ P ∈ E.points.filter (fun P => f.eval P.1 P.2 = 0),
         g.eval P.1 P.2
   ```

   Source statement: Silverman Exercise II.2.11 states Weil reciprocity
   as `f(div g) = g(div f)` for rational functions with disjoint divisor
   support. Stichtenoth Corollary 4.3.3 gives the residue theorem behind
   the logarithmic-differential proof.

   Lean specialization: for nonzero coordinate-ring representatives
   `f,g` with disjoint zero supports on `E.points`, the two finite
   products over the corresponding zero sets are equal.

   Citation: `axioms/weil_reciprocity_honest.md`,
   `axioms/snippets/silverman-ex-II.2.11-weil-reciprocity-057.png`,
   `axioms/snippets/stichtenoth-cor-4.3.3-residue-theorem-182.png`, and
   `Divisor/Axioms/AxiomWeilReciprocity.lean`.

Related theorem-backed declarations: `CoordRingElt.exists_divisor_multiplicity`
is proved from `ordAt`/`divisorClass_eq_zero_of_b_ne_zero`, and
`bivariate_poly_zeros_on_ExE_le` is a theorem whose project-axiom dependency is
`Divisor.hasse_weil`.
