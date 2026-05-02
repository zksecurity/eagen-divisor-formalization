/-
  Divisor/PartialFractionExpansion.lean

  Denominator-cleared partial-fraction expansion for a polynomial that
  splits over a commutative ring. For a polynomial of the form

      p = C c * ∏ α ∈ s, (X - C α) ^ m α

  (a typical "product-of-linears" decomposition obtained by
  `C_leadingCoeff_mul_prod_multiset_X_sub_C` + `prod_multiset_root_eq_finset_root`
  when the root count equals the degree), the derivative admits the
  explicit sum

      p.derivative = C c * ∑ α ∈ s,
        C (m α : R) * (X - C α) ^ (m α - 1) * ∏ β ∈ s.erase α, (X - C β) ^ m β.

  Multiplying both sides by the "missing" factor `(X - C α) ^ m α` at a
  chosen α₀ ∈ s shows up as the polynomial numerator of the partial-fraction
  term `m α₀ / (X - C α₀)` — this is the "denominator-cleared" partial-
  fraction identity that downstream Q3 steps consume when applied to
  `p = normPoly E D`.

  The module is deliberately generic: it knows nothing of the elliptic
  curve, `normPoly`, `betaConstructive`, or `polyG`. It only manipulates
  univariate polynomials.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Polynomial Finset

namespace Divisor

/-! ### Derivative of a product of powers over a `Finset`

This is the core combinatorial identity, stated over an arbitrary
commutative (semi)ring. It is the Finset version of Mathlib's
`Polynomial.derivative_prod` (multiset form), specialized to products
of powers of a family of polynomials. We only need the `f i = X - C (α i)`
case later, but the general statement is just as easy. -/

variable {R : Type*} [CommRing R]

section DerivativeProdPow

/-- Product rule for the Finset-indexed product `∏ i ∈ s, f i ^ m i`:
the derivative equals the sum over `i ∈ s` of
`m i · f i ^ (m i - 1) · (derivative (f i)) · ∏_{j ≠ i} f j ^ m j`. -/
theorem derivative_prod_pow [DecidableEq R]
    (s : Finset R) (f : R → R[X]) (m : R → ℕ) :
    derivative (∏ α ∈ s, (f α) ^ (m α)) =
      ∑ α ∈ s, (C ((m α : R)) * (f α) ^ (m α - 1) * derivative (f α) *
        ∏ β ∈ s.erase α, (f β) ^ (m β)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, derivative_mul, ih, derivative_pow,
        Finset.sum_insert ha]
    have h_erase_a : (insert a s).erase a = s := Finset.erase_insert ha
    rw [h_erase_a]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α hα => ?_)
    have ha_neq : a ≠ α := fun h => ha (h ▸ hα)
    have h_erase_α : (insert a s).erase α = insert a (s.erase α) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hxα, hxa | hxs⟩
        · exact Or.inl hxa
        · exact Or.inr ⟨hxα, hxs⟩
      · rintro (rfl | ⟨hxα, hxs⟩)
        · exact ⟨ha_neq, Or.inl rfl⟩
        · exact ⟨hxα, Or.inr hxs⟩
    have hnot : a ∉ s.erase α := fun h => ha (Finset.mem_of_mem_erase h)
    rw [h_erase_α, Finset.prod_insert hnot]
    ring

end DerivativeProdPow

/-! ### Specialization to `f α = X - C α`

For the rest of the file, we specialize to the linear factor case, which
is what downstream consumers need for `normPoly D`. -/

section LinearFactors

variable {K : Type*} [CommRing K]

/-- Core combinatorial identity: the derivative of the "split" product
`∏ α ∈ s, (X - C α) ^ m α` equals
`∑ α ∈ s, C (m α) * (X - C α) ^ (m α - 1) * ∏ β ∈ s.erase α, (X - C β) ^ m β`. -/
theorem derivative_prod_X_sub_C_pow [DecidableEq K]
    (s : Finset K) (m : K → ℕ) :
    derivative (∏ α ∈ s, (X - C α) ^ (m α)) =
      ∑ α ∈ s, (C ((m α : K)) * (X - C α) ^ (m α - 1) *
        ∏ β ∈ s.erase α, (X - C β) ^ (m β)) := by
  rw [derivative_prod_pow (R := K) s (fun α => X - C α) m]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [derivative_X_sub_C, mul_one]

/-- Variant where the leading coefficient `c : K` is factored out in
front: the derivative of `C c * ∏ α ∈ s, (X - C α) ^ m α` is
`C c * ∑ α ∈ s, C (m α) · (X - C α)^(m α - 1) · ∏_{β ≠ α} (X - C β)^(m β)`.

This is the denominator-cleared partial-fraction expansion: each summand
is the polynomial numerator of the `m α / (X - C α)` term in the rational
partial fraction `p' / p`. -/
theorem derivative_C_mul_prod_X_sub_C_pow [DecidableEq K]
    (c : K) (s : Finset K) (m : K → ℕ) :
    derivative (C c * ∏ α ∈ s, (X - C α) ^ (m α)) =
      C c * ∑ α ∈ s, (C ((m α : K)) * (X - C α) ^ (m α - 1) *
        ∏ β ∈ s.erase α, (X - C β) ^ (m β)) := by
  rw [derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_prod_X_sub_C_pow]

/-! ### Partial-fraction identity for a split polynomial

When `p` is known to split over `K` in the explicit form
`p = C p.leadingCoeff * ∏ α ∈ p.roots.toFinset, (X - C α) ^ (rootMultiplicity α p)`
(an equality of polynomials — this is what Mathlib's
`C_leadingCoeff_mul_prod_multiset_X_sub_C` combined with
`prod_multiset_root_eq_finset_root` gives when the root multiset has the
same cardinality as `natDegree p`), the derivative admits the sum
expansion below. -/

/-- **Denominator-cleared partial-fraction identity for a split polynomial.**

If a polynomial `p : K[X]` is equal to
`C p.leadingCoeff · ∏ α ∈ S, (X - C α) ^ (m α)` for some Finset `S` of
"roots" (normally `p.roots.toFinset`) and multiplicities `m`, then

  p.derivative = C p.leadingCoeff · ∑ α ∈ S,
    C (m α) · (X - C α) ^ (m α - 1) · ∏ β ∈ S.erase α, (X - C β) ^ (m β).

The RHS is a sum of polynomial terms; no denominators appear. Dividing
each summand by `∏ β ∈ S, (X - C β) ^ (m β)` recovers the rational
partial-fraction expression `p'/p = ∑ α m α / (X - C α)`. -/
theorem derivative_eq_sum_of_split_factorization [DecidableEq K]
    (p : K[X]) (S : Finset K) (m : K → ℕ)
    (hSplit : p = C p.leadingCoeff * ∏ α ∈ S, (X - C α) ^ (m α)) :
    derivative p = C p.leadingCoeff *
      ∑ α ∈ S, (C ((m α : K)) * (X - C α) ^ (m α - 1) *
        ∏ β ∈ S.erase α, (X - C β) ^ (m β)) := by
  -- Set the leading coefficient aside to avoid `rw` rewriting it on the RHS.
  set c := p.leadingCoeff
  -- hSplit now reads: p = C c * ∏ α ∈ S, (X - C α)^(m α)
  rw [hSplit]
  exact derivative_C_mul_prod_X_sub_C_pow c S m

/-! ### Denominator-cleared identity using `roots.toFinset`

The most common instance of the above, specialized to the root set of
`p` with `rootMultiplicity` as the multiplicity map. This is the
shape consumed when instantiating on `p = normPoly E D`. -/

/-- **PFE over `p.roots.toFinset`.** When `p` admits the "split" form
with roots from `p.roots.toFinset` and multiplicities `rootMultiplicity _ p`,
the derivative expands as a single sum over `p.roots.toFinset`. -/
theorem derivative_eq_sum_rootMultiplicity [DecidableEq K] [IsDomain K]
    (p : K[X])
    (hSplit : p = C p.leadingCoeff *
      ∏ α ∈ p.roots.toFinset, (X - C α) ^ (rootMultiplicity α p)) :
    derivative p = C p.leadingCoeff *
      ∑ α ∈ p.roots.toFinset,
        (C ((rootMultiplicity α p : K)) *
          (X - C α) ^ ((rootMultiplicity α p) - 1) *
          ∏ β ∈ p.roots.toFinset.erase α,
            (X - C β) ^ (rootMultiplicity β p)) :=
  derivative_eq_sum_of_split_factorization p p.roots.toFinset
    (fun α => rootMultiplicity α p) hSplit

/-! ### Construction of the "split" hypothesis from root count

The hypothesis `p = C p.leadingCoeff * ∏ α ∈ p.roots.toFinset, ...` is
not an axiom — it follows from Mathlib's
`C_leadingCoeff_mul_prod_multiset_X_sub_C` (which needs
`Multiset.card p.roots = p.natDegree`, i.e. "p has as many roots as
its degree") combined with `prod_multiset_root_eq_finset_root`
(which rewrites the multiset product as a Finset product of powers).

We package the needed step here for convenience. -/

/-- A polynomial whose roots (counted with multiplicity) account for its
entire degree admits the explicit split factorization. -/
theorem splits_factorization_of_roots_card_eq [DecidableEq K] [IsDomain K]
    (p : K[X])
    (hroots : Multiset.card p.roots = p.natDegree) :
    p = C p.leadingCoeff *
      ∏ α ∈ p.roots.toFinset, (X - C α) ^ (rootMultiplicity α p) := by
  have h1 : C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have h2 : (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p :=
    prod_multiset_root_eq_finset_root
  rw [h2] at h1
  exact h1.symm

/-- End-to-end PFE when `Multiset.card p.roots = p.natDegree`: no explicit
split hypothesis needed. -/
theorem derivative_eq_sum_rootMultiplicity_of_roots_card_eq
    [DecidableEq K] [IsDomain K] (p : K[X])
    (hroots : Multiset.card p.roots = p.natDegree) :
    derivative p = C p.leadingCoeff *
      ∑ α ∈ p.roots.toFinset,
        (C ((rootMultiplicity α p : K)) *
          (X - C α) ^ ((rootMultiplicity α p) - 1) *
          ∏ β ∈ p.roots.toFinset.erase α,
            (X - C β) ^ (rootMultiplicity β p)) :=
  derivative_eq_sum_rootMultiplicity p
    (splits_factorization_of_roots_card_eq p hroots)

/-! ### Denominator-cleared identity: multiplying by the full product

The useful shape is:

  p.derivative · (X - C α₀)
    = something involving (rootMult α₀ p) on the "singular" summand,
      plus smooth contributions from β ≠ α₀.

Concretely, at a distinguished root `α₀ ∈ S`, the RHS of the PFE
equals `(rootMult α₀) / (X - C α₀)` times the full product plus regular
terms. Multiplying through by `(X - C α₀)` isolates the `rootMult α₀`
coefficient plus terms that vanish to higher order at `X = α₀`.

We package the "partial fraction at α₀" form below. -/

/-- Pull out the `α = α₀` summand of the PFE, identifying it as the
singular term `C (m α₀) · (X - C α₀)^(m α₀ - 1) · ∏_{β ≠ α₀} (X - C β)^(m β)`
and leaving the remaining sum over `S.erase α₀`. -/
theorem derivative_C_mul_prod_X_sub_C_pow_isolate
    [DecidableEq K] (c : K) (S : Finset K) (m : K → ℕ)
    {α₀ : K} (hα₀ : α₀ ∈ S) :
    derivative (C c * ∏ α ∈ S, (X - C α) ^ (m α)) =
      C c * (C ((m α₀ : K)) * (X - C α₀) ^ (m α₀ - 1) *
        ∏ β ∈ S.erase α₀, (X - C β) ^ (m β))
      + C c * ∑ α ∈ S.erase α₀,
          (C ((m α : K)) * (X - C α) ^ (m α - 1) *
            ∏ β ∈ S.erase α, (X - C β) ^ (m β)) := by
  rw [derivative_C_mul_prod_X_sub_C_pow c S m, ← mul_add]
  congr 1
  exact (Finset.add_sum_erase S _ hα₀).symm

end LinearFactors

/-! ### Indexed version (product over an arbitrary Finset ι)

The downstream `normZ` uses indexing over `Finset (ZMod E.q × ZMod E.q)`
(a Finset of elliptic-curve points), not over the scalar field. The
derivative identity transfers with no essential changes. -/

section LinearFactorsIndexed

variable {K : Type*} [CommRing K] {ι : Type*}

/-- Indexed product rule: derivative of `∏ i ∈ s, (X - C (f i)) ^ (m i)`. -/
theorem derivative_prod_X_sub_C_pow_indexed [DecidableEq ι]
    (s : Finset ι) (f : ι → K) (m : ι → ℕ) :
    derivative (∏ i ∈ s, (X - C (f i)) ^ (m i)) =
      ∑ i ∈ s, (C ((m i : K)) * (X - C (f i)) ^ (m i - 1) *
        ∏ j ∈ s.erase i, (X - C (f j)) ^ (m j)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, derivative_mul, ih, derivative_pow,
        Finset.sum_insert ha]
    have h_erase_a : (insert a s).erase a = s := Finset.erase_insert ha
    rw [h_erase_a]
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have ha_neq : a ≠ i := fun h => ha (h ▸ hi)
    have h_erase_i : (insert a s).erase i = insert a (s.erase i) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hxi, hxa | hxs⟩
        · exact Or.inl hxa
        · exact Or.inr ⟨hxi, hxs⟩
      · rintro (rfl | ⟨hxi, hxs⟩)
        · exact ⟨ha_neq, Or.inl rfl⟩
        · exact ⟨hxi, Or.inr hxs⟩
    have hnot : a ∉ s.erase i := fun h => ha (Finset.mem_of_mem_erase h)
    rw [h_erase_i, Finset.prod_insert hnot]
    ring

/-- Indexed variant of `derivative_C_mul_prod_X_sub_C_pow`: the leading
    coefficient `c` is factored out in front. -/
theorem derivative_C_mul_prod_X_sub_C_pow_indexed [DecidableEq ι]
    (c : K) (s : Finset ι) (f : ι → K) (m : ι → ℕ) :
    derivative (C c * ∏ i ∈ s, (X - C (f i)) ^ (m i)) =
      C c * ∑ i ∈ s, (C ((m i : K)) * (X - C (f i)) ^ (m i - 1) *
        ∏ j ∈ s.erase i, (X - C (f j)) ^ (m j)) := by
  rw [derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_prod_X_sub_C_pow_indexed]

end LinearFactorsIndexed

/-! ### Root multiplicity of `C c · ∏ (X - C (f i)) ^ m i`

Generic helper: over a (commutative) integral domain `K` with decidable
equality, for a nonzero scalar `c` and any indexed product of linear
factors, the multiplicity of an arbitrary point `z : K` as a root is
the sum of `m i` over those `i ∈ s` with `f i = z`. No injectivity
assumption on `f` is needed; collisions are handled by the filter.

This is the dual of the splits-factorisation lemmas above: those go
*from* `rootMultiplicity` *to* a product of linear factors when `p`
has as many roots as its degree; this one goes *from* a known product
shape *to* `rootMultiplicity`.

Used downstream wherever a base-changed polynomial over `Fqbar E`
admits a factorisation `C c · ∏ Q ∈ gd.support, (X - C (zLambdaBar Q)) ^ gd.mult Q`
(for example via `chord_fiber_product_bar_factorisation` in
`Divisor/GeometricSoundness.lean`): the per-`z` root multiplicity is
read off as `∑_{Q : zLambdaBar Q = z} gd.mult Q` directly. -/

section RootMultiplicityProductOfLinears

variable {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}

/-- Root multiplicity formula for `C c · ∏ i ∈ s, (X - C (f i)) ^ (m i)`
over a commutative integral domain `K`. The scalar `c` must be nonzero;
no injectivity hypothesis is placed on `f`. -/
theorem rootMultiplicity_C_mul_prod_X_sub_C_pow [DecidableEq K]
    (s : Finset ι) (f : ι → K) (m : ι → ℕ)
    {c : K} (hc : c ≠ 0) (z : K) :
    rootMultiplicity z (C c * ∏ i ∈ s, (X - C (f i)) ^ (m i)) =
      ∑ i ∈ s.filter (fun i => f i = z), m i := by
  classical
  have hprod_ne : (∏ i ∈ s, (X - C (f i)) ^ (m i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero (f i))
  rw [← Polynomial.count_roots, Polynomial.roots_C_mul _ hc,
      Polynomial.roots_prod _ _ hprod_ne, Multiset.count_bind]
  simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C,
             Multiset.count_nsmul, Multiset.count_singleton]
  -- After `simp only`, LHS is `(s.val.map (fun i => m i * if z = f i then 1 else 0)).sum`
  -- which is definitionally `∑ i ∈ s, m i * if z = f i then 1 else 0`.
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : f i = z
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun H => h H.symm), mul_zero]

/-- **Multiplicity squeeze lemma**: a nonzero polynomial `p ∈ K[X]` over a
commutative integral domain whose roots are exactly the image of a finite
indexing set under `φ` has its `rootMultiplicity` at every `z` agreeing
with the per-fibre exponent sum, given just two extra hypotheses:

* fibrewise divisibility by `(X - C z)` to the per-fibre power
  (lower bound),
* a global degree bound `natDegree p ≤ ∑ i, m i` (upper bound).

The conclusion captures the typical "norm/divisor pushforward" packaging
used in algebraic-geometry arguments: knowing where a polynomial vanishes,
its order at each point, and a global degree count is enough to pin
multiplicities exactly without further machinery (no splitting field or
local-ring analysis).

The conclusion is stated for *every* `z : K`, not just `z ∈ s.image φ`:
off-image, both sides are `0` (no fibre, and `z ∉ p.roots`). -/
theorem rootMultiplicity_eq_of_fiberwise_dvd_natDegree_le
    [DecidableEq K] [DecidableEq ι]
    (p : K[X]) (s : Finset ι) (φ : ι → K) (m : ι → ℕ)
    (hp : p ≠ 0)
    (hroots : p.roots.toFinset = s.image φ)
    (hdvd : ∀ z ∈ s.image φ,
      (X - C z) ^ (∑ i ∈ s.filter (fun i => φ i = z), m i) ∣ p)
    (hdeg : p.natDegree ≤ ∑ i ∈ s, m i) :
    ∀ z : K,
      p.rootMultiplicity z =
        ∑ i ∈ s.filter (fun i => φ i = z), m i := by
  classical
  -- Re-indexing identity for the fibrewise sum.
  have hMaps : ∀ i ∈ s, φ i ∈ s.image φ :=
    fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hReindex :
      ∑ z ∈ s.image φ, ∑ i ∈ s.filter (fun i => φ i = z), m i
        = ∑ i ∈ s, m i :=
    Finset.sum_fiberwise_of_maps_to hMaps m
  -- Lower bound: fibrewise divisibility ⇒ rootMultiplicity ≥ fibre sum.
  have hLower : ∀ z ∈ s.image φ,
      ∑ i ∈ s.filter (fun i => φ i = z), m i ≤ p.rootMultiplicity z := by
    intro z hz
    rw [le_rootMultiplicity_iff hp]
    exact hdvd z hz
  -- Sum of multiplicities over the root set equals roots.card ≤ natDegree.
  have hSumMult :
      ∑ z ∈ s.image φ, p.rootMultiplicity z ≤ p.natDegree := by
    have hcount : ∀ z ∈ s.image φ, p.rootMultiplicity z = p.roots.count z := by
      intro z _; exact (Polynomial.count_roots p).symm
    rw [Finset.sum_congr rfl hcount, ← hroots]
    -- ∑ z ∈ p.roots.toFinset, p.roots.count z = p.roots.card
    rw [Multiset.toFinset_sum_count_eq]
    exact p.card_roots'
  -- Combined squeeze: ∑ fibre ≤ ∑ multi ≤ natDegree ≤ ∑ i m i = ∑ fibre.
  have hSumEq :
      ∑ z ∈ s.image φ, p.rootMultiplicity z =
        ∑ z ∈ s.image φ, ∑ i ∈ s.filter (fun i => φ i = z), m i := by
    refine le_antisymm ?_ (Finset.sum_le_sum hLower)
    calc ∑ z ∈ s.image φ, p.rootMultiplicity z
        ≤ p.natDegree := hSumMult
      _ ≤ ∑ i ∈ s, m i := hdeg
      _ = ∑ z ∈ s.image φ, ∑ i ∈ s.filter (fun i => φ i = z), m i :=
            hReindex.symm
  -- Per-z equality follows by contradiction: a strict gap at z would
  -- imply ∑ multi > ∑ fibre, contradicting hSumEq.
  have hPerZ : ∀ z ∈ s.image φ,
      p.rootMultiplicity z = ∑ i ∈ s.filter (fun i => φ i = z), m i := by
    intro z hz
    refine le_antisymm ?_ (hLower z hz)
    by_contra hLt
    push_neg at hLt
    have hStrictAtZ :
        ∑ i ∈ s.filter (fun i => φ i = z), m i < p.rootMultiplicity z :=
      hLt
    have hSumLt :
        ∑ z' ∈ s.image φ, ∑ i ∈ s.filter (fun i => φ i = z'), m i
          < ∑ z' ∈ s.image φ, p.rootMultiplicity z' :=
      Finset.sum_lt_sum hLower ⟨z, hz, hStrictAtZ⟩
    exact absurd hSumEq.symm hSumLt.ne
  -- Off-image: rootMultiplicity z = 0 = empty sum.
  intro z
  by_cases hz : z ∈ s.image φ
  · exact hPerZ z hz
  · -- Off-image: filter is empty (no i ∈ s maps to z).
    have hFilterEmpty : s.filter (fun i => φ i = z) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hi heq
      exact hz (Finset.mem_image.mpr ⟨i, hi, heq⟩)
    rw [hFilterEmpty, Finset.sum_empty]
    -- z ∉ p.roots, so rootMultiplicity z = 0.
    have hNotRoot : ¬ p.IsRoot z := by
      intro h
      apply hz
      rw [← hroots]
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots' (p := p)).mpr ⟨hp, h⟩)
    exact rootMultiplicity_eq_zero hNotRoot

end RootMultiplicityProductOfLinears

end Divisor
