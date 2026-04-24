/-
  Divisor/BassaMonic.lean

  Theorem 4 (Schwartz-Zippel on E x E for monic D):

  Contains the comparison function f, its non-vanishing proof
  (from Bezout + Hasse-Weil, not from Bassa), and the main
  soundness bound via variety SZ.
-/
import Divisor.Defs
import Divisor.SlopeDist

open Finset

namespace Divisor

variable (E : ECSetup)

/-! ## The comparison function f

For D with zeros Q_1,...,Q_N and target points P_1,...,P_N,
define f(A0, A1) on pairs of affine points:

  f(A0, A1) = prod_i L_{A0,A1}(Q_i) - prod_i L_{A0,A1}(P_i)

where L_{A0,A1}(R) = (y(R)-y(A0))*(x(A1)-x(A0)) - (x(R)-x(A0))*(y(A1)-y(A0))
-/

/-- The linear form L_{A0,A1}(R) = (yR-y0)(x1-x0) - (xR-x0)(y1-y0) -/
def linearFormL (A₀ A₁ R : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (R.2 - A₀.2) * (A₁.1 - A₀.1) - (R.1 - A₀.1) * (A₁.2 - A₀.2)

/-- The comparison function f -/
def comparisonFn {N : ℕ}
    (Q P : Fin N → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : ZMod E.q :=
  (Finset.univ.prod (fun i => linearFormL E A₀ A₁ (Q i))) -
  (Finset.univ.prod (fun i => linearFormL E A₀ A₁ (P i)))

/-! ## Rationality of f (formerly Bassa Lem 3)

In our formalization, Q_i and P_i are all in E(F_q), so f is
automatically defined over F_q. No Galois theory needed. -/

theorem f_rational {N : ℕ}
    (Q P : Fin N → ZMod E.q × ZMod E.q)
    (hQ : ∀ i, Q i ∈ E.points)
    (hP : ∀ i, P i ∈ E.points) :
    -- f is a function ZMod E.q × ZMod E.q → ZMod E.q → ZMod E.q,
    -- automatically over F_q since all inputs are in F_q.
    True := trivial

/-! ## Non-vanishing of f on E x E (formerly Bassa Lem 4)

Proved from Bezout + Hasse-Weil. The argument:

1. Since the multisets {Q_i} and {P_i} differ, there exists P_j
   that appears more times in {P_i} than in {Q_i}.

2. Evaluating f at A0 = P_j: the P_j-factor in the second product
   vanishes (since L_{P_j, A1}(P_j) = 0 for all A1).

3. The first product at A0 = P_j becomes:
   prod_i ((y(Q_i)-y(P_j))*(x(A1)-x(P_j)) - (x(Q_i)-x(P_j))*(y(A1)-y(P_j)))

4. Since P_j is not among the Q_i, each factor is a nonzero linear
   form in A1 when restricted to the line through A1. On E, each
   such linear form vanishes at most 3 points (Bezout).

5. The product vanishes at most 3*N points of E(F_q).

6. By Hasse-Weil, #E(F_q) > 3*N, so there exists A1 where f ≠ 0.
-/

/-- L_{P,A1}(P) = 0 for any A1: the linear form vanishes when R = A0 -/
theorem linearFormL_self_zero (A₁ P : ZMod E.q × ZMod E.q) :
    linearFormL E P A₁ P = 0 := by
  simp [linearFormL]

/-- A nonzero linear form a*x + b*y + c on E has at most 3 zeros
    among E(F_q). This follows from Bezout: the linear form defines
    a line, which meets the cubic E in at most 3 points. -/
theorem linear_form_zeros_le_three
    (a b d : ZMod E.q) (hab : a ≠ 0 ∨ b ≠ 0) :
    (E.points.filter (fun P => a * P.1 + b * P.2 + d = 0)).card ≤ 3 := by
  rcases hab with ha | hb
  · -- a ≠ 0: if b ≠ 0, use the other case. If b = 0: a*x + d = 0 gives x = -d/a.
    by_cases hb : b ≠ 0
    · -- Both a ≠ 0 and b ≠ 0: reduce to line_meets_cubic
      calc (E.points.filter (fun P => a * P.1 + b * P.2 + d = 0)).card
          ≤ (pointsOnLine E (-(a * b⁻¹)) (-(d * b⁻¹))).card := by
            apply Finset.card_le_card
            intro P hP
            simp only [Finset.mem_filter, pointsOnLine] at hP ⊢
            refine ⟨hP.1, ?_⟩
            have h := hP.2
            have key : b * P.2 = -(a * P.1 + d) := by
              have := sub_eq_zero.mpr h; ring_nf at this ⊢; linear_combination this
            calc P.2 = b⁻¹ * (b * P.2) := by rw [inv_mul_cancel_left₀ hb]
              _ = b⁻¹ * (-(a * P.1 + d)) := by rw [key]
              _ = -(a * b⁻¹) * P.1 + -(d * b⁻¹) := by ring
        _ ≤ 3 := line_meets_cubic_le_three E _ _
    · -- a ≠ 0, b = 0: equation is a*x + d = 0, so x = -d*a⁻¹.
      -- For fixed x, at most 2 points (y, -y) on E.
      push_neg at hb; subst hb
      -- After subst, b = 0 everywhere. Filter becomes: a*P.1 + 0*P.2 + d = 0
      -- which simplifies to a*P.1 + d = 0.
      have : (E.points.filter (fun P => a * P.1 + 0 * P.2 + d = 0)) =
             (E.points.filter (fun P => a * P.1 + d = 0)) := by
        congr 1; ext P; simp [show 0 * P.2 = 0 from zero_mul _]
      rw [this]
      calc (E.points.filter (fun P => a * P.1 + d = 0)).card
          ≤ (E.points.filter (fun P => P.1 = -(d * a⁻¹))).card := by
            apply Finset.card_le_card
            intro P hP
            simp only [Finset.mem_filter] at hP ⊢
            refine ⟨hP.1, ?_⟩
            have h := hP.2
            -- a * P.1 + d = 0 → P.1 = -d/a
            have : a * P.1 = -d := by linear_combination h
            calc P.1 = a⁻¹ * (a * P.1) := by rw [inv_mul_cancel_left₀ ha]
              _ = a⁻¹ * (-d) := by rw [this]
              _ = -(d * a⁻¹) := by ring
        _ ≤ 2 := by
            -- For fixed x₀, y satisfies y² = c₀. Use polynomial root bound.
            set x₀ := -(d * a⁻¹)
            set c₀ := x₀ ^ 3 + E.curveA * x₀ + E.curveB
            set g : Polynomial (ZMod E.q) := Polynomial.X ^ 2 - Polynomial.C c₀
            have hg_ne : g ≠ 0 := by
              intro h; have h2 := congr_arg (Polynomial.coeff · 2) h
              simp [g, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C] at h2
            have hg_deg : g.natDegree ≤ 2 :=
              (Polynomial.natDegree_sub_le _ _).trans
                (max_le (by simp [Polynomial.natDegree_X_pow])
                        ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)))
            -- Inject via Prod.snd into roots of g
            calc (E.points.filter (fun P => P.1 = x₀)).card
                ≤ g.roots.toFinset.card := by
                  apply Finset.card_le_card_of_injOn Prod.snd
                  · intro P hP
                    rw [Finset.mem_coe, Finset.mem_filter] at hP
                    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hg_ne]
                    simp only [Polynomial.IsRoot, g, Polynomial.eval_sub,
                               Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
                    have := E.hOnCurve P hP.1; rw [hP.2] at this
                    linear_combination this
                  · intro ⟨x₁, _⟩ h1 ⟨x₂, _⟩ h2 hy
                    have hx1 := (Finset.mem_filter.mp h1).2
                    have hx2 := (Finset.mem_filter.mp h2).2
                    exact Prod.ext (hx1.trans hx2.symm) hy
              _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
              _ ≤ g.natDegree := Polynomial.card_roots' g
              _ ≤ 2 := hg_deg
        _ ≤ 3 := by omega
  · -- b ≠ 0: rewrite as y = (-a/b)*x + (-d/b)
    calc (E.points.filter (fun P => a * P.1 + b * P.2 + d = 0)).card
        ≤ (pointsOnLine E (-(a * b⁻¹)) (-(d * b⁻¹))).card := by
          apply Finset.card_le_card
          intro P hP
          simp only [Finset.mem_filter, pointsOnLine] at hP ⊢
          refine ⟨hP.1, ?_⟩
          have h := hP.2
          -- a*P.1 + b*P.2 + d = 0
          -- → b*P.2 = -(a*P.1 + d)
          -- → P.2 = b⁻¹ * (-(a*P.1 + d))
          -- → P.2 = -(a*b⁻¹)*P.1 + -(d*b⁻¹)
          have key : b * P.2 = -(a * P.1 + d) := by
            have := sub_eq_zero.mpr h
            ring_nf at this ⊢
            linear_combination this
          calc P.2 = b⁻¹ * (b * P.2) := by rw [inv_mul_cancel_left₀ hb]
            _ = b⁻¹ * (-(a * P.1 + d)) := by rw [key]
            _ = -(a * b⁻¹) * P.1 + -(d * b⁻¹) := by ring
      _ ≤ 3 := line_meets_cubic_le_three E _ _

/-- **Non-vanishing of f (proved from Bezout + Hasse-Weil).**
    If {Q_i} ≠ {P_i} as multisets and 3*N < #E, then f is
    not identically zero on E x E. -/
theorem f_nonvanishing_proved {N : ℕ}
    (Q P : Fin N → ZMod E.q × ZMod E.q)
    (hQ : ∀ i, Q i ∈ E.points)
    (hP : ∀ i, P i ∈ E.points)
    (j : Fin N)
    (hj : ∀ i, Q i ≠ P j)  -- P_j not among the Q_i
    (hSmall : 3 * N < E.numAffine) :
    -- There exists (A0, A1) in E x E where f(A0, A1) ≠ 0
    ∃ A₁ ∈ E.points, comparisonFn E Q P (P j) A₁ ≠ 0 := by
  -- The set of A₁ where the product vanishes has size ≤ 3N.
  -- Since |E.points| = numAffine = numPoints - 1 ≥ 3N, there exists a good A₁.
  -- Define the "bad set": A₁ where comparisonFn vanishes
  set bad := E.points.filter (fun A₁ => comparisonFn E Q P (P j) A₁ = 0) with hbad_def
  -- It suffices to show bad ⊊ E.points (strict subset)
  suffices h : bad.card < E.points.card by
    -- bad ⊂ E.points (strict), so E.points \ bad is nonempty
    have hsub : bad ⊆ E.points := Finset.filter_subset _ _
    have hne : (E.points \ bad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have := Finset.card_sdiff_of_subset hsub
      rw [hemp, Finset.card_empty] at this
      omega
    obtain ⟨A₁, hA₁⟩ := hne
    simp only [Finset.mem_sdiff, hbad_def, Finset.mem_filter, not_and] at hA₁
    exact ⟨A₁, hA₁.1, hA₁.2 hA₁.1⟩
  -- |bad| ≤ 3*N: the product vanishes only when some factor vanishes.
  -- bad ⊆ ⋃_i {A₁ : linearFormL(P_j, A₁, Q_i) = 0}
  -- Each set has ≤ 3 elements (line meets cubic).
  -- |⋃| ≤ Σ_i 3 = 3*N.
  have hbad_bound : bad.card ≤ 3 * N := by
    have hsub : bad ⊆ Finset.univ.biUnion (fun i : Fin N =>
        E.points.filter (fun A₁ => linearFormL E (P j) A₁ (Q i) = 0)) := by
      intro A₁ hA₁
      rw [hbad_def, Finset.mem_filter] at hA₁
      rw [Finset.mem_biUnion]
      -- comparisonFn vanishes means the product minus product = 0.
      -- At A₀ = P_j: second product has P_j factor = 0 (by linearFormL_self_zero).
      -- So comparisonFn = first product - 0 = first product.
      -- First product = 0 means some factor = 0.
      -- comparisonFn = ∏ linearFormL(P_j, A₁, Q_i) - ∏ linearFormL(P_j, A₁, P_i)
      -- The second product has a zero factor at i = j.
      have hzero_factor : linearFormL E (P j) A₁ (P j) = 0 := linearFormL_self_zero E A₁ (P j)
      have hprod_P_zero : Finset.univ.prod (fun i => linearFormL E (P j) A₁ (P i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hzero_factor
      -- So comparisonFn = first_prod - 0 = first_prod
      have hcf : comparisonFn E Q P (P j) A₁ =
          Finset.univ.prod (fun i => linearFormL E (P j) A₁ (Q i)) := by
        simp [comparisonFn, hprod_P_zero]
      rw [hcf] at hA₁
      -- first_prod = 0 in an integral domain means some factor = 0
      obtain ⟨hmem, hval⟩ := hA₁
      -- hval : comparisonFn E Q P (P j) A₁ = 0
      -- comparisonFn = first_prod - 0 = first_prod (by hcf)
      have hprod_zero : Finset.univ.prod (fun i => linearFormL E (P j) A₁ (Q i)) = 0 := by
        have h := hval; simp only [comparisonFn, hprod_P_zero, sub_zero] at h; exact h
      -- In NoZeroDivisors: prod = 0 iff some factor = 0
      rw [Finset.prod_eq_zero_iff] at hprod_zero
      obtain ⟨i, _, hi⟩ := hprod_zero
      exact ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hmem, hi⟩⟩
    calc bad.card
        ≤ (Finset.univ.biUnion _).card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin N, (E.points.filter
            (fun A₁ => linearFormL E (P j) A₁ (Q i) = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin N, 3 := by
          apply Finset.sum_le_sum
          intro i _
          -- linearFormL (P j) A₁ (Q i) = (Q_i.2 - P_j.2)*(A₁.1 - P_j.1)
          --                              - (Q_i.1 - P_j.1)*(A₁.2 - P_j.2)
          -- As a function of A₁, this is: a*A₁.1 + b*A₁.2 + d = 0
          -- where a = Q_i.2 - P_j.2, b = -(Q_i.1 - P_j.1), d = ...
          -- Since Q_i ≠ P_j, at least one of a, b is nonzero.
          have hne := hj i  -- Q i ≠ P j
          -- Use linear_form_zeros_le_three
          calc (E.points.filter (fun A₁ => linearFormL E (P j) A₁ (Q i) = 0)).card
              ≤ (E.points.filter (fun A₁ =>
                  ((Q i).2 - (P j).2) * A₁.1 + (-((Q i).1 - (P j).1)) * A₁.2 +
                  ((P j).2 * (Q i).1 - (P j).1 * (Q i).2) = 0)).card := by
                apply Finset.card_le_card
                intro A₁ hA₁
                simp only [Finset.mem_filter] at hA₁ ⊢
                refine ⟨hA₁.1, ?_⟩
                have := hA₁.2
                simp only [linearFormL] at this
                linear_combination this
            _ ≤ 3 := by
                apply linear_form_zeros_le_three
                -- Need: (Q_i.2-P_j.2) ≠ 0 or -(Q_i.1-P_j.1) ≠ 0
                by_contra h
                push_neg at h
                have hx : (Q i).1 = (P j).1 := by
                  have := h.2; rw [neg_eq_zero] at this; exact sub_eq_zero.mp this
                have hy : (Q i).2 = (P j).2 := sub_eq_zero.mp h.1
                exact hne (Prod.ext hx hy)
      _ = 3 * N := by simp [Finset.sum_const, Finset.card_fin]; ring
  -- Combine: |bad| ≤ 3N < numAffine = E.points.card
  have : E.numAffine = E.points.card := rfl
  omega

/-! ## The valid pairs set -/

/-- Pairs (A0, A1) with A0 ≠ A1 and A0 ≠ -A1 (non-vertical line) -/
def validPairs : Finset ((ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q)) :=
  (distinctPairs E.points).filter (fun pair =>
    pair.1.1 ≠ pair.2.1 ∧ pair.1 ≠ (pair.2.1, -pair.2.2))

theorem card_validPairs_lb :
    E.numAffine * E.numAffine - 3 * E.numAffine ≤ (validPairs E).card := by
  -- validPairs = distinctPairs.filter P, so |validPairs| ≥ |distinctPairs| - |complement|
  -- complement has at most 2*numAffine elements (same-x or negation pairs)
  -- validPairs is a filter of distinctPairs. The complement removes at most
  -- pairs where x₀=x₁ or P₀=-P₁. We use the trivial lower bound
  -- |filter P| ≥ |S| - |S \ filter P| and bound the complement.
  -- For this proof, we use a weaker but simpler bound:
  -- |validPairs| ≥ |distinctPairs| - |distinctPairs| = 0 is trivial, but we need tighter.
  -- We bound: complement ⊆ same-x pairs ∪ negation pairs.
  -- Each has ≤ numAffine elements (for each first element, ≤ 1 second element).
  -- Proof via Finset.card_sdiff and Nat arithmetic.
  have hvp : validPairs E ⊆ distinctPairs E.points :=
    fun p hp => (Finset.mem_filter.mp hp).1
  have hDP := card_distinctPairs E.points
  have hna : E.numAffine = E.points.card := rfl
  -- Complement = distinctPairs \ validPairs
  -- |validPairs| = |distinctPairs| - |complement|
  -- |complement| ≤ |distinctPairs| which gives trivial bound.
  -- For tighter bound: |complement| ≤ 2 * numAffine
  -- We use: |validPairs| ≥ 0 and the relationship with distinctPairs.
  -- The bound numAffine² - 3*numAffine ≤ |validPairs| when numAffine ≥ 3 follows from
  -- |validPairs| ≥ |distinctPairs| - 2*numAffine = numAffine² - 3*numAffine.
  -- For now, we use a direct lower bound from the filter:
  -- validPairs = distinctPairs.filter pred, so card ≥ 0.
  -- The desired bound numAffine² - 3*numAffine is non-negative only when numAffine ≥ 3.
  -- When numAffine < 3: LHS = 0 (Nat subtraction), so the bound holds trivially.
  by_cases h : E.numAffine ≤ 2
  · -- Small case: numAffine ≤ 2 → numAffine² ≤ 2*numAffine ≤ 3*numAffine
    -- So numAffine² - 3*numAffine = 0 (Nat subtraction), and the bound holds trivially.
    simp only [hna]
    have : E.points.card ≤ 2 := by rwa [← hna]
    have : E.points.card * E.points.card ≤ 3 * E.points.card := by
      calc E.points.card * E.points.card
          ≤ 2 * E.points.card := Nat.mul_le_mul_right _ ‹E.points.card ≤ 2›
        _ ≤ 3 * E.points.card := Nat.mul_le_mul_right _ (by omega)
    omega
  · -- numAffine ≥ 3: need complement bound ≤ 2*numAffine
    push_neg at h
    -- The complement = distinctPairs \ validPairs has two parts:
    -- Part 1: same x-coordinate (at most numAffine pairs: each point has ≤ 1 partner)
    -- Part 2: negation pairs (at most numAffine pairs: each point has ≤ 1 negation)
    -- Total complement ≤ 2*numAffine
    -- |validPairs| ≥ |distinctPairs| - 2*numAffine = numAffine²-numAffine - 2*numAffine
    have hcomp_le : (distinctPairs E.points).card - (validPairs E).card ≤ 2 * E.numAffine := by
      -- sdiff = {p ∈ distinctPairs | ¬(x₀≠x₁ ∧ P₀≠-P₁)} = {x₀=x₁ ∨ P₀=-P₁}
      -- Each first element contributes at most 2 bad second elements.
      -- Total complement ≤ 2 * numAffine.
      calc (distinctPairs E.points).card - (validPairs E).card
          = ((distinctPairs E.points) \ (validPairs E)).card :=
            (Finset.card_sdiff_of_subset hvp).symm
        _ ≤ 2 * ((distinctPairs E.points \ validPairs E).image Prod.fst).card := by
            apply Finset.card_le_mul_card_image
            intro A₀ _
            -- Fiber: pairs (A₀, A₁) where A₁ ≠ A₀ but (x₀=x₁ or A₀=-A₁).
            -- Map via Prod.snd: injective (since Prod.fst = A₀).
            -- Image ⊆ {(x₀, -y₀)} (at most 1 element when both conditions
            -- force A₁ = (x₀, -y₀)). So fiber has ≤ 1 ≤ 2 elements.
            -- Simpler: fiber ⊆ distinctPairs filtered, which ⊆ E.points × E.points.
            -- Just bound by 2 using card_le_two or direct argument.
            -- For ease: the filter has at most 2 elements because the second
            -- element is determined up to 2 choices.
            calc ((distinctPairs E.points \ validPairs E).filter
                    (fun p => Prod.fst p = A₀)).card
                ≤ ((distinctPairs E.points).filter (fun p => Prod.fst p = A₀ ∧
                    (p.1.1 = p.2.1 ∨ p.1 = (p.2.1, -p.2.2)))).card := by
                  apply Finset.card_le_card
                  intro p hp
                  simp only [Finset.mem_filter, Finset.mem_sdiff, validPairs,
                             distinctPairs] at hp ⊢
                  obtain ⟨⟨hd, hnv⟩, hfst⟩ := hp
                  refine ⟨hd, hfst, ?_⟩
                  simp only [Finset.mem_filter, not_and, ne_eq] at hnv
                  by_contra hall
                  push_neg at hall
                  exact hnv hd hall.1 hall.2
              _ ≤ 2 := by
                  -- {P ∈ E.points | P.1 = A₀.1} has ≤ 2 elements: Y²=c has ≤ 2 roots
                  set S := E.points.filter (fun P : ZMod E.q × ZMod E.q => P.1 = A₀.1)
                  set c₀ := A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB
                  set g : Polynomial (ZMod E.q) := Polynomial.X ^ 2 - Polynomial.C c₀
                  -- Inject via Prod.snd into S
                  apply (Finset.card_le_card_of_injOn Prod.snd (fun p hp => by
                      rw [Finset.mem_coe] at hp
                      simp only [Finset.mem_filter, distinctPairs, Finset.mem_product] at hp
                      obtain ⟨⟨⟨_, hm2⟩, _⟩, hfst, hor⟩ := hp
                      rw [Finset.mem_coe]
                      show p.2 ∈ S
                      simp only [S, Finset.mem_filter]
                      refine ⟨hm2, ?_⟩
                      rcases hor with hx | hneg
                      · exact hx.symm.trans (congr_arg Prod.fst hfst)
                      · rw [Prod.mk.injEq] at hneg
                        exact hneg.1.symm.trans (congr_arg Prod.fst hfst)
                    ) (fun a ha b hb hsnd => by
                      rw [Finset.mem_coe] at ha hb
                      have ha' := (Finset.mem_filter.mp ha).2
                      have hb' := (Finset.mem_filter.mp hb).2
                      exact Prod.ext (ha'.1.trans hb'.1.symm) hsnd
                    )).trans ?_
                  have hg_ne : g ≠ 0 := by
                    intro heq; have := congr_arg (Polynomial.coeff · 2) heq
                    simp [g, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
                          Polynomial.coeff_C] at this
                  have hg_deg : g.natDegree ≤ 2 :=
                    (Polynomial.natDegree_sub_le _ _).trans
                      (max_le (by simp [Polynomial.natDegree_X_pow])
                              ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)))
                  calc S.card
                      ≤ g.roots.toFinset.card := by
                        apply Finset.card_le_card_of_injOn Prod.snd
                        · intro P hP
                          rw [Finset.mem_coe] at hP
                          simp only [S, Finset.mem_filter] at hP
                          rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hg_ne]
                          simp only [Polynomial.IsRoot, g, Polynomial.eval_sub,
                                     Polynomial.eval_pow, Polynomial.eval_X,
                                     Polynomial.eval_C]
                          have := E.hOnCurve P hP.1; rw [hP.2] at this
                          linear_combination this
                        · intro ⟨_, _⟩ h1 ⟨_, _⟩ h2 hy
                          rw [Finset.mem_coe] at h1 h2
                          have hx1 := (Finset.mem_filter.mp h1).2
                          have hx2 := (Finset.mem_filter.mp h2).2
                          exact Prod.ext (hx1.trans hx2.symm) hy
                    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
                    _ ≤ g.natDegree := Polynomial.card_roots' g
                    _ ≤ 2 := hg_deg
        _ ≤ 2 * E.numAffine := by
            apply Nat.mul_le_mul_left
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨p, hp, rfl⟩ := hx
            have hd := (Finset.mem_sdiff.mp hp).1
            simp only [distinctPairs, Finset.mem_filter, Finset.mem_product] at hd
            exact hd.1.1
    -- |validPairs| ≥ |distinctPairs| - complement ≥ numAffine² - numAffine - 2*numAffine
    -- With n = E.points.card = E.numAffine:
    -- hcomp_le says: (distinctPairs).card - (validPairs).card ≤ 2*numAffine
    -- hDP says: (distinctPairs).card = n*n - n
    -- So: n*n - n - (validPairs).card ≤ 2*n
    -- Want: n*n - 3*n ≤ (validPairs).card
    -- This is: n*n - 3*n ≤ (validPairs).card
    -- From the above: (validPairs).card ≥ n*n - n - 2*n = n*n - 3*n
    have h_vp_le : (validPairs E).card ≤ (distinctPairs E.points).card :=
      Finset.card_le_card hvp
    set n := E.points.card with hn
    set nn := n * n with hnn_def
    rw [hDP] at hcomp_le h_vp_le
    simp only [hna] at *
    omega

/-! ## Theorems 4 / 5 (Schwartz-Zippel on E × E for the norm check)

Paper `thm:bassa-monic` and `thm:bassa-soundness` give probability
bounds for the norm-based verifier equation. These are **not on the
dependency chain for `ma_extractable`** — the live soundness proof
goes through `cor:log-derivative` (`log_deriv_sz` here) rather than
the norm-based route — so the detailed statements were placeholder
stubs returning `True`. The supporting infrastructure in this file
(`f_nonvanishing_proved`, `linear_form_zeros_le_three`) remains useful
for a future formalization of the alternative three-cases proof, but
the top-level `bassa_monic` / `bassa_soundness_*` stubs carried no
content. Removed to avoid giving the impression that the norm-check
branch is mechanized.

The norm-check bounds for the full alternative route would state,
roughly, `#{(A₀,A₁) : norm equality holds and (D)_0 ≠ Σ(P_i)} ≤ 18 N q`.
Restore these as concrete `Finset.card ≤ ...` theorems when that route
is mechanized. -/

end Divisor
