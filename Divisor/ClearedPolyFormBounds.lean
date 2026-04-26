/-
  Divisor/ClearedPolyFormBounds.lean

  Cardinality bounds (F4-F8 + B5 + total) for the
  `clearedFiberPoly`-based log-derivative check, building on
  `Divisor/ClearedPolyForm.lean`'s polynomial-form identities.

  Topics covered:
    * Vertical-pair bound `2·|E|`.
    * F4: `D(A_0) = 0` factor bound.
    * F5/F6: dx/dz denominator bounds at `A_0`, `A_1`, `A_2`.
    * F7/F8: line-through-`-P`/`B_j` factor bounds.
    * non-vanishing of `clearedFiberPoly %ₘ curveEqPoly`.
    * Total bound `logDerivCheckFn_undefined_set_bound` (and tight
      version `logDerivCheckFn_undefined_set_bound_tight`).

  Split from `ClearedPolyForm.lean` .
-/
import Divisor.ClearedPolyForm

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ### Helper: vertical pairs bound -/

/-- Pairs `(A₀, A₁) ∈ E × E` with `A₀.1 = A₁.1` are at most `2·|E|`. -/
theorem card_vertical_pairs_le :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
         p.1.1 = p.2.1)).card ≤ 2 * E.points.card := by
  classical
  have hfib := card_filter_product_fiber_eq E E.points E.points
    (fun a b : ZMod E.q × ZMod E.q => a.1 = b.1)
  rw [hfib]
  have hper : ∀ A₀ ∈ E.points,
      (E.points.filter (fun A₁ => A₀.1 = A₁.1)).card ≤ 2 := by
    intro A₀ _
    have heq : E.points.filter (fun A₁ => A₀.1 = A₁.1)
             = E.points.filter (fun A₁ => A₁.1 = A₀.1) := by
      apply Finset.filter_congr; intros; tauto
    rw [heq]
    exact card_points_with_fst_eq_le E A₀.1
  calc ∑ A₀ ∈ E.points, (E.points.filter (fun A₁ => A₀.1 = A₁.1)).card
      ≤ ∑ A₀ ∈ E.points, 2 := Finset.sum_le_sum hper
    _ = 2 * E.points.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Helper: per-A₀ polynomial zero-set bound

    Given a family `Q : (ZMod q × ZMod q) → (ZMod q)[X][X]` of bivariate
    polynomials with `Q A₀` having outer-natDegree `< 2` (so mod `curveEq`
    is identity) and resultantX natDegree `≤ degBound` whenever `Q A₀ ≠ 0`,
    the count of `(A₀, A₁) ∈ E × E` with `bivEval (Q A₀) A₁ = 0` is at most
    `2·degBound·|E| + |{A₀ ∈ E : Q A₀ = 0}|·|E|`. -/
theorem card_bivEval_Q_zero_pairs_le
    (Q : (ZMod E.q × ZMod E.q) → (ZMod E.q)[X][X])
    (hOuter : ∀ A₀, (Q A₀).natDegree < 2)
    (degBound : ℕ)
    (hDeg : ∀ A₀, Q A₀ ≠ 0 → (resultantX E (Q A₀)).natDegree ≤ degBound) :
    ((E.points ×ˢ E.points).filter
       (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          bivEval (Q p.1) p.2 = 0)).card
    ≤ 2 * degBound * E.points.card
      + (E.points.filter (fun A₀ => Q A₀ = 0)).card * E.points.card := by
  classical
  have hfib := card_filter_product_fiber_eq E E.points E.points
    (fun a b : ZMod E.q × ZMod E.q => bivEval (Q a) b = 0)
  rw [hfib]
  -- Split E.points into exceptional (Q A₀ = 0) and non-exceptional.
  set Exc := E.points.filter (fun A₀ => Q A₀ = 0) with hExcdef
  set NonExc := E.points.filter (fun A₀ => Q A₀ ≠ 0) with hNonExcdef
  have hSum : E.points = Exc ∪ NonExc := by
    ext A₀
    simp only [hExcdef, hNonExcdef, Finset.mem_union, Finset.mem_filter]
    by_cases h : A₀ ∈ E.points
    · by_cases hQ : Q A₀ = 0
      · exact ⟨fun _ => Or.inl ⟨h, hQ⟩, fun _ => h⟩
      · exact ⟨fun _ => Or.inr ⟨h, hQ⟩, fun _ => h⟩
    · exact ⟨fun hh => absurd hh h, fun hh => (hh.elim (fun ⟨hh', _⟩ => absurd hh' h)
                                              (fun ⟨hh', _⟩ => absurd hh' h))⟩
  have hDisj : Disjoint Exc NonExc := by
    rw [Finset.disjoint_filter]
    intros; tauto
  have hSplit : ∑ A₀ ∈ E.points,
      (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
      = ∑ A₀ ∈ Exc, (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
      + ∑ A₀ ∈ NonExc, (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card := by
    rw [show E.points = Exc ∪ NonExc from hSum,
        Finset.sum_union hDisj]
  rw [hSplit]
  -- Bound each piece.
  have hExcBd : ∑ A₀ ∈ Exc,
        (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
        ≤ Exc.card * E.points.card := by
    calc ∑ A₀ ∈ Exc, (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
        ≤ ∑ A₀ ∈ Exc, E.points.card := by
            apply Finset.sum_le_sum; intros; exact Finset.card_filter_le _ _
      _ = Exc.card * E.points.card := by rw [Finset.sum_const, smul_eq_mul]
  have hNonExcBd : ∑ A₀ ∈ NonExc,
        (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
        ≤ 2 * degBound * E.points.card := by
    have hper : ∀ A₀ ∈ NonExc,
        (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card ≤ 2 * degBound := by
      intro A₀ hA₀
      simp only [hNonExcdef, Finset.mem_filter] at hA₀
      obtain ⟨_, hQne⟩ := hA₀
      have hMod : Q A₀ %ₘ curveEqPoly E ≠ 0 := by
        have hSelf : Q A₀ %ₘ curveEqPoly E = Q A₀ := by
          apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
          rw [Polynomial.degree_eq_natDegree hQne,
              Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
              curveEqPoly_natDegree_eq]
          exact_mod_cast hOuter A₀
        rw [hSelf]; exact hQne
      calc (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
          ≤ 2 * (resultantX E (Q A₀)).natDegree := card_zeros_on_E_le E (Q A₀) hMod
        _ ≤ 2 * degBound := Nat.mul_le_mul_left 2 (hDeg A₀ hQne)
    calc ∑ A₀ ∈ NonExc, (E.points.filter (fun A₁ => bivEval (Q A₀) A₁ = 0)).card
        ≤ ∑ A₀ ∈ NonExc, 2 * degBound := Finset.sum_le_sum hper
      _ = NonExc.card * (2 * degBound) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ E.points.card * (2 * degBound) := by
            exact Nat.mul_le_mul_right _ (Finset.card_le_card (by
              intro _ h; exact (Finset.mem_filter.mp h).1))
      _ = 2 * degBound * E.points.card := by ring
  calc _ ≤ Exc.card * E.points.card + 2 * degBound * E.points.card :=
          Nat.add_le_add hExcBd hNonExcBd
    _ = 2 * degBound * E.points.card + Exc.card * E.points.card := by ring

/-! ### F4: `dxdz(A₀) = 0` factor bound

    The factor `3·A₀.1² + curveA - 2·λ·A₀.2` vanishing corresponds (on
    non-vertical pairs, using `lamDen = A₁.1 − A₀.1`) to
    `bivEval (dxdzDenA₀Scaled A₀) A₁ = 0`. Split vertical (≤ 2·|E|) /
    non-vertical (via `card_bivEval_Q_zero_pairs_le` with `degBound = 3`
    and Exc ⊆ {A₀ : A₀.2 = 0 ∧ 3·A₀.1² + curveA = 0}, ≤ 2 points on E). -/

theorem dxdzDenA₀Scaled_natDegree_lt_two (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₀Scaled (E := E) A₀).natDegree < 2 := by
  refine lt_of_le_of_lt ?_ (Nat.lt_succ_self 1)
  unfold dxdzDenA₀Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, lamDenPoly_natDegree_le]; omega
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add]
    exact lamNumPoly_natDegree_le E A₀

theorem dxdzDenA₀Scaled_modByMonic_self (A₀ : ZMod E.q × ZMod E.q) :
    dxdzDenA₀Scaled (E := E) A₀ %ₘ curveEqPoly E
      = dxdzDenA₀Scaled (E := E) A₀ := by
  by_cases hZ : dxdzDenA₀Scaled (E := E) A₀ = 0
  · rw [hZ, Polynomial.zero_modByMonic]
  · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
    rw [Polynomial.degree_eq_natDegree hZ,
        Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
        curveEqPoly_natDegree_eq]
    exact_mod_cast dxdzDenA₀Scaled_natDegree_lt_two E A₀

/-- Canonical form of `dxdzDenA₀Scaled A₀`: `C xp + C yp · X` with
    `xp = C (3·A₀.1² + curveA) · (X - C A₀.1) + C (2·A₀.2²)` and
    `yp = C (-(2·A₀.2))`. -/
theorem dxdzDenA₀Scaled_eq (A₀ : ZMod E.q × ZMod E.q) :
    dxdzDenA₀Scaled (E := E) A₀ =
      C (C (3 * A₀.1 ^ 2 + E.curveA) * (Polynomial.X - C A₀.1)
           + C (2 * A₀.2 ^ 2))
        + C (C (-(2 * A₀.2))) * X := by
  simp only [dxdzDenA₀Scaled, embedScalar, lamDenPoly, lamNumPoly,
             innerA₁x, outerA₁y, map_mul, map_sub, map_add, map_neg,
             map_pow]
  ring

theorem dxdzDenA₀Scaled_coeff_zero (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₀Scaled (E := E) A₀).coeff 0 =
      C (3 * A₀.1 ^ 2 + E.curveA) * (Polynomial.X - C A₀.1)
        + C (2 * A₀.2 ^ 2) := by
  rw [dxdzDenA₀Scaled_eq, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_mul_X_zero, add_zero]

theorem dxdzDenA₀Scaled_coeff_one (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₀Scaled (E := E) A₀).coeff 1 = C (-(2 * A₀.2)) := by
  rw [dxdzDenA₀Scaled_eq, Polynomial.coeff_add,
      Polynomial.coeff_C_ne_zero (by norm_num : (1 : ℕ) ≠ 0),
      Polynomial.coeff_C_mul_X, if_pos rfl, zero_add]

theorem dxdzDenA₀Scaled_xPart (A₀ : ZMod E.q × ZMod E.q) :
    xPart E (dxdzDenA₀Scaled (E := E) A₀ %ₘ curveEqPoly E) =
      C (3 * A₀.1 ^ 2 + E.curveA) * (Polynomial.X - C A₀.1)
        + C (2 * A₀.2 ^ 2) := by
  rw [dxdzDenA₀Scaled_modByMonic_self, xPart, dxdzDenA₀Scaled_coeff_zero]

theorem dxdzDenA₀Scaled_yPart (A₀ : ZMod E.q × ZMod E.q) :
    yPart E (dxdzDenA₀Scaled (E := E) A₀ %ₘ curveEqPoly E) =
      C (-(2 * A₀.2)) := by
  rw [dxdzDenA₀Scaled_modByMonic_self, yPart, dxdzDenA₀Scaled_coeff_one]

/-- `(resultantX (dxdzDenA₀Scaled A₀)).natDegree ≤ 3`. Reason:
    `xPart` is linear in inner X, so `xPart²` has natDegree ≤ 2;
    `yPart` is constant, so `yPart² · curveX` has natDegree ≤ 3. -/
theorem resultantX_dxdzDenA₀Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (dxdzDenA₀Scaled (E := E) A₀)).natDegree ≤ 3 := by
  unfold resultantX
  rw [dxdzDenA₀Scaled_xPart, dxdzDenA₀Scaled_yPart]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · -- xPart² natDegree ≤ 2 ≤ 3
    rw [Polynomial.natDegree_pow]
    have hXp : (C (3 * A₀.1 ^ 2 + E.curveA) * (Polynomial.X - C A₀.1)
                  + C (2 * A₀.2 ^ 2)).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine Polynomial.natDegree_C_mul_le _ _ |>.trans ?_
        exact (Polynomial.natDegree_X_sub_C _).le
      · exact (Polynomial.natDegree_C _).le.trans (Nat.zero_le _)
    omega
  · -- yPart² · curveX natDegree ≤ 0 + 3 = 3
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C]
    simpa using curveX_natDegree_le_three E

/-- Generic: `|{A₀ ∈ E.points : p.eval A₀.1 = 0}| ≤ 2 · natDegree p` for
    any nonzero polynomial `p`. Proof: inject `Prod.fst` into `p.roots`;
    each root has ≤ 2 `y`-values on `E`. -/
theorem card_points_on_E_polyRoot_le {p : (ZMod E.q)[X]} (hp : p ≠ 0) :
    (E.points.filter (fun A₀ => p.eval A₀.1 = 0)).card ≤ 2 * p.natDegree := by
  classical
  set S := E.points.filter (fun A₀ => p.eval A₀.1 = 0) with hSdef
  set xProj := S.image Prod.fst with hxProjdef
  have hxProj_sub : xProj ⊆ p.roots.toFinset := by
    intro x hx
    rw [hxProjdef, Finset.mem_image] at hx
    obtain ⟨A₀, hA₀, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    simp only [hSdef, Finset.mem_filter] at hA₀
    exact hA₀.2
  have hxProj_card : xProj.card ≤ p.natDegree :=
    le_trans (Finset.card_le_card hxProj_sub)
      (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p))
  have hFiber : ∀ x ∈ xProj, (S.filter (fun A₀ => A₀.1 = x)).card ≤ 2 := by
    intro x _
    refine le_trans (Finset.card_le_card ?_) (card_points_with_fst_eq_le E x)
    intro A₀ hA₀
    simp only [hSdef, Finset.mem_filter] at hA₀ ⊢
    exact ⟨hA₀.1.1, hA₀.2⟩
  calc S.card
      ≤ 2 * xProj.card := Finset.card_le_mul_card_image _ _ hFiber
    _ ≤ 2 * p.natDegree := Nat.mul_le_mul_left 2 hxProj_card

/-- Exceptional A₀ set (where `dxdzDenA₀Scaled A₀ = 0`) on `E.points` has
    size ≤ 6. Reason: `Q A₀ = 0` on `E.points` forces A₀.1 to be a root of
    `-X³ + curveA·X + 2·curveB`, a polynomial of natDegree ≤ 3. -/
theorem card_dxdzDenA₀Scaled_zero_A₀_le :
    (E.points.filter (fun A₀ => dxdzDenA₀Scaled (E := E) A₀ = 0)).card ≤ 6 := by
  classical
  set p : (ZMod E.q)[X] :=
    -Polynomial.X ^ 3 + C E.curveA * Polynomial.X + C (2 * E.curveB) with hpdef
  have hp_deg : p.natDegree ≤ 3 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · rw [Polynomial.natDegree_neg]; exact (Polynomial.natDegree_X_pow 3).le
      · refine Polynomial.natDegree_C_mul_le _ _ |>.trans ?_
        exact Polynomial.natDegree_X_le.trans (by omega)
    · exact (Polynomial.natDegree_C _).le.trans (Nat.zero_le _)
  have hp_ne : p ≠ 0 := by
    intro hZ
    have hcoeff3 : p.coeff 3 = -1 := by
      simp [hpdef, Polynomial.coeff_add, Polynomial.coeff_neg,
             Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
             Polynomial.coeff_X, Polynomial.coeff_C]
    rw [hZ, Polynomial.coeff_zero] at hcoeff3
    have h1 : (1 : ZMod E.q) = 0 := by linear_combination hcoeff3
    exact one_ne_zero h1
  have hSub : E.points.filter (fun A₀ => dxdzDenA₀Scaled (E := E) A₀ = 0)
            ⊆ E.points.filter (fun A₀ => p.eval A₀.1 = 0) := by
    intro A₀ hA₀
    simp only [Finset.mem_filter] at hA₀ ⊢
    obtain ⟨hE, hQ⟩ := hA₀
    refine ⟨hE, ?_⟩
    -- From Q A₀ = 0: inner poly (coeff 0 of Q) = 0 as element of ZMod q[X];
    -- evaluating at X = 0 gives -(3A₀.1²+A)·A₀.1 + 2A₀.2² = 0.
    have hcoeff0 : (dxdzDenA₀Scaled (E := E) A₀).coeff 0 = 0 := by
      rw [hQ]; simp
    rw [dxdzDenA₀Scaled_coeff_zero] at hcoeff0
    have hEval : (C (3 * A₀.1 ^ 2 + E.curveA) * (Polynomial.X - C A₀.1)
                    + C (2 * A₀.2 ^ 2)).eval 0 = 0 := by
      rw [hcoeff0]; simp
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow] at hEval
    have hOC : A₀.2 ^ 2 = A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB := E.hOnCurve A₀ hE
    rw [hpdef]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
          Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C]
    linear_combination hEval - 2 * hOC
  calc _ ≤ (E.points.filter (fun A₀ => p.eval A₀.1 = 0)).card :=
          Finset.card_le_card hSub
    _ ≤ 2 * p.natDegree := card_points_on_E_polyRoot_le E hp_ne
    _ ≤ 6 := Nat.mul_le_mul_left 2 hp_deg

/-- F4: pairs `(A₀, A₁) ∈ E × E` with `3·A₀.1² + curveA - 2·λ·A₀.2 = 0`
    (where `λ = slopeOf A₀ A₁`) have cardinality ≤ `10 · |E|`.

    Split: vertical (`A₀.1 = A₁.1`, ≤ 2·|E| via `card_vertical_pairs_le`);
    non-vertical (via `card_bivEval_Q_zero_pairs_le` on `dxdzDenA₀Scaled`
    with `degBound = 3` and Exc ≤ 6). -/
theorem dxdzA₀_zero_pairs_card_le :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        3 * p.1.1 ^ 2 + E.curveA
          - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.1.2 = 0)).card
    ≤ 14 * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.1.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.1.2 = 0) with hSdef
  -- Split S ⊆ Svert ∪ Snv where Snv ⊆ {bivEval(Q) = 0}.
  set Svert := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      p.1.1 = p.2.1) with hSvertdef
  set Sbiv := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
       bivEval (dxdzDenA₀Scaled (E := E) p.1) p.2 = 0) with hSbivdef
  have hSub : S ⊆ Svert ∪ Sbiv := by
    intro p hp
    simp only [hSdef, Finset.mem_filter] at hp
    rw [Finset.mem_union]
    by_cases hV : p.1.1 = p.2.1
    · left
      simp only [hSvertdef, Finset.mem_filter]
      exact ⟨hp.1, hV⟩
    · right
      simp only [hSbivdef, Finset.mem_filter]
      refine ⟨hp.1, ?_⟩
      -- bivEval = (A₁.1 - A₀.1) · (factor). factor = 0 ⇒ bivEval = 0.
      have hEval := bivEval_dxdzDenA₀Scaled_eq E p.1 p.2 hV
      rw [hEval]
      have hFactor : 3 * p.1.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.1.2 = 0 := hp.2
      linear_combination (p.2.1 - p.1.1) * hFactor
  have hSvert_bd : Svert.card ≤ 2 * E.points.card := card_vertical_pairs_le E
  have hSbiv_bd : Sbiv.card ≤ 2 * 3 * E.points.card + 6 * E.points.card := by
    have hbd :=
      card_bivEval_Q_zero_pairs_le E
        (fun A₀ => dxdzDenA₀Scaled (E := E) A₀)
        (dxdzDenA₀Scaled_natDegree_lt_two E)
        3
        (fun A₀ _ => resultantX_dxdzDenA₀Scaled_natDegree_le E A₀)
    refine le_trans hbd ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _
      (card_dxdzDenA₀Scaled_zero_A₀_le E)) _
  calc S.card ≤ (Svert ∪ Sbiv).card := Finset.card_le_card hSub
    _ ≤ Svert.card + Sbiv.card := Finset.card_union_le _ _
    _ ≤ 2 * E.points.card + (2 * 3 * E.points.card + 6 * E.points.card) :=
        Nat.add_le_add hSvert_bd hSbiv_bd
    _ = 14 * E.points.card := by ring

/-! ### F5: `dxdz(A₁) = 0` factor bound

    The factor `3·A₁.1² + curveA - 2·λ·A₁.2` vanishing at non-vertical
    `(A₀, A₁)` corresponds to `(A₁.1 − A₀.1)·factor = 0`, which on
    `E.points` (using `A₁.2² = curveX(A₁.1)`) reduces to a polynomial
    identity `bivEval (dxdzDenA₁Reduced A₀) A₁ = 0` where
    `dxdzDenA₁Reduced` has outer natDegree < 2. Split vertical /
    non-vertical as in F4, but the reduced polynomial has
    `resultantX.natDegree ≤ 6` (cubic inner in `X³`). -/

/-- Reduced form of `dxdzDenA₁Scaled A₀`: after using `Y² = curveX`,
    the polynomial has outer natDegree ≤ 1 and the bivEval on `E.points`
    equals `(A₁.1 − A₀.1)·factor(A₁)` where `factor(A₁) = 3·A₁.1² + curveA
    − 2·λ·A₁.2`. -/
noncomputable def dxdzDenA₁Reduced (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  C (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
       - C E.curveA * Polynomial.X - C (E.curveA * A₀.1 + 2 * E.curveB))
    + C (C (2 * A₀.2)) * X

theorem dxdzDenA₁Reduced_natDegree_lt_two (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₁Reduced (E := E) A₀).natDegree < 2 := by
  refine lt_of_le_of_lt ?_ (by omega : 1 < 2)
  unfold dxdzDenA₁Reduced
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C _).le.trans (by omega)
  · have : ((C (C (2 * A₀.2)) : (ZMod E.q)[X][X]) * X ^ 1).natDegree ≤ 1 :=
      Polynomial.natDegree_C_mul_X_pow_le _ _
    simpa using this

theorem dxdzDenA₁Reduced_modByMonic_self (A₀ : ZMod E.q × ZMod E.q) :
    dxdzDenA₁Reduced (E := E) A₀ %ₘ curveEqPoly E
      = dxdzDenA₁Reduced (E := E) A₀ := by
  by_cases hZ : dxdzDenA₁Reduced (E := E) A₀ = 0
  · rw [hZ, Polynomial.zero_modByMonic]
  · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
    rw [Polynomial.degree_eq_natDegree hZ,
        Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
        curveEqPoly_natDegree_eq]
    exact_mod_cast dxdzDenA₁Reduced_natDegree_lt_two E A₀

theorem dxdzDenA₁Reduced_coeff_zero (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₁Reduced (E := E) A₀).coeff 0 =
      Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
        - C E.curveA * Polynomial.X - C (E.curveA * A₀.1 + 2 * E.curveB) := by
  unfold dxdzDenA₁Reduced
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_mul_X_zero, add_zero]

theorem dxdzDenA₁Reduced_coeff_one (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₁Reduced (E := E) A₀).coeff 1 = C (2 * A₀.2) := by
  unfold dxdzDenA₁Reduced
  rw [Polynomial.coeff_add,
      Polynomial.coeff_C_ne_zero (by norm_num : (1 : ℕ) ≠ 0),
      Polynomial.coeff_C_mul_X, if_pos rfl, zero_add]

theorem dxdzDenA₁Reduced_xPart (A₀ : ZMod E.q × ZMod E.q) :
    xPart E (dxdzDenA₁Reduced (E := E) A₀ %ₘ curveEqPoly E)
      = Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
          - C E.curveA * Polynomial.X - C (E.curveA * A₀.1 + 2 * E.curveB) := by
  rw [dxdzDenA₁Reduced_modByMonic_self, xPart, dxdzDenA₁Reduced_coeff_zero]

theorem dxdzDenA₁Reduced_yPart (A₀ : ZMod E.q × ZMod E.q) :
    yPart E (dxdzDenA₁Reduced (E := E) A₀ %ₘ curveEqPoly E)
      = C (2 * A₀.2) := by
  rw [dxdzDenA₁Reduced_modByMonic_self, yPart, dxdzDenA₁Reduced_coeff_one]

/-- `bivEval (dxdzDenA₁Reduced A₀) A₁` on E.points equals
    `(A₁.1 − A₀.1)·(3·A₁.1² + curveA − 2·λ·A₁.2)` (with `λ = slopeOf`).
    Derivation: expand the reduced polynomial's bivEval and substitute
    `A₁.2² = A₁.1³ + curveA·A₁.1 + curveB`. -/
theorem bivEval_dxdzDenA₁Reduced_eq_of_onCurve
    (A₀ A₁ : ZMod E.q × ZMod E.q) (_hA₁ : A₁ ∈ E.points) :
    bivEval (dxdzDenA₁Reduced (E := E) A₀) A₁ =
      A₁.1 ^ 3 - 3 * A₀.1 * A₁.1 ^ 2 - E.curveA * A₁.1
        - (E.curveA * A₀.1 + 2 * E.curveB) + 2 * A₀.2 * A₁.2 := by
  unfold dxdzDenA₁Reduced
  simp [bivEval, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_add]

/-- On non-vertical `(A₀, A₁)` with `A₁ ∈ E.points`, `bivEval dxdzDenA₁Reduced`
    equals `(A₁.1 − A₀.1) · factor(A₁)`. -/
theorem bivEval_dxdzDenA₁Reduced_eq_chord
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1) :
    bivEval (dxdzDenA₁Reduced (E := E) A₀) A₁ =
      (A₁.1 - A₀.1) * (3 * A₁.1 ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₁.2) := by
  rw [bivEval_dxdzDenA₁Reduced_eq_of_onCurve E A₀ A₁ hA₁]
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  have hOC : A₁.2 ^ 2 = A₁.1 ^ 3 + E.curveA * A₁.1 + E.curveB := E.hOnCurve A₁ hA₁
  have hlam : slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    unfold slopeOf
    field_simp
  -- Target after pulling lam out: (A₁.1-A₀.1) · [(3·A₁.1² + A) - 2·A₁.2·lam]
  --   = (A₁.1-A₀.1)(3·A₁.1²+A) - 2·A₁.2·(A₁.2-A₀.2)  (using hlam)
  linear_combination 2 * hOC + 2 * A₁.2 * hlam

/-- The xPart polynomial used in `dxdzDenA₁Reduced` has natDegree ≤ 3. -/
private theorem dxdzDenA₁Reduced_xPart_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
        - C E.curveA * Polynomial.X
        - C (E.curveA * A₀.1 + 2 * E.curveB) : (ZMod E.q)[X]).natDegree ≤ 3 := by
  have h1 : (Polynomial.X ^ 3 : (ZMod E.q)[X]).natDegree ≤ 3 :=
    (Polynomial.natDegree_X_pow 3).le
  have h2 : (C (3 * A₀.1) * Polynomial.X ^ 2 : (ZMod E.q)[X]).natDegree ≤ 3 := by
    have := Polynomial.natDegree_C_mul_X_pow_le (3 * A₀.1) 2
    omega
  have h3 : (C E.curveA * Polynomial.X : (ZMod E.q)[X]).natDegree ≤ 3 := by
    have := Polynomial.natDegree_C_mul_X_pow_le E.curveA 1
    rw [pow_one] at this
    omega
  have h4 : (C (E.curveA * A₀.1 + 2 * E.curveB) : (ZMod E.q)[X]).natDegree ≤ 3 := by
    have := Polynomial.natDegree_C (E.curveA * A₀.1 + 2 * E.curveB)
    omega
  calc (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
          - C E.curveA * Polynomial.X
          - C (E.curveA * A₀.1 + 2 * E.curveB) : (ZMod E.q)[X]).natDegree
      ≤ max (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
              - C E.curveA * Polynomial.X : (ZMod E.q)[X]).natDegree
          (C (E.curveA * A₀.1 + 2 * E.curveB) : (ZMod E.q)[X]).natDegree :=
          Polynomial.natDegree_sub_le _ _
    _ ≤ 3 := by
        refine max_le ?_ h4
        calc (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
                - C E.curveA * Polynomial.X : (ZMod E.q)[X]).natDegree
            ≤ max (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
                    : (ZMod E.q)[X]).natDegree
              (C E.curveA * Polynomial.X : (ZMod E.q)[X]).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ 3 := by
              refine max_le ?_ h3
              calc (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
                      : (ZMod E.q)[X]).natDegree
                  ≤ max (Polynomial.X ^ 3 : (ZMod E.q)[X]).natDegree
                        (C (3 * A₀.1) * Polynomial.X ^ 2
                            : (ZMod E.q)[X]).natDegree :=
                      Polynomial.natDegree_sub_le _ _
                _ ≤ 3 := max_le h1 h2

/-- `resultantX (dxdzDenA₁Reduced A₀)` has natDegree ≤ 6. Reason:
    `xPart` is cubic (natDegree ≤ 3), `yPart` is constant (natDegree 0);
    resultantX = xPart² − yPart²·curveX has natDegree ≤ max(6, 3) = 6. -/
theorem resultantX_dxdzDenA₁Reduced_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (dxdzDenA₁Reduced (E := E) A₀)).natDegree ≤ 6 := by
  unfold resultantX
  rw [dxdzDenA₁Reduced_xPart, dxdzDenA₁Reduced_yPart]
  have hXp := dxdzDenA₁Reduced_xPart_natDegree_le E A₀
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · -- xPart² natDegree ≤ 2·3 = 6
    rw [Polynomial.natDegree_pow]
    omega
  · -- yPart² · curveX natDegree ≤ 0 + 3 = 3 ≤ 6
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C]
    have := curveX_natDegree_le_three E
    omega

/-- `dxdzDenA₁Reduced A₀ ≠ 0` for any `A₀`. Reason: `xPart` has
    leading coefficient 1 for `X³`, hence nonzero. -/
theorem dxdzDenA₁Reduced_ne_zero (A₀ : ZMod E.q × ZMod E.q) :
    dxdzDenA₁Reduced (E := E) A₀ ≠ 0 := by
  intro hZ
  have hcoeff : (dxdzDenA₁Reduced (E := E) A₀).coeff 0 = 0 := by
    rw [hZ]; simp
  rw [dxdzDenA₁Reduced_coeff_zero] at hcoeff
  have e1 : (Polynomial.X ^ 3 : (ZMod E.q)[X]).coeff 3 = 1 := by
    rw [Polynomial.coeff_X_pow]; simp
  have e2 : (C (3 * A₀.1) * Polynomial.X ^ 2 : (ZMod E.q)[X]).coeff 3 = 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
  have e3 : (C E.curveA * Polynomial.X : (ZMod E.q)[X]).coeff 3 = 0 := by
    rw [Polynomial.coeff_C_mul]
    simp [Polynomial.coeff_X]
  have e4 : (C (E.curveA * A₀.1 + 2 * E.curveB) : (ZMod E.q)[X]).coeff 3 = 0 :=
    Polynomial.coeff_C_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  have hxp3 : (Polynomial.X ^ 3 - C (3 * A₀.1) * Polynomial.X ^ 2
                - C E.curveA * Polynomial.X
                - C (E.curveA * A₀.1 + 2 * E.curveB)).coeff 3 = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_sub,
        e1, e2, e3, e4]
    ring
  rw [hcoeff, Polynomial.coeff_zero] at hxp3
  exact one_ne_zero hxp3.symm

/-- F5: pairs `(A₀, A₁) ∈ E × E` with `3·A₁.1² + curveA - 2·λ·A₁.2 = 0`
    have cardinality ≤ `14 · |E|`. Split vertical / non-vertical as F4. -/
theorem dxdzA₁_zero_pairs_card_le :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        3 * p.2.1 ^ 2 + E.curveA
          - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.2.2 = 0)).card
    ≤ 14 * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.2.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.2.2 = 0) with hSdef
  set Svert := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      p.1.1 = p.2.1) with hSvertdef
  set Sbiv := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
       bivEval (dxdzDenA₁Reduced (E := E) p.1) p.2 = 0) with hSbivdef
  have hSub : S ⊆ Svert ∪ Sbiv := by
    intro p hp
    simp only [hSdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1E, hp2E⟩, hFactor⟩ := hp
    rw [Finset.mem_union]
    by_cases hV : p.1.1 = p.2.1
    · left
      simp only [hSvertdef, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp1E, hp2E⟩, hV⟩
    · right
      simp only [hSbivdef, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hp1E, hp2E⟩, ?_⟩
      rw [bivEval_dxdzDenA₁Reduced_eq_chord E p.1 p.2 hp2E hV]
      linear_combination (p.2.1 - p.1.1) * hFactor
  have hSvert_bd : Svert.card ≤ 2 * E.points.card := card_vertical_pairs_le E
  have hSbiv_bd : Sbiv.card ≤ 2 * 6 * E.points.card := by
    have hbd :=
      card_bivEval_Q_zero_pairs_le E
        (fun A₀ => dxdzDenA₁Reduced (E := E) A₀)
        (dxdzDenA₁Reduced_natDegree_lt_two E)
        6
        (fun A₀ _ => resultantX_dxdzDenA₁Reduced_natDegree_le E A₀)
    -- Exc = ∅ because dxdzDenA₁Reduced A₀ ≠ 0 for any A₀.
    have hExc : (E.points.filter (fun A₀ => dxdzDenA₁Reduced (E := E) A₀ = 0)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro A₀ hA₀
      simp only [Finset.mem_filter] at hA₀
      exact dxdzDenA₁Reduced_ne_zero E A₀ hA₀.2
    refine le_trans hbd ?_
    rw [hExc]
    simp
  calc S.card ≤ (Svert ∪ Sbiv).card := Finset.card_le_card hSub
    _ ≤ Svert.card + Sbiv.card := Finset.card_union_le _ _
    _ ≤ 2 * E.points.card + 2 * 6 * E.points.card :=
        Nat.add_le_add hSvert_bd hSbiv_bd
    _ = 14 * E.points.card := by ring

/-! ### F6: `dxdz(A_2) = 0` factor bound

    The factor `3·x₂² + curveA - 2·λ·y₂` (at the third intersection
    `A₂ = (x₂, y₂)` with chord slope `λ`) vanishing at non-vertical
    `(A₀, A₁)` corresponds — via `bivEval (dxdzDenA₂Scaled A₀) A₁ =
    lamDen^4 · factor` — to vanishing of the scaled polynomial on the
    non-vertical cone. Reducing modulo the curve equation (using
    `A₁.2² = curveX(A₁.1)` on `E.points`) produces `dxdzDenA₂Reduced A₀
    = C xPart + C yPart · Y` with outer natDegree < 2, where `xPart`
    has inner natDegree ≤ 6 and `yPart` ≤ 3. Therefore `resultantX` has
    natDegree ≤ 12. The exceptional set `{A₀ : dxdzDenA₂Reduced A₀ = 0}`
    forces `A₀.2 = 0` (via evaluation at the reflection `(A₀.1, -A₀.2)`
    yielding `16·A₀.2⁴`), so the exceptional set on `E.points` is
    bounded by `6` (roots of `curveX`, with each root projecting from
    at most 2 y-values). -/

/-- xPart of `dxdzDenA₂Scaled A₀` after reducing `Y² → curveX`.
    Shape: `cx² + 6·b²·cx + b⁴ - 2·(a+2·X)·Δx²·(cx + b²)
           + (3·(a+X)² + A)·Δx⁴ + 2·b²·Δx³`
    with `a := A₀.1, b := A₀.2, cx := X³ + A·X + B, Δx := X - a`. -/
noncomputable def dxdzDenA₂xPart (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X] :=
  (Polynomial.X ^ 3 + C E.curveA * Polynomial.X + C E.curveB) ^ 2
    + C (6 * A₀.2 ^ 2) *
        (Polynomial.X ^ 3 + C E.curveA * Polynomial.X + C E.curveB)
    + C (A₀.2 ^ 4)
    - C 2 * (C A₀.1 + C 2 * Polynomial.X) * (Polynomial.X - C A₀.1) ^ 2 *
        ((Polynomial.X ^ 3 + C E.curveA * Polynomial.X + C E.curveB)
          + C (A₀.2 ^ 2))
    + (C 3 * (C A₀.1 + Polynomial.X) ^ 2 + C E.curveA) *
        (Polynomial.X - C A₀.1) ^ 4
    + C (2 * A₀.2 ^ 2) * (Polynomial.X - C A₀.1) ^ 3

/-- yPart of `dxdzDenA₂Scaled A₀` after reducing `Y² → curveX`.
    Shape: `2·b·(-2·(cx + b²) + 2·(a + 2·X)·Δx² - Δx³)`. -/
noncomputable def dxdzDenA₂yPart (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X] :=
  C (2 * A₀.2) * (
    -(C 2) * ((Polynomial.X ^ 3 + C E.curveA * Polynomial.X + C E.curveB)
              + C (A₀.2 ^ 2))
    + C 2 * (C A₀.1 + C 2 * Polynomial.X) * (Polynomial.X - C A₀.1) ^ 2
    - (Polynomial.X - C A₀.1) ^ 3)

/-- Reduced form of `dxdzDenA₂Scaled A₀` after using `Y² = curveX`. -/
noncomputable def dxdzDenA₂Reduced (A₀ : ZMod E.q × ZMod E.q) :
    (ZMod E.q)[X][X] :=
  C (dxdzDenA₂xPart (E := E) A₀) + C (dxdzDenA₂yPart (E := E) A₀) * X

theorem dxdzDenA₂Reduced_natDegree_lt_two (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂Reduced (E := E) A₀).natDegree < 2 := by
  refine lt_of_le_of_lt ?_ (by omega : 1 < 2)
  unfold dxdzDenA₂Reduced
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C _).le.trans (by omega)
  · have : ((C (dxdzDenA₂yPart (E := E) A₀) : (ZMod E.q)[X][X]) *
              X ^ 1).natDegree ≤ 1 :=
      Polynomial.natDegree_C_mul_X_pow_le _ _
    simpa using this

theorem dxdzDenA₂Reduced_modByMonic_self (A₀ : ZMod E.q × ZMod E.q) :
    dxdzDenA₂Reduced (E := E) A₀ %ₘ curveEqPoly E
      = dxdzDenA₂Reduced (E := E) A₀ := by
  by_cases hZ : dxdzDenA₂Reduced (E := E) A₀ = 0
  · rw [hZ, Polynomial.zero_modByMonic]
  · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
    rw [Polynomial.degree_eq_natDegree hZ,
        Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
        curveEqPoly_natDegree_eq]
    exact_mod_cast dxdzDenA₂Reduced_natDegree_lt_two E A₀

theorem dxdzDenA₂Reduced_coeff_zero (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂Reduced (E := E) A₀).coeff 0 = dxdzDenA₂xPart (E := E) A₀ := by
  unfold dxdzDenA₂Reduced
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_mul_X_zero, add_zero]

theorem dxdzDenA₂Reduced_coeff_one (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂Reduced (E := E) A₀).coeff 1 = dxdzDenA₂yPart (E := E) A₀ := by
  unfold dxdzDenA₂Reduced
  rw [Polynomial.coeff_add,
      Polynomial.coeff_C_ne_zero (by norm_num : (1 : ℕ) ≠ 0),
      Polynomial.coeff_C_mul_X, if_pos rfl, zero_add]

theorem dxdzDenA₂Reduced_xPart (A₀ : ZMod E.q × ZMod E.q) :
    xPart E (dxdzDenA₂Reduced (E := E) A₀ %ₘ curveEqPoly E)
      = dxdzDenA₂xPart (E := E) A₀ := by
  rw [dxdzDenA₂Reduced_modByMonic_self, xPart, dxdzDenA₂Reduced_coeff_zero]

theorem dxdzDenA₂Reduced_yPart (A₀ : ZMod E.q × ZMod E.q) :
    yPart E (dxdzDenA₂Reduced (E := E) A₀ %ₘ curveEqPoly E)
      = dxdzDenA₂yPart (E := E) A₀ := by
  rw [dxdzDenA₂Reduced_modByMonic_self, yPart, dxdzDenA₂Reduced_coeff_one]

/-- `bivEval (dxdzDenA₂Reduced A₀) A₁ = bivEval (dxdzDenA₂Scaled A₀) A₁`
    on `E.points` (using `Y² = curveX` for the reduction).
    Derivation: the `Y² - curveX` witness is
    `6·b² - 2·(a+2X)·Δx² - 4·b·Y + Y² + cx` multiplied into `S - R`. -/
theorem bivEval_dxdzDenA₂Reduced_eq_of_onCurve
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hA₁ : A₁ ∈ E.points) :
    bivEval (dxdzDenA₂Reduced (E := E) A₀) A₁
      = bivEval (dxdzDenA₂Scaled (E := E) A₀) A₁ := by
  rw [bivEval_dxdzDenA₂Scaled]
  unfold dxdzDenA₂Reduced dxdzDenA₂xPart dxdzDenA₂yPart
  simp only [bivEval, Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
             Polynomial.eval_C, Polynomial.eval_X]
  have hOC : A₁.2 ^ 2 = A₁.1 ^ 3 + E.curveA * A₁.1 + E.curveB :=
    E.hOnCurve A₁ hA₁
  linear_combination
    (-6 * A₀.2 ^ 2 + 2 * (A₀.1 + 2 * A₁.1) * (A₁.1 - A₀.1) ^ 2
      + 4 * A₀.2 * A₁.2
      - A₁.2 ^ 2 - A₁.1 ^ 3 - E.curveA * A₁.1 - E.curveB) * hOC

/-- On non-vertical pairs with `A₁ ∈ E.points`, if the F6 factor vanishes
    then `bivEval dxdzDenA₂Reduced A₀ A₁ = 0`. Proof strategy: multiply
    `hFactor` by `(A₁.1 - A₀.1)^4 ≠ 0` and use `hlam : slope · lamDen =
    lamNum` to clear inverses, reducing to `bivEval dxdzDenA₂Scaled A₀ A₁
    = (A₁.1 - A₀.1)^4 · factor`; combined with bivEval scaled ↔ reduced
    on E.points, this gives the result. -/
theorem dxdzDenA₂Reduced_eq_zero_of_factor_zero
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hFactor :
      3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
        - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁) = 0) :
    bivEval (dxdzDenA₂Reduced (E := E) A₀) A₁ = 0 := by
  rw [bivEval_dxdzDenA₂Reduced_eq_of_onCurve E A₀ A₁ hA₁,
      bivEval_dxdzDenA₂Scaled]
  have hden : A₁.1 - A₀.1 ≠ 0 := sub_ne_zero.mpr hNV.symm
  have hlam : slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) = A₁.2 - A₀.2 := by
    unfold slopeOf; field_simp
  -- `chordX₂ · lamDen² = lamNum² - lamDen²·(a+x)`.
  have hX₂ : chordX₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 2
      = (A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (A₀.1 + A₁.1) := by
    unfold chordX₂
    linear_combination
      (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) + (A₁.2 - A₀.2)) * hlam
  -- `chordY₂ · lamDen³ = lamNum·(lamNum² - lamDen²·(2a+x)) + b·lamDen³`.
  have hY₂ : chordY₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 3
      = (A₁.2 - A₀.2) *
          ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (2 * A₀.1 + A₁.1))
        + A₀.2 * (A₁.1 - A₀.1) ^ 3 := by
    unfold chordY₂ chordX₂
    linear_combination
      ((slopeOf A₀.1 A₀.2 A₁.1 A₁.2) ^ 2 * (A₁.1 - A₀.1) ^ 2
        + slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1) * (A₁.2 - A₀.2)
        + (A₁.2 - A₀.2) ^ 2
        - (2 * A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2) * hlam
  -- Main identity (inverse-free, obtained by multiplying factor by lamDen⁴):
  -- `3·(lamDen²·chordX₂)² + A·lamDen⁴ - 2·lamNum·(lamDen³·chordY₂)
  --  = bivEval dxdzDenA₂Scaled`, equal to `lamDen⁴ · factor`.
  have hMain :
      3 * ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2) ^ 2
        + E.curveA * (A₁.1 - A₀.1) ^ 4
        - 2 * (A₁.2 - A₀.2)
          * ((A₁.2 - A₀.2)
              * ((A₁.2 - A₀.2) ^ 2 - (A₀.1 + A₁.1) * (A₁.1 - A₀.1) ^ 2)
             + (A₀.2 * (A₁.1 - A₀.1) - A₀.1 * (A₁.2 - A₀.2))
                 * (A₁.1 - A₀.1) ^ 2)
      = (A₁.1 - A₀.1) ^ 4 *
          (3 * (chordX₂ A₀ A₁) ^ 2 + E.curveA
            - 2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (chordY₂ A₀ A₁)) := by
    linear_combination
      (-3 * ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (A₀.1 + A₁.1)
              + chordX₂ A₀ A₁ * (A₁.1 - A₀.1) ^ 2)) * hX₂
      + (2 * slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * (A₁.1 - A₀.1)) * hY₂
      + 2 * ((A₁.2 - A₀.2) *
              ((A₁.2 - A₀.2) ^ 2 - (A₁.1 - A₀.1) ^ 2 * (2 * A₀.1 + A₁.1))
             + A₀.2 * (A₁.1 - A₀.1) ^ 3) * hlam
  rw [hMain, hFactor, mul_zero]

/-- `dxdzDenA₂xPart A₀` has natDegree ≤ 6. -/
theorem dxdzDenA₂xPart_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂xPart (E := E) A₀).natDegree ≤ 6 := by
  unfold dxdzDenA₂xPart
  compute_degree

/-- `dxdzDenA₂yPart A₀` has natDegree ≤ 3. -/
theorem dxdzDenA₂yPart_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂yPart (E := E) A₀).natDegree ≤ 3 := by
  unfold dxdzDenA₂yPart
  compute_degree

/-- `resultantX (dxdzDenA₂Reduced A₀)` has natDegree ≤ 12. Reason:
    `xPart` ≤ 6, `yPart` ≤ 3, `curveX` ≤ 3; `xPart² - yPart²·curveX`
    natDegree ≤ max(12, 6+3) = 12. -/
theorem resultantX_dxdzDenA₂Reduced_natDegree_le
    (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (dxdzDenA₂Reduced (E := E) A₀)).natDegree ≤ 12 := by
  unfold resultantX
  rw [dxdzDenA₂Reduced_xPart, dxdzDenA₂Reduced_yPart]
  have hXp := dxdzDenA₂xPart_natDegree_le E A₀
  have hYp := dxdzDenA₂yPart_natDegree_le E A₀
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_pow]; omega
  · refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow]
    have := curveX_natDegree_le_three E
    omega

/-- `(2 : ZMod E.q) ≠ 0` (since `E.q ≥ 5` is prime, so `E.q ≠ 2`). -/
theorem ZMod_two_ne_zero_of_E : (2 : ZMod E.q) ≠ 0 := by
  have hq5 := E.hq_ge
  have hlt : (2 : ℕ) < E.q := by omega
  have hne : (↑(2 : ℕ) : ZMod E.q) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod E.q) E.q]
    intro hdvd
    exact Nat.not_lt.mpr (Nat.le_of_dvd (by omega) hdvd) hlt
  exact_mod_cast hne

/-- Exceptional A₀ set for F6: if `dxdzDenA₂Reduced A₀ = 0` then
    `A₀.2 = 0` (via evaluation at the reflection point), so
    `A₀.1` is a root of `curveX`, giving a count bound ≤ 6. -/
theorem card_dxdzDenA₂Reduced_zero_A₀_le :
    (E.points.filter
      (fun A₀ => dxdzDenA₂Reduced (E := E) A₀ = 0)).card ≤ 6 := by
  classical
  have hSub : E.points.filter (fun A₀ => dxdzDenA₂Reduced (E := E) A₀ = 0)
            ⊆ E.points.filter (fun A₀ => (curveX E).eval A₀.1 = 0) := by
    intro A₀ hA₀
    simp only [Finset.mem_filter] at hA₀ ⊢
    obtain ⟨hE, hQ⟩ := hA₀
    refine ⟨hE, ?_⟩
    have hOC : A₀.2 ^ 2 = A₀.1 ^ 3 + E.curveA * A₀.1 + E.curveB :=
      E.hOnCurve A₀ hE
    have hRefl : (A₀.1, -A₀.2) ∈ E.points := by
      apply E.hComplete
      show (-A₀.2) ^ 2 = _
      have hneg : (-A₀.2) ^ 2 = A₀.2 ^ 2 := by ring
      rw [hneg]; exact hOC
    have hBE : bivEval (dxdzDenA₂Reduced (E := E) A₀) (A₀.1, -A₀.2) = 0 := by
      rw [hQ]; simp [bivEval]
    rw [bivEval_dxdzDenA₂Reduced_eq_of_onCurve E A₀ _ hRefl,
        bivEval_dxdzDenA₂Scaled] at hBE
    -- hBE reduces algebraically to `16 * A₀.2^4 = 0` (via `ring` witness).
    have h16 : (16 : ZMod E.q) * A₀.2 ^ 4 = 0 := by linear_combination hBE
    have h2ne : (2 : ZMod E.q) ≠ 0 := ZMod_two_ne_zero_of_E E
    have h16ne : (16 : ZMod E.q) ≠ 0 := by
      have heq : (16 : ZMod E.q) = 2 ^ 4 := by norm_num
      rw [heq]
      exact pow_ne_zero _ h2ne
    have h24 : A₀.2 ^ 4 = 0 :=
      (mul_eq_zero.mp h16).resolve_left h16ne
    have h2e : A₀.2 = 0 := by
      have hRewrite : A₀.2 ^ 4 = (A₀.2 ^ 2) ^ 2 := by ring
      rw [hRewrite] at h24
      have hsq : A₀.2 ^ 2 = 0 := pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h24
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hsq
    -- A₀.1 is a root of curveX.
    unfold curveX
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
               Polynomial.eval_X, Polynomial.eval_C]
    linear_combination -hOC + A₀.2 * h2e
  calc _ ≤ (E.points.filter (fun A₀ => (curveX E).eval A₀.1 = 0)).card :=
          Finset.card_le_card hSub
    _ ≤ 2 * (curveX E).natDegree :=
          card_points_on_E_polyRoot_le E (curveX_ne_zero E)
    _ ≤ 6 := by
        have := curveX_natDegree_le_three E
        omega

/-- F6: pairs `(A₀, A₁) ∈ E × E` with F6 factor zero have cardinality
    ≤ `32 · |E|`. Split: vertical (≤ 2·|E|) / non-vertical with bivEval
    equal to `lamDen^4 · factor` (using `dxdzDenA₂Reduced` on
    `E.points`; Exc ≤ 6). -/
theorem dxdzA₂_zero_pairs_card_le :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        3 * (chordX₂ p.1 p.2) ^ 2 + E.curveA
          - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * (chordY₂ p.1 p.2) = 0)).card
    ≤ 32 * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * (chordX₂ p.1 p.2) ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * (chordY₂ p.1 p.2) = 0) with hSdef
  set Svert := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      p.1.1 = p.2.1) with hSvertdef
  set Sbiv := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
       bivEval (dxdzDenA₂Reduced (E := E) p.1) p.2 = 0) with hSbivdef
  have hSub : S ⊆ Svert ∪ Sbiv := by
    intro p hp
    simp only [hSdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1E, hp2E⟩, hFactor⟩ := hp
    rw [Finset.mem_union]
    by_cases hV : p.1.1 = p.2.1
    · left
      simp only [hSvertdef, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp1E, hp2E⟩, hV⟩
    · right
      simp only [hSbivdef, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hp1E, hp2E⟩, ?_⟩
      exact dxdzDenA₂Reduced_eq_zero_of_factor_zero E p.1 p.2 hp2E hV hFactor
  have hSvert_bd : Svert.card ≤ 2 * E.points.card := card_vertical_pairs_le E
  have hSbiv_bd : Sbiv.card ≤ 2 * 12 * E.points.card + 6 * E.points.card := by
    have hbd :=
      card_bivEval_Q_zero_pairs_le E
        (fun A₀ => dxdzDenA₂Reduced (E := E) A₀)
        (dxdzDenA₂Reduced_natDegree_lt_two E)
        12
        (fun A₀ _ => resultantX_dxdzDenA₂Reduced_natDegree_le E A₀)
    refine le_trans hbd ?_
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (card_dxdzDenA₂Reduced_zero_A₀_le E)) _
  calc S.card ≤ (Svert ∪ Sbiv).card := Finset.card_le_card hSub
    _ ≤ Svert.card + Sbiv.card := Finset.card_union_le _ _
    _ ≤ 2 * E.points.card + (2 * 12 * E.points.card + 6 * E.points.card) :=
        Nat.add_le_add hSvert_bd hSbiv_bd
    _ = 32 * E.points.card := by ring

/-! ### F7 / F8: line factor bounds

    The factor `(lineThrough A₀ A₁).eval pt.1 pt.2` (for some fixed `pt`,
    either `(P.1, -P.2)` or one of the `B_j`s) vanishes iff `pt` lies on
    the chord `A₀A₁`. On non-vertical pairs, `(A₁.1 - A₀.1)·factor` equals
    `bivEval (lineEvalNumAt A₀ pt) A₁` (which has outer natDegree ≤ 1).

    `resultantX (lineEvalNumAt A₀ pt)` has natDegree ≤ 3; Exc (≤ 1) is
    when `A₀ = pt`. Total F7-shape bound per line: ≤ 9·|E|. -/

theorem lineEvalNumAt_natDegree_lt_two (A₀ pt : ZMod E.q × ZMod E.q) :
    (lineEvalNumAt (E := E) A₀ pt).natDegree < 2 :=
  lt_of_le_of_lt (lineEvalNumAt_natDegree_le E A₀ pt) (by omega)

theorem lineEvalNumAt_modByMonic_self (A₀ pt : ZMod E.q × ZMod E.q) :
    lineEvalNumAt (E := E) A₀ pt %ₘ curveEqPoly E
      = lineEvalNumAt (E := E) A₀ pt := by
  by_cases hZ : lineEvalNumAt (E := E) A₀ pt = 0
  · rw [hZ, Polynomial.zero_modByMonic]
  · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
    rw [Polynomial.degree_eq_natDegree hZ,
        Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
        curveEqPoly_natDegree_eq]
    exact_mod_cast lineEvalNumAt_natDegree_lt_two E A₀ pt

theorem lineEvalNumAt_eq (A₀ pt : ZMod E.q × ZMod E.q) :
    lineEvalNumAt (E := E) A₀ pt =
      C (C (pt.2 - A₀.2) * (Polynomial.X - C A₀.1)
           + C ((pt.1 - A₀.1) * A₀.2))
        + C (C (-(pt.1 - A₀.1))) * X := by
  simp only [lineEvalNumAt, embedScalar, lamDenPoly, lamNumPoly,
             innerA₁x, outerA₁y, map_mul, map_sub, map_add, map_neg]
  ring

theorem lineEvalNumAt_coeff_zero (A₀ pt : ZMod E.q × ZMod E.q) :
    (lineEvalNumAt (E := E) A₀ pt).coeff 0 =
      C (pt.2 - A₀.2) * (Polynomial.X - C A₀.1)
        + C ((pt.1 - A₀.1) * A₀.2) := by
  rw [lineEvalNumAt_eq, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_mul_X_zero, add_zero]

theorem lineEvalNumAt_coeff_one (A₀ pt : ZMod E.q × ZMod E.q) :
    (lineEvalNumAt (E := E) A₀ pt).coeff 1 = C (-(pt.1 - A₀.1)) := by
  rw [lineEvalNumAt_eq, Polynomial.coeff_add,
      Polynomial.coeff_C_ne_zero (by norm_num : (1 : ℕ) ≠ 0),
      Polynomial.coeff_C_mul_X, if_pos rfl, zero_add]

theorem lineEvalNumAt_xPart (A₀ pt : ZMod E.q × ZMod E.q) :
    xPart E (lineEvalNumAt (E := E) A₀ pt %ₘ curveEqPoly E) =
      C (pt.2 - A₀.2) * (Polynomial.X - C A₀.1)
        + C ((pt.1 - A₀.1) * A₀.2) := by
  rw [lineEvalNumAt_modByMonic_self, xPart, lineEvalNumAt_coeff_zero]

theorem lineEvalNumAt_yPart (A₀ pt : ZMod E.q × ZMod E.q) :
    yPart E (lineEvalNumAt (E := E) A₀ pt %ₘ curveEqPoly E) =
      C (-(pt.1 - A₀.1)) := by
  rw [lineEvalNumAt_modByMonic_self, yPart, lineEvalNumAt_coeff_one]

theorem resultantX_lineEvalNumAt_natDegree_le (A₀ pt : ZMod E.q × ZMod E.q) :
    (resultantX E (lineEvalNumAt (E := E) A₀ pt)).natDegree ≤ 3 := by
  unfold resultantX
  rw [lineEvalNumAt_xPart, lineEvalNumAt_yPart]
  have hXp : (C (pt.2 - A₀.2) * (Polynomial.X - C A₀.1)
                + C ((pt.1 - A₀.1) * A₀.2) : (ZMod E.q)[X]).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ((Polynomial.natDegree_C _).le.trans (by omega))
    refine Polynomial.natDegree_C_mul_le _ _ |>.trans ?_
    exact (Polynomial.natDegree_X_sub_C _).le
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_pow]
    omega
  · refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C]
    have := curveX_natDegree_le_three E
    omega

/-- Exceptional A₀ set (where `lineEvalNumAt A₀ pt = 0`) on `E.points` has
    size ≤ 1. Reason: `yPart = 0` forces `A₀.1 = pt.1`; evaluating `xPart`
    at `A₀.1 + 1` (using `A₀.1 = pt.1`) forces `A₀.2 = pt.2`. -/
theorem card_lineEvalNumAt_zero_A₀_le (pt : ZMod E.q × ZMod E.q) :
    (E.points.filter
      (fun A₀ => lineEvalNumAt (E := E) A₀ pt = 0)).card ≤ 1 := by
  classical
  refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({pt} : Finset _))) (by simp)
  intro A₀ hA₀
  simp only [Finset.mem_filter] at hA₀
  obtain ⟨_, hZ⟩ := hA₀
  -- Step 1: pt.1 = A₀.1 via coeff 1 of lineEvalNumAt.
  have hy : (lineEvalNumAt (E := E) A₀ pt).coeff 1 = 0 := by rw [hZ]; simp
  rw [lineEvalNumAt_coeff_one] at hy
  have hy' : -(pt.1 - A₀.1) = 0 := by
    have := congrArg (fun p : (ZMod E.q)[X] => p.eval 0) hy
    simpa using this
  have hx1_sub : pt.1 - A₀.1 = 0 := neg_eq_zero.mp hy'
  have hx1 : pt.1 = A₀.1 := sub_eq_zero.mp hx1_sub
  -- Step 2: pt.2 = A₀.2 via coeff 0 evaluated at A₀.1 + 1.
  have hx : (lineEvalNumAt (E := E) A₀ pt).coeff 0 = 0 := by rw [hZ]; simp
  rw [lineEvalNumAt_coeff_zero] at hx
  have heval : ((C (pt.2 - A₀.2) * (Polynomial.X - C A₀.1)
                  + C ((pt.1 - A₀.1) * A₀.2)).eval (A₀.1 + 1) : ZMod E.q) = 0 := by
    rw [hx]; simp
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
             Polynomial.eval_X, Polynomial.eval_C] at heval
  -- heval : (pt.2 - A₀.2) * (A₀.1 + 1 - A₀.1) + (pt.1 - A₀.1) * A₀.2 = 0
  have hx2_sub : pt.2 - A₀.2 = 0 := by linear_combination heval - A₀.2 * hx1_sub
  have hx2 : pt.2 = A₀.2 := sub_eq_zero.mp hx2_sub
  rw [Finset.mem_singleton]
  exact Prod.ext hx1.symm hx2.symm

/-- Generic line-factor bound: pairs `(A₀, A₁) ∈ E × E` with the chord
    `A₀A₁` passing through `pt` have cardinality ≤ `9 · |E|`. -/
theorem lineEval_at_point_zero_pairs_card_le (pt : ZMod E.q × ZMod E.q) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval pt.1 pt.2 = 0)).card
    ≤ 9 * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval pt.1 pt.2 = 0) with hSdef
  set Svert := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      p.1.1 = p.2.1) with hSvertdef
  set Sbiv := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
       bivEval (lineEvalNumAt (E := E) p.1 pt) p.2 = 0) with hSbivdef
  have hSub : S ⊆ Svert ∪ Sbiv := by
    intro p hp
    simp only [hSdef, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_union]
    by_cases hV : p.1.1 = p.2.1
    · left
      simp only [hSvertdef, Finset.mem_filter, Finset.mem_product]
      exact ⟨hp.1, hV⟩
    · right
      simp only [hSbivdef, Finset.mem_filter, Finset.mem_product]
      refine ⟨hp.1, ?_⟩
      rw [bivEval_lineEvalNumAt]
      have hFactor := hp.2
      simp only [Line.eval, lineThrough] at hFactor
      have hden : p.2.1 - p.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hV)
      have hlam : slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * (p.2.1 - p.1.1)
                  = p.2.2 - p.1.2 := by
        unfold slopeOf
        field_simp
      linear_combination (p.2.1 - p.1.1) * hFactor + (pt.1 - p.1.1) * hlam
  have hSvert_bd : Svert.card ≤ 2 * E.points.card := card_vertical_pairs_le E
  have hSbiv_bd : Sbiv.card ≤ 2 * 3 * E.points.card + 1 * E.points.card := by
    have hbd :=
      card_bivEval_Q_zero_pairs_le E
        (fun A₀ => lineEvalNumAt (E := E) A₀ pt)
        (fun A₀ => lineEvalNumAt_natDegree_lt_two E A₀ pt)
        3
        (fun A₀ _ => resultantX_lineEvalNumAt_natDegree_le E A₀ pt)
    refine le_trans hbd ?_
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (card_lineEvalNumAt_zero_A₀_le E pt)) _
  calc S.card ≤ (Svert ∪ Sbiv).card := Finset.card_le_card hSub
    _ ≤ Svert.card + Sbiv.card := Finset.card_union_le _ _
    _ ≤ 2 * E.points.card + (2 * 3 * E.points.card + 1 * E.points.card) :=
        Nat.add_le_add hSvert_bd hSbiv_bd
    _ = 9 * E.points.card := by ring

/-- F7: `L(-P) = 0` pair count bound. -/
theorem linePNeg_zero_pairs_card_le (P : ZMod E.q × ZMod E.q) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval P.1 (-P.2) = 0)).card
    ≤ 9 * E.points.card :=
  lineEval_at_point_zero_pairs_card_le E (P.1, -P.2)

/-- F8: `∏_j L(B_j) = 0` pair count bound (union over `j`). -/
theorem lineBj_zero_pairs_card_le
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        ∃ j : Fin k,
          (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval (B j).1 (B j).2 = 0)).card
    ≤ 9 * k * E.points.card := by
  classical
  set S := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ∃ j : Fin k,
        (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval (B j).1 (B j).2 = 0) with hSdef
  have hSub : S ⊆ (Finset.univ : Finset (Fin k)).biUnion (fun j =>
      (E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval (B j).1 (B j).2 = 0)) := by
    intro p hp
    simp only [hSdef, Finset.mem_filter] at hp
    obtain ⟨hmem, j, hj⟩ := hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨j, hmem, hj⟩
  calc S.card
      ≤ ((Finset.univ : Finset (Fin k)).biUnion (fun j =>
          (E.points ×ˢ E.points).filter
            (fun p => (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval
                        (B j).1 (B j).2 = 0))).card := Finset.card_le_card hSub
    _ ≤ ∑ j : Fin k, ((E.points ×ˢ E.points).filter
          (fun p => (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval
                      (B j).1 (B j).2 = 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin k, 9 * E.points.card := by
        apply Finset.sum_le_sum
        intros j _
        exact lineEval_at_point_zero_pairs_card_le E (B j)
    _ = k * (9 * E.points.card) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = 9 * k * E.points.card := by ring

/-! ## `logDerivCheckFn_zero_set_bound` as a theorem.

    Issue 2 fix: the count is split into two bounds, corresponding to
    the "defined" subset (where all `logDerivCheckFn` denominators are
    nonzero and Lean semantics matches the paper) and the "undefined
    bad event" subset (where some denominator vanishes).

    * On the **defined** subset, the fiber-argument route gives a
      `fiber + badA₀` count bound (via `clearedFiberPoly`'s structure).
    * On the **undefined** subset, the bad event (some denominator
      vanishes) is itself polynomially bounded by counting zeros of
      each denominator factor on E × E.

    Together they upper-bound the Lean-semantics zero set.

    All three axioms are paper-mechanical: polynomial counting, no
    classical AG content beyond `card_zeros_on_E_le`. -/

/-- Short predicate: all denominators of `logDerivCheckFn` are nonzero
    at `(A₀, A₁)`. On this subset Lean and paper semantics agree. -/
noncomputable def logDerivCheckFnDefined
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) : Prop :=
  logDerivCheckFnDenom E D P B A₀ A₁ ≠ 0

/-! ## outer natDegree bounds for `clearedFiberPoly`

    The outer natDegree of `clearedFiberPoly E D P k B m A₀` (as a
    polynomial in the outer variable `A₁.2`) is bounded by `D.degE + k + 8`.
    This is one of two ingredients feeding T1's fiber-count bound;
    the other is an inner-coefficient natDegree bound used together
    with this one to bound `resultantX`. -/

theorem x₂Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (x₂Scaled (E := E) A₀).natDegree ≤ 2 := by
  unfold x₂Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_pow]
    have := lamNumPoly_natDegree_le E A₀
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 : (embedScalar (E := E) A₀.1 + innerA₁x (E := E)).natDegree ≤ 0 :=
      (natDegree_add_le _ _).trans
        (max_le (by rw [embedScalar_natDegree_le])
                (by rw [innerA₁x_natDegree]))
    have h2 : (lamDenPoly (E := E) A₀ ^ 2).natDegree = 0 := by
      rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le]
    omega

theorem y₂Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (y₂Scaled (E := E) A₀).natDegree ≤ 3 := by
  unfold y₂Scaled
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have h1 := lamNumPoly_natDegree_le E A₀
    have h2 := x₂Scaled_natDegree_le E A₀
    omega
  · refine natDegree_mul_le.trans ?_
    have h1 : (embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀
                 - embedScalar (E := E) A₀.1
                   * lamNumPoly (E := E) A₀).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        rw [embedScalar_natDegree_le, lamDenPoly_natDegree_le]
        omega
      · refine natDegree_mul_le.trans ?_
        rw [embedScalar_natDegree_le, Nat.zero_add]
        exact lamNumPoly_natDegree_le E A₀
    have h2 : (lamDenPoly (E := E) A₀ ^ 2).natDegree = 0 := by
      rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le]
    omega

theorem dxdzDenA₁Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₁Scaled (E := E) A₀).natDegree ≤ 2 := by
  unfold dxdzDenA₁Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    have h1 : (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
                 + embedScalar (E := E) E.curveA).natDegree ≤ 0 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        rw [embedScalar_natDegree_le, Polynomial.natDegree_pow,
            innerA₁x_natDegree]
      · rw [embedScalar_natDegree_le]
    rw [lamDenPoly_natDegree_le]
    omega
  · refine natDegree_mul_le.trans ?_
    refine Nat.add_le_add ?_ (lamNumPoly_natDegree_le E A₀)
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, outerA₁y_natDegree]

theorem dxdzDenA₂Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzDenA₂Scaled (E := E) A₀).natDegree ≤ 4 := by
  unfold dxdzDenA₂Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_mul_le.trans ?_
      rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow]
      have := x₂Scaled_natDegree_le E A₀
      omega
    · refine natDegree_mul_le.trans ?_
      rw [embedScalar_natDegree_le, Polynomial.natDegree_pow,
          lamDenPoly_natDegree_le]
      omega
  · refine natDegree_mul_le.trans ?_
    refine Nat.add_le_add ?_ (y₂Scaled_natDegree_le E A₀)
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add]
    exact lamNumPoly_natDegree_le E A₀

theorem DAtA₀Poly_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DAtA₀Poly (E := E) D A₀).natDegree = 0 := by
  unfold DAtA₀Poly
  exact embedScalar_natDegree_le E _

theorem DDerivAtA₀Poly_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DDerivAtA₀Poly (E := E) D A₀).natDegree = 0 := by
  unfold DDerivAtA₀Poly
  exact embedScalar_natDegree_le E _

theorem DDerivAtA₁Poly_natDegree_le (D : CoordRingElt E.q) :
    (DDerivAtA₁Poly (E := E) D).natDegree ≤ 1 := by
  unfold DDerivAtA₁Poly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [embedInnerPoly_natDegree_le]; exact Nat.zero_le _
  · refine natDegree_mul_le.trans ?_
    rw [embedInnerPoly_natDegree_le, outerA₁y_natDegree]

/-- `DAPartAtA₂Scaled D A₀` has outer natDegree ≤ `2·D.a.natDegree`,
    hence ≤ `D.degE`. -/
theorem DAPartAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DAPartAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DAPartAtA₂Scaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro n hn
  have hn' : n ≤ D.a.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hx := x₂Scaled_natDegree_le E A₀
  have h1 : (embedScalar (E := E) (D.a.coeff n)
                * x₂Scaled (E := E) A₀ ^ n).natDegree ≤ 2 * n := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow]
    calc n * (x₂Scaled (E := E) A₀).natDegree
        ≤ n * 2 := Nat.mul_le_mul_left n hx
      _ = 2 * n := by ring
  have h2 : (lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n)).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le, Nat.mul_zero]
  have h3 : 2 * n ≤ D.degE :=
    (Nat.mul_le_mul_left 2 hn').trans (le_max_left _ _)
  refine natDegree_mul_le.trans ?_
  omega

theorem DBPartAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DBPartAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DBPartAtA₂Scaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro n hn
  have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hx := x₂Scaled_natDegree_le E A₀
  have h1 : (embedScalar (E := E) (D.b.coeff n)
                * x₂Scaled (E := E) A₀ ^ n).natDegree ≤ 2 * n := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow]
    calc n * (x₂Scaled (E := E) A₀).natDegree
        ≤ n * 2 := Nat.mul_le_mul_left n hx
      _ = 2 * n := by ring
  have h2 : (y₂Scaled (E := E) A₀).natDegree ≤ 3 := y₂Scaled_natDegree_le E A₀
  have h3 : (lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n - 3)).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le, Nat.mul_zero]
  have h4 : 2 * n + 3 ≤ D.degE := by
    have hmax : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
    have : 2 * n ≤ 2 * D.b.natDegree := Nat.mul_le_mul_left 2 hn'
    omega
  refine natDegree_mul_le.trans ?_
  have hmul : (embedScalar (E := E) _ * x₂Scaled (E := E) A₀ ^ n
               * y₂Scaled (E := E) A₀).natDegree ≤ 2 * n + 3 :=
    natDegree_mul_le.trans (Nat.add_le_add h1 h2)
  exact (Nat.add_le_add hmul h3.le).trans (by omega)

theorem DAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DAtA₂Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact DAPartAtA₂Scaled_natDegree_le E D A₀
  · exact DBPartAtA₂Scaled_natDegree_le E D A₀

theorem DDerivAPartAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DDerivAPartAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DDerivAPartAtA₂Scaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.a).natDegree :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hda : (Polynomial.derivative D.a).natDegree ≤ D.a.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hnDa : n ≤ D.a.natDegree := hn'.trans hda
  have hx := x₂Scaled_natDegree_le E A₀
  have h1 : (embedScalar (E := E) ((Polynomial.derivative D.a).coeff n)
                * x₂Scaled (E := E) A₀ ^ n).natDegree ≤ 2 * n := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow]
    calc n * (x₂Scaled (E := E) A₀).natDegree
        ≤ n * 2 := Nat.mul_le_mul_left n hx
      _ = 2 * n := by ring
  have h2 : (lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n)).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le, Nat.mul_zero]
  have h3 : 2 * n ≤ D.degE :=
    (Nat.mul_le_mul_left 2 hnDa).trans (le_max_left _ _)
  refine natDegree_mul_le.trans ?_
  omega

theorem DDerivBPartAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DDerivBPartAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DDerivBPartAtA₂Scaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.b).natDegree :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hdb : (Polynomial.derivative D.b).natDegree ≤ D.b.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hnDb : n ≤ D.b.natDegree := hn'.trans hdb
  have hx := x₂Scaled_natDegree_le E A₀
  have h1 : (embedScalar (E := E) ((Polynomial.derivative D.b).coeff n)
                * x₂Scaled (E := E) A₀ ^ n).natDegree ≤ 2 * n := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow]
    calc n * (x₂Scaled (E := E) A₀).natDegree
        ≤ n * 2 := Nat.mul_le_mul_left n hx
      _ = 2 * n := by ring
  have h2 : (y₂Scaled (E := E) A₀).natDegree ≤ 3 := y₂Scaled_natDegree_le E A₀
  have h3 : (lamDenPoly (E := E) A₀ ^ (D.degE - 2 * n - 3)).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le, Nat.mul_zero]
  have h4 : 2 * n + 3 ≤ D.degE := by
    have hmax : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
    have : 2 * n ≤ 2 * D.b.natDegree := Nat.mul_le_mul_left 2 hnDb
    omega
  refine natDegree_mul_le.trans ?_
  have hmul : (embedScalar (E := E) _ * x₂Scaled (E := E) A₀ ^ n
               * y₂Scaled (E := E) A₀).natDegree ≤ 2 * n + 3 :=
    natDegree_mul_le.trans (Nat.add_le_add h1 h2)
  exact (Nat.add_le_add hmul h3.le).trans (by omega)

theorem DDerivAtA₂Scaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DDerivAtA₂Scaled (E := E) D A₀).natDegree ≤ D.degE := by
  unfold DDerivAtA₂Scaled
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact DDerivAPartAtA₂Scaled_natDegree_le E D A₀
  · exact DDerivBPartAtA₂Scaled_natDegree_le E D A₀

theorem linesProductScaled_natDegree_le
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (linesProductScaled (E := E) P k B A₀).natDegree ≤ k + 1 := by
  unfold linesProductScaled
  refine natDegree_mul_le.trans ?_
  have h1 := lineEvalNumAt_natDegree_le E A₀ (P.1, -P.2)
  have h2 : (∏ j : Fin k, lineEvalNumAt (E := E) A₀ (B j)).natDegree ≤ k := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j : Fin k, (lineEvalNumAt (E := E) A₀ (B j)).natDegree
        ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum
            (fun j _ => lineEvalNumAt_natDegree_le E A₀ (B j))
      _ = k := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                      smul_eq_mul, Nat.mul_one]
  omega

theorem linesProductNoNegPScaled_natDegree_le
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (linesProductNoNegPScaled (E := E) k B A₀).natDegree ≤ k := by
  unfold linesProductNoNegPScaled
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ j : Fin k, (lineEvalNumAt (E := E) A₀ (B j)).natDegree
      ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum
          (fun j _ => lineEvalNumAt_natDegree_le E A₀ (B j))
    _ = k := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    smul_eq_mul, Nat.mul_one]

theorem linesProductSkipBjScaled_natDegree_le
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) (j₀ : Fin k) :
    (linesProductSkipBjScaled (E := E) P k B A₀ j₀).natDegree ≤ k := by
  classical
  unfold linesProductSkipBjScaled
  refine natDegree_mul_le.trans ?_
  have hcard : ((Finset.univ (α := Fin k)).erase j₀).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
  have hk_pos : 1 ≤ k := Fin.pos_iff_nonempty.mpr ⟨j₀⟩
  have hprod :
      (∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
         lineEvalNumAt (E := E) A₀ (B j)).natDegree ≤ k - 1 := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j ∈ (Finset.univ (α := Fin k)).erase j₀,
              (lineEvalNumAt (E := E) A₀ (B j)).natDegree
        ≤ ∑ _j ∈ (Finset.univ (α := Fin k)).erase j₀, 1 :=
              Finset.sum_le_sum
                (fun j _ => lineEvalNumAt_natDegree_le E A₀ (B j))
      _ = k - 1 := by rw [Finset.sum_const, hcard, smul_eq_mul, Nat.mul_one]
  calc (lineEvalNumAt (E := E) A₀ (P.1, -P.2)).natDegree
          + (∏ j ∈ (Finset.univ (α := Fin k)).erase j₀,
               lineEvalNumAt (E := E) A₀ (B j)).natDegree
      ≤ 1 + (k - 1) := Nat.add_le_add
          (lineEvalNumAt_natDegree_le E A₀ _) hprod
    _ = k := by omega

theorem dxdzAllScaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dxdzAllScaled (E := E) A₀).natDegree ≤ 7 := by
  unfold dxdzAllScaled
  refine natDegree_mul_le.trans ?_
  have h0 : (dxdzDenA₀Scaled (E := E) A₀).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (dxdzDenA₀Scaled_natDegree_lt_two E A₀)
  have h1 := dxdzDenA₁Scaled_natDegree_le E A₀
  have h2 := dxdzDenA₂Scaled_natDegree_le E A₀
  have hmul : (dxdzDenA₀Scaled (E := E) A₀ * dxdzDenA₁Scaled (E := E) A₀).natDegree ≤ 3 :=
    natDegree_mul_le.trans (Nat.add_le_add h0 h1)
  exact (Nat.add_le_add hmul h2).trans (by omega)

theorem DAllScaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DAllScaled (E := E) D A₀).natDegree ≤ D.degE + 1 := by
  unfold DAllScaled
  refine natDegree_mul_le.trans ?_
  have h0 : (DAtA₀Poly (E := E) D A₀).natDegree = 0 :=
    DAtA₀Poly_natDegree_le E D A₀
  have h1 : (DAtA₁Poly (E := E) D).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (DAtA₁Poly_natDegree_lt_two E D)
  have h2 := DAtA₂Scaled_natDegree_le E D A₀
  have hmul : (DAtA₀Poly (E := E) D A₀ * DAtA₁Poly (E := E) D).natDegree ≤ 1 := by
    refine natDegree_mul_le.trans ?_
    rw [h0, Nat.zero_add]; exact h1
  exact (Nat.add_le_add hmul h2).trans (by omega)

/-- natDegree bound for `DBdydzAtA₀Poly`: it's a scalar embedding, degree 0. -/
theorem DBdydzAtA₀Poly_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DBdydzAtA₀Poly (E := E) D A₀).natDegree = 0 := by
  unfold DBdydzAtA₀Poly
  exact embedScalar_natDegree_le E _

/-- natDegree bound for `DBdydzAtA₁Poly`. Linear in outerY? No — outer-degree 0
    since neither factor involves outerY (inner polys only). -/
theorem DBdydzAtA₁Poly_natDegree_le (D : CoordRingElt E.q) :
    (DBdydzAtA₁Poly (E := E) D).natDegree ≤ 0 := by
  unfold DBdydzAtA₁Poly
  refine natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_neg, embedInnerPoly_natDegree_le, Nat.zero_add]
  refine (natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow,
        innerA₁x_natDegree, Nat.mul_zero]
  · exact (embedScalar_natDegree_le E _).le

/-- natDegree bound for `DbAtA₂TightScaled`: `2·b.natDegree`. -/
theorem DbAtA₂TightScaled_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (DbAtA₂TightScaled (E := E) D A₀).natDegree ≤ 2 * D.b.natDegree := by
  unfold DbAtA₂TightScaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro n hn
  have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  refine natDegree_mul_le.trans ?_
  have h1 : (embedScalar (E := E) (D.b.coeff n) *
            x₂Scaled (E := E) A₀ ^ n).natDegree ≤ 0 + 2 * n :=
    natDegree_mul_le.trans (Nat.add_le_add
      (embedScalar_natDegree_le E _).le
      (Polynomial.natDegree_pow_le.trans (by
        have : (x₂Scaled (E := E) A₀).natDegree ≤ 2 := x₂Scaled_natDegree_le E A₀
        calc n * (x₂Scaled (E := E) A₀).natDegree ≤ n * 2 :=
              Nat.mul_le_mul_left _ this
          _ = 2 * n := by ring)))
  have h2 : (lamDenPoly (E := E) A₀ ^ (2 * D.b.natDegree - 2 * n)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le]
    omega
  refine (Nat.add_le_add h1 h2).trans ?_
  omega

/-- natDegree bound for `dydzNumA₂Scaled`: ≤ 4 (from `x₂Scaled^2` contribution). -/
theorem dydzNumA₂Scaled_natDegree_le (A₀ : ZMod E.q × ZMod E.q) :
    (dydzNumA₂Scaled (E := E) A₀).natDegree ≤ 4 := by
  unfold dydzNumA₂Scaled
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add]
    refine Polynomial.natDegree_pow_le.trans ?_
    have : (x₂Scaled (E := E) A₀).natDegree ≤ 2 := x₂Scaled_natDegree_le E A₀
    calc 2 * (x₂Scaled (E := E) A₀).natDegree ≤ 2 * 2 :=
          Nat.mul_le_mul_left _ this
      _ = 4 := rfl
  · refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add, Polynomial.natDegree_pow,
        lamDenPoly_natDegree_le, Nat.mul_zero]
    omega

/-- natDegree bound for `correctionA₂ScaledCore`. -/
theorem correctionA₂ScaledCore_natDegree_le (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (correctionA₂ScaledCore (E := E) D A₀).natDegree ≤ 2 * D.b.natDegree + 4 := by
  unfold correctionA₂ScaledCore
  refine natDegree_mul_le.trans ?_
  have h1 : (- DbAtA₂TightScaled (E := E) D A₀ *
            dydzNumA₂Scaled (E := E) A₀).natDegree
          ≤ 2 * D.b.natDegree + 4 := by
    refine natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_neg]
    exact Nat.add_le_add (DbAtA₂TightScaled_natDegree_le E D A₀)
      (dydzNumA₂Scaled_natDegree_le E A₀)
  have h2 : (lamDenPoly (E := E) A₀ ^
            (D.degE - 2 * D.b.natDegree - 3)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le]
    omega
  refine (Nat.add_le_add h1 h2).trans ?_
  omega

theorem lhsTerm0Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (lhsTerm0Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold lhsTerm0Scaled
  have h1 : (DDerivAtA₀Poly (E := E) D A₀).natDegree ≤ 0 :=
    (DDerivAtA₀Poly_natDegree_le E D A₀).le
  have h2 : (embedScalar (E := E) (2 * A₀.2)).natDegree ≤ 0 :=
    (embedScalar_natDegree_le E _).le
  have h3 : (DAtA₁Poly (E := E) D).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (DAtA₁Poly_natDegree_lt_two E D)
  have h4 := DAtA₂Scaled_natDegree_le E D A₀
  have h5 := dxdzDenA₁Scaled_natDegree_le E A₀
  have h6 := dxdzDenA₂Scaled_natDegree_le E A₀
  have h7 := linesProductScaled_natDegree_le E P k B A₀
  refine le_trans ?_ (by omega : 0 + 0 + 1 + D.degE + 2 + 4 + (k + 1) ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add
            (natDegree_mul_le.trans (Nat.add_le_add h1 h2))
            h3))
          h4))
        h5))
      h6))
    h7)

theorem lhsTerm1Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (lhsTerm1Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold lhsTerm1Scaled
  have h1 := DDerivAtA₁Poly_natDegree_le E D
  have h2 : (embedScalar (E := E) 2 * outerA₁y (E := E)).natDegree ≤ 1 := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, outerA₁y_natDegree]
  have h3 : (DAtA₀Poly (E := E) D A₀).natDegree ≤ 0 :=
    (DAtA₀Poly_natDegree_le E D A₀).le
  have h4 := DAtA₂Scaled_natDegree_le E D A₀
  have h5 : (dxdzDenA₀Scaled (E := E) A₀).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (dxdzDenA₀Scaled_natDegree_lt_two E A₀)
  have h6 := dxdzDenA₂Scaled_natDegree_le E A₀
  have h7 := linesProductScaled_natDegree_le E P k B A₀
  refine le_trans ?_ (by omega : 1 + 1 + 0 + D.degE + 1 + 4 + (k + 1) ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add
            (natDegree_mul_le.trans (Nat.add_le_add h1 h2))
            h3))
          h4))
        h5))
      h6))
    h7)

theorem lhsTerm2Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (lhsTerm2Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold lhsTerm2Scaled
  have h1 := DDerivAtA₂Scaled_natDegree_le E D A₀
  have h2 : (embedScalar (E := E) 2 * y₂Scaled (E := E) A₀).natDegree ≤ 3 := by
    refine natDegree_mul_le.trans ?_
    rw [embedScalar_natDegree_le, Nat.zero_add]
    exact y₂Scaled_natDegree_le E A₀
  have h3 : (DAtA₀Poly (E := E) D A₀).natDegree ≤ 0 :=
    (DAtA₀Poly_natDegree_le E D A₀).le
  have h4 : (DAtA₁Poly (E := E) D).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (DAtA₁Poly_natDegree_lt_two E D)
  have h5 : (dxdzDenA₀Scaled (E := E) A₀).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (dxdzDenA₀Scaled_natDegree_lt_two E A₀)
  have h6 := dxdzDenA₁Scaled_natDegree_le E A₀
  have h7 := linesProductScaled_natDegree_le E P k B A₀
  refine le_trans ?_ (by omega : D.degE + 3 + 0 + 1 + 1 + 2 + (k + 1) ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add
            (natDegree_mul_le.trans (Nat.add_le_add h1 h2))
            h3))
          h4))
        h5))
      h6))
    h7)

/-- natDegree bound for correctionTerm0Scaled. -/
theorem correctionTerm0Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (correctionTerm0Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold correctionTerm0Scaled
  have h1 := DBdydzAtA₀Poly_natDegree_le E D A₀
  have h2 : (DAtA₁Poly (E := E) D).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (DAtA₁Poly_natDegree_lt_two E D)
  have h3 := DAtA₂Scaled_natDegree_le E D A₀
  have h4 := dxdzDenA₁Scaled_natDegree_le E A₀
  have h5 := dxdzDenA₂Scaled_natDegree_le E A₀
  have h6 := linesProductScaled_natDegree_le E P k B A₀
  refine le_trans ?_ (by omega : 0 + 1 + D.degE + 2 + 4 + (k + 1) ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add h1.le h2))
          h3))
        h4))
      h5))
    h6)

/-- natDegree bound for correctionTerm1Scaled. -/
theorem correctionTerm1Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (correctionTerm1Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold correctionTerm1Scaled
  have h1 := DBdydzAtA₁Poly_natDegree_le E D
  have h2 : (DAtA₀Poly (E := E) D A₀).natDegree ≤ 0 :=
    (DAtA₀Poly_natDegree_le E D A₀).le
  have h3 := DAtA₂Scaled_natDegree_le E D A₀
  have h4 : (dxdzDenA₀Scaled (E := E) A₀).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (dxdzDenA₀Scaled_natDegree_lt_two E A₀)
  have h5 := dxdzDenA₂Scaled_natDegree_le E A₀
  have h6 := linesProductScaled_natDegree_le E P k B A₀
  refine le_trans ?_ (by omega : 0 + 0 + D.degE + 1 + 4 + (k + 1) ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add h1 h2))
          h3))
        h4))
      h5))
    h6)

/-- natDegree bound for correctionTerm2Scaled. -/
theorem correctionTerm2Scaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (correctionTerm2Scaled (E := E) D P k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold correctionTerm2Scaled
  have h1 := correctionA₂ScaledCore_natDegree_le E D A₀
  have h2 : (DAtA₀Poly (E := E) D A₀).natDegree ≤ 0 :=
    (DAtA₀Poly_natDegree_le E D A₀).le
  have h3 : (DAtA₁Poly (E := E) D).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (DAtA₁Poly_natDegree_lt_two E D)
  have h4 : (dxdzDenA₀Scaled (E := E) A₀).natDegree ≤ 1 :=
    Nat.le_of_lt_succ (dxdzDenA₀Scaled_natDegree_lt_two E A₀)
  have h5 := dxdzDenA₁Scaled_natDegree_le E A₀
  have h6 := linesProductScaled_natDegree_le E P k B A₀
  have h7 : (lamDenPoly (E := E) A₀ ^ 2).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, lamDenPoly_natDegree_le, Nat.mul_zero]
  have hbMain : 2 * D.b.natDegree + 4 ≤ D.degE + 3 := by
    have : 2 * D.b.natDegree + 3 ≤ D.degE := by
      unfold CoordRingElt.degE; omega
    omega
  refine le_trans ?_ (by omega : (D.degE + 3) + 0 + 1 + 1 + 2 + (k + 1) + 0
                                  ≤ D.degE + k + 8)
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add
            (natDegree_mul_le.trans (Nat.add_le_add (h1.trans hbMain) h2))
            h3))
          h4))
        h5))
      h6))
    h7.le)

theorem rhsTermNegPScaled_natDegree_le (D : CoordRingElt E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (rhsTermNegPScaled (E := E) D k B A₀).natDegree ≤ D.degE + k + 8 := by
  unfold rhsTermNegPScaled
  refine natDegree_mul_le.trans ?_
  have hD := DAllScaled_natDegree_le E D A₀
  have hdx := dxdzAllScaled_natDegree_le E A₀
  have hL := linesProductNoNegPScaled_natDegree_le E k B A₀
  have hmul : (DAllScaled (E := E) D A₀ * dxdzAllScaled (E := E) A₀).natDegree
              ≤ (D.degE + 1) + 7 :=
    natDegree_mul_le.trans (Nat.add_le_add hD hdx)
  exact (Nat.add_le_add hmul hL).trans (by omega)

theorem rhsSumScaled_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (m : Fin k → ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    (rhsSumScaled (E := E) D P k B m A₀).natDegree ≤ D.degE + k + 8 := by
  unfold rhsSumScaled
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  refine natDegree_mul_le.trans ?_
  have hmS : (embedScalar (E := E) (m j)).natDegree = 0 :=
    embedScalar_natDegree_le E _
  have hD := DAllScaled_natDegree_le E D A₀
  have hdx := dxdzAllScaled_natDegree_le E A₀
  have hL := linesProductSkipBjScaled_natDegree_le E P k B A₀ j
  have hmul2 : (embedScalar (E := E) (m j) * DAllScaled (E := E) D A₀).natDegree
               ≤ 0 + (D.degE + 1) := by
    refine natDegree_mul_le.trans ?_
    exact Nat.add_le_add hmS.le hD
  have hmul3 : (embedScalar (E := E) (m j) * DAllScaled (E := E) D A₀
                 * dxdzAllScaled (E := E) A₀).natDegree
               ≤ (0 + (D.degE + 1)) + 7 :=
    natDegree_mul_le.trans (Nat.add_le_add hmul2 hdx)
  exact (Nat.add_le_add hmul3 hL).trans (by omega)

/-- **main**: `clearedFiberPoly` has outer natDegree ≤ `D.degE + k + 8`. -/
theorem clearedFiberPoly_natDegree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (clearedFiberPoly (E := E) D P k B m A₀).natDegree ≤ D.degE + k + 8 := by
  unfold clearedFiberPoly
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact lhsTerm0Scaled_natDegree_le E D P k B A₀
  · exact lhsTerm1Scaled_natDegree_le E D P k B A₀
  · exact lhsTerm2Scaled_natDegree_le E D P k B A₀
  · exact correctionTerm0Scaled_natDegree_le E D P k B A₀
  · exact correctionTerm1Scaled_natDegree_le E D P k B A₀
  · exact correctionTerm2Scaled_natDegree_le E D P k B A₀
  · exact rhsTermNegPScaled_natDegree_le E D k B A₀
  · exact rhsSumScaled_natDegree_le E D P k B m A₀

/-! ## non-vanishing of `clearedFiberPoly %ₘ curveEqPoly`

    If there is at least one "good" `A₁` — non-vertical, with
    `logDerivCheckFn` defined and nonzero — then
    `clearedFiberPoly %ₘ curveEqPoly ≠ 0`. This is the hypothesis
    needed to apply `card_zeros_on_E_le` in T1's fiber count.

    Proof: if `clearedFiberPoly %ₘ curveEqPoly = 0` then
    `bivEval clearedFiberPoly A₁ = 0` on `E.points`. By the B3 identity
    `bivEval clearedFiberPoly A₁ = (A₁.1-A₀.1)^N · logDerivCheckFnCleared`,
    the LHS factor is nonzero (non-vertical) and `logDerivCheckFnDenom`
    is nonzero (defined), so `logDerivCheckFn = 0`, contradicting the
    "good" witness. -/

theorem clearedFiberPoly_modCurve_ne_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q)
    (hFiberNonzero : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    clearedFiberPoly (E := E) D P k B m A₀ %ₘ curveEqPoly E ≠ 0 := by
  obtain ⟨A₁, hA₁, hNV, hDef, hne⟩ := hFiberNonzero
  intro h_vanish
  have hBiv : bivEval (clearedFiberPoly (E := E) D P k B m A₀) A₁ = 0 := by
    rw [bivEval_eq_modByMonic_on_E E _ hA₁, h_vanish]
    unfold bivEval
    simp
  -- Apply B3 identity.
  rw [clearedFiberPoly_identity E D P B m A₀ A₁ hNV hDef] at hBiv
  -- Factor the product: (A₁.1-A₀.1)^N · logDerivCheckFn · denom = 0.
  have hlamNZ : (A₁.1 - A₀.1) ^ (D.degE + k + 6) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hNV))
  -- Unfold logDerivCheckFnCleared to get logDerivCheckFn · denom.
  unfold logDerivCheckFnCleared at hBiv
  -- Three-way factorization: (lamPow · (f · denom)) = 0.
  rw [show (A₁.1 - A₀.1) ^ (D.degE + k + 6)
          * (logDerivCheckFn E D P k B m A₀ A₁
             * logDerivCheckFnDenom E D P B A₀ A₁)
        = (A₁.1 - A₀.1) ^ (D.degE + k + 6)
            * (logDerivCheckFn E D P k B m A₀ A₁
               * logDerivCheckFnDenom E D P B A₀ A₁) from rfl] at hBiv
  rcases mul_eq_zero.mp hBiv with h | h
  · exact hlamNZ h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hne h'
    · exact hDef h'

/-! ## inner natDegree bookkeeping

    For `f : (ZMod E.q)[X][X]`, the "inner natDegree" is the maximum
    natDegree of its outer coefficients (each of which is a univariate
    polynomial in the inner variable). The predicate `InnerDegLe f m`
    says every `f.coeff i` has natDegree ≤ m.

    Combined with the outer natDegree bound `f.natDegree ≤ N`, this
    feeds a generic `resultantX f`.natDegree bound via the modByMonic
    structure of `f %ₘ curveEqPoly`.

    Inner bounds are tracked compositionally (add, sub, mul, pow,
    sum, prod) and applied to each component of `clearedFiberPoly`.
-/

section InnerDegBookkeeping
variable {E : ECSetup}

/-- All outer coefficients of `f` have inner natDegree ≤ `m`. -/
def InnerDegLe (f : (ZMod E.q)[X][X]) (m : ℕ) : Prop :=
  ∀ i, (f.coeff i).natDegree ≤ m

namespace InnerDegLe

theorem weaken {f : (ZMod E.q)[X][X]} {m n : ℕ}
    (hf : InnerDegLe (E := E) f m) (h : m ≤ n) :
    InnerDegLe (E := E) f n :=
  fun i => (hf i).trans h

theorem zero : InnerDegLe (E := E) (0 : (ZMod E.q)[X][X]) 0 :=
  fun _ => by simp

theorem one : InnerDegLe (E := E) (1 : (ZMod E.q)[X][X]) 0 := fun i => by
  rw [Polynomial.coeff_one]
  split <;> simp

theorem add {f g : (ZMod E.q)[X][X]} {m n : ℕ}
    (hf : InnerDegLe (E := E) f m) (hg : InnerDegLe (E := E) g n) :
    InnerDegLe (E := E) (f + g) (max m n) := fun i => by
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hf i) (hg i))

theorem sub {f g : (ZMod E.q)[X][X]} {m n : ℕ}
    (hf : InnerDegLe (E := E) f m) (hg : InnerDegLe (E := E) g n) :
    InnerDegLe (E := E) (f - g) (max m n) := fun i => by
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max (hf i) (hg i))

theorem neg {f : (ZMod E.q)[X][X]} {m : ℕ}
    (hf : InnerDegLe (E := E) f m) :
    InnerDegLe (E := E) (-f) m := fun i => by
  rw [Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hf i

theorem mul {f g : (ZMod E.q)[X][X]} {m n : ℕ}
    (hf : InnerDegLe (E := E) f m) (hg : InnerDegLe (E := E) g n) :
    InnerDegLe (E := E) (f * g) (m + n) := fun i => by
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  rintro ⟨a, b⟩ _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf a) (hg b))

theorem pow {f : (ZMod E.q)[X][X]} {m : ℕ}
    (hf : InnerDegLe (E := E) f m) (n : ℕ) :
    InnerDegLe (E := E) (f ^ n) (n * m) := by
  induction n with
  | zero => simp only [pow_zero, Nat.zero_mul]; exact one
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hf

theorem sum {α : Type*} (s : Finset α) (f : α → (ZMod E.q)[X][X]) (m : ℕ)
    (hf : ∀ a ∈ s, InnerDegLe (E := E) (f a) m) :
    InnerDegLe (E := E) (∑ a ∈ s, f a) m := fun i => by
  rw [Polynomial.finset_sum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro a ha
  exact hf a ha i

theorem prod {α : Type*} (s : Finset α) (f : α → (ZMod E.q)[X][X]) (ms : α → ℕ)
    (hf : ∀ a ∈ s, InnerDegLe (E := E) (f a) (ms a)) :
    InnerDegLe (E := E) (∏ a ∈ s, f a) (∑ a ∈ s, ms a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact one
  | @insert a s hmem ih =>
    rw [Finset.prod_insert hmem, Finset.sum_insert hmem]
    exact (hf _ (Finset.mem_insert_self _ _)).mul
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

end InnerDegLe

/-! ### Inner bounds for primitive embeddings. -/

theorem InnerDegLe_embedScalar (c : ZMod E.q) :
    InnerDegLe (E := E) (embedScalar (E := E) c) 0 := fun i => by
  unfold embedScalar
  rw [Polynomial.coeff_C]
  split <;> simp

theorem InnerDegLe_embedInnerPoly (p : (ZMod E.q)[X]) :
    InnerDegLe (E := E) (embedInnerPoly (E := E) p) p.natDegree := fun i => by
  unfold embedInnerPoly
  rw [Polynomial.coeff_C]
  split
  · exact le_refl _
  · simp

theorem InnerDegLe_innerA₁x : InnerDegLe (E := E) (innerA₁x (E := E)) 1 := fun i => by
  unfold innerA₁x
  rw [Polynomial.coeff_C]
  split
  · exact Polynomial.natDegree_X_le
  · simp

theorem InnerDegLe_outerA₁y : InnerDegLe (E := E) (outerA₁y (E := E)) 0 := fun i => by
  unfold outerA₁y
  rw [Polynomial.coeff_X]
  split <;> simp

/-! ### Inner bounds for lam, x₂, y₂, dxdz, line factors. -/

theorem InnerDegLe_lamNumPoly (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lamNumPoly (E := E) A₀) 0 := by
  unfold lamNumPoly
  exact (InnerDegLe_outerA₁y.sub (InnerDegLe_embedScalar _)).weaken (by simp)

theorem InnerDegLe_lamDenPoly (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lamDenPoly (E := E) A₀) 1 := by
  unfold lamDenPoly
  exact (InnerDegLe_innerA₁x.sub (InnerDegLe_embedScalar _)).weaken (by simp)

theorem InnerDegLe_lineEvalNumAt (A₀ pt : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lineEvalNumAt (E := E) A₀ pt) 1 := by
  unfold lineEvalNumAt
  exact (((InnerDegLe_embedScalar _).mul (InnerDegLe_lamDenPoly A₀)).sub
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_lamNumPoly A₀))).weaken (by simp)

theorem InnerDegLe_x₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (x₂Scaled (E := E) A₀) 3 := by
  unfold x₂Scaled
  have h1 : InnerDegLe (E := E) ((lamNumPoly (E := E) A₀) ^ 2) 0 :=
    ((InnerDegLe_lamNumPoly A₀).pow 2).weaken (by simp)
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) A₀.1 + innerA₁x (E := E)) 1 :=
    ((InnerDegLe_embedScalar _).add InnerDegLe_innerA₁x).weaken (by simp)
  have h3 : InnerDegLe (E := E) ((lamDenPoly (E := E) A₀) ^ 2) 2 :=
    (InnerDegLe_lamDenPoly A₀).pow 2
  have h4 : InnerDegLe (E := E) ((embedScalar (E := E) A₀.1 + innerA₁x (E := E))
                                  * (lamDenPoly (E := E) A₀) ^ 2) 3 := h2.mul h3
  exact (h1.sub h4).weaken (by simp)

theorem InnerDegLe_y₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (y₂Scaled (E := E) A₀) 3 := by
  unfold y₂Scaled
  have h1 : InnerDegLe (E := E) (lamNumPoly (E := E) A₀ * x₂Scaled (E := E) A₀) 3 :=
    (InnerDegLe_lamNumPoly A₀).mul (InnerDegLe_x₂Scaled A₀)
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀) 1 :=
    (InnerDegLe_embedScalar _).mul (InnerDegLe_lamDenPoly A₀)
  have h3 : InnerDegLe (E := E) (embedScalar (E := E) A₀.1 * lamNumPoly (E := E) A₀) 0 :=
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_lamNumPoly A₀)).weaken (by simp)
  have h4 : InnerDegLe (E := E) (embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀
                                  - embedScalar (E := E) A₀.1 * lamNumPoly (E := E) A₀) 1 :=
    (h2.sub h3).weaken (by simp)
  have h5 : InnerDegLe (E := E) (lamDenPoly (E := E) A₀ ^ 2) 2 :=
    (InnerDegLe_lamDenPoly A₀).pow 2
  have h6 : InnerDegLe (E := E) ((embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀
                                  - embedScalar (E := E) A₀.1 * lamNumPoly (E := E) A₀)
                                  * lamDenPoly (E := E) A₀ ^ 2) 3 := h4.mul h5
  have h7 : InnerDegLe (E := E)
      (lamNumPoly (E := E) A₀ * x₂Scaled (E := E) A₀
        + (embedScalar (E := E) A₀.2 * lamDenPoly (E := E) A₀
           - embedScalar (E := E) A₀.1 * lamNumPoly (E := E) A₀)
          * lamDenPoly (E := E) A₀ ^ 2) 3 :=
    (h1.add h6).weaken (by simp)
  exact h7

theorem InnerDegLe_dxdzDenA₀Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (dxdzDenA₀Scaled (E := E) A₀) 1 := by
  unfold dxdzDenA₀Scaled
  have h1 : InnerDegLe (E := E) (embedScalar (E := E) (3 * A₀.1 ^ 2 + E.curveA)
                                  * lamDenPoly (E := E) A₀) 1 :=
    (InnerDegLe_embedScalar _).mul (InnerDegLe_lamDenPoly A₀)
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) (2 * A₀.2)
                                  * lamNumPoly (E := E) A₀) 0 :=
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_lamNumPoly A₀)).weaken (by simp)
  exact (h1.sub h2).weaken (by simp)

theorem InnerDegLe_dxdzDenA₁Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (dxdzDenA₁Scaled (E := E) A₀) 3 := by
  unfold dxdzDenA₁Scaled
  have h1 : InnerDegLe (E := E) (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2) 2 :=
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_innerA₁x.pow 2)).weaken (by simp)
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
                                  + embedScalar (E := E) E.curveA) 2 :=
    (h1.add (InnerDegLe_embedScalar _)).weaken (by simp)
  have h3 : InnerDegLe (E := E) ((embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
                                  + embedScalar (E := E) E.curveA)
                                  * lamDenPoly (E := E) A₀) 3 :=
    h2.mul (InnerDegLe_lamDenPoly A₀)
  have h4 : InnerDegLe (E := E) (embedScalar (E := E) 2 * outerA₁y (E := E)) 0 :=
    ((InnerDegLe_embedScalar _).mul InnerDegLe_outerA₁y).weaken (by simp)
  have h5 : InnerDegLe (E := E) (embedScalar (E := E) 2 * outerA₁y (E := E)
                                  * lamNumPoly (E := E) A₀) 0 :=
    (h4.mul (InnerDegLe_lamNumPoly A₀)).weaken (by simp)
  exact (h3.sub h5).weaken (by simp)

theorem InnerDegLe_dxdzDenA₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (dxdzDenA₂Scaled (E := E) A₀) 6 := by
  unfold dxdzDenA₂Scaled
  have h1 : InnerDegLe (E := E) (embedScalar (E := E) 3 * (x₂Scaled (E := E) A₀) ^ 2) 6 :=
    ((InnerDegLe_embedScalar _).mul ((InnerDegLe_x₂Scaled A₀).pow 2)).weaken (by simp)
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) E.curveA
                                  * (lamDenPoly (E := E) A₀) ^ 4) 4 :=
    ((InnerDegLe_embedScalar _).mul ((InnerDegLe_lamDenPoly A₀).pow 4)).weaken (by simp)
  have h3 : InnerDegLe (E := E) (embedScalar (E := E) 3 * (x₂Scaled (E := E) A₀) ^ 2
                                  + embedScalar (E := E) E.curveA
                                    * (lamDenPoly (E := E) A₀) ^ 4) 6 :=
    (h1.add h2).weaken (by simp)
  have h4 : InnerDegLe (E := E) (embedScalar (E := E) 2 * lamNumPoly (E := E) A₀) 0 :=
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_lamNumPoly A₀)).weaken (by simp)
  have h5 : InnerDegLe (E := E) (embedScalar (E := E) 2 * lamNumPoly (E := E) A₀
                                  * y₂Scaled (E := E) A₀) 3 :=
    (h4.mul (InnerDegLe_y₂Scaled A₀)).weaken (by simp)
  exact (h3.sub h5).weaken (by simp)

/-! ### Inner bounds for D-evaluated polynomials. -/

theorem InnerDegLe_DAtA₀Poly (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DAtA₀Poly (E := E) D A₀) 0 := by
  unfold DAtA₀Poly
  exact InnerDegLe_embedScalar _

theorem InnerDegLe_DDerivAtA₀Poly (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DDerivAtA₀Poly (E := E) D A₀) 0 := by
  unfold DDerivAtA₀Poly
  exact InnerDegLe_embedScalar _

theorem InnerDegLe_DAtA₁Poly (D : CoordRingElt E.q) :
    InnerDegLe (E := E) (DAtA₁Poly (E := E) D) D.degE := by
  unfold DAtA₁Poly
  have h1 : InnerDegLe (E := E) (embedInnerPoly (E := E) D.a) D.a.natDegree :=
    InnerDegLe_embedInnerPoly _
  have h2 : InnerDegLe (E := E) (embedInnerPoly (E := E) D.b) D.b.natDegree :=
    InnerDegLe_embedInnerPoly _
  have h3 : InnerDegLe (E := E) (embedInnerPoly (E := E) D.b * outerA₁y (E := E))
                      D.b.natDegree := (h2.mul InnerDegLe_outerA₁y).weaken (by simp)
  have hDa : 2 * D.a.natDegree ≤ D.degE := le_max_left _ _
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  exact (h1.sub h3).weaken (by simp; omega)

theorem InnerDegLe_DDerivAtA₁Poly (D : CoordRingElt E.q) :
    InnerDegLe (E := E) (DDerivAtA₁Poly (E := E) D) D.degE := by
  unfold DDerivAtA₁Poly
  have h1 : InnerDegLe (E := E) (embedInnerPoly (E := E) (Polynomial.derivative D.a))
                      (Polynomial.derivative D.a).natDegree :=
    InnerDegLe_embedInnerPoly _
  have h2 : InnerDegLe (E := E) (embedInnerPoly (E := E) (Polynomial.derivative D.b))
                      (Polynomial.derivative D.b).natDegree :=
    InnerDegLe_embedInnerPoly _
  have h3 : InnerDegLe (E := E) (embedInnerPoly (E := E) (Polynomial.derivative D.b)
                                  * outerA₁y (E := E))
                      (Polynomial.derivative D.b).natDegree :=
    (h2.mul InnerDegLe_outerA₁y).weaken (by simp)
  have hdA : (Polynomial.derivative D.a).natDegree ≤ D.a.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hdB : (Polynomial.derivative D.b).natDegree ≤ D.b.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hDa : 2 * D.a.natDegree ≤ D.degE := le_max_left _ _
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  exact (h1.sub h3).weaken (by simp; omega)

theorem InnerDegLe_DAPartAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DAPartAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DAPartAtA₂Scaled
  refine InnerDegLe.sum _ _ _ ?_
  intro n hn
  have hn' : n ≤ D.a.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hDa : 2 * D.a.natDegree ≤ D.degE := le_max_left _ _
  have h1 := InnerDegLe_embedScalar (E := E) (D.a.coeff n)
  have h2 := (InnerDegLe_x₂Scaled (E := E) A₀).pow n
  have h3 := (InnerDegLe_lamDenPoly (E := E) A₀).pow (D.degE - 2 * n)
  exact ((h1.mul h2).mul h3).weaken (by omega)

theorem InnerDegLe_DBPartAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DBPartAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DBPartAtA₂Scaled
  refine InnerDegLe.sum _ _ _ ?_
  intro n hn
  have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  have h1 := InnerDegLe_embedScalar (E := E) (D.b.coeff n)
  have h2 := (InnerDegLe_x₂Scaled (E := E) A₀).pow n
  have h3 := InnerDegLe_y₂Scaled (E := E) A₀
  have h4 := (InnerDegLe_lamDenPoly (E := E) A₀).pow (D.degE - 2 * n - 3)
  exact (((h1.mul h2).mul h3).mul h4).weaken (by omega)

theorem InnerDegLe_DAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DAtA₂Scaled
  exact ((InnerDegLe_DAPartAtA₂Scaled D A₀).sub
    (InnerDegLe_DBPartAtA₂Scaled D A₀)).weaken (by simp)

theorem InnerDegLe_DDerivAPartAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DDerivAPartAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DDerivAPartAtA₂Scaled
  refine InnerDegLe.sum _ _ _ ?_
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.a).natDegree :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hdA : (Polynomial.derivative D.a).natDegree ≤ D.a.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hDa : 2 * D.a.natDegree ≤ D.degE := le_max_left _ _
  have h1 := InnerDegLe_embedScalar (E := E) ((Polynomial.derivative D.a).coeff n)
  have h2 := (InnerDegLe_x₂Scaled (E := E) A₀).pow n
  have h3 := (InnerDegLe_lamDenPoly (E := E) A₀).pow (D.degE - 2 * n)
  exact ((h1.mul h2).mul h3).weaken (by omega)

theorem InnerDegLe_DDerivBPartAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DDerivBPartAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DDerivBPartAtA₂Scaled
  refine InnerDegLe.sum _ _ _ ?_
  intro n hn
  have hn' : n ≤ (Polynomial.derivative D.b).natDegree :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hdB : (Polynomial.derivative D.b).natDegree ≤ D.b.natDegree :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  have h1 := InnerDegLe_embedScalar (E := E) ((Polynomial.derivative D.b).coeff n)
  have h2 := (InnerDegLe_x₂Scaled (E := E) A₀).pow n
  have h3 := InnerDegLe_y₂Scaled (E := E) A₀
  have h4 := (InnerDegLe_lamDenPoly (E := E) A₀).pow (D.degE - 2 * n - 3)
  exact (((h1.mul h2).mul h3).mul h4).weaken (by omega)

theorem InnerDegLe_DDerivAtA₂Scaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DDerivAtA₂Scaled (E := E) D A₀) (2 * D.degE) := by
  unfold DDerivAtA₂Scaled
  exact ((InnerDegLe_DDerivAPartAtA₂Scaled D A₀).sub
    (InnerDegLe_DDerivBPartAtA₂Scaled D A₀)).weaken (by simp)

/-! ### Inner bounds for line products, dxdzAll, DAll. -/

theorem InnerDegLe_linesProductScaled (P : ZMod E.q × ZMod E.q) (k : ℕ)
    (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (linesProductScaled (E := E) P k B A₀) (k + 1) := by
  unfold linesProductScaled
  have h1 := InnerDegLe_lineEvalNumAt (E := E) A₀ (P.1, -P.2)
  have hp := InnerDegLe.prod (Finset.univ : Finset (Fin k))
    (fun j => lineEvalNumAt (E := E) A₀ (B j)) (fun _ => 1)
    (fun j _ => InnerDegLe_lineEvalNumAt A₀ (B j))
  have h2 : InnerDegLe (E := E) (∏ j : Fin k, lineEvalNumAt (E := E) A₀ (B j)) k :=
    hp.weaken (by simp)
  exact (h1.mul h2).weaken (by omega)

theorem InnerDegLe_linesProductNoNegPScaled (k : ℕ)
    (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (linesProductNoNegPScaled (E := E) k B A₀) k := by
  unfold linesProductNoNegPScaled
  have hp := InnerDegLe.prod (Finset.univ : Finset (Fin k))
    (fun j => lineEvalNumAt (E := E) A₀ (B j)) (fun _ => 1)
    (fun j _ => InnerDegLe_lineEvalNumAt A₀ (B j))
  exact hp.weaken (by simp)

theorem InnerDegLe_linesProductSkipBjScaled (P : ZMod E.q × ZMod E.q) (k : ℕ)
    (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) (j₀ : Fin k) :
    InnerDegLe (E := E) (linesProductSkipBjScaled (E := E) P k B A₀ j₀) k := by
  unfold linesProductSkipBjScaled
  have h1 := InnerDegLe_lineEvalNumAt (E := E) A₀ (P.1, -P.2)
  have hp := InnerDegLe.prod ((Finset.univ (α := Fin k)).erase j₀)
    (fun j => lineEvalNumAt (E := E) A₀ (B j)) (fun _ => 1)
    (fun j _ => InnerDegLe_lineEvalNumAt A₀ (B j))
  have hsum : ∑ _j ∈ (Finset.univ (α := Fin k)).erase j₀, (1 : ℕ) = k - 1 := by
    simp [Finset.card_erase_of_mem]
  have h2 : InnerDegLe (E := E)
      (∏ j ∈ (Finset.univ (α := Fin k)).erase j₀, lineEvalNumAt (E := E) A₀ (B j))
      (k - 1) := by rw [← hsum]; exact hp
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact Fin.elim0 j₀
    · exact hk
  exact (h1.mul h2).weaken (by omega)

theorem InnerDegLe_DAllScaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DAllScaled (E := E) D A₀) (3 * D.degE) := by
  unfold DAllScaled
  have h1 := InnerDegLe_DAtA₀Poly D A₀
  have h2 := InnerDegLe_DAtA₁Poly (E := E) D
  have h3 := InnerDegLe_DAtA₂Scaled D A₀
  exact ((h1.mul h2).mul h3).weaken (by omega)

theorem InnerDegLe_dxdzAllScaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (dxdzAllScaled (E := E) A₀) 10 := by
  unfold dxdzAllScaled
  have h1 := InnerDegLe_dxdzDenA₀Scaled A₀
  have h2 := InnerDegLe_dxdzDenA₁Scaled A₀
  have h3 := InnerDegLe_dxdzDenA₂Scaled A₀
  exact ((h1.mul h2).mul h3).weaken (by omega)

/-! ### Inner bounds for Session-39 correction polynomials. -/

theorem InnerDegLe_DBdydzAtA₀Poly (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DBdydzAtA₀Poly (E := E) D A₀) 0 := by
  unfold DBdydzAtA₀Poly
  exact InnerDegLe_embedScalar _

theorem InnerDegLe_DBdydzAtA₁Poly (D : CoordRingElt E.q) :
    InnerDegLe (E := E) (DBdydzAtA₁Poly (E := E) D) (D.b.natDegree + 2) := by
  unfold DBdydzAtA₁Poly
  have h1 : InnerDegLe (E := E) (- embedInnerPoly (E := E) D.b) D.b.natDegree :=
    (InnerDegLe_embedInnerPoly D.b).neg
  have h2A : InnerDegLe (E := E) (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2) 2 := by
    have := ((InnerDegLe_embedScalar (E := E) 3).mul
              (InnerDegLe.pow (InnerDegLe_innerA₁x (E := E)) 2))
    exact this.weaken (by simp)
  have h2B : InnerDegLe (E := E) (embedScalar (E := E) E.curveA) 2 :=
    (InnerDegLe_embedScalar _).weaken (Nat.zero_le _)
  have h2 : InnerDegLe (E := E)
      (embedScalar (E := E) 3 * innerA₁x (E := E) ^ 2
        + embedScalar (E := E) E.curveA) 2 :=
    (h2A.add h2B).weaken (by simp)
  exact h1.mul h2

theorem InnerDegLe_DbAtA₂TightScaled (D : CoordRingElt E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (DbAtA₂TightScaled (E := E) D A₀) (3 * D.b.natDegree) := by
  unfold DbAtA₂TightScaled
  refine InnerDegLe.sum _ _ _ ?_
  intro n hn
  have hn' : n ≤ D.b.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have h1 := InnerDegLe_embedScalar (E := E) (D.b.coeff n)
  have h2 : InnerDegLe (E := E) (x₂Scaled (E := E) A₀ ^ n) (n * 3) :=
    InnerDegLe.pow (InnerDegLe_x₂Scaled A₀) n
  have h3 : InnerDegLe (E := E) (lamDenPoly (E := E) A₀ ^ (2 * D.b.natDegree - 2 * n))
                      ((2 * D.b.natDegree - 2 * n) * 1) :=
    InnerDegLe.pow (InnerDegLe_lamDenPoly A₀) _
  refine (((h1.mul h2).mul h3)).weaken ?_
  omega

theorem InnerDegLe_dydzNumA₂Scaled (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (dydzNumA₂Scaled (E := E) A₀) 6 := by
  unfold dydzNumA₂Scaled
  have hA : InnerDegLe (E := E) (embedScalar (E := E) 3 * x₂Scaled (E := E) A₀ ^ 2) 6 := by
    have h1 := InnerDegLe_embedScalar (E := E) 3
    have h2 := InnerDegLe.pow (InnerDegLe_x₂Scaled A₀) 2
    exact (h1.mul h2).weaken (by omega)
  have hB : InnerDegLe (E := E)
      (embedScalar (E := E) E.curveA * lamDenPoly (E := E) A₀ ^ 4) 6 := by
    have h1 := InnerDegLe_embedScalar (E := E) E.curveA
    have h2 := InnerDegLe.pow (InnerDegLe_lamDenPoly A₀) 4
    exact (h1.mul h2).weaken (by omega)
  exact (hA.add hB).weaken (by simp)

theorem InnerDegLe_correctionA₂ScaledCore (D : CoordRingElt E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (correctionA₂ScaledCore (E := E) D A₀)
                        (3 * D.b.natDegree + 6 + (D.degE - 2 * D.b.natDegree - 3)) := by
  unfold correctionA₂ScaledCore
  have h1 := (InnerDegLe_DbAtA₂TightScaled D A₀).neg
  have h2 := InnerDegLe_dydzNumA₂Scaled (E := E) A₀
  have h3 := InnerDegLe.pow (InnerDegLe_lamDenPoly A₀) (D.degE - 2 * D.b.natDegree - 3)
  exact ((h1.mul h2).mul h3).weaken (by omega)

/-! ### Inner bounds for clearedFiberPoly summands. -/

theorem InnerDegLe_lhsTerm0Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lhsTerm0Scaled (E := E) D P k B A₀) (3 * D.degE + k + 10) := by
  unfold lhsTerm0Scaled
  have h1 := InnerDegLe_DDerivAtA₀Poly D A₀
  have h2 := InnerDegLe_embedScalar (E := E) (2 * A₀.2)
  have h3 := InnerDegLe_DAtA₁Poly (E := E) D
  have h4 := InnerDegLe_DAtA₂Scaled D A₀
  have h5 := InnerDegLe_dxdzDenA₁Scaled A₀
  have h6 := InnerDegLe_dxdzDenA₂Scaled A₀
  have h7 := InnerDegLe_linesProductScaled P k B A₀
  exact ((((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).mul h7).weaken (by omega)

theorem InnerDegLe_lhsTerm1Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lhsTerm1Scaled (E := E) D P k B A₀) (3 * D.degE + k + 10) := by
  unfold lhsTerm1Scaled
  have h1 := InnerDegLe_DDerivAtA₁Poly (E := E) D
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) 2 * outerA₁y (E := E)) 0 :=
    ((InnerDegLe_embedScalar _).mul InnerDegLe_outerA₁y).weaken (by simp)
  have h3 := InnerDegLe_DAtA₀Poly D A₀
  have h4 := InnerDegLe_DAtA₂Scaled D A₀
  have h5 := InnerDegLe_dxdzDenA₀Scaled A₀
  have h6 := InnerDegLe_dxdzDenA₂Scaled A₀
  have h7 := InnerDegLe_linesProductScaled P k B A₀
  exact ((((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).mul h7).weaken (by omega)

theorem InnerDegLe_lhsTerm2Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (lhsTerm2Scaled (E := E) D P k B A₀) (3 * D.degE + k + 10) := by
  unfold lhsTerm2Scaled
  have h1 := InnerDegLe_DDerivAtA₂Scaled D A₀
  have h2 : InnerDegLe (E := E) (embedScalar (E := E) 2 * y₂Scaled (E := E) A₀) 3 :=
    ((InnerDegLe_embedScalar _).mul (InnerDegLe_y₂Scaled A₀)).weaken (by simp)
  have h3 := InnerDegLe_DAtA₀Poly D A₀
  have h4 := InnerDegLe_DAtA₁Poly (E := E) D
  have h5 := InnerDegLe_dxdzDenA₀Scaled A₀
  have h6 := InnerDegLe_dxdzDenA₁Scaled A₀
  have h7 := InnerDegLe_linesProductScaled P k B A₀
  exact ((((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).mul h7).weaken (by omega)

theorem InnerDegLe_rhsTermNegPScaled (D : CoordRingElt E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (rhsTermNegPScaled (E := E) D k B A₀) (3 * D.degE + k + 10) := by
  unfold rhsTermNegPScaled
  have h1 := InnerDegLe_DAllScaled D A₀
  have h2 := InnerDegLe_dxdzAllScaled (E := E) A₀
  have h3 := InnerDegLe_linesProductNoNegPScaled k B A₀
  exact ((h1.mul h2).mul h3).weaken (by omega)

theorem InnerDegLe_rhsSumScaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (rhsSumScaled (E := E) D P k B m A₀) (3 * D.degE + k + 10) := by
  unfold rhsSumScaled
  refine InnerDegLe.sum _ _ _ ?_
  intro j _
  have h1 := InnerDegLe_embedScalar (E := E) (m j)
  have h2 := InnerDegLe_DAllScaled D A₀
  have h3 := InnerDegLe_dxdzAllScaled (E := E) A₀
  have h4 := InnerDegLe_linesProductSkipBjScaled P k B A₀ j
  exact (((h1.mul h2).mul h3).mul h4).weaken (by omega)

theorem InnerDegLe_correctionTerm0Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (correctionTerm0Scaled (E := E) D P k B A₀)
        (3 * D.degE + k + 10) := by
  unfold correctionTerm0Scaled
  have h1 := InnerDegLe_DBdydzAtA₀Poly D A₀
  have h2 := InnerDegLe_DAtA₁Poly (E := E) D
  have h3 := InnerDegLe_DAtA₂Scaled D A₀
  have h4 := InnerDegLe_dxdzDenA₁Scaled A₀
  have h5 := InnerDegLe_dxdzDenA₂Scaled A₀
  have h6 := InnerDegLe_linesProductScaled P k B A₀
  exact (((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).weaken (by omega)

theorem InnerDegLe_correctionTerm1Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (correctionTerm1Scaled (E := E) D P k B A₀)
        (3 * D.degE + k + 10) := by
  unfold correctionTerm1Scaled
  have h1 := InnerDegLe_DBdydzAtA₁Poly (E := E) D
  have h2 := InnerDegLe_DAtA₀Poly D A₀
  have h3 := InnerDegLe_DAtA₂Scaled D A₀
  have h4 := InnerDegLe_dxdzDenA₀Scaled A₀
  have h5 := InnerDegLe_dxdzDenA₂Scaled A₀
  have h6 := InnerDegLe_linesProductScaled P k B A₀
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  exact (((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).weaken (by omega)

theorem InnerDegLe_correctionTerm2Scaled (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (correctionTerm2Scaled (E := E) D P k B A₀)
        (3 * D.degE + k + 10) := by
  unfold correctionTerm2Scaled
  have h1 := InnerDegLe_correctionA₂ScaledCore D A₀
  have h2 := InnerDegLe_DAtA₀Poly D A₀
  have h3 := InnerDegLe_DAtA₁Poly (E := E) D
  have h4 := InnerDegLe_dxdzDenA₀Scaled A₀
  have h5 := InnerDegLe_dxdzDenA₁Scaled A₀
  have h6 := InnerDegLe_linesProductScaled P k B A₀
  have h7 := InnerDegLe.pow (InnerDegLe_lamDenPoly A₀) 2
  have hDb : 3 + 2 * D.b.natDegree ≤ D.degE := le_max_right _ _
  exact ((((((h1.mul h2).mul h3).mul h4).mul h5).mul h6).mul h7).weaken (by omega)

/-! ### Inner bound for `clearedFiberPoly`. -/

theorem InnerDegLe_clearedFiberPoly (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (clearedFiberPoly (E := E) D P k B m A₀)
              (3 * D.degE + k + 10) := by
  unfold clearedFiberPoly
  have h0 := InnerDegLe_lhsTerm0Scaled (E := E) D P k B A₀
  have h1 := InnerDegLe_lhsTerm1Scaled (E := E) D P k B A₀
  have h2 := InnerDegLe_lhsTerm2Scaled (E := E) D P k B A₀
  have hC0 := InnerDegLe_correctionTerm0Scaled (E := E) D P k B A₀
  have hC1 := InnerDegLe_correctionTerm1Scaled (E := E) D P k B A₀
  have hC2 := InnerDegLe_correctionTerm2Scaled (E := E) D P k B A₀
  have h3 := InnerDegLe_rhsTermNegPScaled (E := E) D k B A₀
  have h4 := InnerDegLe_rhsSumScaled (E := E) D P k B m A₀
  exact ((((((((h0.add h1).add h2).add hC0).add hC1).add hC2).add h3).add h4)).weaken (by simp)

/-! ### Inner bound on mod-by-curveEqPoly.

    Reducing `f ∈ R[X][Y]` mod the curve equation `Y² - curveX` replaces
    each `Y^{2k}` by `curveX^k` and each `Y^{2k+1}` by `Y · curveX^k`.
    Since `curveX.natDegree ≤ 3`, each reduction step grows the inner
    degree by at most 3. The total growth is ≤ `3 · ⌈f.natDegree/2⌉`.

    Proved by induction on `k`, where `2k+1 ≥ f.natDegree`. Each step
    kills the top two outer powers (X^N and X^{N-1}) by subtracting
    `C(f.coeff N) · X^{N-2} · curveEqPoly` and analogous for N-1,
    adding at most 3 to the inner bound. -/

/-- `(p + q · m) %ₘ m = p %ₘ m` when `m` is monic. -/
private lemma add_mul_monic_modByMonic_aux {R : Type*} [CommRing R] [Nontrivial R]
    {m : R[X]} (hm : m.Monic) (p q : R[X]) :
    (p + q * m) %ₘ m = p %ₘ m := by
  apply (Polynomial.div_modByMonic_unique (q + p /ₘ m) (p %ₘ m) hm ?_).2
  refine ⟨?_, Polynomial.degree_modByMonic_lt p hm⟩
  have h1 := Polynomial.modByMonic_add_div p hm
  calc (p %ₘ m) + m * (q + p /ₘ m)
      = m * q + ((p %ₘ m) + m * (p /ₘ m)) := by ring
    _ = m * q + p := by rw [h1]
    _ = p + q * m := by ring

/-- Inner bound for `curveEqPoly E = X² - C (curveX E)`: inner ≤ 3. -/
theorem InnerDegLe_curveEqPoly : InnerDegLe (E := E) (curveEqPoly E) 3 := by
  unfold curveEqPoly
  have hX2 : InnerDegLe (E := E) ((X : (ZMod E.q)[X][X]) ^ 2) 0 := by
    intro i
    simp only [Polynomial.coeff_X_pow]
    split <;> simp
  have hCurveX : InnerDegLe (E := E) (C (curveX E) : (ZMod E.q)[X][X]) 3 :=
    (InnerDegLe_embedInnerPoly (E := E) (curveX E)).weaken
      (curveX_natDegree_le_three E)
  exact (hX2.sub hCurveX).weaken (by simp)

/-- Inner bound for `X^n` in `R[X][X]`: inner ≤ 0 (coefficients are 0 or 1). -/
theorem InnerDegLe_Xpow (n : ℕ) :
    InnerDegLe (E := E) ((X : (ZMod E.q)[X][X]) ^ n) 0 := by
  intro i
  simp only [Polynomial.coeff_X_pow]
  split <;> simp

/-- Inner bound for `C c * X^n * curveEqPoly E`: inner ≤ c.natDegree + 3. -/
theorem InnerDegLe_C_mul_Xpow_mul_curveEqPoly (c : (ZMod E.q)[X]) (n : ℕ) :
    InnerDegLe (E := E) (C c * X ^ n * curveEqPoly E) (c.natDegree + 3) := by
  have hC : InnerDegLe (E := E) (C c : (ZMod E.q)[X][X]) c.natDegree :=
    InnerDegLe_embedInnerPoly (E := E) c
  have hXn : InnerDegLe (E := E) ((X : (ZMod E.q)[X][X]) ^ n) 0 :=
    InnerDegLe_Xpow n
  have hCurve : InnerDegLe (E := E) (curveEqPoly E) 3 := InnerDegLe_curveEqPoly (E := E)
  exact ((hC.mul hXn).mul hCurve).weaken (by omega)

/-- **Inner bound for mod-by-curveEqPoly.** If `f.natDegree ≤ 2k+1` and
    all outer coefficients of `f` have inner natDegree ≤ M, then the outer
    coefficients of `f %ₘ curveEqPoly E` have inner natDegree ≤ M + 3k. -/
theorem InnerDegLe_modByMonic_curveEqPoly (f : (ZMod E.q)[X][X]) (M k : ℕ)
    (hM : InnerDegLe (E := E) f M) (hN : f.natDegree ≤ 2 * k + 1) :
    InnerDegLe (E := E) (f %ₘ curveEqPoly E) (M + 3 * k) := by
  induction k generalizing f M with
  | zero =>
    -- Base: f.natDegree ≤ 1 < 2, so f %ₘ curveEq = f.
    have hself : f %ₘ curveEqPoly E = f := by
      by_cases hfz : f = 0
      · rw [hfz, Polynomial.zero_modByMonic]
      · apply (Polynomial.modByMonic_eq_self_iff (curveEqPoly_monic E)).mpr
        rw [Polynomial.degree_eq_natDegree hfz,
            Polynomial.degree_eq_natDegree (curveEqPoly_monic E).ne_zero,
            curveEqPoly_natDegree_eq]
        exact_mod_cast (show f.natDegree < 2 by omega)
    rw [hself]
    simpa using hM
  | succ k ih =>
    -- hN : f.natDegree ≤ 2 * (k + 1) + 1 = 2k+3. Set N := 2k+3.
    set N := 2 * (k + 1) + 1 with hNdef
    have hN2_sub : N - 2 + 2 = N := by omega
    have hN3_sub : N - 3 + 2 = N - 1 := by omega
    -- Define the reduction step.
    set cN := f.coeff N
    set cNm1 := f.coeff (N - 1)
    set A : (ZMod E.q)[X][X] := C cN * X ^ (N - 2) * curveEqPoly E with hAdef
    set B : (ZMod E.q)[X][X] := C cNm1 * X ^ (N - 3) * curveEqPoly E with hBdef
    set g := f - A - B with hgdef
    -- (1) InnerDegLe g (M + 3)
    have hInner_A : InnerDegLe (E := E) A (M + 3) := by
      have := InnerDegLe_C_mul_Xpow_mul_curveEqPoly (E := E) cN (N - 2)
      exact this.weaken (by
        have : cN.natDegree ≤ M := hM N
        omega)
    have hInner_B : InnerDegLe (E := E) B (M + 3) := by
      have := InnerDegLe_C_mul_Xpow_mul_curveEqPoly (E := E) cNm1 (N - 3)
      exact this.weaken (by
        have : cNm1.natDegree ≤ M := hM (N - 1)
        omega)
    have hInner_g : InnerDegLe (E := E) g (M + 3) := by
      have := ((hM.weaken (by omega : M ≤ M + 3)).sub hInner_A).sub hInner_B
      exact this.weaken (by simp)
    -- (2) g.natDegree ≤ 2k+1 = N-2.
    -- Compute A and B's coefficients explicitly.
    have hA_eq : A = C cN * X ^ N - C (cN * curveX E) * X ^ (N - 2) := by
      simp only [hAdef, curveEqPoly, mul_sub]
      congr 1
      · rw [mul_assoc, ← pow_add, hN2_sub]
      · rw [show C cN * X ^ (N - 2) * C (curveX E) = C (cN * curveX E) * X ^ (N - 2) by
              rw [C_mul]; ring]
    have hB_eq : B = C cNm1 * X ^ (N - 1) - C (cNm1 * curveX E) * X ^ (N - 3) := by
      simp only [hBdef, curveEqPoly, mul_sub]
      congr 1
      · rw [mul_assoc, ← pow_add, hN3_sub]
      · rw [show C cNm1 * X ^ (N - 3) * C (curveX E) = C (cNm1 * curveX E) * X ^ (N - 3) by
              rw [C_mul]; ring]
    -- Coefficient of g at indices ≥ N-1 are zero; g.natDegree ≤ N - 2.
    have hg_nd : g.natDegree ≤ 2 * k + 1 := by
      have hNrel : 2 * k + 1 = N - 2 := by omega
      rw [hNrel]
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro i hi
      -- hi : N - 2 < i
      simp only [hgdef, hA_eq, hB_eq, Polynomial.coeff_sub,
                 Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h_iN : i = N
      · -- i = N: A's X^N term contributes cN; everything else cancels f.coeff N.
        subst h_iN
        have hne1 : ¬ (N = N - 1) := by omega
        have hne2 : ¬ (N = N - 2) := by omega
        have hne3 : ¬ (N = N - 3) := by omega
        have hN_self : (N = N) := rfl
        simp only [hne1, hne2, hne3, hN_self, if_true, if_false,
                   mul_one, mul_zero]
        show cN - (cN - 0) - (0 - 0) = 0
        ring
      · by_cases h_iNm1 : i = N - 1
        · -- i = N - 1: B's X^(N-1) term contributes cNm1; cancels f.coeff (N-1).
          subst h_iNm1
          have hne0 : ¬ (N - 1 = N) := by omega
          have hne2 : ¬ (N - 1 = N - 2) := by omega
          have hne3 : ¬ (N - 1 = N - 3) := by omega
          have h_self : (N - 1 = N - 1) := rfl
          simp only [hne0, hne2, hne3, h_self, if_true, if_false,
                     mul_one, mul_zero]
          show cNm1 - (0 - 0) - (cNm1 - 0) = 0
          ring
        · -- i ∉ {N, N-1} and i > N-2 ⇒ i > N.
          have hi_gt : i > N := by omega
          have hfi : f.coeff i = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
          have hne2 : ¬ (i = N - 2) := by omega
          have hne3 : ¬ (i = N - 3) := by omega
          simp only [hfi, h_iN, h_iNm1, hne2, hne3, if_false, mul_zero, sub_zero]
    -- (3) f %ₘ curveEq = g %ₘ curveEq.
    have hMod : f %ₘ curveEqPoly E = g %ₘ curveEqPoly E := by
      have hfeq : f = g + (C cN * X ^ (N - 2) + C cNm1 * X ^ (N - 3)) * curveEqPoly E := by
        simp only [hgdef, hAdef, hBdef]
        ring
      rw [hfeq]
      exact add_mul_monic_modByMonic_aux (curveEqPoly_monic E) g _
    rw [hMod]
    have := ih g (M + 3) hInner_g hg_nd
    exact this.weaken (by omega)

end InnerDegBookkeeping

/-! ### From InnerDegLe to `xPart`/`yPart`/`resultantX` bounds.

    Applying `InnerDegLe_modByMonic_curveEqPoly` gives the inner bound
    for `f %ₘ curveEqPoly`. Since `xPart` and `yPart` of a polynomial
    with outer natDegree < 2 are just its outer coefficients 0 and 1,
    their natDegrees are bounded by the InnerDegLe value. The
    `resultantX` bound is `2·M' + 3` where `M'` is the mod'd inner bound. -/

/-- Bound the natDegree of `xPart (f %ₘ curveEqPoly E)` via InnerDegLe. -/
theorem xPart_modByMonic_curveEqPoly_natDegree_le
    (f : (ZMod E.q)[X][X]) (M k : ℕ)
    (hM : InnerDegLe (E := E) f M) (hN : f.natDegree ≤ 2 * k + 1) :
    (xPart E (f %ₘ curveEqPoly E)).natDegree ≤ M + 3 * k :=
  InnerDegLe_modByMonic_curveEqPoly (E := E) f M k hM hN 0

/-- Bound the natDegree of `yPart (f %ₘ curveEqPoly E)` via InnerDegLe. -/
theorem yPart_modByMonic_curveEqPoly_natDegree_le
    (f : (ZMod E.q)[X][X]) (M k : ℕ)
    (hM : InnerDegLe (E := E) f M) (hN : f.natDegree ≤ 2 * k + 1) :
    (yPart E (f %ₘ curveEqPoly E)).natDegree ≤ M + 3 * k :=
  InnerDegLe_modByMonic_curveEqPoly (E := E) f M k hM hN 1

/-- **Generic `resultantX` natDegree bound** from InnerDegLe and outer degree. -/
theorem resultantX_natDegree_le_of_InnerDegLe
    (f : (ZMod E.q)[X][X]) (M k : ℕ)
    (hM : InnerDegLe (E := E) f M) (hN : f.natDegree ≤ 2 * k + 1) :
    (resultantX E f).natDegree ≤ 2 * (M + 3 * k) + 3 := by
  unfold resultantX
  have hX : (xPart E (f %ₘ curveEqPoly E)).natDegree ≤ M + 3 * k :=
    xPart_modByMonic_curveEqPoly_natDegree_le (E := E) f M k hM hN
  have hY : (yPart E (f %ₘ curveEqPoly E)).natDegree ≤ M + 3 * k :=
    yPart_modByMonic_curveEqPoly_natDegree_le (E := E) f M k hM hN
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · -- (xPart _)^2.natDegree ≤ 2 · (M + 3k)
    rw [Polynomial.natDegree_pow]
    calc 2 * (xPart E (f %ₘ curveEqPoly E)).natDegree
        ≤ 2 * (M + 3 * k) := Nat.mul_le_mul_left 2 hX
      _ ≤ 2 * (M + 3 * k) + 3 := Nat.le_add_right _ _
  · -- ((yPart _)^2 * curveX E).natDegree ≤ 2 * (M + 3k) + 3
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_pow]
    calc 2 * (yPart E (f %ₘ curveEqPoly E)).natDegree + (curveX E).natDegree
        ≤ 2 * (M + 3 * k) + 3 :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 hY) (curveX_natDegree_le_three E)

/-- **Resultant bound for `clearedFiberPoly`.** Bounded by `9·D.degE + 5k + 50`.
    This feeds T1's fiber bound: `2·(9D+5k+50) + 2 = 18D+10k+102 ≤ 18·(D+k+6)+2`. -/
theorem resultantX_clearedFiberPoly_natDegree_le
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (clearedFiberPoly (E := E) D P k B m A₀)).natDegree
      ≤ 9 * D.degE + 5 * k + 50 := by
  -- Inner M = 3·D.degE + k + 10, outer N ≤ D.degE + k + 8.
  -- Choose k_ind = (N + 1) / 2; then 2·k_ind + 1 ≥ N.
  set N := D.degE + k + 8 with hNdef
  set M := 3 * D.degE + k + 10 with hMdef
  set k_ind := (N + 1) / 2 with hkIndDef
  have hNcon : (clearedFiberPoly (E := E) D P k B m A₀).natDegree ≤ 2 * k_ind + 1 := by
    have hfn : (clearedFiberPoly (E := E) D P k B m A₀).natDegree ≤ N :=
      clearedFiberPoly_natDegree_le (E := E) D P B m A₀
    have h2k : 2 * k_ind + 1 ≥ N := by
      simp only [hkIndDef]
      omega
    omega
  have hM_cfp : InnerDegLe (E := E) (clearedFiberPoly (E := E) D P k B m A₀) M :=
    InnerDegLe_clearedFiberPoly (E := E) D P k B m A₀
  have hRes := resultantX_natDegree_le_of_InnerDegLe (E := E)
                (clearedFiberPoly (E := E) D P k B m A₀) M k_ind hM_cfp hNcon
  refine hRes.trans ?_
  have hki : 2 * k_ind ≤ N + 1 := by simp only [hkIndDef]; omega
  -- 2·(M + 3·k_ind) + 3 ≤ 2M + 3(N+1) + 3.
  have : 2 * (M + 3 * k_ind) + 3 ≤ 2 * M + 3 * (N + 1) + 3 := by
    have : 6 * k_ind ≤ 3 * (N + 1) := by omega
    omega
  refine this.trans ?_
  -- 2M + 3(N+1) + 3 = 2·(3D+k+10) + 3·(D+k+9) + 3 = 9D+5k+50.
  simp only [hMdef, hNdef]
  omega

/-! ## `denomScaledPoly`: polynomial witness for the `logDerivCheckFnDenom`
      zero-set slice. Used together with `clearedFiberPoly` to bound `bad_A₀_set`
      in T2 via a role-swap argument. -/

/-- Polynomial encoding of the full `logDerivCheckFnDenom` after clearing
    slope inverses. On the non-vertical cone, its `bivEval` equals
    `(A₁.1 - A₀.1)^(D.degE+k+7) · logDerivCheckFnDenom E D P B A₀ A₁`. -/
noncomputable def denomScaledPoly (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) : (ZMod E.q)[X][X] :=
  DAllScaled (E := E) D A₀
    * dxdzAllScaled (E := E) A₀
    * linesProductScaled (E := E) P k B A₀

theorem bivEval_denomScaledPoly_eq (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ A₁ : ZMod E.q × ZMod E.q) (hNV : A₀.1 ≠ A₁.1) :
    bivEval (denomScaledPoly (E := E) D P k B A₀) A₁
      = (A₁.1 - A₀.1) ^ (D.degE + k + 7) *
          logDerivCheckFnDenom E D P B A₀ A₁ := by
  unfold denomScaledPoly
  rw [bivEval_mul, bivEval_mul,
      bivEval_DAllScaled_eq E D A₀ A₁ hNV,
      bivEval_dxdzAllScaled_eq E A₀ A₁ hNV,
      bivEval_linesProductScaled_eq E P k B A₀ A₁ hNV,
      logDerivCheckFnDenom_eq_explicit]
  have hpow : (A₁.1 - A₀.1) ^ (D.degE + k + 7)
            = (A₁.1 - A₀.1) ^ D.degE * (A₁.1 - A₀.1) ^ 6
              * (A₁.1 - A₀.1) ^ (k + 1) := by
    rw [show D.degE + k + 7 = D.degE + 6 + (k + 1) from by omega,
        pow_add, pow_add]
  rw [hpow]; ring

theorem denomScaledPoly_natDegree_le (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    (denomScaledPoly (E := E) D P k B A₀).natDegree ≤ D.degE + k + 9 := by
  unfold denomScaledPoly
  have h1 := DAllScaled_natDegree_le E D A₀
  have h2 := dxdzAllScaled_natDegree_le E A₀
  have h3 := linesProductScaled_natDegree_le E P k B A₀
  refine natDegree_mul_le.trans ?_
  refine (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add h1 h2)) h3).trans ?_
  omega

theorem InnerDegLe_denomScaledPoly (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q) :
    InnerDegLe (E := E) (denomScaledPoly (E := E) D P k B A₀)
              (3 * D.degE + k + 11) := by
  unfold denomScaledPoly
  have h1 := InnerDegLe_DAllScaled (E := E) D A₀
  have h2 := InnerDegLe_dxdzAllScaled (E := E) A₀
  have h3 := InnerDegLe_linesProductScaled (E := E) P k B A₀
  exact ((h1.mul h2).mul h3).weaken (by omega)

theorem resultantX_denomScaledPoly_natDegree_le (D : CoordRingElt E.q)
    (P : ZMod E.q × ZMod E.q) (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) :
    (resultantX E (denomScaledPoly (E := E) D P k B A₀)).natDegree
      ≤ 9 * D.degE + 5 * k + 55 := by
  set N := D.degE + k + 9 with hNdef
  set M := 3 * D.degE + k + 11 with hMdef
  set k_ind := (N + 1) / 2 with hkIndDef
  have hNcon : (denomScaledPoly (E := E) D P k B A₀).natDegree ≤ 2 * k_ind + 1 := by
    have hfn : (denomScaledPoly (E := E) D P k B A₀).natDegree ≤ N :=
      denomScaledPoly_natDegree_le (E := E) D P k B A₀
    simp only [hkIndDef]; omega
  have hM_dsp : InnerDegLe (E := E) (denomScaledPoly (E := E) D P k B A₀) M :=
    InnerDegLe_denomScaledPoly (E := E) D P k B A₀
  have hRes := resultantX_natDegree_le_of_InnerDegLe (E := E)
                (denomScaledPoly (E := E) D P k B A₀) M k_ind hM_dsp hNcon
  refine hRes.trans ?_
  have hbd : 2 * (M + 3 * k_ind) + 3 ≤ 2 * M + 3 * (N + 1) + 3 := by
    simp only [hkIndDef]; omega
  refine hbd.trans ?_
  simp only [hMdef, hNdef]; omega

theorem denomScaledPoly_modCurve_ne_zero
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (A₀ : ZMod E.q × ZMod E.q)
    (hWitness : ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
      logDerivCheckFnDefined E D P B A₀ A₁) :
    denomScaledPoly (E := E) D P k B A₀ %ₘ curveEqPoly E ≠ 0 := by
  obtain ⟨A₁, hA₁, hNV, hDef⟩ := hWitness
  intro hModZero
  have hBiv : bivEval (denomScaledPoly (E := E) D P k B A₀) A₁ = 0 := by
    rw [bivEval_eq_modByMonic_on_E E _ hA₁, hModZero]
    unfold bivEval; simp
  rw [bivEval_denomScaledPoly_eq E D P k B A₀ A₁ hNV] at hBiv
  have hLam : (A₁.1 - A₀.1) ^ (D.degE + k + 7) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hNV))
  exact hDef ((mul_eq_zero.mp hBiv).resolve_left hLam)

section Phase2
open Classical

/-- Per-fiber bound restricted to the defined subset: for each
    A₀ ∈ E.points, either the defined fiber is identically zero on the
    **non-vertical** subset, or its zero count is bounded by
    `K := 18·(D.degE+k+6)+2`.

    The Or.inr is restricted to non-vertical pairs because
    `clearedFiberPoly_identity` only connects the polynomial vanishing
    to `logDerivCheckFn = 0` on the non-vertical cone `A₀.1 ≠ A₁.1`.
    At vertical pairs, the polynomial's zero carries no information
    about `logDerivCheckFn`. -/
theorem logDerivCheckFn_fiber_count_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (A₀ : ZMod E.q × ZMod E.q) (_hA₀ : A₀ ∈ E.points) :
    (E.points.filter (fun A₁ =>
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
         logDerivCheckFn E D P k B m A₀ A₁ = 0)).card
      ≤ 18 * (D.degE + k + 6) + 2
    ∨ (∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
         logDerivCheckFnDefined E D P B A₀ A₁ →
         logDerivCheckFn E D P k B m A₀ A₁ = 0) := by
  classical
  by_cases hNVWitness :
    ∃ A₁ ∈ E.points, A₀.1 ≠ A₁.1 ∧
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
       logDerivCheckFn E D P k B m A₀ A₁ ≠ 0
  · -- Non-vertical witness: apply B5 + card_zeros_on_E_le.
    left
    have hCFPNz : clearedFiberPoly (E := E) D P k B m A₀ %ₘ curveEqPoly E ≠ 0 :=
      clearedFiberPoly_modCurve_ne_zero E D P B m A₀ hNVWitness
    -- Split fiber by vertical vs. non-vertical.
    set fiber := E.points.filter (fun A₁ =>
       logDerivCheckFnDefined E D P B A₀ A₁ ∧
         logDerivCheckFn E D P k B m A₀ A₁ = 0) with hfiber_def
    set vertFiber := fiber.filter (fun A₁ => A₁.1 = A₀.1) with hvfdef
    set nvFiber := fiber.filter (fun A₁ => A₁.1 ≠ A₀.1) with hnvfdef
    have hDisj : Disjoint vertFiber nvFiber := by
      simp only [hvfdef, hnvfdef, Finset.disjoint_filter]
      intros _ _ hx hy
      exact hy hx
    have hUnion : vertFiber ∪ nvFiber = fiber := by
      ext x
      simp only [hvfdef, hnvfdef, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h : x.1 = A₀.1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    have hSplit : fiber.card = vertFiber.card + nvFiber.card := by
      rw [← hUnion, Finset.card_union_of_disjoint hDisj]
    -- vertFiber has ≤ 2 elements (vertical points on E).
    have hVert : vertFiber.card ≤ 2 := by
      calc vertFiber.card
          ≤ (E.points.filter (fun A₁ => A₁.1 = A₀.1)).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [hvfdef, hfiber_def, Finset.mem_filter] at hp
            exact Finset.mem_filter.mpr ⟨hp.1.1, hp.2⟩
        _ ≤ 2 := card_points_with_fst_eq_le E A₀.1
    -- nvFiber ⊆ zeros of clearedFiberPoly on E.points (by B3 identity).
    have hNV : nvFiber.card ≤ 2 * (9 * D.degE + 5 * k + 50) := by
      have hSubZ : nvFiber ⊆ E.points.filter
          (fun A₁ => bivEval (clearedFiberPoly (E := E) D P k B m A₀) A₁ = 0) := by
        intro A₁ hA₁
        simp only [hnvfdef, hfiber_def, Finset.mem_filter] at hA₁
        obtain ⟨⟨hA₁E, hDef, hfZero⟩, hNVA₁⟩ := hA₁
        simp only [Finset.mem_filter]
        refine ⟨hA₁E, ?_⟩
        rw [clearedFiberPoly_identity E D P B m A₀ A₁ (Ne.symm hNVA₁) hDef]
        unfold logDerivCheckFnCleared
        rw [hfZero]
        ring
      calc nvFiber.card
          ≤ (E.points.filter
                (fun A₁ => bivEval (clearedFiberPoly (E := E) D P k B m A₀) A₁ = 0)).card :=
            Finset.card_le_card hSubZ
        _ ≤ 2 * (resultantX E (clearedFiberPoly (E := E) D P k B m A₀)).natDegree :=
            card_zeros_on_E_le E _ hCFPNz
        _ ≤ 2 * (9 * D.degE + 5 * k + 50) :=
            Nat.mul_le_mul_left 2 (resultantX_clearedFiberPoly_natDegree_le E D P k B m A₀)
    calc fiber.card
        = vertFiber.card + nvFiber.card := hSplit
      _ ≤ 2 + 2 * (9 * D.degE + 5 * k + 50) := Nat.add_le_add hVert hNV
      _ ≤ 18 * (D.degE + k + 6) + 2 := by omega
  · -- No non-vertical witness: Or.inr.
    right
    push_neg at hNVWitness
    exact hNVWitness

/-- Bad-A₀ count on the defined subset: when the check is globally
    non-identically-zero on non-vertical defined pairs, the set of A₀
    with fiber ≡ 0 on the non-vertical defined part of E.points is bounded.

    Proof strategy: fix the hGlobalNonzero witness pair `(A₀*, A₁*)` and
    bound `bad_A₀_set` via a role-swap + `card_zeros_on_E_le` on two
    polynomials anchored at `A₁*`:
    * `clearedFiberPoly A₁*`: captures bad `A₀`'s with `defined(A₀, A₁*)`
      via the B3 identity + symmetry (f(A₀, A₁*) = 0 from bad ⇒ bivEval = 0).
    * `denomScaledPoly A₁*`: captures bad `A₀`'s with `¬ defined(A₀, A₁*)`
      (its bivEval vanishes exactly when `denom = 0` on the non-vertical cone).
    * Plus a 2-point "vertical at A₁*" contribution. -/
theorem logDerivCheckFn_badA₀_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (hGlobalNonzero :
      ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
        logDerivCheckFnDefined E D P B A₀ A₁ ∧
        logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    (E.points.filter
      (fun A₀ => ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
         logDerivCheckFnDefined E D P B A₀ A₁ →
         logDerivCheckFn E D P k B m A₀ A₁ = 0)).card
      ≤ 36 * (D.degE + k + 6) + 2 := by
  classical
  obtain ⟨A₀s, A₁s, hA₀s, hA₁s, hNVs, hDefs, hfnes⟩ := hGlobalNonzero
  -- Swap roles: witness for `clearedFiberPoly_modCurve_ne_zero` at A₁s.
  have hCFPNz : clearedFiberPoly (E := E) D P k B m A₁s %ₘ curveEqPoly E ≠ 0 := by
    apply clearedFiberPoly_modCurve_ne_zero E D P B m A₁s
    refine ⟨A₀s, hA₀s, Ne.symm hNVs, ?_, ?_⟩
    · -- defined (A₁s, A₀s) by symm of denom on non-vertical.
      unfold logDerivCheckFnDefined
      rw [logDerivCheckFnDenom_symm E D P B A₁s A₀s (Ne.symm hNVs)]
      exact hDefs
    · -- f (A₁s, A₀s) ≠ 0 by symm of f.
      rw [logDerivCheckFn_symm E D P B m A₁s A₀s (Ne.symm hNVs)]
      exact hfnes
  -- And for `denomScaledPoly_modCurve_ne_zero`.
  have hDSPNz : denomScaledPoly (E := E) D P k B A₁s %ₘ curveEqPoly E ≠ 0 := by
    apply denomScaledPoly_modCurve_ne_zero E D P k B A₁s
    refine ⟨A₀s, hA₀s, Ne.symm hNVs, ?_⟩
    unfold logDerivCheckFnDefined
    rw [logDerivCheckFnDenom_symm E D P B A₁s A₀s (Ne.symm hNVs)]
    exact hDefs
  -- Zero sets.
  set cfp_zeros : Finset (ZMod E.q × ZMod E.q) := E.points.filter (fun A₀ =>
      bivEval (clearedFiberPoly (E := E) D P k B m A₁s) A₀ = 0) with hcfp_zeros
  set dsp_zeros : Finset (ZMod E.q × ZMod E.q) := E.points.filter (fun A₀ =>
      bivEval (denomScaledPoly (E := E) D P k B A₁s) A₀ = 0) with hdsp_zeros
  set vert_set : Finset (ZMod E.q × ZMod E.q) := E.points.filter
      (fun A₀ => A₀.1 = A₁s.1) with hvert_set
  -- Cardinalities.
  have hZCFP : cfp_zeros.card ≤ 2 * (9 * D.degE + 5 * k + 50) := by
    calc cfp_zeros.card
        ≤ 2 * (resultantX E (clearedFiberPoly (E := E) D P k B m A₁s)).natDegree :=
          card_zeros_on_E_le E _ hCFPNz
      _ ≤ 2 * (9 * D.degE + 5 * k + 50) :=
          Nat.mul_le_mul_left 2 (resultantX_clearedFiberPoly_natDegree_le E D P k B m A₁s)
  have hZDSP : dsp_zeros.card ≤ 2 * (9 * D.degE + 5 * k + 55) := by
    calc dsp_zeros.card
        ≤ 2 * (resultantX E (denomScaledPoly (E := E) D P k B A₁s)).natDegree :=
          card_zeros_on_E_le E _ hDSPNz
      _ ≤ 2 * (9 * D.degE + 5 * k + 55) :=
          Nat.mul_le_mul_left 2 (resultantX_denomScaledPoly_natDegree_le E D P k B A₁s)
  have hZVert : vert_set.card ≤ 2 := card_points_with_fst_eq_le E A₁s.1
  -- bad_A₀_set is contained in the union of the three.
  set bad_A₀_set : Finset (ZMod E.q × ZMod E.q) := E.points.filter
    (fun A₀ => ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
       logDerivCheckFnDefined E D P B A₀ A₁ →
       logDerivCheckFn E D P k B m A₀ A₁ = 0) with hbadA₀
  have hSub : bad_A₀_set ⊆ cfp_zeros ∪ vert_set ∪ dsp_zeros := by
    intro A₀ hA₀
    simp only [hbadA₀, Finset.mem_filter] at hA₀
    obtain ⟨hA₀E, hbadP⟩ := hA₀
    simp only [Finset.mem_union, hcfp_zeros, hvert_set, hdsp_zeros,
               Finset.mem_filter]
    by_cases hV : A₀.1 = A₁s.1
    · left; right; exact ⟨hA₀E, hV⟩
    · -- Non-vertical cases. Let hVne : A₁s.1 ≠ A₀.1 (role-swap order).
      have hVne : A₁s.1 ≠ A₀.1 := Ne.symm hV
      by_cases hDef : logDerivCheckFnDefined E D P B A₀ A₁s
      · -- Defined case: in cfp_zeros via B3 identity + bad predicate.
        left; left
        refine ⟨hA₀E, ?_⟩
        -- Apply the identity at (A₁s, A₀) using role-swap.
        have hDefSwap : logDerivCheckFnDenom E D P B A₁s A₀ ≠ 0 := by
          rw [logDerivCheckFnDenom_symm E D P B A₁s A₀ hVne]
          exact hDef
        rw [clearedFiberPoly_identity E D P B m A₁s A₀ hVne hDefSwap]
        unfold logDerivCheckFnCleared
        have hfZero : logDerivCheckFn E D P k B m A₁s A₀ = 0 := by
          rw [logDerivCheckFn_symm E D P B m A₁s A₀ hVne]
          exact hbadP A₁s hA₁s hV hDef
        rw [hfZero]; ring
      · -- Undefined case: in dsp_zeros.
        right
        refine ⟨hA₀E, ?_⟩
        rw [bivEval_denomScaledPoly_eq E D P k B A₁s A₀ hVne]
        have hDenomZero : logDerivCheckFnDenom E D P B A₁s A₀ = 0 := by
          unfold logDerivCheckFnDefined at hDef
          push_neg at hDef
          rw [logDerivCheckFnDenom_symm E D P B A₁s A₀ hVne]
          exact hDef
        rw [hDenomZero]; ring
  -- Combine.
  calc bad_A₀_set.card
      ≤ (cfp_zeros ∪ vert_set ∪ dsp_zeros).card := Finset.card_le_card hSub
    _ ≤ (cfp_zeros ∪ vert_set).card + dsp_zeros.card := Finset.card_union_le _ _
    _ ≤ (cfp_zeros.card + vert_set.card) + dsp_zeros.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (2 * (9 * D.degE + 5 * k + 50) + 2) + 2 * (9 * D.degE + 5 * k + 55) :=
        Nat.add_le_add (Nat.add_le_add hZCFP hZVert) hZDSP
    _ ≤ 36 * (D.degE + k + 6) + 2 := by omega

open Classical in
/-- **Bad event bound** (mechanized). The undefined subset (pairs where
    some `logDerivCheckFn` denominator vanishes) has cardinality bounded
    polynomially in `D.degE + k` times `|E.points|`.

    Derived from F1-F8 factor-zero bounds via union-bound; hypothesis
    `hD : ¬ (D.a = 0 ∧ D.b = 0)` is needed for F1/F2/F3 to have
    finitely-many zeros. -/
theorem logDerivCheckFn_undefined_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card
      ≤ 18 * (D.degE + k + 6) * E.points.card := by
  classical
  -- Define the 8 sub-events (one per `logDerivCheckFnDenom` factor).
  set S1 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval p.1.1 p.1.2 = 0) with hS1def
  set S2 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval p.2.1 p.2.2 = 0) with hS2def
  set S3 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0) with hS3def
  set S4 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.1.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.1.2 = 0) with hS4def
  set S5 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.2.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.2.2 = 0) with hS5def
  set S6 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * (chordX₂ p.1 p.2) ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * (chordY₂ p.1 p.2) = 0) with hS6def
  set S7 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval P.1 (-P.2) = 0) with hS7def
  set S8 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ∃ j : Fin k, (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval (B j).1 (B j).2 = 0)
    with hS8def
  -- The undefined set is contained in the union of the 8 sub-events.
  set U := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hUdef
  have hSub : U ⊆ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8 := by
    intro p hp
    simp only [hUdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1E, h2E⟩, hNotDef⟩ := hp
    have hDenom : logDerivCheckFnDenom E D P B p.1 p.2 = 0 := by
      unfold logDerivCheckFnDefined at hNotDef
      exact not_not.mp hNotDef
    unfold logDerivCheckFnDenom at hDenom
    simp only [Finset.mem_union, hS1def, hS2def, hS3def, hS4def, hS5def,
               hS6def, hS7def, hS8def, Finset.mem_filter, Finset.mem_product]
    -- Chain of mul_eq_zero: 8 possibilities.
    have h1 := hDenom
    rcases mul_eq_zero.mp h1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · rcases mul_eq_zero.mp h with h | h
              · rcases mul_eq_zero.mp h with h | h
                · -- Factor 1: D.eval A₀
                  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
                    (Or.inl ⟨⟨h1E, h2E⟩, h⟩))))))
                · -- Factor 2: D.eval A₁
                  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
                    (Or.inr ⟨⟨h1E, h2E⟩, h⟩))))))
              · -- Factor 3: D.eval A₂ (= D.eval chordX₂ chordY₂)
                exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
                  ⟨⟨h1E, h2E⟩, h⟩)))))
            · -- Factor 4: dxdz(A₀)
              exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
                ⟨⟨h1E, h2E⟩, h⟩))))
          · -- Factor 5: dxdz(A₁)
            exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩)))
        · -- Factor 6: dxdz(A₂)
          exact Or.inl (Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩))
      · -- Factor 7: L(-P)
        exact Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩)
    · -- Factor 8: ∏ L(B_j). Convert product=0 into ∃ j, factor = 0.
      right
      refine ⟨⟨h1E, h2E⟩, ?_⟩
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨j, _, hj⟩ := h
      exact ⟨j, hj⟩
  -- Bound each sub-event.
  have hS1 : S1.card ≤ 2 * D.degE * E.points.card :=
    DAtA₀_zero_pairs_card_le E D hD
  have hS2 : S2.card ≤ 2 * D.degE * E.points.card :=
    DAtA₁_zero_pairs_card_le E D hD
  have hS3 : S3.card ≤ (2 * D.degE + 2) * E.points.card :=
    DAtA₂_zero_pairs_card_le E D hD
  have hS4 : S4.card ≤ 14 * E.points.card :=
    dxdzA₀_zero_pairs_card_le E
  have hS5 : S5.card ≤ 14 * E.points.card :=
    dxdzA₁_zero_pairs_card_le E
  have hS6 : S6.card ≤ 32 * E.points.card :=
    dxdzA₂_zero_pairs_card_le E
  have hS7 : S7.card ≤ 9 * E.points.card :=
    linePNeg_zero_pairs_card_le E P
  have hS8 : S8.card ≤ 9 * k * E.points.card :=
    lineBj_zero_pairs_card_le E B
  -- Assemble.
  calc U.card
      ≤ (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8).card :=
        Finset.card_le_card hSub
    _ ≤ S1.card + S2.card + S3.card + S4.card + S5.card + S6.card
         + S7.card + S8.card := by
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        exact Finset.card_union_le _ _
    _ ≤ 2 * D.degE * E.points.card + 2 * D.degE * E.points.card
         + (2 * D.degE + 2) * E.points.card + 14 * E.points.card
         + 14 * E.points.card + 32 * E.points.card + 9 * E.points.card
         + 9 * k * E.points.card := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add hS1 hS2) hS3) hS4) hS5) hS6) hS7) hS8
    _ = (6 * D.degE + 9 * k + 71) * E.points.card := by ring
    _ ≤ 18 * (D.degE + k + 6) * E.points.card := by
        apply Nat.mul_le_mul_right
        omega

/-- **Tight boundary bound.** The undefined subset has cardinality at
    most `(6·d + 9·k + 71)·|E|`, where `d = D.degE`. This is the
    pre-relaxation form of `logDerivCheckFn_undefined_set_bound`
    (which rounds up to `18·(d+k+6)·|E|`). -/
theorem logDerivCheckFn_undefined_set_bound_tight
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (k : ℕ) (B : Fin k → ZMod E.q × ZMod E.q)
    (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ((E.points ×ˢ E.points).filter
      (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
        ¬ logDerivCheckFnDefined E D P B p.1 p.2)).card
      ≤ (6 * D.degE + 9 * k + 71) * E.points.card := by
  classical
  set S1 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval p.1.1 p.1.2 = 0) with hS1def
  set S2 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval p.2.1 p.2.2 = 0) with hS2def
  set S3 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      D.eval (chordX₂ p.1 p.2) (chordY₂ p.1 p.2) = 0) with hS3def
  set S4 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.1.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.1.2 = 0) with hS4def
  set S5 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * p.2.1 ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * p.2.2 = 0) with hS5def
  set S6 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      3 * (chordX₂ p.1 p.2) ^ 2 + E.curveA
        - 2 * slopeOf p.1.1 p.1.2 p.2.1 p.2.2 * (chordY₂ p.1 p.2) = 0) with hS6def
  set S7 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval P.1 (-P.2) = 0) with hS7def
  set S8 := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ∃ j : Fin k, (lineThrough p.1.1 p.1.2 p.2.1 p.2.2).eval (B j).1 (B j).2 = 0)
    with hS8def
  set U := (E.points ×ˢ E.points).filter
    (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
      ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hUdef
  have hSub : U ⊆ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8 := by
    intro p hp
    simp only [hUdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1E, h2E⟩, hNotDef⟩ := hp
    have hDenom : logDerivCheckFnDenom E D P B p.1 p.2 = 0 := by
      unfold logDerivCheckFnDefined at hNotDef
      exact not_not.mp hNotDef
    unfold logDerivCheckFnDenom at hDenom
    simp only [Finset.mem_union, hS1def, hS2def, hS3def, hS4def, hS5def,
               hS6def, hS7def, hS8def, Finset.mem_filter, Finset.mem_product]
    have h1 := hDenom
    rcases mul_eq_zero.mp h1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · rcases mul_eq_zero.mp h with h | h
              · rcases mul_eq_zero.mp h with h | h
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
                    (Or.inl ⟨⟨h1E, h2E⟩, h⟩))))))
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
                    (Or.inr ⟨⟨h1E, h2E⟩, h⟩))))))
              · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
                  ⟨⟨h1E, h2E⟩, h⟩)))))
            · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
                ⟨⟨h1E, h2E⟩, h⟩))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩))
      · exact Or.inl (Or.inr ⟨⟨h1E, h2E⟩, h⟩)
    · right
      refine ⟨⟨h1E, h2E⟩, ?_⟩
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨j, _, hj⟩ := h
      exact ⟨j, hj⟩
  have hS1 : S1.card ≤ 2 * D.degE * E.points.card :=
    DAtA₀_zero_pairs_card_le E D hD
  have hS2 : S2.card ≤ 2 * D.degE * E.points.card :=
    DAtA₁_zero_pairs_card_le E D hD
  have hS3 : S3.card ≤ (2 * D.degE + 2) * E.points.card :=
    DAtA₂_zero_pairs_card_le E D hD
  have hS4 : S4.card ≤ 14 * E.points.card :=
    dxdzA₀_zero_pairs_card_le E
  have hS5 : S5.card ≤ 14 * E.points.card :=
    dxdzA₁_zero_pairs_card_le E
  have hS6 : S6.card ≤ 32 * E.points.card :=
    dxdzA₂_zero_pairs_card_le E
  have hS7 : S7.card ≤ 9 * E.points.card :=
    linePNeg_zero_pairs_card_le E P
  have hS8 : S8.card ≤ 9 * k * E.points.card :=
    lineBj_zero_pairs_card_le E B
  calc U.card
      ≤ (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8).card :=
        Finset.card_le_card hSub
    _ ≤ S1.card + S2.card + S3.card + S4.card + S5.card + S6.card
         + S7.card + S8.card := by
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        refine le_trans (Finset.card_union_le _ _) ?_
        refine Nat.add_le_add ?_ le_rfl
        exact Finset.card_union_le _ _
    _ ≤ 2 * D.degE * E.points.card + 2 * D.degE * E.points.card
         + (2 * D.degE + 2) * E.points.card + 14 * E.points.card
         + 14 * E.points.card + 32 * E.points.card + 9 * E.points.card
         + 9 * k * E.points.card := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add hS1 hS2) hS3) hS4) hS5) hS6) hS7) hS8
    _ = (6 * D.degE + 9 * k + 71) * E.points.card := by ring

/-- **main theorem**: mechanized zero-set bound on `E × E`.
    Derived from the defined-fiber + bad-A₀ + undefined-bad-event
    axioms via the set-union split.

    Since the challenge space is fixed (not D-dependent), the
    undefined-denominator points are bad events the verifier might
    accept at; we bound the total Lean-zero set as
    (defined zeros) + (undefined pairs). -/
theorem logDerivCheckFn_zero_set_bound
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    {k : ℕ} (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
    (_hDeg : D.degE < E.q)
    (hNonzero : ∃ A₀ A₁, A₀ ∈ E.points ∧ A₁ ∈ E.points ∧ A₀.1 ≠ A₁.1 ∧
      logDerivCheckFnDefined E D P B A₀ A₁ ∧
      logDerivCheckFn E D P k B m A₀ A₁ ≠ 0) :
    ((E.points ×ˢ E.points).filter
      (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0)).card
      ≤ (72 * (D.degE + k + 6) + 4) * E.points.card := by
  classical
  set K := 18 * (D.degE + k + 6) + 2 with hKdef
  set K' := 36 * (D.degE + k + 6) + 2 with hK'def
  -- Split: zeros = (defined zeros) ⊎ (some subset of undefined).
  set zSet := (E.points ×ˢ E.points).filter
    (fun p => logDerivCheckFn E D P k B m p.1 p.2 = 0) with hzSet
  set defZ := (E.points ×ˢ E.points).filter
    (fun p => logDerivCheckFnDefined E D P B p.1 p.2 ∧
              logDerivCheckFn E D P k B m p.1 p.2 = 0) with hdefZ
  set undefAll := (E.points ×ˢ E.points).filter
    (fun p => ¬ logDerivCheckFnDefined E D P B p.1 p.2) with hundefAll
  have hSplit : zSet.card ≤ defZ.card + undefAll.card := by
    have hSub : zSet ⊆ defZ ∪ undefAll := by
      intro p hp
      simp only [hzSet, Finset.mem_filter] at hp
      simp only [hdefZ, hundefAll, Finset.mem_union, Finset.mem_filter]
      by_cases hDef : logDerivCheckFnDefined E D P B p.1 p.2
      · exact Or.inl ⟨hp.1, hDef, hp.2⟩
      · exact Or.inr ⟨hp.1, hDef⟩
    exact le_trans (Finset.card_le_card hSub) (Finset.card_union_le _ _)
  -- Bound defZ by summing per-A₀ contributions.
  -- `bad_A₀_set`: A₀'s where the fiber is identically zero on the
  -- **non-vertical** defined subset. Matches the weakened T1/T2 form,
  -- since `clearedFiberPoly_identity` only couples polynomial vanishing
  -- to `logDerivCheckFn = 0` on the non-vertical cone.
  set bad_A₀_set : Finset (ZMod E.q × ZMod E.q) := E.points.filter
    (fun A₀ => ∀ A₁ ∈ E.points, A₀.1 ≠ A₁.1 →
       logDerivCheckFnDefined E D P B A₀ A₁ →
       logDerivCheckFn E D P k B m A₀ A₁ = 0) with hbadA₀
  have hBadBound : bad_A₀_set.card ≤ K' :=
    logDerivCheckFn_badA₀_bound E D P k B m
      (by obtain ⟨A₀, A₁, hA₀, hA₁, hNV, hDef, hne⟩ := hNonzero
          exact ⟨A₀, A₁, hA₀, hA₁, hNV, hDef, hne⟩)
  have hDefZ : defZ.card ≤ (K + K') * E.points.card := by
    -- Split defZ by whether A₀ is "bad" (fully identically-zero on defined fiber)
    -- or "good" (fiber count bounded by K).
    set goodZ := defZ.filter (fun p => p.1 ∉ bad_A₀_set) with hgoodZ
    set badZ := defZ.filter (fun p => p.1 ∈ bad_A₀_set) with hbadZ
    have hZsplit : defZ.card = goodZ.card + badZ.card := by
      rw [hgoodZ, hbadZ, Nat.add_comm,
          Finset.filter_card_add_filter_neg_card_eq_card]
    have hBadZcard : badZ.card ≤ K' * E.points.card := by
      have hSub : badZ ⊆ bad_A₀_set ×ˢ E.points := by
        intro p hp
        simp only [hbadZ, hdefZ, Finset.mem_filter, Finset.mem_product] at hp
        simp only [Finset.mem_product]
        exact ⟨hp.2, hp.1.1.2⟩
      calc badZ.card
          ≤ (bad_A₀_set ×ˢ E.points).card := Finset.card_le_card hSub
        _ = bad_A₀_set.card * E.points.card := Finset.card_product _ _
        _ ≤ K' * E.points.card := Nat.mul_le_mul_right _ hBadBound
    have hGoodZcard : goodZ.card ≤ E.points.card * K := by
      -- Each good A₀'s fiber in goodZ has ≤ K elements.
      have hFiberGood : ∀ A₀ ∈ E.points,
          (goodZ.filter (fun p => p.1 = A₀)).card ≤ K := by
        intro A₀ hA₀
        by_cases hBadA₀ : A₀ ∈ bad_A₀_set
        · -- A₀ ∈ bad ⇒ goodZ.filter (p.1 = A₀) = ∅.
          have : goodZ.filter (fun p => p.1 = A₀) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro p hp
            simp only [hgoodZ, Finset.mem_filter] at hp
            exact hp.1.2 (hp.2 ▸ hBadA₀)
          rw [this]; simp
        · -- A₀ ∉ bad ⇒ fiber has ≤ K elements via hFiber axiom.
          rcases logDerivCheckFn_fiber_count_bound E D P k B m A₀ hA₀ with h | h
          · calc (goodZ.filter (fun p => p.1 = A₀)).card
                ≤ (E.points.filter (fun A₁ =>
                    logDerivCheckFnDefined E D P B A₀ A₁ ∧
                    logDerivCheckFn E D P k B m A₀ A₁ = 0)).card := by
                  apply Finset.card_le_card_of_injOn Prod.snd
                  · intro p hp
                    simp only [Finset.mem_coe, hgoodZ, hdefZ, Finset.mem_filter,
                               Finset.mem_product] at hp
                    rw [Finset.mem_coe, Finset.mem_filter]
                    obtain ⟨⟨⟨⟨_, hp2⟩, hDef, hf⟩, _⟩, hpeq⟩ := hp
                    exact ⟨hp2, hpeq ▸ hDef, hpeq ▸ hf⟩
                  · intro p hp q hq heq
                    rw [Finset.mem_coe] at hp hq
                    have hpe : p.1 = A₀ := (Finset.mem_filter.mp hp).2
                    have hqe : q.1 = A₀ := (Finset.mem_filter.mp hq).2
                    exact Prod.ext (hpe.trans hqe.symm) heq
              _ ≤ K := h
          · -- A₀ ∉ bad contradicts hFiber's right branch.
            exfalso; apply hBadA₀
            simp only [hbadA₀, Finset.mem_filter]
            exact ⟨hA₀, h⟩
      have hImgSub : goodZ.image Prod.fst ⊆ E.points := by
        intro A₀ hA₀
        rw [Finset.mem_image] at hA₀
        obtain ⟨p, hp, rfl⟩ := hA₀
        simp only [hgoodZ, hdefZ, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.1.1.1
      calc goodZ.card
          ≤ K * (goodZ.image Prod.fst).card := by
            exact Finset.card_le_mul_card_image _ _
              (fun A₀ hA₀ => hFiberGood A₀ (hImgSub hA₀))
        _ ≤ K * E.points.card := Nat.mul_le_mul_left _ (Finset.card_le_card hImgSub)
        _ = E.points.card * K := Nat.mul_comm _ _
    calc defZ.card = goodZ.card + badZ.card := hZsplit
      _ ≤ E.points.card * K + K' * E.points.card := by
          exact Nat.add_le_add hGoodZcard hBadZcard
      _ = (K + K') * E.points.card := by ring
  -- Derive `hD` (D is not identically zero) from hNonzero: if `D.a = 0`
  -- and `D.b = 0`, then `D.eval` is identically zero, so
  -- `logDerivCheckFnDenom` has a factor `D.eval A₀ = 0` everywhere,
  -- contradicting the nonzero-denominator witness.
  have hD : ¬ (D.a = 0 ∧ D.b = 0) := by
    intro hDab
    obtain ⟨A₀, A₁, hA₀, _, _, hDef, _⟩ := hNonzero
    apply hDef
    unfold logDerivCheckFnDenom CoordRingElt.eval
    rw [hDab.1, hDab.2]
    simp
  -- Bound undefAll via the mechanized undefined-set-bound theorem.
  have hUndef : undefAll.card ≤ 18 * (D.degE + k + 6) * E.points.card :=
    logDerivCheckFn_undefined_set_bound E D P k B hD
  -- Combine.
  calc zSet.card
      ≤ defZ.card + undefAll.card := hSplit
    _ ≤ (K + K') * E.points.card + 18 * (D.degE + k + 6) * E.points.card := by
        exact Nat.add_le_add hDefZ hUndef
    _ = ((K + K') + 18 * (D.degE + k + 6)) * E.points.card := by ring
    _ = (72 * (D.degE + k + 6) + 4) * E.points.card := by
        rw [hKdef, hK'def]; ring

end Phase2

end Divisor
