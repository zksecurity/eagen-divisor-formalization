/-
  Divisor/OrdP/LocalRing.lean

  Algebraic API for `ordAt` (order of vanishing of `D = a − b·y` at
  affine F_q-rational points), restated against the *sound* `ordAt`
  defined in `Divisor.OrdP.Uniformizer`.

  The previous file used a 0/1 placeholder for `ordAt`; the
  splitting-time accounting and group-sum-zero identities were
  provably FALSE under that placeholder (concrete F_5 counterexample:
  `D = X(1+X) − X·y` on `y² = x³+1`).  The redesign here:

  * Uses the new `ordAt` from `Uniformizer.lean`, dispatching to
    `ordAt_twoTorsion` (closed form) at 2-torsion points and
    `ordAt_nonTwoTorsion` (recursive lone/twin trichotomy) elsewhere.
  * Proves all support / coverage / sum bounds and the splitting-time
    `Σ ordAt = natDeg(normPoly)` identity from primitives.
  * Reduces the function-field / regular-function content to a
    single explicit axiom `ordAt_divisor_isPrincipal` (Section 7).

  Layout:

    Section 1–2: shape lemmas — `ordAt_eq_zero_offE`,
                 `ordAt_pos_iff_zero`.
    Section 3:   2-torsion ord identity (Obligation A — proved).
                 Sub-lemmas: `ordAt_twoTorsion_eq_rootMult_normPoly`
                 (split into `aZero` / `bZero` / `min` cases via
                 `rootMult_normPoly_min_at_two_torsion` and
                 `rootMult_normPoly_at_two_torsion_aZero`).
    Section 4:   per-fiber sum identity (Obligation B — proved).
                 `ordAt_nonTwoTorsion_pair_eq_rootMult` via fuel
                 induction on the recursive helper.
    Section 5:   `sum_ordAt_le_degE` (unconditional).
    Section 6:   `sum_ordAt_eq_natDegree_under_split` (proved).
    Section 7:   `divisorOfD` definition + the principal-divisor
                 bridge axiom + `ordAt_group_sum_zero_under_split`
                 (derived from the bridge axiom +
                 `principal_divisor_iff`).
    Section 8:   `exists_divisor_multiplicity_proved` — discharges
                 the existential axiom with witness `ordAt E D`.

  Axiomatic surface introduced by this file: exactly one axiom,
  `ordAt_divisor_isPrincipal` (the principal-divisor bridge for the
  specific divisor `divisorOfD E D`).  See its docstring for the full
  scope and a comparison with `exists_divisor_multiplicity` (which it
  replaces — and is strictly weaker than).

  References: Silverman AEC II §1 (local orders) + III.3.5
  (principal divisor characterisation / Abel's theorem).
-/
import Divisor.OrdP.Uniformizer
import Divisor.Axioms.AxiomPrincipalDivisorIff
import Divisor.SplitsOnE

open Polynomial Finset

namespace Divisor

variable (E : ECSetup)

/-! ## Section 1: trivial shape lemmas -/

/-- Off `E.points`, `ordAt = 0` by definition. -/
theorem ordAt_eq_zero_offE
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hP : P ∉ E.points) :
    ordAt E D P = 0 :=
  ordAt_eq_zero_of_offE_or_zero E D P (fun h => hP h.1)

/-- For the zero divisor, `ordAt = 0` everywhere by definition. -/
theorem ordAt_eq_zero_of_zero
    {D : CoordRingElt E.q} (hD : D.a = 0 ∧ D.b = 0)
    (P : ZMod E.q × ZMod E.q) :
    ordAt E D P = 0 :=
  ordAt_eq_zero_of_offE_or_zero E D P (fun h => h.2 hD)

/-! ## Section 2: support — `0 < ordAt ↔ D vanishes` -/

/-- Auxiliary: at any positive fuel, `ordAt_nonTwoTorsion_aux` is
    positive iff `D` vanishes at `P`.  The `+1` step in the twin
    branch makes the result positive structurally regardless of the
    deeper recursive value, so no induction on fuel is needed. -/
theorem ordAt_nonTwoTorsion_aux_pos_iff
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (fuel : ℕ) (hFuel : 0 < fuel)
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hP : P ∈ E.points) :
    0 < ordAt_nonTwoTorsion_aux E fuel D P ↔ D.eval P.1 P.2 = 0 := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
    ⟨fuel - 1, (Nat.sub_add_cancel hFuel).symm⟩
  unfold ordAt_nonTwoTorsion_aux
  rw [if_neg hD]
  by_cases h2 : D.eval P.1 P.2 ≠ 0
  · rw [if_pos h2]
    refine ⟨fun hp => absurd hp (lt_irrefl 0), fun he => absurd he h2⟩
  · push_neg at h2
    rw [if_neg (not_not.mpr h2)]
    by_cases h3 : D.eval P.1 (-P.2) ≠ 0
    · rw [if_pos h3]
      refine ⟨fun _ => h2, fun _ => ?_⟩
      rw [rootMultiplicity_pos (normPoly_ne_zero E D hD)]
      show (normPoly E D).eval P.1 = 0
      rw [normPoly_eval_eq_D_mul_D_neg E D hP, h2, zero_mul]
    · rw [if_neg h3]
      refine ⟨fun _ => h2, fun _ => by omega⟩

theorem ordAt_nonTwoTorsion_pos_iff
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hP : P ∈ E.points) :
    0 < ordAt_nonTwoTorsion E D P ↔ D.eval P.1 P.2 = 0 := by
  unfold ordAt_nonTwoTorsion
  exact ordAt_nonTwoTorsion_aux_pos_iff E D _ (by omega) hD hP

theorem ordAt_twoTorsion_pos_iff
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hY : P.2 = 0) :
    0 < ordAt_twoTorsion E D P ↔ D.eval P.1 P.2 = 0 := by
  classical
  -- D.eval P.1 P.2 = a(P.1) when y = 0.
  have hEval : D.eval P.1 P.2 = D.a.eval P.1 := by
    show D.a.eval P.1 - D.b.eval P.1 * P.2 = D.a.eval P.1
    rw [hY]; ring
  rw [hEval]
  unfold ordAt_twoTorsion
  rw [if_neg hD]
  by_cases ha : D.a = 0
  · rw [if_pos ha]
    refine ⟨fun _ => by rw [ha]; exact Polynomial.eval_zero, fun _ => by omega⟩
  · rw [if_neg ha]
    by_cases hb : D.b = 0
    · rw [if_pos hb]
      constructor
      · intro h
        have hRMpos : 0 < rootMultiplicity P.1 D.a := by omega
        exact (rootMultiplicity_pos ha).mp hRMpos
      · intro he
        have hRMpos : 0 < rootMultiplicity P.1 D.a :=
          (rootMultiplicity_pos ha).mpr he
        omega
    · rw [if_neg hb]
      constructor
      · intro hMin
        rw [lt_min_iff] at hMin
        have h1 : 0 < 2 * rootMultiplicity P.1 D.a := hMin.1
        have hRMpos : 0 < rootMultiplicity P.1 D.a := by omega
        exact (rootMultiplicity_pos ha).mp hRMpos
      · intro he
        have hRMpos : 0 < rootMultiplicity P.1 D.a :=
          (rootMultiplicity_pos ha).mpr he
        rw [lt_min_iff]
        refine ⟨?_, ?_⟩
        · omega
        · omega

theorem ordAt_pos_iff_zero
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (P : ZMod E.q × ZMod E.q) (hP : P ∈ E.points) :
    0 < ordAt E D P ↔ D.eval P.1 P.2 = 0 := by
  classical
  rw [ordAt_eq_dispatch E D hP hD]
  by_cases hY : P.2 = 0
  · rw [if_pos hY]; exact ordAt_twoTorsion_pos_iff E D hD hY
  · rw [if_neg hY]; exact ordAt_nonTwoTorsion_pos_iff E D hD hP

/-! ## Section 3: deep structural obligations (Section A and B) -/

/-! ### Helpers for 2-torsion smoothness and curveX factorisation -/

/-- At a 2-torsion x-coordinate, the tangent denominator `3x₀² + A`
    is nonzero: smoothness of `E` (`hDisc : 4A³ + 27B² ≠ 0`) prevents
    `(x³ + Ax + B)` from having a repeated root, so its derivative
    `3x² + A` cannot share that root.  Direct algebraic argument:
    if both vanish at `x₀`, then `A = -3x₀²`, `B = 2x₀³`, and
    `4A³ + 27B² = 0`, contradicting `hDisc`. -/
theorem three_xSq_plus_A_ne_zero_at_two_torsion
    {x₀ : ZMod E.q} (hx : x₀ ^ 3 + E.curveA * x₀ + E.curveB = 0) :
    3 * x₀ ^ 2 + E.curveA ≠ 0 := by
  intro h
  apply E.hDisc
  have hA : E.curveA = -(3 * x₀ ^ 2) := by linear_combination h
  have hB : E.curveB = 2 * x₀ ^ 3 := by linear_combination hx - x₀ * h
  rw [hA, hB]; ring

/-- Factorisation of the cubic `curveX = X³ + AX + B` at a 2-torsion
    x-coordinate: `curveX = (X − C x₀) · q` where
    `q = X² + (C x₀)·X + C (x₀² + A)` evaluates at `x₀` to
    `3x₀² + A ≠ 0`.  Standard `(x − x₀)`-factor extraction. -/
theorem curveX_factor_at_two_torsion
    {x₀ : ZMod E.q} (hx : x₀ ^ 3 + E.curveA * x₀ + E.curveB = 0) :
    ∃ q : (ZMod E.q)[X],
      curveX E = (Polynomial.X - Polynomial.C x₀) * q ∧
      q.eval x₀ = 3 * x₀ ^ 2 + E.curveA ∧
      q ≠ 0 := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C x₀ * Polynomial.X
            + Polynomial.C (x₀ ^ 2 + E.curveA), ?_, ?_, ?_⟩
  · -- Algebraic identity, modulo `hx`.
    unfold curveX
    have hB : E.curveB = -(x₀ ^ 3 + E.curveA * x₀) := by linear_combination hx
    rw [hB]
    -- Push C through the negation/sum/product/pow on both sides, then `ring`.
    simp only [Polynomial.C_neg, Polynomial.C_add, Polynomial.C_mul,
               Polynomial.C_pow]
    ring
  · simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
               Polynomial.eval_X, Polynomial.eval_C]
    ring
  · -- Nonzero: monic quadratic.
    intro hZero
    have h2 : (Polynomial.X ^ 2 + Polynomial.C x₀ * Polynomial.X
                + Polynomial.C (x₀ ^ 2 + E.curveA) :
               (ZMod E.q)[X]).natDegree = 2 := by
      compute_degree!
    rw [hZero, Polynomial.natDegree_zero] at h2
    exact absurd h2 (by norm_num)

/-- Auxiliary: if `(X − C x₀)^j ∣ p` and `(X − C x₀)^k ∣ q` with
    `j < k`, and `(X − C x₀)^(j+1) ∤ p`, then
    `rootMultiplicity x₀ (p − q) = j`.

    Proof: ≥ direction is direct (`(X − C x₀)^j` divides both `p` and
    `q`, so divides their difference).  ≤ direction uses the
    contrapositive: if `(X − C x₀)^(j+1)` divided `p − q`, it would
    also divide `p = (p − q) + q` (since it divides `q` because
    `j + 1 ≤ k`), contradicting `j` being the exact multiplicity at
    `p`. -/
theorem rootMultiplicity_sub_of_lt
    {p q : (ZMod E.q)[X]}
    {x₀ : ZMod E.q} {j k : ℕ}
    (hjp : (Polynomial.X - Polynomial.C x₀) ^ j ∣ p)
    (hjp' : ¬ (Polynomial.X - Polynomial.C x₀) ^ (j + 1) ∣ p)
    (hkq : (Polynomial.X - Polynomial.C x₀) ^ k ∣ q)
    (hjk : j < k) (hpqNZ : p - q ≠ 0) :
    rootMultiplicity x₀ (p - q) = j := by
  classical
  have hjq : (Polynomial.X - Polynomial.C x₀) ^ j ∣ q :=
    dvd_trans (pow_dvd_pow _ hjk.le) hkq
  have hjk1 : j + 1 ≤ k := hjk
  have hj1q : (Polynomial.X - Polynomial.C x₀) ^ (j + 1) ∣ q :=
    dvd_trans (pow_dvd_pow _ hjk1) hkq
  -- ≥ direction: (X − C x₀)^j divides p − q.
  have hLB : j ≤ rootMultiplicity x₀ (p - q) :=
    (Polynomial.le_rootMultiplicity_iff hpqNZ).mpr (dvd_sub hjp hjq)
  -- ≤ direction: if rootMultiplicity x₀ (p - q) > j, contradiction.
  have hUB : rootMultiplicity x₀ (p - q) ≤ j := by
    by_contra hContra
    push_neg at hContra
    have : (Polynomial.X - Polynomial.C x₀) ^ (j + 1) ∣ (p - q) :=
      (Polynomial.le_rootMultiplicity_iff hpqNZ).mp hContra
    have hpDiv : (Polynomial.X - Polynomial.C x₀) ^ (j + 1) ∣ p := by
      have := dvd_add this hj1q
      simpa using this
    exact hjp' hpDiv
  omega

/-- Auxiliary: rootMult x₀ (-p) = rootMult x₀ p, via `-p = C(-1) · p`. -/
theorem rootMultiplicity_neg
    {p : (ZMod E.q)[X]} (hp : p ≠ 0) {x₀ : ZMod E.q} :
    rootMultiplicity x₀ (-p) = rootMultiplicity x₀ p := by
  have hEq : (-p : (ZMod E.q)[X]) = Polynomial.C (-1) * p := by
    rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
  rw [hEq, Polynomial.rootMultiplicity_mul]
  · rw [Polynomial.rootMultiplicity_C]; omega
  · rw [← hEq]; exact neg_ne_zero.mpr hp

/-- **Sub-obligation A.min — non-cancellation at the parity gap.**
    When both `a ≠ 0` and `b ≠ 0`, the rootMult of
    `normPoly = a² − b²·(X−x₀)·q` at `x₀` is exactly
    `min(2·rootMult x₀ a, 2·rootMult x₀ b + 1)`. -/
theorem rootMult_normPoly_min_at_two_torsion
    (D : CoordRingElt E.q) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    {x₀ : ZMod E.q} (hX : x₀ ^ 3 + E.curveA * x₀ + E.curveB = 0) :
    rootMultiplicity x₀ (normPoly E D)
      = min (2 * rootMultiplicity x₀ D.a) (2 * rootMultiplicity x₀ D.b + 1) := by
  classical
  obtain ⟨q, hqEq, hqEval, hqNZ⟩ := curveX_factor_at_two_torsion E hX
  set ma := rootMultiplicity x₀ D.a with hma_def
  set mb := rootMultiplicity x₀ D.b with hmb_def
  -- q has rootMult 0 at x₀.
  have hqRMz : rootMultiplicity x₀ q = 0 := by
    apply rootMultiplicity_eq_zero
    intro hRoot
    exact three_xSq_plus_A_ne_zero_at_two_torsion E hX (hqEval ▸ hRoot)
  -- a² has rootMult 2·ma; b²·(X-C x₀)·q has rootMult 2·mb + 1.
  have ha2NZ : D.a ^ 2 ≠ 0 := pow_ne_zero _ ha
  have hb2NZ : D.b ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hXsubCNZ : (Polynomial.X - Polynomial.C x₀ : (ZMod E.q)[X]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hMul2NZ : (Polynomial.X - Polynomial.C x₀) * q ≠ 0 :=
    mul_ne_zero hXsubCNZ hqNZ
  have hSideNZ : D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q) ≠ 0 :=
    mul_ne_zero hb2NZ hMul2NZ
  have hRMa2 : rootMultiplicity x₀ (D.a ^ 2) = 2 * ma := by
    rw [pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero ha ha)]
    show ma + ma = 2 * ma; ring
  have hRMside :
      rootMultiplicity x₀ (D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q))
        = 2 * mb + 1 := by
    rw [Polynomial.rootMultiplicity_mul hSideNZ,
        pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero hb hb),
        Polynomial.rootMultiplicity_mul hMul2NZ,
        Polynomial.rootMultiplicity_X_sub_C_self,
        hqRMz]
    show mb + mb + (1 + 0) = 2 * mb + 1; ring
  -- normPoly = a² - b²·(X-C x₀)·q.
  have hN : normPoly E D
            = D.a ^ 2 - D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q) := by
    rw [normPoly_eq, hqEq]
  have hNNZ : normPoly E D ≠ 0 :=
    normPoly_ne_zero E D (fun ⟨h1, _⟩ => ha h1)
  rw [hN]
  set p1 := D.a ^ 2 with hp1_def
  set p2 := D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q) with hp2_def
  have hp1NZ : p1 ≠ 0 := ha2NZ
  have hp2NZ : p2 ≠ 0 := hSideNZ
  have hRMp1 : rootMultiplicity x₀ p1 = 2 * ma := hRMa2
  have hRMp2 : rootMultiplicity x₀ p2 = 2 * mb + 1 := hRMside
  have hSubNZ : p1 - p2 ≠ 0 := by rw [hp1_def, hp2_def, ← hN]; exact hNNZ
  -- Parity: 2·ma is even, 2·mb + 1 is odd ⇒ they're different.
  have hNeq : 2 * ma ≠ 2 * mb + 1 := by omega
  rcases lt_or_gt_of_ne hNeq with hLT | hGT
  · -- 2·ma < 2·mb + 1; min = 2·ma.
    rw [min_eq_left hLT.le]
    apply rootMultiplicity_sub_of_lt E (j := 2 * ma) (k := 2 * mb + 1)
    · rw [← hRMp1]; exact pow_rootMultiplicity_dvd _ _
    · rw [show 2 * ma + 1 = rootMultiplicity x₀ p1 + 1 from by rw [hRMp1]]
      exact pow_rootMultiplicity_not_dvd hp1NZ _
    · rw [← hRMp2]; exact pow_rootMultiplicity_dvd _ _
    · exact hLT
    · exact hSubNZ
  · -- 2·ma > 2·mb + 1; min = 2·mb + 1.  Symmetrise via `p1 - p2 = -(p2 - p1)`.
    rw [min_eq_right (le_of_lt hGT)]
    have hSubSwap : p1 - p2 = -(p2 - p1) := by ring
    rw [hSubSwap]
    have hSubSwapNZ : p2 - p1 ≠ 0 := by
      intro h; apply hSubNZ; rw [hSubSwap, h, neg_zero]
    rw [rootMultiplicity_neg E hSubSwapNZ]
    apply rootMultiplicity_sub_of_lt E (j := 2 * mb + 1) (k := 2 * ma)
    · rw [← hRMp2]; exact pow_rootMultiplicity_dvd _ _
    · rw [show 2 * mb + 1 + 1 = rootMultiplicity x₀ p2 + 1 from by rw [hRMp2]]
      exact pow_rootMultiplicity_not_dvd hp2NZ _
    · rw [← hRMp1]; exact pow_rootMultiplicity_dvd _ _
    · exact hGT
    · exact hSubSwapNZ

/-- **Sub-obligation A.aZero — `a = 0`, `b ≠ 0` case.**
    `normPoly = −b²·(X − C x₀)·q` with `q(x₀) ≠ 0`, so its rootMult
    at `x₀` is `2·rootMult x₀ b + 1`. -/
theorem rootMult_normPoly_at_two_torsion_aZero
    (D : CoordRingElt E.q) (ha : D.a = 0) (hb : D.b ≠ 0)
    {x₀ : ZMod E.q} (hX : x₀ ^ 3 + E.curveA * x₀ + E.curveB = 0) :
    rootMultiplicity x₀ (normPoly E D) = 2 * rootMultiplicity x₀ D.b + 1 := by
  classical
  obtain ⟨q, hqEq, hqEval, hqNZ⟩ := curveX_factor_at_two_torsion E hX
  -- q(x₀) ≠ 0 ⇒ rootMult x₀ q = 0.
  have hqRMz : rootMultiplicity x₀ q = 0 := by
    apply rootMultiplicity_eq_zero
    intro hRoot
    exact three_xSq_plus_A_ne_zero_at_two_torsion E hX (hqEval ▸ hRoot)
  -- normPoly = -(b²·(X-C x₀)·q) since a = 0.
  have hN : normPoly E D = -(D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q)) := by
    rw [normPoly_eq, hqEq, ha]; ring
  rw [hN]
  -- rootMult x₀ (-p) = rootMult x₀ p, via -p = C(-1) * p.
  have hRMneg : ∀ {p : (ZMod E.q)[X]}, p ≠ 0 →
      rootMultiplicity x₀ (-p) = rootMultiplicity x₀ p := by
    intro p hp
    have hEq : (-p : (ZMod E.q)[X]) = Polynomial.C (-1) * p := by
      rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
    rw [hEq, Polynomial.rootMultiplicity_mul]
    · rw [Polynomial.rootMultiplicity_C]; omega
    · rw [← hEq]; exact neg_ne_zero.mpr hp
  have hbsqNZ : D.b ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hXsubCNZ : (Polynomial.X - Polynomial.C x₀ : (ZMod E.q)[X]) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hMul2NZ : (Polynomial.X - Polynomial.C x₀) * q ≠ 0 :=
    mul_ne_zero hXsubCNZ hqNZ
  have hMulNZ : D.b ^ 2 * ((Polynomial.X - Polynomial.C x₀) * q) ≠ 0 :=
    mul_ne_zero hbsqNZ hMul2NZ
  rw [hRMneg hMulNZ, Polynomial.rootMultiplicity_mul hMulNZ,
      Polynomial.rootMultiplicity_mul hMul2NZ,
      Polynomial.rootMultiplicity_X_sub_C_self,
      hqRMz, pow_two,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hb hb)]
  ring

/-- **Obligation A — 2-torsion ord identity.**
    At a 2-torsion point `P = (x₀, 0)`, the closed-form definition
    `ordAt_twoTorsion = min(2·rootMult x₀ a, 2·rootMult x₀ b + 1)`
    coincides with `rootMult x₀ (normPoly E D)`.

    Now structured as a case-split on `D.a = 0` / `D.b = 0`:
    * `b = 0` (and `a ≠ 0`): direct via `rootMultiplicity_mul`
      applied to `a² = a · a` — fully proved here.
    * `a = 0` (and `b ≠ 0`): handled by
      `rootMult_normPoly_at_two_torsion_aZero`.
    * both nonzero: handled by `rootMult_normPoly_min_at_two_torsion`. -/
theorem ordAt_twoTorsion_eq_rootMult_normPoly
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 = 0) :
    ordAt_twoTorsion E D P = rootMultiplicity P.1 (normPoly E D) := by
  classical
  -- 2-torsion: x₀³ + Ax₀ + B = 0.
  have hX : P.1 ^ 3 + E.curveA * P.1 + E.curveB = 0 := by
    have hOC := E.hOnCurve P hP
    rw [hY] at hOC
    linear_combination -hOC
  unfold ordAt_twoTorsion
  rw [if_neg hD]
  by_cases ha : D.a = 0
  · rw [if_pos ha]
    have hb : D.b ≠ 0 := fun h => hD ⟨ha, h⟩
    exact (rootMult_normPoly_at_two_torsion_aZero E D ha hb hX).symm
  · rw [if_neg ha]
    by_cases hb : D.b = 0
    · rw [if_pos hb]
      -- normPoly = a² (since b = 0).
      have hN' : normPoly E D = D.a ^ 2 := by
        rw [normPoly_eq, hb]; ring
      rw [hN', pow_two, Polynomial.rootMultiplicity_mul (mul_ne_zero ha ha)]
      ring
    · rw [if_neg hb]
      exact (rootMult_normPoly_min_at_two_torsion E D ha hb hX).symm

/-! ### Obligation B — non-2-torsion norm identity.

    Strategy: prove the auxiliary version on the fuel-recursive
    `ordAt_nonTwoTorsion_aux` first, by induction on the fuel.  Three
    helper lemmas isolate the structural steps:

    * `normPoly_divLin` — when `(X − C x₀)` divides both `a` and `b`,
      `normPoly E D = (X − C x₀)² · normPoly E (D.divLin x₀)`.
    * `divLin_not_both_zero` — `divLin` doesn't introduce the zero
      divisor.
    * `divLin_natDegree_sum_lt` — `divLin` strictly decreases the
      `(a.natDeg + b.natDeg)` measure.
-/

/-- When `(X − C x₀)` divides both `D.a` and `D.b` (equivalently,
    `D.a.eval x₀ = 0` and `D.b.eval x₀ = 0`),
    `normPoly E D = (X − C x₀)² · normPoly E (D.divLin x₀)`. -/
theorem normPoly_divLin_factor
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (ha : D.a.eval x₀ = 0) (hb : D.b.eval x₀ = 0) :
    normPoly E D = (Polynomial.X - Polynomial.C x₀) ^ 2
                  * normPoly E (D.divLin x₀) := by
  classical
  rw [normPoly_eq, normPoly_eq]
  unfold CoordRingElt.divLin
  -- D.a = (X − C x₀) · (D.a /ₘ (X − C x₀))
  have hAfact : D.a = (Polynomial.X - Polynomial.C x₀)
                      * (D.a /ₘ (Polynomial.X - Polynomial.C x₀)) :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
  have hBfact : D.b = (Polynomial.X - Polynomial.C x₀)
                      * (D.b /ₘ (Polynomial.X - Polynomial.C x₀)) :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hb).symm
  conv_lhs => rw [hAfact, hBfact]
  ring

/-- `divLin` doesn't collapse a non-zero divisor into the zero divisor:
    if `D ≠ 0` and `(X − C x₀)` divides both `D.a, D.b`, then
    `D.divLin x₀ ≠ 0` componentwise. -/
theorem divLin_not_both_zero
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (ha : D.a.eval x₀ = 0) (hb : D.b.eval x₀ = 0) :
    ¬ ((D.divLin x₀).a = 0 ∧ (D.divLin x₀).b = 0) := by
  classical
  intro ⟨ha', hb'⟩
  apply hD
  refine ⟨?_, ?_⟩
  · rw [CoordRingElt.divLin_a,
        Polynomial.divByMonic_eq_zero_iff (Polynomial.monic_X_sub_C _),
        Polynomial.degree_X_sub_C] at ha'
    -- D.a.degree < 1.
    by_cases haz : D.a = 0
    · exact haz
    · -- D.a is a nonzero constant; D.a.eval x₀ = 0 ⇒ D.a = 0, contradiction.
      have hND : D.a.natDegree = 0 := by
        rw [Polynomial.degree_eq_natDegree haz] at ha'
        exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast ha')
      have hC : D.a = Polynomial.C (D.a.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hND
      have hCoeff0 : D.a.coeff 0 = 0 := by
        rw [hC, Polynomial.eval_C] at ha; exact ha
      rw [hC, hCoeff0, Polynomial.C_0]
  · rw [CoordRingElt.divLin_b,
        Polynomial.divByMonic_eq_zero_iff (Polynomial.monic_X_sub_C _),
        Polynomial.degree_X_sub_C] at hb'
    by_cases hbz : D.b = 0
    · exact hbz
    · have hND : D.b.natDegree = 0 := by
        rw [Polynomial.degree_eq_natDegree hbz] at hb'
        exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hb')
      have hC : D.b = Polynomial.C (D.b.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hND
      have hCoeff0 : D.b.coeff 0 = 0 := by
        rw [hC, Polynomial.eval_C] at hb; exact hb
      rw [hC, hCoeff0, Polynomial.C_0]

/-- `divLin` strictly decreases `D.a.natDegree + D.b.natDegree` when
    `D ≠ 0` and `(X − C x₀)` divides both. -/
theorem divLin_natDegree_sum_lt
    (D : CoordRingElt E.q) {x₀ : ZMod E.q}
    (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (ha : D.a.eval x₀ = 0) (hb : D.b.eval x₀ = 0) :
    (D.divLin x₀).a.natDegree + (D.divLin x₀).b.natDegree
      < D.a.natDegree + D.b.natDegree := by
  classical
  rw [CoordRingElt.divLin_a, CoordRingElt.divLin_b,
      Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
      Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
      Polynomial.natDegree_X_sub_C]
  -- Subgoal: D.a.natDegree - 1 + (D.b.natDegree - 1) < D.a.natDegree + D.b.natDegree.
  have natDegree_pos_of_dvd : ∀ {p : (ZMod E.q)[X]}, p ≠ 0 →
      p.eval x₀ = 0 → 1 ≤ p.natDegree := by
    intro p hp hpEval
    have hDvd : (Polynomial.X - Polynomial.C x₀) ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr hpEval
    have hLe := Polynomial.natDegree_le_of_dvd hDvd hp
    rw [Polynomial.natDegree_X_sub_C] at hLe
    exact hLe
  by_cases haz : D.a = 0
  · have hbz : D.b ≠ 0 := fun h => hD ⟨haz, h⟩
    have hbDeg : 1 ≤ D.b.natDegree := natDegree_pos_of_dvd hbz hb
    rw [haz, Polynomial.natDegree_zero]
    omega
  · have haDeg : 1 ≤ D.a.natDegree := natDegree_pos_of_dvd haz ha
    by_cases hbz : D.b = 0
    · rw [hbz, Polynomial.natDegree_zero]; omega
    · have hbDeg : 1 ≤ D.b.natDegree := natDegree_pos_of_dvd hbz hb
      omega

/-- Auxiliary: pair identity on the fuel-recursive helper, by
    induction on `fuel` with `D` generalised. -/
theorem ordAt_nonTwoTorsion_aux_pair_eq_rootMult
    (fuel : ℕ) (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 ≠ 0)
    (hFuel : D.a.natDegree + D.b.natDegree < fuel) :
    ordAt_nonTwoTorsion_aux E fuel D P
      + ordAt_nonTwoTorsion_aux E fuel D (P.1, -P.2)
      = rootMultiplicity P.1 (normPoly E D) := by
  classical
  induction fuel generalizing D with
  | zero => omega
  | succ n IH =>
    -- Unfold both calls.
    show
      (if D.a = 0 ∧ D.b = 0 then 0
       else if D.eval P.1 P.2 ≠ 0 then 0
       else if D.eval P.1 (-P.2) ≠ 0 then rootMultiplicity P.1 (normPoly E D)
       else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) P) +
      (if D.a = 0 ∧ D.b = 0 then 0
       else if D.eval P.1 (-P.2) ≠ 0 then 0
       else if D.eval P.1 (-(-P.2)) ≠ 0
              then rootMultiplicity P.1 (normPoly E D)
       else 1 + ordAt_nonTwoTorsion_aux E n (D.divLin P.1) (P.1, -P.2))
      = rootMultiplicity P.1 (normPoly E D)
    rw [if_neg hD, if_neg hD, neg_neg]
    by_cases h1 : D.eval P.1 P.2 = 0
    · rw [if_neg (not_not.mpr h1)]
      by_cases h2 : D.eval P.1 (-P.2) = 0
      · -- Twin case — both sheets vanish.
        rw [if_neg (not_not.mpr h2), if_neg (not_not.mpr h2),
            if_neg (not_not.mpr h1)]
        obtain ⟨hax, hbx⟩ : D.a.eval P.1 = 0 ∧ D.b.eval P.1 = 0 :=
          Da_Db_eval_zero_of_both_sheets_zero E D hY h1 h2
        have hD' : ¬ ((D.divLin P.1).a = 0 ∧ (D.divLin P.1).b = 0) :=
          divLin_not_both_zero E D hD hax hbx
        have hFuel' : (D.divLin P.1).a.natDegree + (D.divLin P.1).b.natDegree < n := by
          have := divLin_natDegree_sum_lt E D hD hax hbx
          omega
        have hIH := IH (D := D.divLin P.1) hD' hFuel'
        have hNFact := normPoly_divLin_factor E D hax hbx
        have hXsubCNZ : (Polynomial.X - Polynomial.C P.1 : (ZMod E.q)[X]) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero _
        have h2sq : (Polynomial.X - Polynomial.C P.1) ^ 2 ≠ 0 :=
          pow_ne_zero _ hXsubCNZ
        have hN'NZ : normPoly E (D.divLin P.1) ≠ 0 := normPoly_ne_zero E _ hD'
        have hMulNZ :
            (Polynomial.X - Polynomial.C P.1) ^ 2 * normPoly E (D.divLin P.1) ≠ 0 :=
          mul_ne_zero h2sq hN'NZ
        rw [hNFact, Polynomial.rootMultiplicity_mul hMulNZ,
            show (Polynomial.X - Polynomial.C P.1) ^ 2
                = (Polynomial.X - Polynomial.C P.1) * (Polynomial.X - Polynomial.C P.1)
              from sq _,
            Polynomial.rootMultiplicity_mul (mul_ne_zero hXsubCNZ hXsubCNZ),
            Polynomial.rootMultiplicity_X_sub_C_self]
        omega
      · -- Lone at P; D(P^σ) ≠ 0.
        rw [if_pos h2, if_pos h2]
        omega
    · -- D(P) ≠ 0; ord at P is 0.
      rw [if_pos h1]
      by_cases h2 : D.eval P.1 (-P.2) = 0
      · -- Lone at P^σ.
        rw [if_neg (not_not.mpr h2), if_pos h1]
        ring
      · -- Neither vanishes.
        push_neg at h2
        rw [if_pos h2]
        symm
        apply rootMultiplicity_eq_zero
        intro hRoot
        have hZE : (normPoly E D).eval P.1 = 0 := hRoot
        rw [normPoly_eval_eq_D_mul_D_neg E D hP] at hZE
        rcases mul_eq_zero.mp hZE with h | h
        · exact h1 h
        · exact h2 h

/-- **Obligation B** — non-2-torsion norm identity. -/
theorem ordAt_nonTwoTorsion_pair_eq_rootMult
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hY : P.2 ≠ 0) :
    ordAt_nonTwoTorsion E D P + ordAt_nonTwoTorsion E D (P.1, -P.2)
      = rootMultiplicity P.1 (normPoly E D) := by
  unfold ordAt_nonTwoTorsion
  -- Both calls use the same fuel `D.a.natDegree + D.b.natDegree + 1`.
  -- (At (P.1, -P.2), the fuel formula would compute the same since
  -- D doesn't change.)
  exact ordAt_nonTwoTorsion_aux_pair_eq_rootMult E _ D hD hP hY (by omega)

/-! ## Section 4: per-fiber sum identities -/

/-- For each `x₀`, the sum of `ordAt E D P` over F_q-points of `E`
    above `x₀` equals `rootMult x₀ (normPoly E D)` whenever there is
    at least one F_q-point above `x₀`.  Bounded by `rootMult` in
    general (case 0 F_q-points above ⇒ sum is 0). -/
theorem sum_ordAt_fst_eq_eq_rootMult
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (x₀ : ZMod E.q)
    (hExists : ∃ P : ZMod E.q × ZMod E.q, P ∈ E.points ∧ P.1 = x₀) :
    (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P)
      = rootMultiplicity x₀ (normPoly E D) := by
  classical
  set S := E.points.filter (fun P => P.1 = x₀) with hS
  have hCard : S.card ≤ 2 := card_points_with_fst_eq_le E x₀
  -- Card is 1 or 2 (since `hExists` makes it ≥ 1).
  obtain ⟨P0, hP0E, hP0x⟩ := hExists
  have hCardPos : 1 ≤ S.card := by
    have : P0 ∈ S := Finset.mem_filter.mpr ⟨hP0E, hP0x⟩
    exact Finset.card_pos.mpr ⟨P0, this⟩
  interval_cases hScard : S.card
  · -- |S| = 1: must be 2-torsion (else (-y) sheet would be in S too).
    rw [Finset.card_eq_one] at hScard
    obtain ⟨P, hSP⟩ := hScard
    rw [hSP, Finset.sum_singleton]
    have hPS : P ∈ S := by rw [hSP]; exact Finset.mem_singleton_self P
    have hPE : P ∈ E.points := (Finset.mem_filter.mp hPS).1
    have hPx : P.1 = x₀ := (Finset.mem_filter.mp hPS).2
    -- y₀ = 0 (else opposite sheet would also be in S).
    have hY0 : P.2 = 0 := by
      by_contra hY
      have ⟨hNegE, hNeq⟩ := neg_sheet_on_E E P hPE hY
      have hNegS : (P.1, -P.2) ∈ S := Finset.mem_filter.mpr ⟨hNegE, hPx⟩
      rw [hSP] at hNegS
      exact hNeq (Finset.mem_singleton.mp hNegS)
    -- Apply A.
    rw [ordAt_eq_dispatch E D hPE hD, if_pos hY0,
        ordAt_twoTorsion_eq_rootMult_normPoly E D hD hPE hY0, hPx]
  · -- |S| = 2: twin sheets (P, (P.1, -P.2)).
    rw [Finset.card_eq_two] at hScard
    obtain ⟨P₁, P₂, hNeq, hSP⟩ := hScard
    rw [hSP, Finset.sum_insert (Finset.notMem_singleton.mpr hNeq),
        Finset.sum_singleton]
    have hP₁ : P₁ ∈ E.points ∧ P₁.1 = x₀ := by
      have : P₁ ∈ S := by rw [hSP]; exact Finset.mem_insert_self _ _
      exact Finset.mem_filter.mp this
    have hP₂ : P₂ ∈ E.points ∧ P₂.1 = x₀ := by
      have : P₂ ∈ S := by
        rw [hSP]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact Finset.mem_filter.mp this
    -- y-coords differ; from y² = same, we get y₂ = -y₁.
    have hYneq : P₁.2 ≠ P₂.2 := fun h => hNeq (Prod.ext (hP₁.2.trans hP₂.2.symm) h)
    have hY₁sq : P₁.2 ^ 2 = P₁.1 ^ 3 + E.curveA * P₁.1 + E.curveB :=
      E.hOnCurve P₁ hP₁.1
    have hY₂sq : P₂.2 ^ 2 = P₂.1 ^ 3 + E.curveA * P₂.1 + E.curveB :=
      E.hOnCurve P₂ hP₂.1
    have hYsum : P₁.2 ^ 2 = P₂.2 ^ 2 := by
      rw [hY₁sq, hY₂sq, hP₁.2, hP₂.2]
    have hFactor : (P₁.2 - P₂.2) * (P₁.2 + P₂.2) = 0 := by linear_combination hYsum
    have hYneg : P₂.2 = -P₁.2 := by
      have hSumZero : P₁.2 + P₂.2 = 0 := by
        rcases mul_eq_zero.mp hFactor with h | h
        · exact absurd (sub_eq_zero.mp h) hYneq
        · exact h
      linear_combination hSumZero
    have hY₁ : P₁.2 ≠ 0 := by
      intro h
      apply hYneq
      rw [h, hYneg, h, neg_zero]
    -- ord at P₁ + ord at P₂ = ord_{P₁} + ord_{(P₁.1, -P₁.2)} = rootMult x₀ N(D).
    rw [ordAt_eq_dispatch E D hP₁.1 hD, if_neg hY₁,
        ordAt_eq_dispatch E D hP₂.1 hD, if_neg (by rw [hYneg]; simp [hY₁])]
    have hP₂coord : P₂ = (P₁.1, -P₁.2) := by
      apply Prod.ext
      · exact hP₂.2.trans hP₁.2.symm
      · exact hYneg
    rw [hP₂coord]
    rw [ordAt_nonTwoTorsion_pair_eq_rootMult E D hD hP₁.1 hY₁, hP₁.2]

/-- Per-x₀ bound (general case): `Σ_P ordAt ≤ rootMult x₀ (normPoly)`.
    Holds even when there are no F_q-points above x₀. -/
theorem sum_ordAt_fst_eq_le
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (x₀ : ZMod E.q) :
    (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P)
      ≤ rootMultiplicity x₀ (normPoly E D) := by
  classical
  by_cases hExists : ∃ P : ZMod E.q × ZMod E.q, P ∈ E.points ∧ P.1 = x₀
  · rw [sum_ordAt_fst_eq_eq_rootMult E D hD x₀ hExists]
  · have hEmpty : E.points.filter (fun P => P.1 = x₀) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro P hP hPx
      exact hExists ⟨P, hP, hPx⟩
    rw [hEmpty, Finset.sum_empty]
    exact Nat.zero_le _

/-! ## Section 5: `sum_ordAt_le_degE` -/

theorem sum_ordAt_le_degE
    (D : CoordRingElt E.q) :
    (∑ P ∈ E.points, ordAt E D P) ≤ D.degE := by
  classical
  by_cases hD : ¬ (D.a = 0 ∧ D.b = 0)
  · rw [sum_E_points_eq_sum_fiberwise E]
    calc (∑ x₀ : ZMod E.q,
            ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P)
        ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E D) :=
          Finset.sum_le_sum (fun x₀ _ => sum_ordAt_fst_eq_le E D hD x₀)
      _ ≤ (normPoly E D).natDegree :=
          sum_rootMultiplicity_le_natDegree E (normPoly E D)
      _ ≤ D.degE := normPoly_natDegree_le E D
  · push_neg at hD
    have hAllZero : ∀ P ∈ E.points, ordAt E D P = 0 := by
      intro P _; exact ordAt_eq_zero_of_zero E hD P
    calc (∑ P ∈ E.points, ordAt E D P)
        = 0 := Finset.sum_eq_zero hAllZero
      _ ≤ D.degE := Nat.zero_le _

/-! ## Section 6: equality under split -/

theorem sum_ordAt_eq_natDegree_under_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D) :
    (∑ P ∈ E.points, ordAt E D P) = (normPoly E D).natDegree := by
  classical
  rw [sum_E_points_eq_sum_fiberwise E]
  have hPer : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E D P)
        = rootMultiplicity x₀ (normPoly E D) := by
    intro x₀
    by_cases hRoot : x₀ ∈ (normPoly E D).roots
    · -- α is a root → splitsOnE.fiber gives F_q-point above.
      obtain ⟨y, hy⟩ := hSplit.2 x₀ hRoot
      exact sum_ordAt_fst_eq_eq_rootMult E D hD x₀ ⟨(x₀, y), hy, rfl⟩
    · -- Not a root → rootMult = 0; F_q-points above don't D-vanish.
      have hRMz : rootMultiplicity x₀ (normPoly E D) = 0 := by
        by_contra hne
        apply hRoot
        rw [Polynomial.mem_roots (normPoly_ne_zero E D hD)]
        exact (rootMultiplicity_pos (normPoly_ne_zero E D hD)).mp
          (Nat.pos_of_ne_zero hne)
      rw [hRMz]
      apply Finset.sum_eq_zero
      intro P hP
      simp only [Finset.mem_filter] at hP
      obtain ⟨hPE, hPx⟩ := hP
      have hDeval : D.eval P.1 P.2 ≠ 0 := by
        intro he
        apply hRoot
        rw [Polynomial.mem_roots (normPoly_ne_zero E D hD)]
        show (normPoly E D).IsRoot x₀
        unfold Polynomial.IsRoot
        rw [← hPx, normPoly_eval_eq_D_mul_D_neg E D hPE, he, zero_mul]
      have : ¬ 0 < ordAt E D P := by
        rw [ordAt_pos_iff_zero E D hD P hPE]; exact hDeval
      omega
  rw [Finset.sum_congr rfl (fun x₀ _ => hPer x₀)]
  rw [sum_rootMultiplicity_eq_card_roots]
  exact hSplit.1

/-! ## Section 7: group-sum-zero (Obligation C + Abel via principal_divisor_iff) -/

/-- The integer-valued divisor associated to a nonzero `D` on `E`:
    `Σ ordAt(D, P)·(P) − natDeg(N(D))·(O)` viewed as a function
    `ECPoint E → ℤ`.  Total degree is zero by construction (via
    `sum_ordAt_eq_natDegree_under_split` under splitsOnE; the
    unconditional total can differ when N(D) doesn't split).

    Defined here so we can phrase IsPrincipal of the divisor of D
    cleanly. -/
noncomputable def divisorOfD (D : CoordRingElt E.q) :
    ECPoint E → ℤ := by
  classical
  intro P
  exact
    match P with
    | WeierstrassCurve.Affine.Point.zero =>
        -((normPoly E D).natDegree : ℤ)
    | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ =>
        (ordAt E D (x, y) : ℤ)

/-- **Principal-divisor bridge axiom.**

    The divisor of `D = a − b·y ∈ F_q[E]^×`,
      `Σ_P ord_P(D) · (P) − natDeg(N(D)) · (∞)`,
    is principal — witnessed by `D` itself viewed as an element of the
    function field `F_q(E)`.

    The `splitsOnE` precondition is essential: without splitting, some
    geometric divisor mass lies on non-F_q-rational points, and the
    F_q-restricted `divisorOfD` cannot be principal (its degree is
    `-natDeg + Σ ordAt`, which equals zero only under splitting, by
    `sum_ordAt_eq_natDegree_under_split`).

    ## Why this is an axiom and not a theorem

    `IsPrincipal` is opaque (`Divisor/DefsPre.lean`).  The codebase
    exposes only one fact about it: `principal_divisor_iff`, which
    relates `IsPrincipal` to `(deg = 0 ∧ group_sum = 0)`.  That
    biconditional is itself an axiom.

    Every direct attempt to discharge `ordAt_divisor_isPrincipal` is
    circular within the current API:
    * `principal_divisor_iff.mp` requires `IsPrincipal` as input;
    * `principal_divisor_iff.mpr` requires `group_sum = 0`, which is
      exactly what we want to derive downstream from this bridge;
    * `CoordRingElt.has_principal_divisor` packages an existential
      `β` whose group-sum-zero is the original axiom we are
      discharging.

    Closing the loop requires the regular-function/divisor bridge for
    elliptic curves, which Mathlib does not currently provide at the
    `ECPoint`-level abstraction.

    ## This is *not* `exists_divisor_multiplicity` in disguise

    `exists_divisor_multiplicity` bundles five clauses:
      (i)   `β` exists with support on F_q-rational `D`-zeros;
      (ii)  `β` covers every F_q-rational `D`-zero;
      (iii) `Σ β ≤ D.degE` (unconditional);
      (iv)  `Σ β = (normPoly E D).natDegree` under splitting;
      (v)   group-sum-zero of `β` under splitting.

    This axiom supplies *only* the principal-divisor bridge for the
    specific witness `divisorOfD E D` (with `β = ordAt E D`).
    Clauses (i)–(iv) are fully **proved** from the redesigned
    `ordAt`:
    * (i), (ii) follow from `ordAt_pos_iff_zero`,
      `ordAt_eq_zero_offE` (Section 1–2 above);
    * (iii) is `sum_ordAt_le_degE`;
    * (iv) is `sum_ordAt_eq_natDegree_under_split` (modulo the
      proved Obligations A and B above).
    Clause (v) is derived from this axiom + the (axiomatic)
    `principal_divisor_iff` in `ordAt_group_sum_zero_under_split`.

    So the axiomatic content is strictly weaker: a single algebraic
    fact about regular functions on E, in place of a packaged
    existential with five clauses.

    ## Long-term cleanup

    Replacing both this axiom and `principal_divisor_iff` with proved
    theorems requires formalising:
    * `F_q(E)` as the fraction field of the coordinate ring;
    * the DVR structure of the local ring at each smooth affine point;
    * the divisor map `div : F_q(E)^× → (ECPoint E → ℤ)`;
    * `IsPrincipal` as `∃ f ∈ F_q(E)^×, div(f) = coeffs`;
    * compatibility of the recursive `ordAt` here with the abstract
      DVR valuation.
    Estimated ~2–3 weeks of focused Mathlib-level work.  Tracked as
    an explicit follow-up; until then, this axiom is the honest
    minimal seam. -/
axiom ordAt_divisor_isPrincipal
    (D : CoordRingElt E.q) (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    (_hSplit : splitsOnE E D) :
    IsPrincipal E (divisorOfD E D)

/-- The divisor `divisorOfD` has finite support (covered by
    `E.points` lifted to `ECPoint` via `affine`, plus the point at
    infinity). -/
theorem divisorOfD_finiteSupport
    (D : CoordRingElt E.q) :
    Set.Finite (Function.support (divisorOfD E D)) := by
  classical
  -- Covering finite set: { ECPoint.zero } ∪ image of E.points under affine.
  apply Set.Finite.subset
    (Set.Finite.insert (ECPoint.infinity : ECPoint E)
      (E.points.finite_toSet.image
        (fun P : ZMod E.q × ZMod E.q => ECPoint.affine E P.1 P.2)))
  intro P hP
  -- hP : divisorOfD E D P ≠ 0.
  match hP_match : P with
  | WeierstrassCurve.Affine.Point.zero =>
      exact Set.mem_insert _ _
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
      apply Set.mem_insert_of_mem
      -- (x, y) is on E (from hns being nonsingular ⇒ on curve).
      have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
        (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
      have hMem : (x, y) ∈ E.points := E.hComplete x y hOC
      refine ⟨(x, y), hMem, ?_⟩
      -- Need ECPoint.affine E x y = ECPoint.some hns.
      exact ECPoint.affine_of_nonsingular E hns

/-! ### Bridging helpers for the group-sum proof.

    These definitions require `DecidableEq (ECPoint E)`, which is
    available via `Classical`. -/

open Classical in
/-- Concrete finite cover of `divisorOfD`'s support: `{∞} ∪ image
    (affine) E.points`. -/
private noncomputable def divisorOfD_cover : Finset (ECPoint E) :=
  insert (ECPoint.infinity : ECPoint E)
    (E.points.image (fun P => ECPoint.affine E P.1 P.2))

open Classical in
/-- Infinity is not in the affine image (the `some _` constructor
    differs from `zero`). -/
private theorem infinity_notin_affine_image :
    (ECPoint.infinity : ECPoint E) ∉
      E.points.image (fun P => ECPoint.affine E P.1 P.2) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨Q, hQ, heq⟩ := hContra
  have hns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hns] at heq
  exact (WeierstrassCurve.Affine.Point.some_ne_zero hns) heq

/-- `ECPoint.affine E _.1 _.2` is injective on `E.points`. -/
private theorem affine_inj_on_points
    {P Q : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) (hQ : Q ∈ E.points)
    (h : ECPoint.affine E P.1 P.2 = ECPoint.affine E Q.1 Q.2) : P = Q := by
  classical
  have hPns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  have hQns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hPns,
      ECPoint.affine_of_nonsingular E hQns] at h
  rw [WeierstrassCurve.Affine.Point.some.injEq] at h
  exact Prod.ext h.1 h.2

/-- For `P ∈ E.points`, `divisorOfD E D (affine E P.1 P.2)` equals
    `(ordAt E D P : ℤ)`. -/
private theorem divisorOfD_affine
    (D : CoordRingElt E.q) {P : ZMod E.q × ZMod E.q} (hP : P ∈ E.points) :
    divisorOfD E D (ECPoint.affine E P.1 P.2) = (ordAt E D P : ℤ) := by
  classical
  have hns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  rw [ECPoint.affine_of_nonsingular E hns]
  rcases P with ⟨x, y⟩
  rfl

/-- `divisorOfD E D` is supported within the cover `divisorOfD_cover`. -/
private theorem divisorOfD_support_subset_cover (D : CoordRingElt E.q) :
    Function.support (divisorOfD E D) ⊆ ↑(divisorOfD_cover E) := by
  classical
  intro P hP
  simp only [Function.mem_support] at hP
  rw [Finset.mem_coe]
  unfold divisorOfD_cover
  match P, hP with
  | WeierstrassCurve.Affine.Point.zero, _ => exact Finset.mem_insert_self _ _
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns, hP =>
      refine Finset.mem_insert_of_mem ?_
      have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
        (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
      have hMem : (x, y) ∈ E.points := E.hComplete x y hOC
      exact Finset.mem_image.mpr
        ⟨(x, y), hMem, ECPoint.affine_of_nonsingular E hns⟩

/-- The `dCoeffsCandidate`-shaped weighted sum bridges the
    ECPoint-level and ZMod-pair-level forms. -/
private theorem weightedSum_divisorOfD_cover_eq (D : CoordRingElt E.q) :
    ECPoint.weightedSum E (divisorOfD_cover E)
        (fun P => ECPoint.zsmul E (divisorOfD E D P) P)
      = ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (ordAt E D P)
                        (ECPoint.affine E P.1 P.2)) := by
  classical
  unfold divisorOfD_cover
  rw [ECPoint.weightedSum_insert E (infinity_notin_affine_image E)]
  -- Infinity contribution: zsmul anything · zero = 0.
  rw [show ECPoint.zsmul E (divisorOfD E D (ECPoint.infinity : ECPoint E))
            (ECPoint.infinity : ECPoint E) = 0
        from ECPoint.zsmul_infinity E _,
      zero_add]
  -- Affine image sum = E.points sum (via injectivity).
  unfold ECPoint.weightedSum
  rw [Finset.sum_image
        (fun P₁ hP₁ P₂ hP₂ heq => affine_inj_on_points E hP₁ hP₂ heq)]
  apply Finset.sum_congr rfl
  intro P hP
  rw [divisorOfD_affine E D hP, ECPoint.zsmul_natCast]

/-- **Group-sum-zero** under `splitsOnE`. -/
theorem ordAt_group_sum_zero_under_split
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (hSplit : splitsOnE E D) :
    ECPoint.weightedSum E E.points
      (fun P => ECPoint.nsmul E (ordAt E D P)
                    (ECPoint.affine E P.1 P.2)) = 0 := by
  classical
  -- Step 1: `divisorOfD E D` is principal (uses splitsOnE).
  have hPrin : IsPrincipal E (divisorOfD E D) :=
    ordAt_divisor_isPrincipal E D hD hSplit
  have hFinSup : Set.Finite (Function.support (divisorOfD E D)) :=
    divisorOfD_finiteSupport E D
  -- Step 2: principal_divisor_iff gives Σ_supp zsmul(coeff)·P = 0.
  have hSumZero : ECPoint.weightedSum E hFinSup.toFinset
        (fun P => ECPoint.zsmul E (divisorOfD E D P) P) = 0 :=
    ((principal_divisor_iff E (divisorOfD E D) hFinSup).mp hPrin).2
  -- Step 3: extend to the cover (outside support, divisorOfD = 0 ⇒ zsmul = 0).
  have hSubFS : hFinSup.toFinset ⊆ divisorOfD_cover E := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact divisorOfD_support_subset_cover E D hP
  have hCoverSum :
      ECPoint.weightedSum E (divisorOfD_cover E)
          (fun P => ECPoint.zsmul E (divisorOfD E D P) P) = 0 := by
    rw [ECPoint.weightedSum_subset_of_zero_outside E hSubFS
          (fun P _ hPnotSup => by
            rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
            rw [hPnotSup]; exact ECPoint.zsmul_zero E P)]
    exact hSumZero
  -- Step 4: bridge the cover sum to the E.points sum.
  rw [← weightedSum_divisorOfD_cover_eq E D]
  exact hCoverSum

/-! ## Section 8: discharge `exists_divisor_multiplicity` -/

/-- **Goal of Phase 1**: the existential `β` axiom is discharged with
    witness `ordAt E D`.  Once Sections A/B/C above are filled, this
    theorem eliminates the `exists_divisor_multiplicity` axiom. -/
theorem exists_divisor_multiplicity_proved
    (D : CoordRingElt E.q) (hD : ¬ (D.a = 0 ∧ D.b = 0)) :
    ∃ β : ZMod E.q × ZMod E.q → ℕ,
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      (splitsOnE E D →
        (∑ P ∈ E.points, β P) = (normPoly E D).natDegree) ∧
      (splitsOnE E D →
        ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine E P.1 P.2)) = 0) := by
  refine ⟨ordAt E D, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    refine ⟨?_, ?_⟩
    · by_contra hOff
      exact hP (ordAt_eq_zero_offE E D hOff)
    · by_contra hNZ
      apply hP
      have hOnE : P ∈ E.points :=
        by_contra fun hOff => hP (ordAt_eq_zero_offE E D hOff)
      have : ¬ 0 < ordAt E D P := by
        rw [ordAt_pos_iff_zero E D hD P hOnE]; exact hNZ
      omega
  · intro P hP hZ
    rw [← Nat.pos_iff_ne_zero, ordAt_pos_iff_zero E D hD P hP]
    exact hZ
  · exact sum_ordAt_le_degE E D
  · exact sum_ordAt_eq_natDegree_under_split E D hD
  · exact ordAt_group_sum_zero_under_split E D hD

end Divisor
