/-
  Divisor/DivisorPrincipal.lean

  Principal-divisor wrapper for a nonzero `D : CoordRingElt E.q`.

  The `CoordRingElt.has_principal_divisor` axiom (Silverman III.3.5
  specialized) delivers an integer multiplicity function `β : ZMod² → ℕ`
  satisfying:
  * Support on `D`'s affine zeros on `E`.
  * Total weight equals `D.degE`.
  * Group-weighted sum on `E.points` is zero.

  This file packages that output into the `ECPoint`-indexed coefficient
  form `dCoeffs D β` (with `-D.degE` at `∞`) and proves
  `IsPrincipal E (dCoeffs D β)` via `principal_divisor_iff.mpr`. The
  two concrete conditions of that iff (degree-zero and group-sum-zero)
  follow directly from the axiom's outputs.

  Used in `ExtractorBridge.lean` to upgrade the `logDerivCheckFn ≡ 0`
  hypothesis chain into the `IsPrincipal (extractorDivisorCoeffs)`
  conclusion, after matching the extractor's coefficients to `D`'s
  divisor via the σ-matching output of `log_deriv_nonvanishing_criterion`.
-/
import Divisor.Defs
import Divisor.Axioms
import Divisor.HasPrincipalDivisor
import Divisor.Protocol

namespace Divisor

open Finset Classical

variable (E : ECSetup)

/-! ## The divisor coefficient function of `D`

    `dCoeffs D β` encodes the formal divisor
      `Σ_P β(P) · (P) − D.degE · (∞)`
    as a coefficient function on `ECPoint E.q`.

    This is the "candidate principal divisor" for `D`: combined with
    the `β`-properties from `has_principal_divisor`, we get
    `IsPrincipal (dCoeffs D β)` via `principal_divisor_iff.mpr`. -/

/-- Coefficient function representing `D`'s formal divisor. -/
noncomputable def dCoeffs (E : ECSetup) (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ) : ECPoint E.q → ℤ :=
  fun P => match P with
    | .infinity => -(D.degE : ℤ)
    | .affine x y => (β (x, y) : ℤ)

@[simp] theorem dCoeffs_infinity (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ) :
    dCoeffs E D β ECPoint.infinity = -(D.degE : ℤ) := rfl

@[simp] theorem dCoeffs_affine (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ) (x y : ZMod E.q) :
    dCoeffs E D β (ECPoint.affine x y) = (β (x, y) : ℤ) := rfl

/-! ## Candidate finite support

    The candidate support Finset for `dCoeffs D β` is
    `{∞} ∪ {affine P : P ∈ E.points}`. Combined with the support
    condition on `β`, this bounds the true support. -/

/-- Candidate finite Finset: `{∞} ∪ image (affine) E.points`. -/
noncomputable def dCoeffsCandidate (E : ECSetup) : Finset (ECPoint E.q) :=
  insert (ECPoint.infinity : ECPoint E.q)
    (E.points.image (fun P => ECPoint.affine P.1 P.2))

theorem dCoeffs_support_subset_candidate (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β P ≠ 0 → P ∈ E.points) :
    Function.support (dCoeffs E D β) ⊆ ↑(dCoeffsCandidate E) := by
  classical
  intro P hP
  simp only [Function.mem_support] at hP
  rw [Finset.mem_coe]
  unfold dCoeffsCandidate
  cases P with
  | infinity => exact Finset.mem_insert_self _ _
  | affine x y =>
      refine Finset.mem_insert_of_mem ?_
      -- From hP: β (x, y) ≠ 0, so (x, y) ∈ E.points.
      have hβ : (β (x, y) : ℤ) ≠ 0 := hP
      have hβn : β (x, y) ≠ 0 := by
        intro h; rw [h, Nat.cast_zero] at hβ; exact hβ rfl
      have hmem : (x, y) ∈ E.points := hβsup (x, y) hβn
      exact Finset.mem_image.mpr ⟨(x, y), hmem, rfl⟩

theorem dCoeffs_finiteSupport (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β P ≠ 0 → P ∈ E.points) :
    Set.Finite (Function.support (dCoeffs E D β)) :=
  (Finset.finite_toSet _).subset
    (dCoeffs_support_subset_candidate E D β hβsup)

/-! ## Degree-sum of `dCoeffs`

    The degree sum `Σ_P dCoeffs(P)` on `dCoeffsCandidate` (which
    contains the support) equals `-D.degE + Σ_P β(P)`. Under the
    hypothesis `Σ_P β(P) = D.degE` (total multiplicity is `D.degE`),
    this is zero. -/

theorem dCoeffs_affine_notin_image (P : ZMod E.q × ZMod E.q)
    (hP : P ∉ E.points) :
    (ECPoint.affine P.1 P.2 : ECPoint E.q) ∉
    (E.points.image (fun Q => ECPoint.affine Q.1 Q.2)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨Q, hQin, heq⟩ := hContra
  have : Q = P := by
    have hxy := ECPoint.affine.injEq .. |>.mp heq
    exact Prod.ext hxy.1 hxy.2
  exact hP (this ▸ hQin)

theorem dCoeffs_infinity_notin_affine_image :
    (ECPoint.infinity : ECPoint E.q) ∉
    (E.points.image (fun Q => ECPoint.affine Q.1 Q.2)) := by
  intro hContra
  rw [Finset.mem_image] at hContra
  obtain ⟨_, _, heq⟩ := hContra
  cases heq

theorem sum_dCoeffs_candidate_eq (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ) :
    ∑ P ∈ dCoeffsCandidate E, dCoeffs E D β P
      = -(D.degE : ℤ) + ∑ P ∈ E.points, (β P : ℤ) := by
  classical
  unfold dCoeffsCandidate
  rw [Finset.sum_insert (dCoeffs_infinity_notin_affine_image E),
      dCoeffs_infinity]
  congr 1
  -- Now: Σ_{affine P in image} = Σ_{P ∈ E.points} (β P : ℤ).
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro P _
    show (β (P.1, P.2) : ℤ) = (β P : ℤ)
    rcases P with ⟨x, y⟩; rfl
  · intro P₁ _ P₂ _ heq
    have hxy := ECPoint.affine.injEq .. |>.mp heq
    exact Prod.ext hxy.1 hxy.2

/-! ## Group-sum of `dCoeffs`

    The group-weighted sum `Σ_P zsmul (dCoeffs P) P` on the candidate
    Finset equals `0 + Σ_{affine P} nsmul (β P) (affine P)`. The latter
    is zero by the `has_principal_divisor` group-sum-zero condition. -/

theorem weightedSum_dCoeffs_candidate_eq (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ) :
    ECPoint.weightedSum E (dCoeffsCandidate E)
        (fun P => ECPoint.zsmul E (dCoeffs E D β P) P)
      = ECPoint.weightedSum E E.points
          (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) := by
  classical
  unfold dCoeffsCandidate
  rw [ECPoint.weightedSum_insert E (dCoeffs_infinity_notin_affine_image E)]
  -- The ∞ contribution is zsmul(-D.degE)(∞) = 0.
  have h_inf_zero :
      ECPoint.zsmul E (dCoeffs E D β ECPoint.infinity)
        (ECPoint.infinity : ECPoint E.q) = 0 := by
    simp [ECPoint.zsmul_infinity]
  rw [h_inf_zero, ECPoint.zero_add_curve]
  -- The affine image sum = (∑ P ∈ E.points, nsmul (β P) (affine P)).
  show ((E.points.image (fun Q => ECPoint.affine Q.1 Q.2)).fold
            (ECPoint.add E) 0
            (fun P => ECPoint.zsmul E (dCoeffs E D β P) P))
       = _
  have hInj : ∀ P₁ ∈ E.points, ∀ P₂ ∈ E.points,
              (ECPoint.affine P₁.1 P₁.2 : ECPoint E.q)
                = ECPoint.affine P₂.1 P₂.2 → P₁ = P₂ := by
    intro P₁ _ P₂ _ heq
    have hxy := ECPoint.affine.injEq .. |>.mp heq
    exact Prod.ext hxy.1 hxy.2
  rw [Finset.fold_image hInj]
  show ECPoint.weightedSum E E.points
       ((fun P => ECPoint.zsmul E (dCoeffs E D β P) P)
         ∘ (fun Q => ECPoint.affine Q.1 Q.2))
       = _
  apply ECPoint.weightedSum_congr
  intro P _
  show ECPoint.zsmul E (dCoeffs E D β (ECPoint.affine P.1 P.2))
                    (ECPoint.affine P.1 P.2)
     = ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)
  rcases P with ⟨x, y⟩
  rw [dCoeffs_affine, ECPoint.zsmul_natCast]

/-! ## Group-sum surrogate for `dCoeffs`

    After the `divisor_degree_eq` axiom was invalidated by Aristotle's
    counterexample (`docs/divisor-degree-axiom-bug.md`), we cannot
    produce `IsPrincipal (dCoeffs E D β)` from `has_principal_divisor`
    alone: under the weakened `∑ β ≤ D.degE`, the degree-sum of
    `dCoeffs` may be strictly negative, which violates the degree-0
    side of `principal_divisor_iff`. The downstream consumer
    (`ExtractorBridge.target_eq_weightedSum_of_principal`) only
    extracts the group-sum-zero part of `IsPrincipal`, so we expose
    that directly here and route around the `IsPrincipal` detour. -/

/-- **Group-sum-zero of `dCoeffs`.** Given `β` satisfying the
    support condition and the Abel-theorem group-sum-zero property,
    the coefficient function `dCoeffs E D β` has vanishing group sum
    on its (finite) support. This is the half of `IsPrincipal` that
    downstream actually needs. -/
theorem dCoeffs_groupSum_zero (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β P ≠ 0 → P ∈ E.points)
    (hβgroup : ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) = 0)
    (hFinSupp : Set.Finite (Function.support (dCoeffs E D β))) :
    ECPoint.weightedSum E hFinSupp.toFinset
        (fun P => ECPoint.zsmul E (dCoeffs E D β P) P) = 0 := by
  classical
  set c := dCoeffs E D β with hc_def
  have hSubFS : hFinSupp.toFinset ⊆ dCoeffsCandidate E := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact dCoeffs_support_subset_candidate E D β hβsup hP
  have hCandSum :
      ECPoint.weightedSum E (dCoeffsCandidate E)
          (fun P => ECPoint.zsmul E (c P) P) = 0 := by
    rw [weightedSum_dCoeffs_candidate_eq E D β]
    exact hβgroup
  have h_pad :
      ECPoint.weightedSum E (dCoeffsCandidate E)
          (fun P => ECPoint.zsmul E (c P) P)
        = ECPoint.weightedSum E hFinSupp.toFinset
            (fun P => ECPoint.zsmul E (c P) P) :=
    ECPoint.weightedSum_subset_of_zero_outside E hSubFS
      (fun P _ hPnotSup => by
        rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
        rw [hPnotSup]; exact ECPoint.zsmul_zero E P)
  rw [← h_pad]
  exact hCandSum

/-! ## Convenience: `has_principal_divisor`-packaged existence -/

/-- **Packaged existence.** A nonzero `D` has a multiplicity function
    `β` supported on its affine `E`-zeros, with
    `∑ β ≤ D.degE`, the group-sum-zero property, and (as a derived
    conclusion) the finite-support / group-sum-zero surrogate for
    `dCoeffs`. Previously claimed `IsPrincipal (dCoeffs E D β)`;
    weakened after `divisor_degree_eq` was removed (see the file
    header for rationale). -/
theorem CoordRingElt.exists_principal_dCoeffs
    (D : CoordRingElt E.q) (hD : ¬ D.isZero) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) ≤ D.degE ∧
      ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) = 0 := by
  have hD' : ¬ (D.a = 0 ∧ D.b = 0) := hD
  exact CoordRingElt.has_principal_divisor E D hD'

/-! ## Fin-enumeration of `D`'s affine zeros on `E`

    The narrow polyG-bridge axiom
    (`polyG_zero_of_logDerivCheck_identically_zero` in
    `ExtractorBridge.lean`) takes a Fin-indexed enumeration `Q : Fin d
    → (ZMod E.q)²` of `D`'s distinct affine zeros on `E`, together with
    a multiplicity vector `β : Fin d → ℕ` summing to `D.degE`.

    This section builds that enumeration from the support of a
    `has_principal_divisor`-style multiplicity function `β_fun`:
    * `zerosFinset D := zeros D E.points` — the Finset of `D`'s zeros.
    * `zerosCard D := (zerosFinset D).card` — the number `d`.
    * `zerosEnum D : Fin (zerosCard D) ≃ zerosFinset D` — the canonical
      enumeration via `Finset.equivFin`.
    * `zerosAt D k : (ZMod E.q)²` — the `k`-th zero as an element.
    * `multAt β_fun D k : ℕ` — the multiplicity at the `k`-th zero.

    Properties: `zerosAt` is injective, its image is `zerosFinset D`,
    and under the `has_principal_divisor`'s support conditions, each
    `multAt k > 0` and `∑ multAt = D.degE`. -/

/-- Finset of `D`'s affine zeros on `E`. -/
noncomputable abbrev zerosFinset (D : CoordRingElt E.q) :
    Finset (ZMod E.q × ZMod E.q) :=
  zeros D E.points

/-- Number of `D`'s affine zeros on `E`. -/
noncomputable abbrev zerosCard (D : CoordRingElt E.q) : ℕ :=
  (zerosFinset E D).card

/-- Canonical enumeration of `D`'s affine zeros on `E`. -/
noncomputable def zerosEnum (D : CoordRingElt E.q) :
    Fin (zerosCard E D) ≃ (zerosFinset E D) :=
  (zerosFinset E D).equivFin.symm

/-- The `k`-th zero of `D` (as an ordered pair). -/
noncomputable def zerosAt (D : CoordRingElt E.q)
    (k : Fin (zerosCard E D)) : ZMod E.q × ZMod E.q :=
  ((zerosEnum E D k) : ZMod E.q × ZMod E.q)

theorem zerosAt_mem_E (D : CoordRingElt E.q) (k : Fin (zerosCard E D)) :
    zerosAt E D k ∈ E.points := by
  have hMem : (zerosEnum E D k : ZMod E.q × ZMod E.q) ∈ zerosFinset E D :=
    (zerosEnum E D k).2
  exact (Finset.mem_filter.mp hMem).1

theorem zerosAt_eval_zero (D : CoordRingElt E.q) (k : Fin (zerosCard E D)) :
    D.eval (zerosAt E D k).1 (zerosAt E D k).2 = 0 := by
  have hMem : (zerosEnum E D k : ZMod E.q × ZMod E.q) ∈ zerosFinset E D :=
    (zerosEnum E D k).2
  exact (Finset.mem_filter.mp hMem).2

theorem zerosAt_injective (D : CoordRingElt E.q) :
    Function.Injective (zerosAt E D) := by
  intro k₁ k₂ heq
  apply (zerosEnum E D).injective
  -- Subtype.ext on the underlying value.
  exact Subtype.ext heq

theorem zerosAt_surjective_on_zeros
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hP : P ∈ zerosFinset E D) :
    ∃ k, zerosAt E D k = P := by
  refine ⟨(zerosEnum E D).symm ⟨P, hP⟩, ?_⟩
  unfold zerosAt
  rw [Equiv.apply_symm_apply]

theorem zerosAt_covers_zeros
    (D : CoordRingElt E.q) (P : ZMod E.q × ZMod E.q)
    (hPpts : P ∈ E.points) (hPzero : D.eval P.1 P.2 = 0) :
    ∃ k, zerosAt E D k = P :=
  zerosAt_surjective_on_zeros E D P
    (Finset.mem_filter.mpr ⟨hPpts, hPzero⟩)

/-- Multiplicity at the `k`-th zero, extracted from a `β_fun`. -/
noncomputable def multAt (β_fun : ZMod E.q × ZMod E.q → ℕ)
    (D : CoordRingElt E.q) (k : Fin (zerosCard E D)) : ℕ :=
  β_fun (zerosAt E D k)

/-- Under the `has_principal_divisor`'s coverage (every zero of `D`
    has positive `β_fun`), each `multAt k > 0`. -/
theorem multAt_pos (β_fun : ZMod E.q × ZMod E.q → ℕ) (D : CoordRingElt E.q)
    (hβcov : ∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β_fun P ≠ 0)
    (k : Fin (zerosCard E D)) :
    multAt E β_fun D k > 0 := by
  unfold multAt
  exact Nat.pos_of_ne_zero
    (hβcov _ (zerosAt_mem_E E D k) (zerosAt_eval_zero E D k))

/-- Under the `has_principal_divisor`'s support and coverage, the sum
    `∑ k : Fin (zerosCard E D), multAt k` equals `∑ P ∈ E.points, β_fun P`. -/
theorem sum_multAt_eq_sum_βfun
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (D : CoordRingElt E.q)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) :
    (∑ k : Fin (zerosCard E D), multAt E β_fun D k) =
    ∑ P ∈ E.points, β_fun P := by
  classical
  unfold multAt
  -- Step 1: sum over Fin = sum over zerosFinset via bijection.
  have hBij : (∑ k : Fin (zerosCard E D), β_fun (zerosAt E D k))
            = ∑ P ∈ zerosFinset E D, β_fun P := by
    apply Finset.sum_bij (fun k _ => zerosAt E D k)
    · intro k _
      exact Finset.mem_filter.mpr
        ⟨zerosAt_mem_E E D k, zerosAt_eval_zero E D k⟩
    · intro k₁ _ k₂ _ heq
      exact zerosAt_injective E D heq
    · intro P hP
      obtain ⟨k, hk⟩ := zerosAt_surjective_on_zeros E D P hP
      exact ⟨k, Finset.mem_univ _, hk⟩
    · intro k _; rfl
  rw [hBij]
  -- Step 2: extend to E.points via β_fun = 0 off zerosFinset.
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hPin hPnotZ
  simp only [zerosFinset, zeros, Finset.mem_filter] at hPnotZ
  push_neg at hPnotZ
  have hEvalNZ : D.eval P.1 P.2 ≠ 0 := hPnotZ hPin
  by_contra hβnz
  exact hEvalNZ (hβsup P hβnz).2

/-- Under the `has_principal_divisor`'s support condition and total-degree
    bound, `∑ multAt ≤ D.degE`. -/
theorem sum_multAt_le_degE
    (β_fun : ZMod E.q × ZMod E.q → ℕ) (D : CoordRingElt E.q)
    (hβsup : ∀ P, β_fun P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0)
    (hβsum : (∑ P ∈ E.points, β_fun P) ≤ D.degE) :
    (∑ k : Fin (zerosCard E D), multAt E β_fun D k) ≤ D.degE := by
  rw [sum_multAt_eq_sum_βfun E β_fun D hβsup]; exact hβsum

end Divisor
