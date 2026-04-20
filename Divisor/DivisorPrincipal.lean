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
  exact ECPoint.noConfusion heq

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

/-! ## `dCoeffs_isPrincipal`

    Given `β` satisfying the conditions of `has_principal_divisor`,
    `dCoeffs D β` is principal on `E`. This is the conversion step
    from the axiom's multiplicity-level output to the `IsPrincipal`
    predicate consumed by the D4 infrastructure. -/

/-- **Principal divisor of `D` in coefficient form.** Given `β` from
    `has_principal_divisor`, the coefficient function `dCoeffs D β`
    (with `-D.degE` at `∞` and `β(P)` at affine `P`) is principal. -/
theorem dCoeffs_isPrincipal (D : CoordRingElt E.q)
    (β : ZMod E.q × ZMod E.q → ℕ)
    (hβsup : ∀ P, β P ≠ 0 → P ∈ E.points)
    (hβsum : (∑ P ∈ E.points, β P) = D.degE)
    (hβgroup : ECPoint.weightedSum E E.points
        (fun P => ECPoint.nsmul E (β P) (ECPoint.affine P.1 P.2)) = 0) :
    IsPrincipal E (dCoeffs E D β) := by
  classical
  set c := dCoeffs E D β with hc_def
  have hFinSupp : Set.Finite (Function.support c) :=
    dCoeffs_finiteSupport E D β hβsup
  apply (principal_divisor_iff E c hFinSupp).mpr
  constructor
  -- Degree sum = 0.
  · -- Σ_{P ∈ hFinSupp.toFinset} c P = Σ_{P ∈ candidate} c P.
    have hSubFS : hFinSupp.toFinset ⊆ dCoeffsCandidate E := by
      intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      exact dCoeffs_support_subset_candidate E D β hβsup hP
    have hSumFS_eq_cand :
        ∑ P ∈ hFinSupp.toFinset, c P
          = ∑ P ∈ dCoeffsCandidate E, c P := by
      rw [← Finset.sum_subset hSubFS]
      intro P _ hPnotSup
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hPnotSup
      exact hPnotSup
    rw [hSumFS_eq_cand, sum_dCoeffs_candidate_eq E D β]
    -- Σ (β P : ℤ) = ((Σ β P) : ℤ) = D.degE (by hβsum).
    rw [show ∑ P ∈ E.points, (β P : ℤ)
          = ((∑ P ∈ E.points, β P : ℕ) : ℤ) from by push_cast; rfl,
        hβsum]
    ring
  -- Group sum = 0.
  · have hSubFS : hFinSupp.toFinset ⊆ dCoeffsCandidate E := by
      intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      exact dCoeffs_support_subset_candidate E D β hβsup hP
    have hCandSum :
        ECPoint.weightedSum E (dCoeffsCandidate E)
            (fun P => ECPoint.zsmul E (c P) P) = 0 := by
      rw [weightedSum_dCoeffs_candidate_eq E D β]
      exact hβgroup
    -- The weightedSum on hFinSupp equals the weightedSum on candidate.
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
    `β` whose `dCoeffs`-encoding is principal. Directly combines
    `has_principal_divisor` with `dCoeffs_isPrincipal`. -/
theorem CoordRingElt.exists_principal_dCoeffs
    (D : CoordRingElt E.q) (hD : ¬ D.isZero) :
    ∃ (β : ZMod E.q × ZMod E.q → ℕ),
      (∀ P, β P ≠ 0 → P ∈ E.points ∧ D.eval P.1 P.2 = 0) ∧
      (∀ P ∈ E.points, D.eval P.1 P.2 = 0 → β P ≠ 0) ∧
      (∑ P ∈ E.points, β P) = D.degE ∧
      IsPrincipal E (dCoeffs E D β) := by
  have hD' : ¬ (D.a = 0 ∧ D.b = 0) := hD
  obtain ⟨β, hβsup, hβzeros, hβsum, hβgroup⟩ :=
    CoordRingElt.has_principal_divisor E D hD'
  refine ⟨β, hβsup, hβzeros, hβsum, ?_⟩
  exact dCoeffs_isPrincipal E D β
    (fun P hP => (hβsup P hP).1) hβsum hβgroup

end Divisor
