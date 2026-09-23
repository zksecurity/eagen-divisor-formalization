/-
  Divisor/AdmNormalizer.lean — normalizing a prover message into an
  admissible set.

  An honest prover message is determined only up to a nonzero scalar
  (`eq_smul_of_ordAt_eq`), while the protocol's admissible sets pin a
  normalization (`admSetParker`: `a` has linear coefficient `1`,
  `admSetLine`: constant coefficient `1`, `admSetHash`: nonzero hash).
  An `AdmNormalizer` packages an admissible set with a function that
  picks the scale, and two obligations:

  * `sound`: a returned scale is nonzero and lands in the set;
  * `complete`: if no scale is returned, no nonzero rescaling of the
    input lands in the set.

  Instances are given for the four admissible sets of `Divisor/Protocol.lean`.
-/
import Divisor.Protocol

open Polynomial

namespace Divisor

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- An admissible set together with a scale-picking normalizer. -/
structure AdmNormalizer (q : ℕ) [Fact (Nat.Prime q)] where
  admSet : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop
  normalize : CoordRingElt q → Option (ZMod q)
  sound : ∀ D c, normalize D = some c → c ≠ 0 ∧ admSet ((c • D).a, (c • D).b)
  complete : ∀ D, normalize D = none → ∀ c : ZMod q, c ≠ 0 → ¬ admSet ((c • D).a, (c • D).b)

open Classical in
/-- `admSetMax`: every nonzero element is admissible, so keep the scale. -/
noncomputable def admNormMax : AdmNormalizer q where
  admSet := admSetMax
  normalize D := if D.a = 0 ∧ D.b = 0 then none else some 1
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨one_ne_zero, ?_⟩
    simpa [admSetMax] using hD
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetMax, hD.1, hD.2]

open Classical in
/-- `admSetParker`: scale so that the linear coefficient of `a` is `1`. -/
noncomputable def admNormParker : AdmNormalizer q where
  admSet := admSetParker
  normalize D := if D.a.coeff 1 = 0 then none else some (D.a.coeff 1)⁻¹
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨inv_ne_zero hD, ?_⟩
    simp [admSetParker, inv_mul_cancel₀ hD]
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetParker, hD]

open Classical in
/-- `admSetLine`: scale so that the constant coefficient of `a` is `1`. -/
noncomputable def admNormLine : AdmNormalizer q where
  admSet := admSetLine
  normalize D := if D.a.coeff 0 = 0 then none else some (D.a.coeff 0)⁻¹
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨inv_ne_zero hD, ?_⟩
    simp [admSetLine, inv_mul_cancel₀ hD]
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetLine, hD]

/-- The hash functional is linear in the coefficients, and scaling by a
    nonzero constant preserves both degrees. -/
theorem admSetHashInner_smul (r : ℕ → ZMod q) (c : ZMod q) (hc : c ≠ 0)
    (D : CoordRingElt q) :
    admSetHashInner r ((c • D).a, (c • D).b) = c * admSetHashInner r (D.a, D.b) := by
  unfold admSetHashInner
  rw [CoordRingElt.smul_a, CoordRingElt.smul_b,
    Polynomial.natDegree_smul _ hc, Polynomial.natDegree_smul _ hc,
    mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
    rw [Polynomial.coeff_smul, smul_eq_mul] <;> ring

open Classical in
/-- `admSetHash r`: membership is invariant under nonzero scaling, so the
    element is either admissible as is or at no scale. -/
noncomputable def admNormHash (r : ℕ → ZMod q) : AdmNormalizer q where
  admSet := admSetHash r
  normalize D := if admSetHashInner r (D.a, D.b) = 0 then none else some 1
  sound D c h := by
    split_ifs at h with hD
    cases h
    exact ⟨one_ne_zero, by simpa [admSetHash] using hD⟩
  complete D h c hc := by
    split_ifs at h with hD
    have := admSetHashInner_smul r c hc D
    simp only [admSetHash, ne_eq, not_not]
    rw [this, hD, mul_zero]

end Divisor
