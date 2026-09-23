/-
  Divisor/AdmNormalizer.lean — normalizing a prover message into an
  admissible set, computably.

  An honest prover message is determined only up to a nonzero scalar
  (`eq_smul_of_ordAt_eq`), while the protocol's admissible sets pin a
  normalization (`admSetParker`: `a` has linear coefficient `1`,
  `admSetLine`: constant coefficient `1`, `admSetHash`: nonzero hash).
  An `AdmNormalizer` packages an admissible set with a computable
  function that picks the scale from a `CoordRingEltC`, and two
  obligations, stated through `toCoordRingElt`:

  * `sound`: a returned scale is nonzero and lands in the set;
  * `complete`: if no scale is returned, no nonzero rescaling of the
    input lands in the set.

  Instances are given for the four admissible sets of `Divisor/Protocol.lean`.
-/
import Divisor.Protocol
import Divisor.CoordRingEltC.Bridge

open Polynomial

namespace Divisor

/-! ## `CoeffPoly` facts used by the normalizers -/

namespace CoeffPoly

variable {q : ℕ} [Fact (Nat.Prime q)]

theorem coeff_smul (c : ZMod q) (p : CoeffPoly q) (n : ℕ) :
    (c • p).coeff n = c * p.coeff n := by
  show ((p.coeffs.map (c * ·))[n]?).getD 0 = c * (p.coeffs[n]?).getD 0
  rw [List.getElem?_map]
  cases p.coeffs[n]? <;> simp

theorem toPolynomial_smul (c : ZMod q) (p : CoeffPoly q) :
    (c • p).toPolynomial = c • p.toPolynomial := by
  ext n
  rw [toPolynomial_coeff, Polynomial.coeff_smul, toPolynomial_coeff, coeff_smul, smul_eq_mul]

theorem toPolynomial_eq_zero_iff (p : CoeffPoly q) :
    p.toPolynomial = 0 ↔ ∀ x ∈ p.coeffs, x = 0 := by
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    have := congrArg (fun P => P.coeff i) h
    simp only [toPolynomial_coeff, Polynomial.coeff_zero, coeff, hi, Option.getD_some] at this
    exact this
  · intro h
    ext n
    rw [toPolynomial_coeff, Polynomial.coeff_zero, coeff]
    cases hn : p.coeffs[n]? with
    | none => rfl
    | some x => exact h x (List.mem_of_getElem? hn)

/-- Computable degree: the last index with a nonzero coefficient. -/
def natDegC (p : CoeffPoly q) : ℕ :=
  Nat.findGreatest (fun n => p.coeff n ≠ 0) p.coeffs.length

theorem natDegC_eq (p : CoeffPoly q) : p.natDegC = p.toPolynomial.natDegree := by
  rw [natDegC, Nat.findGreatest_eq_iff]
  refine ⟨?_, fun hne => ?_, fun k hk _ => ?_⟩
  · have := natDegree_toPolynomial_le p; omega
  · rw [← toPolynomial_coeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun h0 => hne (by rw [h0, natDegree_zero]))
  · rw [← toPolynomial_coeff, not_not]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hk

end CoeffPoly

variable {q : ℕ} [Fact (Nat.Prime q)]

/-! ## Normalizers -/

/-- An admissible set together with a computable scale-picking normalizer. -/
structure AdmNormalizer (q : ℕ) [Fact (Nat.Prime q)] where
  admSet : Polynomial (ZMod q) × Polynomial (ZMod q) → Prop
  normalize : CoordRingEltC q → Option (ZMod q)
  sound : ∀ D c, normalize D = some c →
    c ≠ 0 ∧ admSet ((c • D.toCoordRingElt).a, (c • D.toCoordRingElt).b)
  complete : ∀ D, normalize D = none → ∀ c : ZMod q, c ≠ 0 →
    ¬ admSet ((c • D.toCoordRingElt).a, (c • D.toCoordRingElt).b)

/-- `admSetMax`: every nonzero element is admissible, so keep the scale. -/
def admNormMax : AdmNormalizer q where
  admSet := admSetMax
  normalize D :=
    if (∀ x ∈ D.a.coeffs, x = 0) ∧ (∀ x ∈ D.b.coeffs, x = 0) then none else some 1
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨one_ne_zero, ?_⟩
    simp only [CoordRingElt.smul_a, CoordRingElt.smul_b, one_smul]
    intro h0
    apply hD
    simp only [Prod.mk.injEq, CoordRingEltC.toCoordRingElt_a,
      CoordRingEltC.toCoordRingElt_b] at h0
    exact ⟨(CoeffPoly.toPolynomial_eq_zero_iff _).mp h0.1,
      (CoeffPoly.toPolynomial_eq_zero_iff _).mp h0.2⟩
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetMax, (CoeffPoly.toPolynomial_eq_zero_iff _).mpr hD.1,
      (CoeffPoly.toPolynomial_eq_zero_iff _).mpr hD.2]

/-- `admSetParker`: scale so that the linear coefficient of `a` is `1`. -/
def admNormParker : AdmNormalizer q where
  admSet := admSetParker
  normalize D := if D.a.coeff 1 = 0 then none else some (D.a.coeff 1)⁻¹
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨inv_ne_zero hD, ?_⟩
    simp [admSetParker, CoeffPoly.toPolynomial_coeff, inv_mul_cancel₀ hD]
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetParker, CoeffPoly.toPolynomial_coeff, hD]

/-- `admSetLine`: scale so that the constant coefficient of `a` is `1`. -/
def admNormLine : AdmNormalizer q where
  admSet := admSetLine
  normalize D := if D.a.coeff 0 = 0 then none else some (D.a.coeff 0)⁻¹
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨inv_ne_zero hD, ?_⟩
    simp [admSetLine, CoeffPoly.toPolynomial_coeff, inv_mul_cancel₀ hD]
  complete D h c _ := by
    split_ifs at h with hD
    simp [admSetLine, CoeffPoly.toPolynomial_coeff, hD]

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

/-- Computable `admSetHashInner` on coefficient lists. -/
def admSetHashInnerC (r : ℕ → ZMod q) (D : CoordRingEltC q) : ZMod q :=
  (∑ i ∈ Finset.range (D.a.natDegC + 1), r i * D.a.coeff i) +
  (∑ i ∈ Finset.range (D.b.natDegC + 1), r (D.a.natDegC + 1 + i) * D.b.coeff i)

theorem admSetHashInnerC_eq (r : ℕ → ZMod q) (D : CoordRingEltC q) :
    admSetHashInnerC r D = admSetHashInner r (D.toCoordRingElt.a, D.toCoordRingElt.b) := by
  simp only [admSetHashInnerC, admSetHashInner, CoordRingEltC.toCoordRingElt_a,
    CoordRingEltC.toCoordRingElt_b, CoeffPoly.natDegC_eq, CoeffPoly.toPolynomial_coeff]

/-- `admSetHash r`: membership is invariant under nonzero scaling, so the
    element is either admissible as is or at no scale. -/
def admNormHash (r : ℕ → ZMod q) : AdmNormalizer q where
  admSet := admSetHash r
  normalize D := if admSetHashInnerC r D = 0 then none else some 1
  sound D c h := by
    split_ifs at h with hD
    cases h
    refine ⟨one_ne_zero, ?_⟩
    simp only [CoordRingElt.smul_a, CoordRingElt.smul_b, one_smul]
    simpa [admSetHash, admSetHashInnerC_eq] using hD
  complete D h c hc := by
    split_ifs at h with hD
    have := admSetHashInner_smul r c hc D.toCoordRingElt
    rw [admSetHashInnerC_eq] at hD
    simp only [admSetHash, ne_eq, not_not]
    rw [this, hD, mul_zero]

end Divisor
