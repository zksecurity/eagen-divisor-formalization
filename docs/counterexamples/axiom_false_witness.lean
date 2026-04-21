/-!
# Historical counterexample — invalidated (Session 39) and superseded (Phase 4)

**This file applied to the OLD `logDerivTerm` definition** that used
the formal `x`-partial numerator `a'(x) − b'(x)·y` only. Under the new
paper-faithful `logDerivTerm` (Session 39 cascade), the numerator is
`(a'(x) − b'(x)·y) · 2y + (−b(x)) · (3x² + A)`.

For `D = y` (a = 0, b = -1), the new numerator evaluates to
`0 · 2y + 1 · (3x² + A) = 3x² + A`, NOT zero. The old `LT_Dy_zero` lemma
is thus no longer provable — the counterexample no longer applies, and
the axiom `polyG_zero_of_logDerivCheck_identically_zero` is no longer
provably false under the new definition.

**Phase 4 update (Session 44)**: the axiom itself has been eliminated
entirely. It is now a theorem taking a `hPolyGZero` hypothesis that
`ma_extractable` carries. This file remains relevant only as a
historical record of the Session 37 unsoundness-flag finding.

**The file is preserved as a historical artifact.** It will no longer
typecheck against the current codebase (`LT_Dy_zero` is false and the
axiom is deleted), but is kept for provenance. Do not import or run. -/
-- This file is NOT part of the Lake build (it lives under `docs/counterexamples/`).
-- Leaving it as historical reference; the lemmas below are false under the new
-- paper-faithful `logDerivTerm` definition.

import Divisor
open Divisor Polynomial

set_option maxHeartbeats 8000000

noncomputable def E7 : ECSetup where
  q := 7
  hq_prime := by decide
  curveA := 0
  curveB := 1
  points := ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7))
  hOnCurve := by
    intro p hp
    fin_cases hp <;> decide
  hComplete := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all (config := {decide := true})
  numPoints := 12
  hNumPoints := by decide
  hq_ge := by decide

-- Provide the Fact instance for ZMod 7 computations.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- D = y: a = 0, b = -1.
noncomputable def Dy : CoordRingElt 7 := { a := 0, b := -1 }

example : ¬ Dy.isZero := by
  intro ⟨_, hb⟩
  -- hb : Dy.b = 0, i.e., (-1 : Polynomial (ZMod 7)) = 0.
  apply_fun (Polynomial.eval 0) at hb
  simp [Dy] at hb

example : Dy.degE = 3 := by
  unfold CoordRingElt.degE Dy
  simp

-- D.eval x y = 0 - (-1)*y = y, so D.eval 3 0 = 0.
example : Dy.eval 3 0 = 0 := by
  unfold CoordRingElt.eval Dy
  simp

-- Q_c: 3 affine zeros of D = y on E.
def Q_c : Fin 3 → ZMod 7 × ZMod 7
  | ⟨0, _⟩ => (3, 0)
  | ⟨1, _⟩ => (5, 0)
  | ⟨2, _⟩ => (6, 0)

def beta_c : Fin 3 → ℕ := fun _ => 1

def B_c : Fin 1 → ZMod 7 × ZMod 7 := fun _ => (0, 6)

def m_c : Fin 1 → ZMod 7 := fun _ => -1

-- polyG computation: should be 5, not 0.
example : polyG E7 Q_c (fun k' => ((beta_c k' : ℕ) : ZMod 7))
            (Fin.cons (α := fun _ => ZMod 7 × ZMod 7) ((0 : ZMod 7), -(1 : ZMod 7)) B_c)
            (Fin.cons (α := fun _ => ZMod 7) (-1 : ZMod 7) m_c)
            (2, 3) (4, 3) = 5 := by
  unfold polyG
  unfold Q_c beta_c B_c m_c
  decide

-- Verify LT_Lean is 0 for D=y.
lemma LT_Dy_zero (lam : ZMod 7) (pt : ZMod 7 × ZMod 7) :
    logDerivTerm E7 Dy E7.curveA lam pt = 0 := by
  unfold logDerivTerm Dy
  simp

-- Verify logDerivCheckFn is zero at every pair (it's identically zero).
example (A₀ A₁ : ZMod 7 × ZMod 7) :
    logDerivCheckFn E7 Dy (0, 1) 1 B_c m_c A₀ A₁ = 0 := by
  unfold logDerivCheckFn
  simp only [LT_Dy_zero]
  -- After zeroing out LT terms, we have lhs = 0.
  -- rhs = -L(-P)⁻¹ + Σⱼ -mⱼ · L(Bⱼ)⁻¹ with m_0 = -1, B_0 = (0, 6) = -P.
  -- -(0,1).2 = -1 = 6 mod 7. So L(-P) at (0, -1) = L at (0, 6) since -1 = 6.
  simp only [B_c, m_c]
  -- P.1 = 0, -P.2 = -1 = 6 in ZMod 7.
  have hNeg : ((-(1 : ZMod 7))) = (6 : ZMod 7) := by decide
  rw [hNeg]
  -- Goal: (lhs = 0) - (-L⁻¹ + (-(-1))·L⁻¹) = 0 where both L are at (0,6).
  simp only [Fin.sum_univ_succ, Finset.sum_empty]
  -- -(-1) = 1 in ZMod 7.
  have h1 : (-(-1 : ZMod 7)) * ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval 0 6)⁻¹
          + 0 = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval 0 6)⁻¹ := by ring
  -- 6·L⁻¹ + L⁻¹ = 7·L⁻¹ = 0 in ZMod 7.
  have : (6 : ZMod 7) = -1 := by decide
  rw [this]
  simp

-- Conclusion: the axiom is FALSE.
-- Premise: logDerivCheckFn ≡ 0 at all pairs (including defined ones). ✓
-- Conclusion: polyG = 0 at all non-vertical E×E pairs.
-- But polyG ≠ 0 at (2,3)×(4,3). ✗
-- Therefore: polyG_zero_of_logDerivCheck_identically_zero is not provable.

-- Membership proofs for (2,3), (4,3).
example : ((2, 3) : ZMod 7 × ZMod 7) ∈ E7.points := by
  show _ ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7))
  decide

example : ((4, 3) : ZMod 7 × ZMod 7) ∈ E7.points := by
  show _ ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7))
  decide

-- Final refutation: assuming the axiom, derive False.
example (axiom_holds :
    ∀ (E : ECSetup) (D : CoordRingElt E.q) (_hD : ¬ D.isZero)
      (P : ZMod E.q × ZMod E.q) (k : ℕ)
      (B : Fin k → ZMod E.q × ZMod E.q) (m : Fin k → ZMod E.q)
      (_hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
        A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
        logDerivCheckFnDefined E D P B A₀ A₁ →
        logDerivCheckFn E D P k B m A₀ A₁ = 0)
      {d : ℕ}
      (Q : Fin d → ZMod E.q × ZMod E.q)
      (_beta : Fin d → ℕ)
      (_hQinj : Function.Injective Q)
      (_hQzeros : ∀ k' : Fin d,
         Q k' ∈ E.points ∧ D.eval (Q k').1 (Q k').2 = 0)
      (_hQcov : ∀ Q' ∈ E.points, D.eval Q'.1 Q'.2 = 0 →
         ∃ k' : Fin d, Q k' = Q')
      (_hβPos : ∀ k', _beta k' > 0)
      (_hβSum : (∑ k' : Fin d, _beta k') = D.degE)
      (A₀ A₁ : ZMod E.q × ZMod E.q)
      (_hA₀ : A₀ ∈ E.points) (_hA₁ : A₁ ∈ E.points) (_hNV : A₀.1 ≠ A₁.1),
      polyG E Q (fun k' => ((_beta k' : ℕ) : ZMod E.q))
                (Fin.cons (P.1, -P.2) B) (Fin.cons (-1) m)
                A₀ A₁ = 0) : False := by
  have hmemA0 : ((2, 3) : ZMod 7 × ZMod 7) ∈ E7.points := by
    show _ ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7))
    decide
  have hmemA1 : ((4, 3) : ZMod 7 × ZMod 7) ∈ E7.points := by
    show _ ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7))
    decide
  have hNZ : ¬ Dy.isZero := by
    intro ⟨_, hb⟩; apply_fun (Polynomial.eval 0) at hb; simp [Dy] at hb
  have hAllZero : ∀ A₀ A₁ : ZMod 7 × ZMod 7,
      A₀ ∈ E7.points → A₁ ∈ E7.points → A₀.1 ≠ A₁.1 →
      logDerivCheckFnDefined E7 Dy (0, 1) B_c A₀ A₁ →
      logDerivCheckFn E7 Dy (0, 1) 1 B_c m_c A₀ A₁ = 0 := by
    intro A₀ A₁ _ _ _ _
    -- Use the earlier proof — logDerivCheckFn ≡ 0 identically for D=y, B=-P.
    -- Copy inline.
    unfold logDerivCheckFn
    simp only [LT_Dy_zero]
    simp only [B_c, m_c]
    have hNeg : ((-(1 : ZMod 7))) = (6 : ZMod 7) := by decide
    rw [hNeg]
    simp only [Fin.sum_univ_succ, Finset.sum_empty]
    have h6 : (6 : ZMod 7) = -1 := by decide
    rw [h6]
    simp
  have hQinj : Function.Injective Q_c := by
    intro a b h
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso; simp [Q_c, Prod.mk.injEq] at h; revert h; decide)
  have hQzeros : ∀ k' : Fin 3, Q_c k' ∈ E7.points ∧ Dy.eval (Q_c k').1 (Q_c k').2 = 0 := by
    intro k'
    constructor
    · fin_cases k' <;> show _ ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7)) <;>
        simp [Q_c] <;> decide
    · fin_cases k' <;> simp [Q_c, Dy, CoordRingElt.eval]
  have hQcov : ∀ Q' ∈ E7.points, Dy.eval Q'.1 Q'.2 = 0 → ∃ k' : Fin 3, Q_c k' = Q' := by
    intro Q' hQ' hEv
    -- Dy.eval Q' = Q'.2 = 0. So Q' has y = 0.
    have hY : Q'.2 = 0 := by simpa [Dy, CoordRingElt.eval] using hEv
    -- Q' ∈ E7.points with y = 0 ⇒ Q' ∈ {(3,0), (5,0), (6,0)}.
    show _
    have : Q' = (3,0) ∨ Q' = (5,0) ∨ Q' = (6,0) := by
      show Q' = (3, 0) ∨ Q' = (5, 0) ∨ Q' = (6, 0)
      have : Q' ∈ ({(0,1),(0,6),(1,3),(1,4),(2,3),(2,4),(3,0),(4,3),(4,4),(5,0),(6,0)} : Finset (ZMod 7 × ZMod 7)) := by
        show _ ∈ E7.points; exact hQ'
      fin_cases this <;> simp_all <;> tauto
    rcases this with h | h | h
    · exact ⟨⟨0, by omega⟩, by simp [Q_c, h]⟩
    · exact ⟨⟨1, by omega⟩, by simp [Q_c, h]⟩
    · exact ⟨⟨2, by omega⟩, by simp [Q_c, h]⟩
  have hβPos : ∀ k', beta_c k' > 0 := fun _ => by simp [beta_c]
  have hβSum : (∑ k' : Fin 3, beta_c k') = Dy.degE := by
    unfold beta_c Dy CoordRingElt.degE; simp
  have hNV : ((2, 3) : ZMod 7 × ZMod 7).1 ≠ ((4, 3) : ZMod 7 × ZMod 7).1 := by decide
  -- Apply the axiom.
  have hConclusion := axiom_holds E7 Dy hNZ (0, 1) 1 B_c m_c hAllZero
    Q_c beta_c hQinj hQzeros hQcov hβPos hβSum (2, 3) (4, 3) hmemA0 hmemA1 hNV
  -- hConclusion : polyG ... = 0. But we computed polyG ... = 5.
  have hPolyG5 : polyG E7 Q_c (fun k' => ((beta_c k' : ℕ) : ZMod 7))
            (Fin.cons (α := fun _ => ZMod 7 × ZMod 7) ((0 : ZMod 7), -(1 : ZMod 7)) B_c)
            (Fin.cons (α := fun _ => ZMod 7) (-1 : ZMod 7) m_c)
            (2, 3) (4, 3) = 5 := by
    unfold polyG
    unfold Q_c beta_c B_c m_c
    decide
  -- P.1 = 0, P.2 = 1, so (P.1, -P.2) = (0, -1). matches.
  have : polyG E7 Q_c (fun k' => ((beta_c k' : ℕ) : ZMod 7))
            (Fin.cons (α := fun _ => ZMod 7 × ZMod 7) ((0 : ZMod 7), -(1 : ZMod 7)) B_c)
            (Fin.cons (α := fun _ => ZMod 7) (-1 : ZMod 7) m_c)
            (2, 3) (4, 3) = 0 := by
    have hP : (((0 : ZMod 7), (1 : ZMod 7)).1, -(((0 : ZMod 7), (1 : ZMod 7)).2))
            = ((0 : ZMod 7), -(1 : ZMod 7)) := rfl
    rw [← hP]
    exact hConclusion
  rw [hPolyG5] at this
  exact absurd this (by decide)
