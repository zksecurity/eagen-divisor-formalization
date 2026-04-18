import Divisor

/-!
  Counterexample.lean

  Demonstrates the logical inconsistency of
    `Divisor.extractorSucceeds_of_logDerivCheck_identically_zero`
  under Eagen's admissible set.

  # The malicious configuration

  - Field: `F_5`. Curve: `y² = x³ + 1` (5 affine F_5-rational points).
  - Statement: `k = 1`, `target = (0, 1)`, `bases 0 = (0, 4) = -target`.
  - Admissible set: Eagen, `{(a, b) : a.coeff 0 = 1}` — accepts `(1, 0)`.
  - Message: `polyA = 1`, `polyB = 0`, `m 0 = 4 = q - 1`.

  # Why the hypotheses hold

  Mechanized directly below:
    1. `toD.degE ≤ 3`: `CoordRingElt` degE uses `natDegree` (= 0 for
       both `1` and `0`), giving `max(0, 3) = 3`.
    2. `3 < 5`: decide.
    3. `admSet (1, 0)`: `(1 : Polynomial).coeff 0 = 1`.

  Argued in comment (paper `obs:neg-P-collapse`):
    4. `∀ A₀ A₁, logDerivCheckFn = 0`:
       - LHS: each `logDerivTerm` has numerator `D.a.derivative.eval -
         D.b.derivative.eval · _`, which is `(0 - 0) = 0` because
         `derivative 1 = 0` and `derivative 0 = 0`. So LHS = 0.
       - RHS: `-1/L(-P) + Σ -m_j/L(B_j)`. Since `B_0 = -P`, both
         denominators are `L(-P)`, so RHS = `(-1 - m_0)/L(-P) =
         -5/L(-P) = 0 · L(-P)⁻¹ = 0` in `ZMod 5` (regardless of whether
         `L(-P)` is zero, because the factor `-5 = 0`).

  # Why the conclusion is false

  `extractorSucceeds E stmt msg 3 rfl` requires the no-underflow
  guard `(1 + groupSum).val ≥ 1` at every canonical position whose
  `base = -P`. At `i = 0` (canonical, bases = -P), `groupSum = msg.m 0
  = 4`. So we need `(1 + 4 : ZMod 5).val ≥ 1`. But `(1 + 4 : ZMod 5) =
  0`, whose `.val = 0`, which fails `≥ 1`.

  This kernel arithmetic is decidable and mechanized below.
-/

open Polynomial
namespace CounterExample

noncomputable def E : Divisor.ECSetup where
  q := 5
  hq_prime := by decide
  curveA := 0
  curveB := 1
  points := {((0 : ZMod 5), (1 : ZMod 5)), ((0, 4)), ((2, 2)), ((2, 3)), ((4, 0))}
  hOnCurve := by decide
  hComplete := by decide
  numPoints := 6
  hNumPoints := by decide
  hq_ge := by decide

noncomputable def stmt : Divisor.DlogStatement E.q where
  k := 1
  bases := fun _ => ((0 : ZMod 5), (4 : ZMod 5))
  target := ((0 : ZMod 5), (1 : ZMod 5))
  admSet := fun p => p.1.coeff 0 = 1
  admSet_excludes_zero := by
    show ¬ ((0 : Polynomial (ZMod 5)).coeff 0 = 1)
    simp [Polynomial.coeff_zero]
    decide

noncomputable def msg : Divisor.MAProverMsg E.q where
  k := 1
  m := fun _ => 4
  polyA := 1
  polyB := 0

/-! ## The arithmetic kernel of the inconsistency -/

/-- **The no-underflow guard fails.** This is the decidable core:
    `(1 + 4 : ZMod 5)` has natural-number value `0`, which is not
    `≥ 1`. The extractor's underflow guard at the `-P` group would
    demand this value be `≥ 1`, but it isn't. -/
theorem no_underflow_guard_fails :
    ¬ ((1 + (4 : ZMod 5)).val ≥ 1) := by decide

/-- Equivalent phrasing: `1 + (q-1) ≡ 0 (mod q)`, and `ZMod.val` of
    that is `0`. -/
theorem sum_val_is_zero : (1 + (4 : ZMod 5)).val = 0 := by decide

/-! ## Structural facts (statically verified)

The three hypotheses of the axiom that can be proven by pure
elaboration/decide on the malicious instance:
-/

theorem admSet_holds : stmt.admSet (msg.polyA, msg.polyB) := by
  show ((1 : Polynomial (ZMod 5)).coeff 0 = 1)
  simp [Polynomial.coeff_one]

theorem toD_degree_le : msg.toD.degE ≤ 3 := by
  show max (2 * ((1 : Polynomial (ZMod 5)).natDegree))
           (3 + 2 * ((0 : Polynomial (ZMod 5)).natDegree)) ≤ 3
  simp [Polynomial.natDegree_one]

theorem three_lt_q : (3 : ℕ) < E.q := by decide

/-! ## Bases alias to -target

The structural fact that drives the inconsistency: the `msg` has a
basis at the target's negation. -/

theorem base_is_neg_target :
    stmt.bases ⟨0, by show 0 < stmt.k; decide⟩ =
      (stmt.target.1, -stmt.target.2) := by
  show ((0 : ZMod 5), (4 : ZMod 5)) = (0, -(1 : ZMod 5))
  decide

/-! ## What remains

To complete the mechanised `False` derivation we need the
`logDerivCheckFn ≡ 0` hypothesis and the translation from
`extractorSucceeds`'s no-underflow guard failure (at `i = 0`) to its
overall falsity. Both are structural/computational:

* `hAllZero`: with `polyA = 1, polyB = 0, m 0 = 4, B_0 = -P`,
  logDerivCheckFn is the zero function on `ZMod 5 × ZMod 5`. Verified
  above in the docstring; proof sketch:
    - LHS `= Σ logDerivTerm(λ, A_i)`. Each numerator is
      `a'.eval - b'.eval · y = 0 - 0 = 0`, so each term is 0.
    - RHS `= -1/L(-P) + -4/L(B_0)`. Denominators equal (B_0 = -P).
      Numerator sum `-1 + -4 = -5 = 0 (ZMod 5)`.

* Packaging `no_underflow_guard_fails` into
  `¬ extractorSucceeds E stmt msg 3 rfl`: apply the second conjunct of
  `extractorSucceeds` at `i = 0` with `isCanonical` (by uniqueness in
  `Fin 1`) and `base = -P` (by `base_is_neg_target`). The hypothesis
  chases through `extractorGroupSum = msg.m 0 = 4` to the false
  inequality above.

Both are mechanisable but require working around `Fin msg.k`
elaboration subtleties (`msg.k = 1` is definitional but the
`OfNat (Fin msg.k)` instance is not automatically found). Future work:
introduce explicit `Fin.mk 0 ⟨proof⟩` helpers and grind through.
-/

/-- Stated form of the final inconsistency theorem. Its proof is
    reducible to (1) the structural `logDerivCheckFn = 0` identity
    from `obs:neg-P-collapse` and (2) the arithmetic kernel
    `no_underflow_guard_fails` above. -/
theorem axiom_is_inconsistent_modulo_structural_facts
    (hAllZero : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points →
      Divisor.logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
        (fun i : Fin stmt.k => msg.m ((by rfl : stmt.k = msg.k) ▸ i)) A₀ A₁ = 0)
    (hSucc_false :
      Divisor.extractorSucceeds E stmt msg 3 rfl →
        ((1 + (4 : ZMod 5)).val ≥ 1)) :
    False := by
  have hSucc := Divisor.extractorSucceeds_of_logDerivCheck_identically_zero
                  E stmt msg 3 toD_degree_le three_lt_q rfl admSet_holds
                  hAllZero
  exact no_underflow_guard_fails (hSucc_false hSucc)

end CounterExample
