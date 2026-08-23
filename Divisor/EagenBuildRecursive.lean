/-
  Divisor/EagenBuildRecursive.lean

  Two things live here:

  1. The recursive `eagenBuild` driver for general-N point lists,
     following Eagen §3.1.1 ("Incremental construction") in 596.pdf.
  2. The `IsHonestForExplicit` completeness bridge: from an honest
     message (divisor identity + on-curve invariants) to verifier
     acceptance off the bad-challenge set, culminating in
     `ma_completeness_via_isHonestForExplicit` and the length-4-simple
     instantiation `isHonestFor_of_isHonestForLength4Simple` consumed
     by `Divisor/Completeness.lean`.

  ## The construction (for sum-zero list `Ps`)

  **Level 0**: pair adjacent inputs `(P_2i, P_2i+1)`, build chord line
  `L_i` through them with third intersection `Q_i = -(P_2i + P_2i+1)`.
  Each such pair produces a level-1 entry `(-Q_i, L_i)` — point is
  `-Q_i = P_2i + P_2i+1` (group sum), polynomial is the chord line.

  **Level k → k+1** (k ≥ 1): given level-k entries `(a_pt, a_poly)` and
  `(b_pt, b_poly)` (where the points are `-Q_*` from previous level),
  build chord line `L'` through `a_pt, b_pt` with third intersection
  `Q'`. The level-(k+1) entry is `(-Q', M)` where:

      M = (L' · a_poly · b_poly) / ((X - x(a_pt)) · (X - x(b_pt)))

  Both `(X - x(a_pt))` and `(X - x(b_pt))` divide cleanly because the
  numerator vanishes at both `±a_pt.1` (since `L'` vanishes at `a_pt`
  and `a_poly` vanishes at `-(a_pt) = Q_{prev}`) and similarly for
  `b_pt`.

  **Termination**: when the input list is sum-zero, the final third
  intersection at the top level is `O` (infinity). The output polynomial
  has divisor exactly `Σ(P_i) - n·O`.

  **Odd lengths**: carry the unpaired entry forward to the next level.

  No correctness theorem for the recursive driver is proved here; the
  production completeness chain goes through the Landmark route
  (`EagenBuildLandmark.lean`, `IsHonestForBinary.lean`,
  `SafeSupport.lean`). The length-4 base case is handled explicitly in
  `Divisor/IncrementalConstruction.lean`.
-/

import Divisor.IncrementalConstruction
import Divisor.LogDerivEagenLength4
import Divisor.WeilReciprocityDescent

open Polynomial Finset Classical

namespace Divisor

variable (E : ECSetup)

/-- An "accumulator" entry at level k > 0: a point (= -Q from prior
    level chord = group-sum of absorbed P's at this level) and the
    accumulated polynomial whose divisor incorporates the absorbed P's
    plus the third intersection. -/
structure EagenAccum where
  point : ZMod E.q × ZMod E.q
  poly : CoordRingElt E.q

/-! ## Level-0 step: build chord lines from input points

For a list of input points `[P_0, P_1, ..., P_{n-1}]`, pair them up and
build chord lines. Each pair `(P_2i, P_2i+1)` produces a level-1 entry
`(-Q_i, L_i)`.

Odd-length input: the last (unpaired) point becomes a level-1 entry
`(P_{n-1}, 1)` carrying just the point with identity polynomial. -/

/-- Build a level-1 accumulator from two distinct affine points.
    The chord through `P, Q` has third intersection `-(P+Q)`; the new
    accumulator is `(-(P+Q), chord)`. -/
noncomputable def EagenAccum.fromChordPair_distinct
    (P Q : ZMod E.q × ZMod E.q) (_h_xx : P.1 ≠ Q.1) : EagenAccum E :=
  let chord := chordCoordRingElt E P Q
  let lam := slopeOf P.1 P.2 Q.1 Q.2
  let Qx := lam ^ 2 - P.1 - Q.1
  let Qy := lam * Qx + (P.2 - lam * P.1)
  -- Third intersection is (Qx, Qy). The "next-level input" is its negation.
  { point := (Qx, -Qy), poly := chord }

/-- Build a level-1 accumulator from two points that are negatives of
    each other (`P = -Q`, so same x, opposite y, sum-zero in group law).
    The chord through `(P, -P)` is the vertical line `(X - x(P))`, which
    has divisor `(P) + (-P) - 2·O`. The "third intersection" is `O`;
    the new accumulator carries the vertical line as polynomial and `P`
    as point (sentinel — actual contribution is at infinity). -/
noncomputable def EagenAccum.fromChordPair_vertical
    (P Q : ZMod E.q × ZMod E.q) (_h_xx : P.1 = Q.1) (_h_yy : P.2 = -Q.2) :
    EagenAccum E :=
  { point := P,  -- Sentinel; level transitions handle this.
    poly := { a := Polynomial.X - Polynomial.C P.1, b := 0 } }

/-- Process the initial input list, pairing adjacent points and building
    chord lines. Returns the level-1 accumulator list. Odd input lengths
    carry the last point forward as `(P_last, 1)`. -/
noncomputable def eagenBuild_level0 (Ps : List (ZMod E.q × ZMod E.q)) :
    List (EagenAccum E) :=
  match Ps with
  | [] => []
  | [P] => [{ point := P, poly := { a := 1, b := 0 } }]
  | P :: Q :: rest =>
      if h : P.1 ≠ Q.1 then
        EagenAccum.fromChordPair_distinct E P Q h :: eagenBuild_level0 rest
      else if hYY : P.2 = -Q.2 then
        -- Vertical chord case: P = -Q.
        EagenAccum.fromChordPair_vertical E P Q
          (Classical.byContradiction (fun h_neq => h h_neq)) hYY ::
          eagenBuild_level0 rest
      else
        -- Tangent doubling case (P = Q): deferred.
        { point := P, poly := { a := 1, b := 0 } } :: eagenBuild_level0 rest

/-! ## Level-(k+1) step (k ≥ 1): combine two level-k accumulators

Combine `(a_pt, a_poly)` and `(b_pt, b_poly)` per the paper formula:
    `new_poly = chord(a_pt, b_pt) · a_poly · b_poly / divLin(a_pt.1) / divLin(b_pt.1)`. -/

noncomputable def EagenAccum.combine_higher_distinct
    (a b : EagenAccum E) (_h_xx : a.point.1 ≠ b.point.1) : EagenAccum E :=
  let chord := chordCoordRingElt E a.point b.point
  let lam := slopeOf a.point.1 a.point.2 b.point.1 b.point.2
  let Qx := lam ^ 2 - a.point.1 - b.point.1
  let Qy := lam * Qx + (a.point.2 - lam * a.point.1)
  let mul_with_chord := mulCoordRingElt E (mulCoordRingElt E chord a.poly) b.poly
  let after_div_a := mul_with_chord.divLin a.point.1
  let after_div_b := after_div_a.divLin b.point.1
  { point := (Qx, -Qy), poly := after_div_b }

/-- Combine two accumulators when their points are negatives of each
    other (`a.point = -b.point`, so `a.point.1 = b.point.1`). The chord
    through `(P, -P)` is the vertical line `(X - x(P))`. Their group sum
    is `0` (the identity = ∞), so the level-(k+1) "third intersection"
    is also `O`.

    Polynomial: `(X - x(a.point)) · a.poly · b.poly / (X - x(a.point))^2
                = a.poly · b.poly / (X - x(a.point))`. -/
noncomputable def EagenAccum.combine_higher_vertical
    (a b : EagenAccum E)
    (_h_xx : a.point.1 = b.point.1) (_h_yy : a.point.2 = -b.point.2) :
    EagenAccum E :=
  -- Combined = a.poly · b.poly / (X - x(a.point)).
  let mul_ab := mulCoordRingElt E a.poly b.poly
  let combined := mul_ab.divLin a.point.1
  -- "New point" is the identity (= O). Encode as the affine pair (a.point.1, 0)
  -- as a sentinel; in the divisor equation, the actual contribution is at ∞.
  -- Since the recursion should terminate here for sum-zero inputs, the
  -- output is whatever consumer extracts.
  { point := a.point, poly := combined }

/-- Process a level-k (k ≥ 1) accumulator list, pairing adjacent entries
    and combining each pair. Odd-length lists carry the last entry forward. -/
noncomputable def eagenBuild_level_step (xs : List (EagenAccum E)) :
    List (EagenAccum E) :=
  match xs with
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
      if h : a.point.1 ≠ b.point.1 then
        EagenAccum.combine_higher_distinct E a b h :: eagenBuild_level_step rest
      else if hYY : a.point.2 = -b.point.2 then
        -- Vertical chord case (a.point = -b.point).
        EagenAccum.combine_higher_vertical E a b
          (Classical.byContradiction (fun h_neq => h h_neq)) hYY ::
          eagenBuild_level_step rest
      else
        -- Tangent doubling: a.point = b.point. Deferred.
        a :: b :: eagenBuild_level_step rest

/-! ## Top-level driver

Iterate `eagenBuild_level_step` until the list reduces to one entry. Use
`fuel := xs.length` as a termination measure (each step at least halves
the list, so log₂ of length is sufficient; length itself is overkill but
safe). -/

noncomputable def eagenBuild_iterate :
    ℕ → List (EagenAccum E) → List (EagenAccum E)
  | 0, xs => xs
  | n + 1, xs =>
      if xs.length ≤ 1 then xs
      else eagenBuild_iterate n (eagenBuild_level_step E xs)

/-- Top-level eagenBuild: from a list of input points (assumed sum-zero),
    produces the polynomial witness whose divisor is `Σ (P_i) - n·O`. -/
noncomputable def eagenBuild (Ps : List (ZMod E.q × ZMod E.q)) : CoordRingElt E.q :=
  let level1 := eagenBuild_level0 E Ps
  let final := eagenBuild_iterate E Ps.length level1
  match final with
  | [] => { a := 1, b := 0 }
  | [single] => single.poly
  | _ => { a := 1, b := 0 }  -- shouldn't happen if iterations sufficient

/-! ## `IsHonestForExplicit` predicate (any-k completeness path)

Definitional alias of `MAProverMsg.isHonestFor` (`Protocol.lean`),
which bundles scalar reduction (`.1`), `splitsOnE` (`.2.1`), the
extensional divisor identity (`.2.2.1`), and the on-curve invariants
(`.2.2.2.1`, `.2.2.2.2`); call sites destructure it through those
projections. -/

def MAProverMsg.IsHonestForExplicit (E : ECSetup) (msg : MAProverMsg E.q)
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hkm : stmt.k = msg.k) : Prop :=
  msg.isHonestFor E stmt wit hk hkm

/-! ## General hQline derivation from `hGood`

For any nonzero D, if `(A_0, A_1) ∉ badChallengesCompleteness E D`, then
the chord through `A_0, A_1` doesn't pass through any zero of D.

Proof: Bezout — chord intersects E in `{A_0, A_1, A_2}`. Any zero of
D on E that's also on the chord must be in this set, but `¬bad` excludes
D vanishing at A_0, A_1, or A_2. -/

theorem hQline_of_hGood_general
    {D : CoordRingElt E.q} (_hD : ¬ (D.a = 0 ∧ D.b = 0))
    {A₀ A₁ : ZMod E.q × ZMod E.q}
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E D) :
    ∀ Q ∈ zerosFinset E D,
      (lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2 ≠ 0 := by
  classical
  intro Q hQzeros
  -- Q ∈ zerosFinset E D = E.points.filter (D.eval = 0).
  unfold zerosFinset zeros at hQzeros
  rw [Finset.mem_filter] at hQzeros
  obtain ⟨hQE, hQzero⟩ := hQzeros
  intro hChord
  -- By chord_line_support_in_E (Bezout), Q ∈ {A_0, A_1, A_2}.
  have hQ_in_chord : Q = A₀ ∨ Q = A₁ ∨
      Q = (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
           slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
             (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
           (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) :=
    chord_line_support_in_E E A₀ A₁ hA₀ hA₁ hNV Q hQE hChord
  -- ¬bad: D doesn't vanish at A_0, A_1, A_2.
  have hMem : (A₀, A₁) ∈ E.points ×ˢ E.points := Finset.mk_mem_product hA₀ hA₁
  have h_unbad : ¬ badPairCompletenessPred E D (A₀, A₁) := fun hbad =>
    hGood (Finset.mem_filter.mpr ⟨hMem, hbad⟩)
  have hThirdEq : thirdPoint E A₀ A₁ =
      some (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1,
            slopeOf A₀.1 A₀.2 A₁.1 A₁.2 *
              (slopeOf A₀.1 A₀.2 A₁.1 A₁.2 ^ 2 - A₀.1 - A₁.1) +
            (A₀.2 - slopeOf A₀.1 A₀.2 A₁.1 A₁.2 * A₀.1)) := by
    unfold thirdPoint
    rw [if_neg hNV]
    rfl
  rcases hQ_in_chord with hQ | hQ | hQ
  · -- Q = A_0: D(A_0) = 0 contradicts ¬bad.
    apply h_unbad
    exact Or.inl (by rw [← hQ]; exact hQzero)
  · -- Q = A_1.
    apply h_unbad
    exact Or.inr (Or.inl (by rw [← hQ]; exact hQzero))
  · -- Q = A_2.
    apply h_unbad
    refine Or.inr (Or.inr (Or.inl ?_))
    show (match thirdPoint E (A₀, A₁).1 (A₀, A₁).2 with
      | none => True
      | some (x, y) => D.eval x y = 0)
    rw [show (A₀, A₁).1 = A₀ from rfl, show (A₀, A₁).2 = A₁ from rfl]
    rw [hThirdEq]
    rw [← hQ]; exact hQzero

/-! ## Any-k bridge: `logDerivCheckFn = 0` for any honest D with explicit hypotheses

Takes a generic msg with `IsHonestForExplicit` plus the splitsOnE,
hAccount, and residue-match side conditions (protocol- and D-specific).
Produces logDerivCheckFn = 0.

For length-4 simple, all these can be discharged via length-4 work.
For general k, the user provides them (e.g., via recursive eagenBuild). -/

theorem logDerivCheckFn_zero_via_isHonestForExplicit_with_sides
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (_h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (A₀ A₁ : ZMod E.q × ZMod E.q)
    (hA₀ : A₀ ∈ E.points) (hA₁ : A₁ ∈ E.points)
    (hNV : A₀.1 ≠ A₁.1)
    (hGood : (A₀, A₁) ∉ badChallengesCompleteness E msg.toD)
    (hResidueMatch :
      (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2))⁻¹
          + (Finset.univ : Finset (Fin stmt.k)).sum
              (fun j => msg.m (hkm ▸ j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (stmt.bases j).1
                  (stmt.bases j).2)⁻¹)) :
    logDerivCheckFn E msg.toD stmt.target stmt.k stmt.bases
      (fun i => msg.m (hkm ▸ i)) A₀ A₁ = 0 := by
  classical
  -- β_fun = ordAt = betaTrue (definitional).
  have hβsup : ∀ Q, ordAt E msg.toD Q ≠ 0 →
      Q ∈ E.points ∧ msg.toD.eval Q.1 Q.2 = 0 :=
    betaTrue_support E msg.toD hD
  have hβcov : ∀ Q ∈ E.points, msg.toD.eval Q.1 Q.2 = 0 →
      ordAt E msg.toD Q ≠ 0 := by
    intro Q hQE hQeval
    have h_pos : 0 < ordAt E msg.toD Q := (ordAt_pos_iff_zero E msg.toD hD Q hQE).mpr hQeval
    omega
  have hβtrue : ∀ Q, ordAt E msg.toD Q = betaTrue E msg.toD hD Q := fun _ => rfl
  -- hQline from general lemma.
  have hQline := hQline_of_hGood_general E hD hA₀ hA₁ hNV hGood
  -- hDen from general lemma (in LogDerivEagenLength4).
  have hDen := hDen_of_hGood E msg.toD A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply logDerivCheckFn_zero_of_explicit_divisor_data.
  exact logDerivCheckFn_zero_of_explicit_divisor_data E msg.toD stmt.target
    stmt.bases (fun i => msg.m (hkm ▸ i)) (ordAt E msg.toD)
    hD hSplit hβsup hβcov hAccount hβtrue
    A₀ A₁ hA₀ hA₁ hNV hGood hQline hDen hResidueMatch

/-! ## Any-k MA completeness via IsHonestForExplicit + side conditions

This is the any-k analog of `ma_completeness_via_isHonestForLength4Simple`.
Takes the protocol-level side conditions (splitsOnE, hAccount, residue
match) as user-provided hypotheses. -/

theorem ma_completeness_via_isHonestForExplicit_with_sides
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB))
    (hResidueMatchAll : ∀ A₀ A₁ : ZMod E.q × ZMod E.q,
      A₀ ∈ E.points → A₁ ∈ E.points → A₀.1 ≠ A₁.1 →
      (A₀, A₁) ∉ badChallengesCompleteness E msg.toD →
      (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) *
          ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)
        = ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval stmt.target.1 (-stmt.target.2))⁻¹
          + (Finset.univ : Finset (Fin stmt.k)).sum
              (fun j => msg.m (hkm ▸ j) *
                ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval (stmt.bases j).1
                  (stmt.bases j).2)⁻¹)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  apply ma_completeness_parameterized E stmt msg hkm hDegK hAdm
  intro A₀ A₁ hA₀ hA₁ hGood
  have hNV : A₀.1 ≠ A₁.1 := hNV_of_hGood E hA₀ hA₁ hGood
  exact logDerivCheckFn_zero_via_isHonestForExplicit_with_sides E
    stmt wit hk msg hkm h_honest hD hSplit hAccount A₀ A₁ hA₀ hA₁ hNV hGood
    (hResidueMatchAll A₀ A₁ hA₀ hA₁ hNV hGood)

/-! ## Padding lemma: extend zerosFinset sum to E.points

For any function f, the sum `∑ Q ∈ zerosFinset E D, ordAt(Q) * f(Q)` equals
`∑ Q ∈ E.points, ordAt(Q) * f(Q)`, since ordAt is zero outside zerosFinset
on E.points. -/

theorem ordAt_sum_extend_to_E_points
    {D : CoordRingElt E.q} (hD : ¬ (D.a = 0 ∧ D.b = 0))
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E D, (ordAt E D Q : ZMod E.q) * f Q)
      = ∑ Q ∈ E.points, (ordAt E D Q : ZMod E.q) * f Q := by
  classical
  -- zerosFinset = E.points.filter (D.eval = 0).
  have hSub : zerosFinset E D ⊆ E.points := by
    unfold zerosFinset zeros; exact Finset.filter_subset _ _
  -- Off zerosFinset, ordAt = 0.
  rw [← Finset.sum_subset hSub]
  intro Q hQE hQnZ
  -- Q ∈ E.points, Q ∉ zerosFinset → D.eval Q ≠ 0 → ordAt Q = 0.
  have hQnZ' : ¬ (D.eval Q.1 Q.2 = 0) := by
    intro h; apply hQnZ
    unfold zerosFinset zeros
    rw [Finset.mem_filter]
    exact ⟨hQE, h⟩
  have h_ord : ordAt E D Q = 0 := by
    by_contra h
    apply hQnZ'
    exact (ordAt_pos_iff_zero E D hD Q hQE).mp (Nat.pos_of_ne_zero h)
  rw [h_ord]
  push_cast
  ring

/-! ## ordAt-to-honestDivisorCoeffs conversion at affine points

When `divisorOfD msg.toD = honestDivisorCoeffs`, the relationship at
affine points is `(ordAt msg.toD Q : ℤ) = honestDivisorCoeffs(affine Q)`. -/

theorem ordAt_eq_honestDivisorCoeffs_at_affine
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    (ordAt E msg.toD Q : ℤ)
      = honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) := by
  have h := h_div (ECPoint.affine E Q.1 Q.2)
  rw [show divisorOfD E msg.toD (ECPoint.affine E Q.1 Q.2)
      = (ordAtPoint E msg.toD (ECPoint.affine E Q.1 Q.2) : ℤ) from ?_,
      ordAtPoint_affine E _ hQ] at h
  · exact h
  · rw [ECPoint.affine_of_nonsingular E
          (E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ)))]
    rfl

/-! ## ZMod-cast of the affine bridge

In ZMod E.q: `(ordAt : ZMod) = (honestDivisorCoeffs : ZMod)` at affine points,
via the ℤ→ZMod cast. -/

theorem ordAt_cast_eq_honestDivisorCoeffs_cast_at_affine
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    ((ordAt E msg.toD Q : ℤ) : ZMod E.q)
      = ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
          : ZMod E.q) := by
  rw [ordAt_eq_honestDivisorCoeffs_at_affine E stmt wit hk msg h_div hQ]

/-! ## Residue match identity from divisor identity

Combines the padding lemma and affine-bridge to derive the residue-sum
identity from `IsHonestForExplicit`. -/

theorem residue_sum_eq_honest_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) * f Q)
      = ∑ Q ∈ E.points,
          ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
            : ZMod E.q) * f Q := by
  classical
  rw [ordAt_sum_extend_to_E_points E hD f]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [show ((ordAt E msg.toD Q : ZMod E.q))
      = ((ordAt E msg.toD Q : ℤ) : ZMod E.q) from by push_cast; rfl]
  rw [ordAt_cast_eq_honestDivisorCoeffs_cast_at_affine E stmt wit hk msg h_div hQ]

/-! ## honestDivisorCoeffs unfolding at affine

The honest divisor coefficient at an affine point splits into:
* An indicator `(if (x,y) = -P_target then 1 else 0)`.
* A bases-sum `Σ_{i: bases i = (x,y)} scalars i`.

Sum over E.points + L-evaluation produces the protocol RHS form. -/

theorem honestDivisorCoeffs_at_affine_split
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) {Q : ZMod E.q × ZMod E.q} (hQ : Q ∈ E.points) :
    honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2)
      = (if Q = (stmt.target.1, -stmt.target.2) then 1 else 0) +
        ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
          (fun i => stmt.bases i = Q),
          (wit.scalars (hk ▸ i) : ℤ) := by
  rw [ECPoint.affine_of_nonsingular E
        (E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ)))]
  rcases Q with ⟨x, y⟩
  rfl

/-! ## Indicator-term reduction

The "indicator" component of `honestDivisorCoeffs` (the `(if (x,y) = -P_target then 1 else 0)`
term), summed over E.points and weighted by L(Q)^{-1}, reduces to `L(-P_target)^{-1}`. -/

theorem indicator_sum_eq_eval_at_negTarget
    (target : ZMod E.q × ZMod E.q) (h_negT : (target.1, -target.2) ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ E.points,
        ((if Q = (target.1, -target.2) then (1 : ℤ) else 0) : ZMod E.q) * f Q)
      = f (target.1, -target.2) := by
  classical
  rw [Finset.sum_eq_single (target.1, -target.2)]
  · simp
  · intro b _ hb
    rw [if_neg hb]
    ring
  · intro h
    exact absurd h_negT h

/-! ## Bases-term reduction

The "bases-sum" component of `honestDivisorCoeffs`, summed over E.points
and weighted by L(Q)^{-1}, reduces to `∑_i (scalars i) · L(bases i)^{-1}`.
Requires bases i ∈ E.points for all i. -/

theorem bases_sum_eq_index_sum
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ E.points, ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
      (fun i => stmt.bases i = Q), (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q)
      = (Finset.univ : Finset (Fin stmt.k)).sum
          (fun i => ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) * f (stmt.bases i)) := by
  classical
  -- Convert the inner filter-sum to an indicator sum.
  rw [show (∑ Q ∈ E.points, ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
    (fun i => stmt.bases i = Q), (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q)
    = (∑ Q ∈ E.points, ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)),
        ((if stmt.bases i = Q then (wit.scalars (hk ▸ i) : ℤ) else 0) : ZMod E.q) * f Q) from by
    apply Finset.sum_congr rfl
    intro Q _
    rw [Finset.sum_filter]
    rw [Finset.sum_mul]]
  -- Swap the sums (inner is now Q-dependent only via the if-branch, but the index set is fixed).
  rw [Finset.sum_comm]
  -- Now: ∑_i ∑_Q (if bases i = Q then scalars i else 0 : ZMod) · f Q.
  apply Finset.sum_congr rfl
  intro i _
  -- For each i, only Q = bases i contributes.
  rw [Finset.sum_eq_single (stmt.bases i)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    ring
  · intro h
    exact absurd (h_bases i) h

/-! ## Full residue-match derivation from IsHonestForExplicit

Combine the helpers to produce `hResidueMatchAll` from divisor identity.

For honest msg with `IsHonestForExplicit`, plus the assumption that
`-P_target ∈ E.points` and all `bases ∈ E.points`, the residue sum equals
the protocol RHS. -/

theorem hResidueMatch_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (f : ZMod E.q × ZMod E.q → ZMod E.q) :
    (∑ Q ∈ zerosFinset E msg.toD, (ordAt E msg.toD Q : ZMod E.q) * f Q)
      = f (stmt.target.1, -stmt.target.2)
        + (Finset.univ : Finset (Fin stmt.k)).sum
            (fun i => ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) * f (stmt.bases i)) := by
  classical
  have h_div := h_honest.2.2.1
  -- Step 1: convert to honestDivisorCoeffs sum over E.points.
  rw [residue_sum_eq_honest_via_isHonestForExplicit E stmt wit hk msg h_div hD f]
  -- Step 2: split honestDivisorCoeffs into indicator + bases-sum.
  rw [show (∑ Q ∈ E.points,
        ((honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) : ℤ)
          : ZMod E.q) * f Q)
      = (∑ Q ∈ E.points,
          (((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
             ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
               (fun i => stmt.bases i = Q),
               (wit.scalars (hk ▸ i) : ℤ) : ℤ) : ZMod E.q) * f Q) from by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [honestDivisorCoeffs_at_affine_split E stmt wit hk msg hQ]]
  -- Step 3: distribute the addition.
  rw [show (∑ Q ∈ E.points,
        ((((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
           ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
             (fun i => stmt.bases i = Q),
             (wit.scalars (hk ▸ i) : ℤ)) : ℤ) : ZMod E.q) * f Q)
      = (∑ Q ∈ E.points,
            ((if Q = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) : ZMod E.q) * f Q)
        + (∑ Q ∈ E.points,
            ((∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
              (fun i => stmt.bases i = Q),
              (wit.scalars (hk ▸ i) : ℤ)) : ZMod E.q) * f Q) from by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    push_cast
    ring]
  -- Step 4: apply the indicator and bases lemmas.
  rw [indicator_sum_eq_eval_at_negTarget E stmt.target h_negT f]
  rw [bases_sum_eq_index_sum E stmt wit hk h_bases f]

/-! ## Tighter any-k MA completeness: hResidueMatchAll discharged

Same as `ma_completeness_via_isHonestForExplicit_with_sides` but with
`hResidueMatchAll` discharged automatically from `IsHonestForExplicit`. -/

theorem ma_completeness_via_isHonestForExplicit_no_residue_match
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (hSplit : splitsOnE E msg.toD)
    (hAccount : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree)
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (h_m_eq_scalars : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q))
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  apply ma_completeness_via_isHonestForExplicit_with_sides E stmt wit hk msg hkm
    h_honest hD hSplit hAccount hDegK hAdm
  intro A₀ A₁ hA₀ hA₁ hNV hGood
  -- Apply hResidueMatch_via_isHonestForExplicit with f = L^{-1}.
  rw [hResidueMatch_via_isHonestForExplicit E stmt wit hk msg hkm h_honest hD
      h_negT h_bases (fun Q => ((lineThrough A₀.1 A₀.2 A₁.1 A₁.2).eval Q.1 Q.2)⁻¹)]
  -- Now we need: f(-target) + Σ_i (scalars : ZMod) · f(bases i) = ((lineThrough.eval target.1 (-target.2))⁻¹) + Σ_j m_j · ...
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h_m_eq_scalars i]

/-! ## Sum of ordAt as ℤ via divisor identity

Cast the natural-number `∑ ordAt` to ℤ, using `divisorOfD = honestDivisorCoeffs`. -/

theorem ordAt_sum_eq_honestDivisorCoeffs_sum_at_affines
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R) :
    ((∑ Q ∈ E.points, ordAt E msg.toD Q : ℕ) : ℤ)
      = ∑ Q ∈ E.points,
          honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2) := by
  push_cast
  apply Finset.sum_congr rfl
  intro Q hQ
  exact ordAt_eq_honestDivisorCoeffs_at_affine E stmt wit hk msg h_div hQ

/-! ## honestDivisorCoeffs at infinity

The infinity coefficient of `honestDivisorCoeffs` is `-degE(msg.toD)`,
directly from the definition. -/

theorem honestDivisorCoeffs_at_infinity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) :
    honestDivisorCoeffs E stmt wit hk msg (0 : ECPoint E) = -(msg.toD.degE : ℤ) := rfl

/-! ## honestDivisorCoeffs has finite support (via divisor identity)

By divisor identity, honestDivisorCoeffs equals the finitely-supported
divisorOfD, hence is also finitely supported. -/

theorem honestDivisorCoeffs_finiteSupport_of_divisor_identity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q)
    (h_div : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R) :
    Set.Finite (Function.support (honestDivisorCoeffs E stmt wit hk msg)) := by
  have h_eq : honestDivisorCoeffs E stmt wit hk msg = divisorOfD E msg.toD := by
    funext R
    exact (h_div R).symm
  rw [h_eq]
  exact divisorOfD_finiteSupport E msg.toD

/-! ## ECPoint.some-to-affinePoints bijection

For any nonsingular .some ECPoint, the underlying (x, y) pair is in
E.points, and `ECPoint.affine E x y` recovers the original ECPoint. -/

theorem some_in_affinePoints {x y : ZMod E.q}
    (h : E.toW.toAffine.Nonsingular x y) :
    (.some _ _ h : ECPoint E) ∈ ECPoint.affinePoints E := by
  classical
  unfold ECPoint.affinePoints
  rw [Finset.mem_image]
  -- (x, y) ∈ E.points: from Nonsingular → Equation → on-curve → hComplete.
  have hEq : E.toW.toAffine.Equation x y := E.equation_iff_nonsingular.mpr h
  have hYsq : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
    (E.equation_iff x y).mp hEq
  have hQ : (x, y) ∈ E.points := E.hComplete x y hYsq
  refine ⟨(x, y), hQ, ?_⟩
  rw [ECPoint.affine_of_nonsingular E h]

/-! ## honestDivisorCoeffs support contained in affinePoints ∪ {0}

Per the previous lemma, every `.some` ECPoint is in `affinePoints E`.
The infinity ECPoint is the additional element. Hence the support of
`honestDivisorCoeffs` (or any function on ECPoints) is contained in
`insert 0 (affinePoints E)`. -/

theorem honestDivisorCoeffs_support_subset_affineAndInfinity
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) :
    Function.support (honestDivisorCoeffs E stmt wit hk msg)
      ⊆ ↑(insert (0 : ECPoint E) (ECPoint.affinePoints E)) := by
  classical
  intro R _hR
  match R with
  | 0 =>
    rw [Finset.coe_insert]
    exact Set.mem_insert _ _
  | .some _ _ h =>
    rw [Finset.coe_insert, Set.mem_insert_iff]
    right
    exact some_in_affinePoints E h

/-! ## `0 ∉ affinePoints E`

The infinity ECPoint is not in `affinePoints E`, since `affinePoints E`
is the image of `E.points` under `affine`, and for any `Q ∈ E.points`,
`affine E Q.1 Q.2 = .some _` (which is `≠ 0`). -/

theorem zero_notMem_affinePoints : (0 : ECPoint E) ∉ ECPoint.affinePoints E := by
  classical
  unfold ECPoint.affinePoints
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨Q, hQ, hEq⟩ := h
  -- ECPoint.affine E Q.1 Q.2 = 0 forces Nonsingular to fail, but it holds for Q ∈ E.points.
  have hNs : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hNs] at hEq
  cases hEq

/-! ## Bridge: `∑_{R ∈ affinePoints E} f R = ∑_{Q ∈ E.points} f (affine E Q.1 Q.2)` -/

theorem affinePoints_sum_eq_image_sum {α : Type*} [AddCommMonoid α]
    (f : ECPoint E → α) :
    (∑ R ∈ ECPoint.affinePoints E, f R)
      = ∑ Q ∈ E.points, f (ECPoint.affine E Q.1 Q.2) := by
  classical
  unfold ECPoint.affinePoints
  rw [Finset.sum_image]
  intro P hP Q hQ h_eq
  simp only at h_eq
  have hPns : E.toW.toAffine.Nonsingular P.1 P.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff P.1 P.2).mpr (E.hOnCurve _ hP))
  have hQns : E.toW.toAffine.Nonsingular Q.1 Q.2 :=
    E.equation_iff_nonsingular.mp ((E.equation_iff Q.1 Q.2).mpr (E.hOnCurve _ hQ))
  rw [ECPoint.affine_of_nonsingular E hPns,
      ECPoint.affine_of_nonsingular E hQns] at h_eq
  -- .some _ _ hPns = .some _ _ hQns implies the implicit x, y match.
  injection h_eq with hx_some hy_some
  exact Prod.ext hx_some hy_some

/-! ## Deg-zero from `splitsOnE` + divisor identity

Replaces the prior route via `principal_divisor_iff`. Uses only
the `splitsOnE` and divisor-identity conjuncts of `isHonestFor`,
plus `sum_ordAt_eq_natDegree_under_split`. The constant-D edge
case is ruled out by the divisor identity at infinity (`degE = 3`
for `D = 0`, but `divisorOfD 0 = 0`, so the identity would force
`-3 = 0`). -/

theorem honestDivisorCoeffs_deg_zero_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    ∃ hFinSupp : Set.Finite (Function.support
        (honestDivisorCoeffs E stmt wit hk msg)),
      ∑ P ∈ hFinSupp.toFinset, honestDivisorCoeffs E stmt wit hk msg P = 0 := by
  classical
  have h_split : splitsOnE E msg.toD := h_honest.2.1
  have h_div_id : ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R :=
    h_honest.2.2.1
  have hFin := honestDivisorCoeffs_finiteSupport_of_divisor_identity E
    stmt wit hk msg h_div_id
  have hSubset := honestDivisorCoeffs_support_subset_affineAndInfinity E stmt wit hk msg
  refine ⟨hFin, ?_⟩
  -- Step 1: extend the sum from support to `insert 0 affinePoints`.
  have h_ext : (∑ R ∈ hFin.toFinset, honestDivisorCoeffs E stmt wit hk msg R)
      = ∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
          honestDivisorCoeffs E stmt wit hk msg R := by
    apply Finset.sum_subset
    · intro R hR; rw [Set.Finite.mem_toFinset] at hR; exact hSubset hR
    · intro R _ hR_notIn; rw [Set.Finite.mem_toFinset] at hR_notIn
      by_contra h; exact hR_notIn h
  rw [h_ext, Finset.sum_insert (zero_notMem_affinePoints E),
      honestDivisorCoeffs_at_infinity E stmt wit hk msg,
      affinePoints_sum_eq_image_sum E (honestDivisorCoeffs E stmt wit hk msg)]
  -- Convert `honestDivisorCoeffs (affine Q)` to `(ordAt msg.toD Q : ℤ)` via divisor identity.
  have h_aff_sum :
      (∑ Q ∈ E.points,
        honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E Q.1 Q.2))
        = ∑ Q ∈ E.points, (ordAt E msg.toD Q : ℤ) :=
    Finset.sum_congr rfl
      (fun Q hQ =>
        (ordAt_eq_honestDivisorCoeffs_at_affine E stmt wit hk msg h_div_id hQ).symm)
  rw [h_aff_sum]
  -- Reduce to: -(degE) + Σ_{Q ∈ E.points} ordAt = 0.
  by_cases hD : msg.toD.a = 0 ∧ msg.toD.b = 0
  · -- Constant-zero D: ruled out by divisor identity at infinity.
    exfalso
    have h_id_at_zero := h_div_id 0
    have hNorm0 : normPoly E msg.toD = 0 := by
      rw [normPoly_eq, hD.1, hD.2]; ring
    have hLHS0 : divisorOfD E msg.toD (0 : ECPoint E) = 0 := by
      show -((normPoly E msg.toD).natDegree : ℤ) = 0
      rw [hNorm0]; simp
    rw [hLHS0, honestDivisorCoeffs_at_infinity] at h_id_at_zero
    have hDegE : msg.toD.degE = 3 := by
      simp [CoordRingElt.degE, hD.1, hD.2]
    omega
  · -- splitsOnE + D ≠ 0 ⇒ Σ ordAt = natDegree(normPoly).
    have hOrdSum : (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree :=
      sum_ordAt_eq_natDegree_under_split E msg.toD hD h_split
    -- Divisor identity at 0 gives natDegree(normPoly) = degE.
    have h_id_at_zero := h_div_id 0
    have hLHS0 : divisorOfD E msg.toD (0 : ECPoint E)
        = -((normPoly E msg.toD).natDegree : ℤ) := rfl
    rw [hLHS0, honestDivisorCoeffs_at_infinity] at h_id_at_zero
    have h_natDeg : ((normPoly E msg.toD).natDegree : ℤ) = (msg.toD.degE : ℤ) := by
      omega
    -- Push cast on the affine sum and substitute.
    have hOrdSumZ : (∑ Q ∈ E.points, (ordAt E msg.toD Q : ℤ))
        = (msg.toD.degE : ℤ) := by
      have h1 : (∑ Q ∈ E.points, (ordAt E msg.toD Q : ℤ))
          = (((∑ Q ∈ E.points, ordAt E msg.toD Q : ℕ) : ℤ)) := by push_cast; rfl
      rw [h1, hOrdSum]
      exact h_natDeg
    linarith [hOrdSumZ]

/-! ## Affine sum = degE for honest divisor

Combines deg-zero with the support subset and the infinity-coefficient
unfolding. -/

theorem honestDivisorCoeffs_affine_sum_eq_degE
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ R ∈ ECPoint.affinePoints E, honestDivisorCoeffs E stmt wit hk msg R)
      = (msg.toD.degE : ℤ) := by
  classical
  obtain ⟨hFin, hSum_zero⟩ :=
    honestDivisorCoeffs_deg_zero_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hSubset := honestDivisorCoeffs_support_subset_affineAndInfinity E stmt wit hk msg
  have hZeroNotIn := zero_notMem_affinePoints E
  have h_ext_sum : (∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
      honestDivisorCoeffs E stmt wit hk msg R) = 0 := by
    rw [show (∑ R ∈ insert (0 : ECPoint E) (ECPoint.affinePoints E),
              honestDivisorCoeffs E stmt wit hk msg R)
        = ∑ R ∈ hFin.toFinset, honestDivisorCoeffs E stmt wit hk msg R from ?_]
    · exact hSum_zero
    · apply (Finset.sum_subset (s₁ := hFin.toFinset)
              (s₂ := insert (0 : ECPoint E) (ECPoint.affinePoints E)) ?_ ?_).symm
      · intro R hR
        rw [Set.Finite.mem_toFinset] at hR
        exact hSubset hR
      · intro R _hR_in hR_notIn
        rw [Set.Finite.mem_toFinset] at hR_notIn
        by_contra h
        exact hR_notIn h
  rw [Finset.sum_insert hZeroNotIn,
      honestDivisorCoeffs_at_infinity E stmt wit hk msg] at h_ext_sum
  linarith

/-! ## ∑ ordAt = degE from divisor identity -/

theorem ordAt_sum_eq_degE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    ((∑ Q ∈ E.points, ordAt E msg.toD Q : ℕ) : ℤ) = (msg.toD.degE : ℤ) := by
  rw [ordAt_sum_eq_honestDivisorCoeffs_sum_at_affines E stmt wit hk msg h_honest.2.2.1]
  rw [← affinePoints_sum_eq_image_sum E (honestDivisorCoeffs E stmt wit hk msg)]
  exact honestDivisorCoeffs_affine_sum_eq_degE E stmt wit hk msg hkm h_honest

/-! ## ∑ ordAt = degE (cast back to ℕ) and natDegree = degE -/

theorem ordAt_sum_eq_degE_nat_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ Q ∈ E.points, ordAt E msg.toD Q) = msg.toD.degE := by
  have h := ordAt_sum_eq_degE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  exact_mod_cast h

theorem natDegree_normPoly_eq_degE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (normPoly E msg.toD).natDegree = msg.toD.degE := by
  -- ∑ ordAt ≤ natDegree ≤ degE (existing infrastructure).
  -- ∑ ordAt = degE (step 4).
  -- Pinch.
  have hSum := ordAt_sum_eq_degE_nat_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hLe1 : (∑ P ∈ E.points, ordAt E msg.toD P) ≤ (normPoly E msg.toD).natDegree := by
    classical
    rw [sum_E_points_eq_sum_fiberwise E]
    by_cases hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)
    · calc (∑ x₀ : ZMod E.q,
              ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) :=
            Finset.sum_le_sum (fun x₀ _ => sum_ordAt_fst_eq_le E msg.toD hD x₀)
        _ ≤ (normPoly E msg.toD).natDegree :=
            sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
    · push_neg at hD
      have : ∀ P ∈ E.points, ordAt E msg.toD P = 0 :=
        fun P _ => ordAt_eq_zero_of_zero E hD P
      have h_inner : ∀ x₀ : ZMod E.q,
          (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P) = 0 := by
        intro x₀
        apply Finset.sum_eq_zero
        intro P hP
        exact this P (Finset.mem_filter.mp hP).1
      rw [show (∑ x₀ : ZMod E.q,
              ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P) = 0 from
            Finset.sum_eq_zero (fun x₀ _ => h_inner x₀)]
      exact Nat.zero_le _
  have hLe2 : (normPoly E msg.toD).natDegree ≤ msg.toD.degE :=
    normPoly_natDegree_le E msg.toD
  omega

/-! ## hAccount from isHonestForExplicit (no splitsOnE needed) -/

theorem hAccount_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm) :
    (∑ Q ∈ E.points, ordAt E msg.toD Q) = (normPoly E msg.toD).natDegree := by
  rw [ordAt_sum_eq_degE_nat_of_isHonestForExplicit E stmt wit hk msg hkm h_honest,
      natDegree_normPoly_eq_degE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest]

/-! ## normPoly splits — `Multiset.card .roots = natDegree` -/

theorem normPoly_splits_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    normPoly_splits_over_Fq E msg.toD := by
  classical
  -- Pinching: ∑ ordAt ≤ ∑ rootMult ≤ natDegree, with ∑ ordAt = natDegree.
  have hSum := hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hFiber : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        ≤ rootMultiplicity x₀ (normPoly E msg.toD) :=
    fun x₀ => sum_ordAt_fst_eq_le E msg.toD hD x₀
  have hFiber_sum : (∑ x₀ : ZMod E.q,
      ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = ∑ Q ∈ E.points, ordAt E msg.toD Q := by
    rw [sum_E_points_eq_sum_fiberwise E (fun P => ordAt E msg.toD P)]
  have hRootMult_sum_le : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        ≤ (normPoly E msg.toD).natDegree :=
    sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
  have hSum_rootMult_eq : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        = (normPoly E msg.toD).natDegree := by
    have h1 : (∑ Q ∈ E.points, ordAt E msg.toD Q)
            ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [← hFiber_sum]
      exact Finset.sum_le_sum (fun x₀ _ => hFiber x₀)
    omega
  unfold normPoly_splits_over_Fq
  rw [← sum_rootMultiplicity_eq_card_roots]
  exact hSum_rootMult_eq

/-! ## fiber rationality

Every root α of normPoly E msg.toD has a y-lift in E.points.
Reason: rootMult > 0 + fiber sum equality from pinching ⇒ fiber non-empty. -/

theorem fiber_rationality_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    ∀ α ∈ (normPoly E msg.toD).roots, ∃ y : ZMod E.q, (α, y) ∈ E.points := by
  classical
  intro α hα
  -- α has rootMult > 0.
  have hRootMult_pos : 0 < rootMultiplicity α (normPoly E msg.toD) := by
    rw [Polynomial.mem_roots (normPoly_ne_zero E msg.toD hD)] at hα
    exact (Polynomial.rootMultiplicity_pos (normPoly_ne_zero E msg.toD hD)).mpr hα
  -- From the pinching equality (proved in normPoly_splits_of_isHonestForExplicit),
  -- ∑ x₀, fiber_sum x₀ = ∑ x₀, rootMult x₀.
  -- With pointwise fiber_sum ≤ rootMult, and total equality, pointwise equality holds.
  have hSum := hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest
  have hFiber_sum_eq_total : (∑ x₀ : ZMod E.q,
      ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = ∑ Q ∈ E.points, ordAt E msg.toD Q := by
    rw [sum_E_points_eq_sum_fiberwise E (fun P => ordAt E msg.toD P)]
  have hFiber_le : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        ≤ rootMultiplicity x₀ (normPoly E msg.toD) :=
    fun x₀ => sum_ordAt_fst_eq_le E msg.toD hD x₀
  have hRootMult_le_natDegree :
      ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        ≤ (normPoly E msg.toD).natDegree :=
    sum_rootMultiplicity_le_natDegree E (normPoly E msg.toD)
  have hSum_eq : ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD)
        = (normPoly E msg.toD).natDegree := by
    have h1 : (∑ Q ∈ E.points, ordAt E msg.toD Q)
            ≤ ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [← hFiber_sum_eq_total]
      exact Finset.sum_le_sum (fun x₀ _ => hFiber_le x₀)
    omega
  -- Pointwise equality: fiber_sum = rootMult at each x₀.
  have hFiber_eq_rootMult : ∀ x₀ : ZMod E.q,
      (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
        = rootMultiplicity x₀ (normPoly E msg.toD) := by
    -- Total equality + pointwise inequality ⇒ pointwise equality.
    have h_total_fiber : (∑ x₀ : ZMod E.q,
        ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          = ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) := by
      rw [hFiber_sum_eq_total, hSum, hSum_eq]
    intro x₀
    by_contra h_ne
    have h_lt : (∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
                < rootMultiplicity x₀ (normPoly E msg.toD) :=
      lt_of_le_of_ne (hFiber_le x₀) h_ne
    have h_strict : (∑ x₀ : ZMod E.q,
        ∑ P ∈ E.points.filter (fun P => P.1 = x₀), ordAt E msg.toD P)
          < ∑ x₀ : ZMod E.q, rootMultiplicity x₀ (normPoly E msg.toD) :=
      Finset.sum_lt_sum (fun x₀ _ => hFiber_le x₀) ⟨x₀, Finset.mem_univ _, h_lt⟩
    omega
  -- At α, fiber_sum = rootMult > 0, so fiber is nonempty.
  have hFiber_pos : 0 <
      ∑ P ∈ E.points.filter (fun P => P.1 = α), ordAt E msg.toD P := by
    rw [hFiber_eq_rootMult α]
    exact hRootMult_pos
  have hFiber_nonempty : (E.points.filter (fun P => P.1 = α)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hFiber_pos
    exact lt_irrefl 0 hFiber_pos
  obtain ⟨P, hP⟩ := hFiber_nonempty
  refine ⟨P.2, ?_⟩
  rw [show α = P.1 from (Finset.mem_filter.mp hP).2.symm]
  exact (Finset.mem_filter.mp hP).1

/-! ## Final: splitsOnE from IsHonestForExplicit -/

theorem splitsOnE_of_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0)) :
    splitsOnE E msg.toD :=
  ⟨normPoly_splits_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD,
   fiber_rationality_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD⟩

/-! ## Bridge: IsHonestForLength4Simple → isHonestFor

From a length-4-simple honest message to the strengthened
`MAProverMsg.isHonestFor`: the divisor identity (at infinity, then at
every affine point), the on-curve invariants, and the `splitsOnE`
conjunct, assembled in `isHonestFor_of_isHonestForLength4Simple`. -/

/-- Divisor identity at infinity: both `divisorOfD` and
    `honestDivisorCoeffs` evaluate to `-4` at the point at infinity. -/
theorem divisor_identity_at_infinity_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k) :
    divisorOfD E msg.toD (0 : ECPoint E)
      = honestDivisorCoeffs E stmt wit hk msg (0 : ECPoint E) := by
  rw [h_simple.h_toD_eq]
  rw [eagenBuild_length4_div_at_infinity E
        h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
        h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
        h_simple.h_xx_01 h_simple.h_xx_23
        h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
        h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion]
  show (-4 : ℤ) = -((msg.toD.degE : ℤ))
  have h_degE : msg.toD.degE = 4 := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_degE_eq_four E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  rw [h_degE]; norm_num

/-- On-curve invariant for `(-target)`: `(target.1, -target.2) ∈ E.points`. -/
theorem negTarget_on_curve_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    (stmt.target.1, -stmt.target.2) ∈ E.points := by
  rw [← h_simple.h_P₀_eq]
  exact h_simple.hP₀

/-- Cast helper: `(h ▸ jj : Fin stmt.k).val = jj.val` where `h : stmt.k = 3`. -/
private theorem cast_subst_val_l4
    {stmt : DlogStatement E.q} (h : stmt.k = 3) (jj : Fin 3) :
    ((h ▸ jj : Fin stmt.k)).val = jj.val := by
  generalize stmt.k = k at h jj
  cases h
  rfl

/-- Helper: extract a specific basis from IsHonestForLength4Simple. The
    cast-rewriting is encapsulated here so the bridge theorem doesn't
    need to fight Lean's dependent-type machinery directly. -/
private theorem bases_at_cast_index_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (j : Fin 3) :
    stmt.bases (h_simple.hk_eq_3 ▸ j) ∈ E.points := by
  fin_cases j
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨0, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨0, by decide⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₁_eq]; exact h_simple.hP₁
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨1, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨1, by decide⟩ : Fin 3) = (1 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₂_eq]; exact h_simple.hP₂
  · show stmt.bases (h_simple.hk_eq_3 ▸ (⟨2, by decide⟩ : Fin 3)) ∈ E.points
    have : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := rfl
    rw [this, ← h_simple.h_P₃_eq]; exact h_simple.hP₃

/-- Affine divisor identity at points in `{P_0..P_3}`: at any of the
    four sum-zero affine points (each appearing with multiplicity 1),
    `divisorOfD = 1` and `honestDivisorCoeffs = 1` (under the simple-case
    hypotheses with `wit.scalars = 1`). -/
theorem divisor_identity_at_affine_off_support_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (_h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (hP : (x, y) ∈ E.points)
    (h_off : (x, y) ≠ h_simple.P₀ ∧ (x, y) ≠ h_simple.P₁ ∧
             (x, y) ≠ h_simple.P₂ ∧ (x, y) ≠ h_simple.P₃) :
    divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some _ _ hns)
      = honestDivisorCoeffs E stmt wit hk msg
          (WeierstrassCurve.Affine.Point.some _ _ hns) := by
  classical
  -- divisorOfD = ordAt (cast to ℤ) at affine.
  rw [show (WeierstrassCurve.Affine.Point.some _ _ hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  -- Step 1: divisorOfD = 0. Use zerosFinset characterization.
  have h_zeros := zerosFinset_eagenBuild_length4_eq E
    h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
    h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
    h_simple.h_xx_01 h_simple.h_xx_23
    h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
    h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
    h_simple.h_P₀_off_L₂ h_simple.h_P₁_off_L₂ h_simple.h_P₂_off_L₁ h_simple.h_P₃_off_L₁
    h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
    h_simple.h_Q₀_off_L₂_inputs h_simple.h_negQ₀_off_L₁_inputs
  have h_notin : (x, y) ∉ zerosFinset E msg.toD := by
    rw [h_simple.h_toD_eq, h_zeros]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨h_off.1, h_off.2.1, h_off.2.2.1, h_off.2.2.2⟩
  have h_eval_ne : msg.toD.eval x y ≠ 0 := by
    intro h
    apply h_notin
    unfold zerosFinset zeros
    rw [Finset.mem_filter]
    exact ⟨hP, h⟩
  have hD_NZ : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0) := by
    rw [h_simple.h_toD_eq]
    exact eagenBuild_length4_explicit_ne_zero E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
  have h_ord_zero : ordAt E msg.toD (x, y) = 0 := by
    by_contra h_ne
    have h_pos : 0 < ordAt E msg.toD (x, y) := Nat.pos_of_ne_zero h_ne
    have := (ordAt_pos_iff_zero E msg.toD hD_NZ (x, y) hP).mp h_pos
    exact h_eval_ne this
  -- Step 2: honestDivisorCoeffs = 0. (x, y) ≠ -target = P_0, no base = (x, y).
  have h_negT : (stmt.target.1, -stmt.target.2) = h_simple.P₀ := h_simple.h_P₀_eq.symm
  have h_indic_zero : ((x, y) = (stmt.target.1, -stmt.target.2)) = False := by
    apply propext
    constructor
    · intro h; rw [h_negT] at h; exact h_off.1 h
    · intro h; exact False.elim h
  -- Bases at h_simple.hk_eq_3 ▸ (0,1,2) are P_1, P_2, P_3, none equal (x, y).
  have h_bases_ne : ∀ i : Fin stmt.k, stmt.bases i ≠ (x, y) := by
    intro i
    have h3 := h_simple.hk_eq_3
    -- Helper: stmt.bases (h3 ▸ j) ≠ (x, y) for any j : Fin 3.
    have h_b_ne_at : ∀ (j : Fin 3), stmt.bases (h3 ▸ j) ≠ (x, y) := by
      intro j
      fin_cases j
      · show stmt.bases (h3 ▸ (⟨0, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨0, by decide⟩ : Fin 3) = (0 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₁_eq]
        intro h; exact h_off.2.1 h.symm
      · show stmt.bases (h3 ▸ (⟨1, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨1, by decide⟩ : Fin 3) = (1 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₂_eq]
        intro h; exact h_off.2.2.1 h.symm
      · show stmt.bases (h3 ▸ (⟨2, by decide⟩ : Fin 3)) ≠ (x, y)
        have heq3 : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := rfl
        rw [heq3, ← h_simple.h_P₃_eq]
        intro h; exact h_off.2.2.2 h.symm
    -- Cast i to Fin 3 and apply.
    have h_eq : stmt.bases i = stmt.bases (h3 ▸ Fin.cast h3 i) := by
      congr 1
      apply Fin.ext
      have h_subst_val : ∀ (h : stmt.k = 3) (jj : Fin 3),
          ((h ▸ jj : Fin stmt.k)).val = jj.val := by
        intro h jj
        generalize stmt.k = k at h jj
        cases h
        rfl
      rw [h_subst_val h3]
      rfl
    rw [h_eq]
    exact h_b_ne_at (Fin.cast h3 i)
  -- Now compute both sides.
  -- divisorOfD at affine = (ordAt : ℤ).
  rw [show divisorOfD E msg.toD (ECPoint.affine E x y)
        = (ordAt E msg.toD (x, y) : ℤ) by
      rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  rw [h_ord_zero]
  show (0 : ℤ) = honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
  rw [show honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
        = (if (x, y) = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
            (fun i => stmt.bases i = (x, y)),
            (wit.scalars (hk ▸ i)) by
        rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  rw [if_neg (by intro h; rw [h_negT] at h; exact h_off.1 h)]
  -- The bases-filter is empty since no base = (x, y).
  have h_filter_empty : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact h_bases_ne i
  rw [h_filter_empty]
  simp

/-! ### Affine on-support case: R ∈ {P_0..P_3}

For each P_i, the divisor identity at .some P_i is `1 = 1`:
* `divisorOfD = 1` from `eagenBuild_length4_div_at_P_i`.
* `honestDivisorCoeffs = 1` from indicator (i = 0) or base-sum (i ≥ 1).

Each sub-case is structurally the same; we keep them separate for
readability. -/

/-- Helper: extract divisorOfD msg.toD = 1 at any of P_0..P_3 (under
    IsHonestForLength4Simple's hypotheses). -/
private theorem div_eq_one_at_P_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_xy : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
            (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃) :
    divisorOfD E msg.toD (WeierstrassCurve.Affine.Point.some _ _ hns) = 1 := by
  rw [show (WeierstrassCurve.Affine.Point.some _ _ hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [h_simple.h_toD_eq]
  rcases h_xy with h0 | h1 | h2 | h3
  · -- (x, y) = P_0: divisorOfD = 1.
    have hx : x = h_simple.P₀.1 := by rw [show x = (x, y).1 from rfl, h0]
    have hy : y = h_simple.P₀.2 := by rw [show y = (x, y).2 from rfl, h0]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₀ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₀_off_L₂ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₁.1 := by rw [show x = (x, y).1 from rfl, h1]
    have hy : y = h_simple.P₁.2 := by rw [show y = (x, y).2 from rfl, h1]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₁ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₁_off_L₂ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₂.1 := by rw [show x = (x, y).1 from rfl, h2]
    have hy : y = h_simple.P₂.2 := by rw [show y = (x, y).2 from rfl, h2]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₂ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₂_off_L₁ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion
  · have hx : x = h_simple.P₃.1 := by rw [show x = (x, y).1 from rfl, h3]
    have hy : y = h_simple.P₃.2 := by rw [show y = (x, y).2 from rfl, h3]
    rw [hx, hy]
    exact eagenBuild_length4_div_at_P₃ E
      h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
      h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
      h_simple.h_xx_01 h_simple.h_xx_23
      h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
      h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
      h_simple.h_P₃_off_L₁ h_simple.h_third_match h_simple.h_y_match
      h_simple.h_Q₀_nontorsion

/-! ### On-support helper: filter-singleton characterisation

For each j : Fin 3, the filter `{i : Fin stmt.k | stmt.bases i = stmt.bases (h3 ▸ j)}`
is the singleton `{h3 ▸ j}`. Uses `h_inputs_distinct` (P_1, P_2, P_3 distinct
modulo P_0 not being a basis index). -/
private theorem bases_filter_singleton_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    (j : Fin 3) :
    (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ j))
      = {h_simple.hk_eq_3 ▸ j} := by
  classical
  have h3 := h_simple.hk_eq_3
  have h_dist := h_simple.h_inputs_distinct
  -- The base identifications.
  have hb0 : stmt.bases (h3 ▸ (0 : Fin 3)) = h_simple.P₁ := h_simple.h_P₁_eq.symm
  have hb1 : stmt.bases (h3 ▸ (1 : Fin 3)) = h_simple.P₂ := h_simple.h_P₂_eq.symm
  have hb2 : stmt.bases (h3 ▸ (2 : Fin 3)) = h_simple.P₃ := h_simple.h_P₃_eq.symm
  -- Distinctness facts in the form needed.
  have hP12 : h_simple.P₁ ≠ h_simple.P₂ := h_dist.2.2.2.1
  have hP13 : h_simple.P₁ ≠ h_simple.P₃ := h_dist.2.2.2.2.1
  have hP23 : h_simple.P₂ ≠ h_simple.P₃ := h_dist.2.2.2.2.2
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · -- Forward: stmt.bases i = stmt.bases (h3 ▸ j) → i = h3 ▸ j.
    intro h_bi
    -- Cast i to a fresh Fin 3 variable ji by obtaining.
    obtain ⟨ji, hji⟩ : ∃ ji : Fin 3, ji = Fin.cast h3 i := ⟨Fin.cast h3 i, rfl⟩
    -- Show stmt.bases i = stmt.bases (h3 ▸ ji).
    have h_i_eq : stmt.bases i = stmt.bases (h3 ▸ ji) := by
      congr 1
      apply Fin.ext
      rw [cast_subst_val_l4 (E := E) h3 ji, hji]
      rfl
    rw [h_i_eq] at h_bi
    -- Now stmt.bases (h3 ▸ ji) = stmt.bases (h3 ▸ j). Case-split on ji and j.
    have h_eq : ji = j := by
      have h_contra : ∀ (h_bi' : stmt.bases (h3 ▸ (0 : Fin 3))
                              = stmt.bases (h3 ▸ (1 : Fin 3))), False := fun h =>
        hP12 ((hb0.symm.trans h).trans hb1)
      have h_contra2 : ∀ (h_bi' : stmt.bases (h3 ▸ (0 : Fin 3))
                              = stmt.bases (h3 ▸ (2 : Fin 3))), False := fun h =>
        hP13 ((hb0.symm.trans h).trans hb2)
      have h_contra3 : ∀ (h_bi' : stmt.bases (h3 ▸ (1 : Fin 3))
                              = stmt.bases (h3 ▸ (0 : Fin 3))), False := fun h =>
        (Ne.symm hP12) ((hb1.symm.trans h).trans hb0)
      have h_contra4 : ∀ (h_bi' : stmt.bases (h3 ▸ (1 : Fin 3))
                              = stmt.bases (h3 ▸ (2 : Fin 3))), False := fun h =>
        hP23 ((hb1.symm.trans h).trans hb2)
      have h_contra5 : ∀ (h_bi' : stmt.bases (h3 ▸ (2 : Fin 3))
                              = stmt.bases (h3 ▸ (0 : Fin 3))), False := fun h =>
        (Ne.symm hP13) ((hb2.symm.trans h).trans hb0)
      have h_contra6 : ∀ (h_bi' : stmt.bases (h3 ▸ (2 : Fin 3))
                              = stmt.bases (h3 ▸ (1 : Fin 3))), False := fun h =>
        (Ne.symm hP23) ((hb2.symm.trans h).trans hb1)
      fin_cases ji <;> fin_cases j
      · rfl
      · exact (h_contra h_bi).elim
      · exact (h_contra2 h_bi).elim
      · exact (h_contra3 h_bi).elim
      · rfl
      · exact (h_contra4 h_bi).elim
      · exact (h_contra5 h_bi).elim
      · exact (h_contra6 h_bi).elim
      · rfl
    -- ji = j, recover i.
    apply Fin.ext
    rw [cast_subst_val_l4 (E := E) h3 j]
    rw [show j.val = ji.val from h_eq ▸ rfl, hji]
    rfl
  · -- Backward.
    intro h_eq
    rw [h_eq]

/-- For (x, y) = P_0: filter (bases i = (x, y)) is empty (P_0 ∉ bases). -/
private theorem bases_filter_empty_at_P0
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = h_simple.P₀) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  intro i _
  -- Cast i to Fin 3 and case-split.
  have h3 := h_simple.hk_eq_3
  have h_dist := h_simple.h_inputs_distinct
  obtain ⟨ji, hji⟩ : ∃ ji : Fin 3, ji = Fin.cast h3 i := ⟨Fin.cast h3 i, rfl⟩
  have h_i_eq : stmt.bases i = stmt.bases (h3 ▸ ji) := by
    congr 1
    apply Fin.ext
    rw [cast_subst_val_l4 (E := E) h3 ji, hji]
    rfl
  rw [h_i_eq]
  fin_cases ji
  · -- ji = 0: bases (h3 ▸ 0) = P_1 ≠ P_0.
    simp only [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl]
    rw [← h_simple.h_P₁_eq]
    exact (Ne.symm h_dist.1)
  · simp only [show (⟨1, by decide⟩ : Fin 3) = 1 from rfl]
    rw [← h_simple.h_P₂_eq]
    exact (Ne.symm h_dist.2.1)
  · simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl]
    rw [← h_simple.h_P₃_eq]
    exact (Ne.symm h_dist.2.2.1)

/-- Helper: at any (x, y) = P_k for k ∈ {0, 1, 2, 3}, honestDivisorCoeffs = 1. -/
private theorem honestCoeffs_eq_one_at_P_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1)
    {x y : ZMod E.q} (hns : E.toW.toAffine.Nonsingular x y)
    (h_xy : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
            (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃) :
    honestDivisorCoeffs E stmt wit hk msg
        (WeierstrassCurve.Affine.Point.some _ _ hns) = 1 := by
  classical
  rw [show (WeierstrassCurve.Affine.Point.some _ _ hns : ECPoint E)
        = ECPoint.affine E x y from (ECPoint.affine_of_nonsingular E hns).symm]
  rw [show honestDivisorCoeffs E stmt wit hk msg (ECPoint.affine E x y)
        = (if (x, y) = (stmt.target.1, -stmt.target.2) then (1 : ℤ) else 0) +
          ∑ i ∈ (Finset.univ : Finset (Fin stmt.k)).filter
            (fun i => stmt.bases i = (x, y)),
            (wit.scalars (hk ▸ i)) by
        rw [ECPoint.affine_of_nonsingular E hns]; rfl]
  have h_negT : (stmt.target.1, -stmt.target.2) = h_simple.P₀ := h_simple.h_P₀_eq.symm
  have h_dist := h_simple.h_inputs_distinct
  rcases h_xy with h0 | h1 | h2 | h3'
  · -- (x, y) = P_0. Indicator = 1, filter = ∅, sum = 0. Total = 1.
    have h_eq_negT : (x, y) = (stmt.target.1, -stmt.target.2) := by
      rw [h_negT]; exact h0
    rw [if_pos h_eq_negT]
    -- Filter is empty.
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = h_simple.P₀) := by
      rw [h0]
    rw [h_filter_eq, bases_filter_empty_at_P0 E h_simple]
    simp
  · -- (x, y) = P_1. Indicator = 0, filter = {h3 ▸ 0}, sum = 1. Total = 1.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h1]; exact (Ne.symm h_dist.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (0 : Fin 3))) := by
      rw [h1, ← h_simple.h_P₁_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 0]
    rw [Finset.sum_singleton, h_scalars]
  · -- (x, y) = P_2.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h2]; exact (Ne.symm h_dist.2.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (1 : Fin 3))) := by
      rw [h2, ← h_simple.h_P₂_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 1]
    rw [Finset.sum_singleton, h_scalars]
  · -- (x, y) = P_3.
    have h_ne_negT : (x, y) ≠ (stmt.target.1, -stmt.target.2) := by
      rw [h_negT, h3']; exact (Ne.symm h_dist.2.2.1)
    rw [if_neg h_ne_negT, zero_add]
    have h_filter_eq : (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = (x, y)) =
        (Finset.univ : Finset (Fin stmt.k)).filter
        (fun i => stmt.bases i = stmt.bases (h_simple.hk_eq_3 ▸ (2 : Fin 3))) := by
      rw [h3', ← h_simple.h_P₃_eq]
    rw [h_filter_eq, bases_filter_singleton_for_length4Simple E h_simple 2]
    rw [Finset.sum_singleton, h_scalars]

/-! ### Full divisor identity ∀ R for length-4 simple

Combines the infinity case, the affine on-support case (R ∈ {P_0..P_3}),
and the affine off-support case (R ∉ {P_0..P_3}). -/

/-- Universal divisor identity: `∀ R : ECPoint E, divisorOfD msg.toD R = honestDivisorCoeffs R`. -/
theorem divisor_identity_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    ∀ R : ECPoint E,
      divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R := by
  classical
  intro R
  match R with
  | WeierstrassCurve.Affine.Point.zero =>
    exact divisor_identity_at_infinity_for_length4Simple E h_simple hk
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) hns =>
    have hOC : y ^ 2 = x ^ 3 + E.curveA * x + E.curveB :=
      (E.equation_iff x y).mp ((E.equation_iff_nonsingular).mpr hns)
    have hP : (x, y) ∈ E.points := E.hComplete x y hOC
    -- Case-split on (x, y) ∈ {P_0..P_3} or not.
    by_cases h_in : (x, y) = h_simple.P₀ ∨ (x, y) = h_simple.P₁ ∨
                    (x, y) = h_simple.P₂ ∨ (x, y) = h_simple.P₃
    · -- On support.
      rw [div_eq_one_at_P_for_length4Simple E h_simple hns h_in]
      rw [honestCoeffs_eq_one_at_P_for_length4Simple E h_simple hk h_scalars hns h_in]
    · -- Off support.
      push_neg at h_in
      obtain ⟨h0, h1, h2, h3⟩ := h_in
      exact divisor_identity_at_affine_off_support_for_length4Simple E h_simple hk h_scalars
        hns hP ⟨h0, h1, h2, h3⟩

/-! ### `splitsOnE msg.toD` for length-4 simple

Direct dispatch to `splitsOnE_eagenBuild_length4` (existing
infrastructure in `Divisor/IncrementalConstruction.lean`). -/

theorem splitsOnE_msg_toD_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    splitsOnE E msg.toD := by
  rw [h_simple.h_toD_eq]
  exact splitsOnE_eagenBuild_length4 E
    h_simple.P₀ h_simple.P₁ h_simple.P₂ h_simple.P₃
    h_simple.hP₀ h_simple.hP₁ h_simple.hP₂ h_simple.hP₃
    h_simple.h_xx_01 h_simple.h_xx_23
    h_simple.h_P₀_ne_A2_01 h_simple.h_P₁_ne_A2_01
    h_simple.h_P₂_ne_A2_23 h_simple.h_P₃_ne_A2_23
    h_simple.h_P₀_off_L₂ h_simple.h_P₁_off_L₂
    h_simple.h_P₂_off_L₁ h_simple.h_P₃_off_L₁
    h_simple.h_third_match h_simple.h_y_match h_simple.h_Q₀_nontorsion
    h_simple.h_Q₀_off_L₂_inputs h_simple.h_negQ₀_off_L₁_inputs
    h_simple.h_inputs_distinct

/-- Scalar reduction for the length-4 simple case (with `wit.scalars = 1`). -/
theorem scalar_reduction_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    let hkm : stmt.k = msg.k := h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm
    ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ZMod E.q)) := by
  intro hkm i
  rw [h_simple.h_m_eq_one (hkm ▸ i)]
  rw [h_scalars (hk ▸ i)]
  push_cast; rfl

/-- On-curve invariant: every `bases i` is on E. -/
theorem bases_on_curve_for_length4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt) :
    ∀ i : Fin stmt.k, stmt.bases i ∈ E.points := by
  intro i
  have h3 := h_simple.hk_eq_3
  -- We need: stmt.bases i ∈ E.points.
  -- Strategy: show stmt.bases i = stmt.bases (h3 ▸ Fin.cast h3 i) and use the helper.
  set j : Fin 3 := Fin.cast h3 i with hj_def
  have h_eq : stmt.bases i = stmt.bases (h3 ▸ j) := by
    congr 1
    -- Goal: i = h3 ▸ j (in Fin stmt.k).
    apply Fin.ext
    -- Goal: i.val = (h3 ▸ j).val
    -- (Fin.cast h3 i).val = i.val by definition.
    have h_cast_val : (Fin.cast h3 i).val = i.val := rfl
    -- (h3 ▸ j).val = j.val (cast preserves val).
    -- This is the tricky part; use generalization.
    have h_subst_val : ∀ (h : stmt.k = 3) (j : Fin 3),
        ((h ▸ j : Fin stmt.k)).val = j.val := by
      intro h jj
      -- Case on h.
      generalize stmt.k = k at h jj
      cases h
      rfl
    rw [h_subst_val h3 j, hj_def, h_cast_val]
  rw [h_eq]
  exact bases_at_cast_index_for_length4Simple E h_simple j

/-! ## Bridge: IsHonestForLength4Simple → isHonestFor (full assembly)

Combines all 5 helper components into the full bridge theorem.
Given a `IsHonestForLength4Simple` plus a `DlogWitness` with all
scalars = 1, produces the strengthened `isHonestFor` predicate.

This is the construction-side validation that the strengthened
`isHonestFor` is satisfiable for the length-4 simple case. -/

theorem isHonestFor_of_isHonestForLength4Simple
    {stmt : DlogStatement E.q} {msg : MAProverMsg E.q}
    (h_simple : MAProverMsg.IsHonestForLength4Simple E msg stmt)
    {wit : DlogWitness E.q} (hk : stmt.k = wit.k)
    (h_scalars : ∀ i : Fin wit.k, wit.scalars i = 1) :
    msg.isHonestFor E stmt wit hk
      (h_simple.hk_eq_3.trans h_simple.hkm_eq_3.symm) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact scalar_reduction_for_length4Simple E h_simple hk h_scalars
  · exact splitsOnE_msg_toD_for_length4Simple E h_simple
  · exact divisor_identity_for_length4Simple E h_simple hk h_scalars
  · exact negTarget_on_curve_for_length4Simple E h_simple
  · exact bases_on_curve_for_length4Simple E h_simple

/-! ## Hypothesis-light any-k completeness

`splitsOnE` and `hAccount` are now both derived from `IsHonestForExplicit`.
The remaining hypotheses are just protocol-level invariants. -/

theorem ma_completeness_via_isHonestForExplicit
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (msg : MAProverMsg E.q) (hkm : stmt.k = msg.k)
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
    (hD : ¬ (msg.toD.a = 0 ∧ msg.toD.b = 0))
    (h_negT : (stmt.target.1, -stmt.target.2) ∈ E.points)
    (h_bases : ∀ i : Fin stmt.k, stmt.bases i ∈ E.points)
    (hDegK : msg.toD.degE ≤ stmt.degBound)
    (hAdm : stmt.admSet (msg.polyA, msg.polyB)) :
    ((E.points ×ˢ E.points).filter
        (fun p : (ZMod E.q × ZMod E.q) × (ZMod E.q × ZMod E.q) =>
          ¬ maVerifierAccepts E stmt msg ⟨p.1, p.2⟩ hkm)).card
      ≤ (3 * numZeros E msg.toD + 4) * E.numAffine := by
  -- The scalar reduction (`isHonestFor`'s first conjunct) gives us h_m_eq_scalars.
  have h_m_eq_scalars : ∀ i : Fin stmt.k,
      msg.m (hkm ▸ i) = ((wit.scalars (hk ▸ i) : ℤ) : ZMod E.q) := by
    intro i
    have := h_honest.1 i
    push_cast at this
    convert this
  apply ma_completeness_via_isHonestForExplicit_no_residue_match E stmt wit hk msg hkm
    h_honest hD
    (splitsOnE_of_isHonestForExplicit E stmt wit hk msg hkm h_honest hD)
    (hAccount_of_isHonestForExplicit E stmt wit hk msg hkm h_honest)
    h_negT h_bases h_m_eq_scalars hDegK hAdm

end Divisor
