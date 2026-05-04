/-
  Divisor/EagenBuildRecursive.lean

  Recursive `eagenBuild` driver for general-N point lists, following
  Eagen §3.1.1 ("Incremental construction") in 596.pdf.

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

  ## Status

  This file holds the skeleton + design. The length-4 base case is in
  `Divisor/IncrementalConstruction.lean` (proved equivalent to the
  paper's level-1 simplification under sum-zero). Generalization to
  any-N requires:

  1. Carry-forward logic for odd lengths.
  2. Division correctness proof (verticals factor cleanly).
  3. Divisor equation by induction on levels.
  4. Tangent doubling / vertical-chord branches at each level.
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

/-! ## Sanity check: length-2 sum-zero base case

For input `[P, -P]` (the simplest sum-zero case), `eagenBuild` produces
the vertical line `(X - x(P))`, whose divisor is `(P) + (-P) - 2·O`. -/

theorem eagenBuild_length2_neg_eq_vertical
    (P : ZMod E.q × ZMod E.q) (hY : P.2 ≠ 0) :
    eagenBuild E [P, (P.1, -P.2)]
      = ({ a := Polynomial.X - Polynomial.C P.1, b := 0 } : CoordRingElt E.q) := by
  unfold eagenBuild eagenBuild_level0
  simp only [List.map]
  -- The pattern matches `P :: Q :: rest` with rest = [].
  -- The condition `P.1 ≠ (P.1, -P.2).1 = P.1` is false.
  have h_xx : ¬ (P.1 ≠ (P.1, -P.2).1) := fun h => h rfl
  have h_yy : P.2 = -((P.1, -P.2).2) := by simp
  -- Level 0 gives a single vertical accumulator; iteration is trivial.
  simp only [eagenBuild_level0, dif_neg h_xx, dif_pos h_yy,
    EagenAccum.fromChordPair_vertical]
  unfold eagenBuild_iterate
  simp

/-! ## Length-4 reduction (deferred)

For length-4 sum-zero distinct inputs, the recursive `eagenBuild`
produces the same polynomial as `eagenBuild_length4_explicit`. The
proof requires careful unfolding of the recursive structure and
matching against the explicit length-4 formula. Substantial bookkeeping
deferred to subsequent firings. -/

/-! ## `IsHonestForExplicit` predicate (any-k completeness path)

Per Codex's guidance: rather than deriving completeness from a specific
constructive `eagenBuild` build, take the divisor identity as a stronger
hypothesis. This handles ANY honest divisor structure (any k, any scalars)
provided the user proves the identity.

For length-4 simple, `eagenBuild_length4_explicit` provides the witness
(via `IsHonestForLength4Simple`). For general k, the witness is the
recursive `eagenBuild` (proof of correctness pending).

The predicate adds to existing `isHonestFor`:
* All conditions of `isHonestFor` (scalar reduction, IsPrincipal).
* PLUS: `∀ R : ECPoint E, divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R`. -/

def MAProverMsg.IsHonestForExplicit (E : ECSetup) (msg : MAProverMsg E.q)
    (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k) (hkm : stmt.k = msg.k) : Prop :=
  msg.isHonestFor E stmt wit hk hkm
  ∧ ∀ R : ECPoint E, divisorOfD E msg.toD R = honestDivisorCoeffs E stmt wit hk msg R

/-! ## General hQline derivation from `hGood`

For any nonzero D, if `(A_0, A_1) ∉ badChallengesCompleteness E D`, then
the chord through `A_0, A_1` doesn't pass through any zero of D.

Proof: Bezout — chord intersects E in `{A_0, A_1, A_2}`. Any zero of
D on E that's also on the chord must be in this set, but `¬bad` excludes
D vanishing at A_0, A_1, or A_2. -/

theorem hQline_of_hGood_general
    {D : CoordRingElt E.q} (hD : ¬ (D.a = 0 ∧ D.b = 0))
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
    (h_honest : msg.IsHonestForExplicit E stmt wit hk hkm)
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
    push_cast
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
    push_cast
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
    push_cast
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
  obtain ⟨_h_basic, h_div⟩ := h_honest
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

/-! ## Notes on remaining infrastructure for any-k completeness

To prove `ma_completeness_via_isHonestForExplicit` for ANY k, we need:

1. **Divisor identity → β-properties** (β_fun = ordAt = betaTrue):
   - hβsup, hβcov: standard from any nonzero D (no divisor identity needed).
   - hβtrue: trivial (`betaTrue = ordAt`).
   - hAccount: ∑ ordAt = natDegree(normPoly E D). Provable from
     `sum_ordAt_eq_natDegree_under_split` IF splitsOnE.

2. **splitsOnE D**: Provable from divisor identity (zeros are at honest
   support, all rational). Substantial — defer or take as explicit hyp.

3. **hQline**: `hQline_of_hGood_general` (proved above) — general for any D.

4. **hDen**: `hDen_of_hGood` (in `Divisor/LogDerivEagenLength4.lean`) is
   already general (no length-4 specifics).

5. **hResidueMatch**: `∑ zerosFinset · L^{-1} = ∑ E.points honestDivisorCoeffs · L^{-1}`
   (since coeff = 0 outside support), then unfold to `L(-P)^{-1} + Σ m_j L(B_j)^{-1}`.
   Requires careful Finset.sum manipulation; substantial.

The full integration is feasible but multi-firing. Length-4 simple
remains the headline demonstration.

## Future work

The skeleton above defines the construction; correctness proofs require:

* **Length-4 reduction**: prove `eagenBuild [P_0, P_1, P_2, P_3]` (assuming
  sum-zero + genericity) reduces to `eagenBuild_length4_explicit` (or an
  equivalent form). Bridge between the recursive definition and the
  explicit length-4 case.
* **Divisor equation by induction**: prove
  `divisorOfD E (eagenBuild Ps) R = Σ_i (R = P_i ? 1 : 0) - n·(R = ∞ ? 1 : 0)`
  for sum-zero `Ps`, by induction on the iteration depth.
* **Carry-forward correctness**: odd lengths.
* **Doubling/vertical branches**: at each level, when adjacent entries have
  the same x-coordinate, dispatch to tangent or vertical-chord handling.

These are deferred to subsequent firings. -/

end Divisor
