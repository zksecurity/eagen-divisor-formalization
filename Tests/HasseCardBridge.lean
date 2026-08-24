/-
  Tests/HasseCardBridge.lean

  Mathlib-vocabulary point-count bridge, supporting a future
  restatement of the `hasse_weil_textbook` axiom.

  Today the Hasse axiom is stated over the project's bespoke `ECSetup`
  (`E.numPoints`, a field pinned to `E.points.card + 1`). A more
  standard statement would quantify over an arbitrary mathlib
  `WeierstrassCurve` with nonzero discriminant over an arbitrary
  finite field, and count points as `Nat.card W.toAffine.Point` — the
  exact shape a future mathlib Hasse-bound lemma would have, making it
  a drop-in swap once mathlib lands one:

    ∀ {F : Type} [Field F] [Fintype F] (W : WeierstrassCurve F),
      W.Δ ≠ 0 →
      |(Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1|
        ≤ 2 * Real.sqrt (Fintype.card F)

  (`proposedHasseStatement` below records this shape; it is a `def`,
  NOT an axiom — this module deliberately adds nothing to the axiom
  surface, as the guard pins in `Tests/AxiomClosurePin.lean` enforce.)

  This file proves the reusable half of the bridge needed to derive
  the current `ECSetup` form from that statement:

    `Nat.card W.toAffine.Point = #{nonsingular affine pairs} + 1`

  for any Weierstrass curve over a finite field. The remaining half
  (`Nat.card {xy // Nonsingular xy.1 xy.2} = E.points.card` for the
  `ECSetup` instance) is `ECSetup`-plumbing via `hOnCurve`/`hComplete`
  and `equation_iff_nonsingular`.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Analysis.Real.Sqrt

open WeierstrassCurve

namespace Tests.HasseCardBridge

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)

/-- Points of the affine model, as `Option` of nonsingular coordinate
pairs: `none` is the point at infinity. -/
noncomputable def pointEquivOption :
    W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} where
  toFun P := match P with
    | .zero => none
    | @Affine.Point.some _ _ _ x y h => some ⟨(x, y), h⟩
  invFun o := match o with
    | none => .zero
    | some ⟨⟨x, y⟩, h⟩ => .some x y h
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

instance : Finite {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} :=
  Subtype.finite

/-- **Point-count bridge.** The mathlib point count of the affine model
is the number of nonsingular affine coordinate pairs plus one (the
point at infinity). -/
theorem card_point_eq :
    Nat.card W.toAffine.Point
      = Nat.card {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2} + 1 := by
  rw [Nat.card_congr (pointEquivOption W), Finite.card_option]

/-- The proposed mathlib-vocabulary Hasse statement (recorded as a
`Prop`-valued `def`, NOT declared as an axiom). General Weierstrass
form over any finite field — char 2 and 3 included. -/
def proposedHasseStatement : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] (W : WeierstrassCurve F), W.Δ ≠ 0 →
    |(Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1|
      ≤ 2 * Real.sqrt (Fintype.card F)

end Tests.HasseCardBridge
