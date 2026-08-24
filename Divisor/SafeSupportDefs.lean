/-
  Divisor/SafeSupportDefs.lean

  Definitions for the any-length binary completeness statements: the
  general-position hypothesis on a support list (`Landmark.SafePairs`),
  its computable, decidable form (`Landmark.SafePairsCert` via
  `Landmark.pointSum`), and the binary support constructor
  (`binarySupport`).

  This module carries no completeness theorems — the proofs live in
  `Divisor/IsHonestForBinary.lean` and `Divisor/SafeSupport.lean` — so
  `Challenge.lean` can import it to state the binary headline theorems
  without importing their proofs.
-/
import Divisor.EagenBuildLandmark
import Divisor.Protocol

namespace Divisor.Landmark

variable (E : ECSetup)

/-- **Semantic general-position hypothesis on a support list.** For
every split `xs ++ ys` of every sublist of `Ps` (both halves
nonempty), the pair of elliptic-curve sums `(Σ xs, Σ ys)` is
chord-safe. Every combine at every level of the accumulation tree is
such a pair, so this hypothesis discharges the whole chain
certificate (`iteratedPointChordCase_of_safePairs` in
`Divisor/SafeSupport.lean`).

Degenerate supports violating it exist — a 2-torsion point in the
support, or block sums related by `B = −2A` — and those genuinely
break the chord accumulation, so some such hypothesis is necessary
for an any-length statement. -/
def SafePairs (Ps : List (ZMod E.q × ZMod E.q)) : Prop :=
  ∀ xs ys : List (ZMod E.q × ZMod E.q),
    xs ≠ [] → ys ≠ [] → (xs ++ ys).Sublist Ps →
    PointChordCase E (sumOnE E xs) (sumOnE E ys)

/-- Computable elliptic-curve sum of a support list, via the point
skeleton (`sumOnE` itself is noncomputable through the group-law
instance). -/
def pointSum (Ps : List (ZMod E.q × ZMod E.q)) : ECPoint E :=
  Ps.foldr (fun P S => pointCombine E (ECPoint.affine E P.1 P.2) S) 0

/-- Computable form of `SafePairs`: quantify over sublists and split
positions. `Decidable`, hence dischargeable by `decide` /
`native_decide` on concrete supports. -/
def SafePairsCert (Ps : List (ZMod E.q × ZMod E.q)) : Prop :=
  ∀ zs ∈ Ps.sublists, ∀ k ∈ List.range zs.length,
    k = 0 ∨ PointChordCase E (pointSum E (zs.take k)) (pointSum E (zs.drop k))

instance safePairsCert_decidable (Ps : List (ZMod E.q × ZMod E.q)) :
    Decidable (SafePairsCert E Ps) := by
  unfold SafePairsCert
  infer_instance

end Divisor.Landmark

namespace Divisor

/-- The binary support list: `(-target)` followed by every statement base
    whose transported binary witness scalar is `1`. -/
def binarySupport
    {E : ECSetup} (stmt : DlogStatement E.q) (wit : DlogWitness E.q)
    (hk : stmt.k = wit.k)
    (_h_binary : ∀ i : Fin wit.k, wit.scalars i = 0 ∨ wit.scalars i = 1) :
    List (ZMod E.q × ZMod E.q) :=
  (stmt.target.1, -stmt.target.2) ::
    (List.finRange wit.k).filterMap (fun i =>
      if wit.scalars i = 1 then
        some (stmt.bases (Fin.cast hk.symm i))
      else
        none)

end Divisor
