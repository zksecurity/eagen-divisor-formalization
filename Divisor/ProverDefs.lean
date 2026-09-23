/-
  Divisor/ProverDefs.lean — the honest MA prover, as definitions only.

  `interpolate` runs the line build on `honestSupport`, the multiset
  `(−P) + Σ nᵢ·(Bᵢ)`; `prove` rescales the result into the statement's
  admissible set through an `AdmNormalizer`, or returns `none`. The
  correctness theorems live in `Divisor/Prover.lean`; this module is
  kept proof-free so `Challenge.lean` can state them.
-/
import Divisor.HonestSupport
import Divisor.AdmNormalizer

open Polynomial

namespace Divisor

variable (E : ECSetup)

variable (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)

/-- The prover message carrying `D`, with the witness residues. -/
noncomputable def msgOfD (D : CoordRingElt E.q) : MAProverMsg E.q stmt.k where
  m i := (wit.scalars (hk ▸ i) : ZMod E.q)
  polyA := D.a
  polyB := D.b

@[simp] theorem msgOfD_toD (D : CoordRingElt E.q) : (msgOfD E stmt wit hk D).toD = D := rfl

/-- The honest prover's polynomial: the line build over `honestSupport`. -/
noncomputable def interpolate : CoordRingElt E.q :=
  LineAccum.lineBuild_singletons E (honestSupport stmt wit hk)

/-- The prover: interpolate, then rescale into the admissible set. -/
noncomputable def prove (N : AdmNormalizer E.q) : Option (MAProverMsg E.q stmt.k) :=
  (N.normalize (interpolate E stmt wit hk)).map fun c =>
    msgOfD E stmt wit hk (c • interpolate E stmt wit hk)

end Divisor
