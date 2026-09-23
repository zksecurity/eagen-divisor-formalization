/-
  Divisor/ProverDefs.lean — the honest MA prover, as executable
  definitions only.

  `proveC` runs the computable singleton line build
  (`LineAccum.lineBuildC_singletons`) on `honestSupport`, the multiset
  `(−P) + Σ nᵢ·(Bᵢ)`, rescales the result into the statement's
  admissible set through an `AdmNormalizer`, and returns a `MsgC`, or
  `none`. `MsgC.toMsg` reads the output as a protocol message,
  coefficient by coefficient. The correctness theorems live in
  `Divisor/Prover.lean`; this module is kept free of them so
  `Challenge.lean` can state them.
-/
import Divisor.HonestSupport
import Divisor.AdmNormalizer
import Divisor.LineBuildComputable.Singletons

open Polynomial

namespace Divisor

/-- The prover's computable output: residues and the coefficient lists of
    `D = a(x) − b(x)·y`. -/
structure MsgC (q k : ℕ) where
  m : Fin k → ZMod q
  a : CoeffPoly q
  b : CoeffPoly q

/-- The protocol message denoted by a prover output. -/
noncomputable def MsgC.toMsg {q k : ℕ} [Fact (Nat.Prime q)] (out : MsgC q k) :
    MAProverMsg q k where
  m := out.m
  polyA := out.a.toPolynomial
  polyB := out.b.toPolynomial

variable (E : ECSetup)

variable (stmt : DlogStatement E.q) (wit : DlogWitness E.q) (hk : stmt.k = wit.k)

/-- **The honest prover**: interpolate by the singleton line build over
    `honestSupport`, then rescale into the admissible set. Executable. -/
def proveC (N : AdmNormalizer E.q) : Option (MsgC E.q stmt.k) :=
  let D := LineAccum.lineBuildC_singletons E (honestSupport stmt wit hk)
  (N.normalize D).map fun c =>
    { m := fun i => (wit.scalars (hk ▸ i) : ZMod E.q), a := c • D.a, b := c • D.b }

end Divisor
