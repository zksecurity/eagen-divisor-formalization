/-
  Divisor/Axioms.lean — re-export hub

  Each classical axiom lives in its own file under `Divisor/Axioms/`,
  with a docstring mirroring the corresponding `axioms/*.md` textbook
  provenance entry. Downstream files that need access to the full axiom
  surface can `import Divisor.Axioms` as a single entry point.

  The hub also provides typeclass instances + cancellation theorems
  that depend on multiple ECPoint axioms (kept outside the individual
  axiom files to preserve one-axiom-per-file discipline).
-/
import Divisor.Axioms.AxiomPrincipalDivisorIff
import Divisor.Axioms.AxiomHasseWeil
import Divisor.Axioms.AxiomWeilReciprocityHonest
import Divisor.Axioms.AxiomCoordRingEltDivisorGroupSumZero
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomChordSumEqChordFiberProductLogDeriv
import Divisor.Axioms.AxiomBivariatePolyZerosOnExELe

-- The four ECPoint group-law axioms (add_comm, add_assoc, neg_add_cancel,
-- and the closure axiom) have been retired: `ECPoint E` is now
-- `WeierstrassCurve.Affine.Point E.toW` from mathlib, which carries an
-- `AddCommGroup` instance derived from the Picard-group bijection
-- (Silverman III.3.4). The chord-tangent law is therefore a theorem,
-- not a primitive of this development.
