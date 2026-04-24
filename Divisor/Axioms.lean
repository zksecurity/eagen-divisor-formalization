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
import Divisor.Axioms.AxiomECPointAddComm
import Divisor.Axioms.AxiomECPointAddAssoc
import Divisor.Axioms.AxiomECPointNegAddCancel
import Divisor.Axioms.AxiomWeilReciprocityHonest
import Divisor.Axioms.AxiomCoordRingEltDivisorGroupSumZero
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomChordSumEqChordFiberProductLogDeriv
import Divisor.Axioms.AxiomBivariatePolyZerosOnExELe

-- All axiom declarations + downstream instances (Std.Commutative /
-- Std.Associative, ECPoint.add_left_cancel) live in their respective
-- files. This hub file exists only as a single import entry point.
