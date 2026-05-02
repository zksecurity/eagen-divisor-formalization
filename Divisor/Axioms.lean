/-
  Divisor/Axioms.lean — re-export hub

  Each classical axiom lives in its own file under `Divisor/Axioms/`,
  with a docstring mirroring the corresponding `axioms/*.md` textbook
  provenance entry. Downstream files that need access to the full axiom
  surface can `import Divisor.Axioms` as a single entry point.
-/
import Divisor.Axioms.AxiomPrincipalDivisorIff
import Divisor.Axioms.AxiomHasseWeil
import Divisor.Axioms.AxiomWeilReciprocityHonest
import Divisor.Axioms.AxiomExistsDivisorMultiplicity
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomChordFiberProductBarFactored
import Divisor.Axioms.AxiomResultantLogDerivAtSplit
import Divisor.Axioms.AxiomTraceLogDeriv
import Divisor.Axioms.AxiomChordSumEqChordFiberProductLogDeriv
