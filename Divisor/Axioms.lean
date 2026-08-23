/-
  Divisor/Axioms.lean — re-export hub

  Each classical axiom lives in its own file under `Divisor/Axioms/`.
  The README records the axiom surface. Downstream files that need
  access to the full axiom surface can `import Divisor.Axioms` as a
  single entry point.

  The Hasse–Weil axiom (`Divisor/Axioms/AxiomHasseWeil.lean`) is
  deliberately NOT re-exported here: it is consumed only by the
  terminal leaf module `Divisor/Hasse.lean`, keeping every theorem
  reachable from this hub axiom-free.
-/
import Divisor.Axioms.AxiomExistsDivisorMultiplicity
import Divisor.Axioms.AxiomChordFiberProductEqNormZUnderSplit
import Divisor.Axioms.AxiomChordFiberProductBarFactored
import Divisor.Axioms.AxiomResultantLogDerivAtSplit
import Divisor.Axioms.AxiomTraceLogDeriv
import Divisor.Axioms.AxiomChordSumEqChordFiberProductLogDeriv
