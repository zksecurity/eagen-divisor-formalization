/-
  Divisor/Bridges.lean — re-export hub for the divisor-calculus bridge
  layer (`Divisor/Bridges/`): divisor-multiplicity existence, the
  chord-fiber-product/norm identities, and the resultant/trace
  logarithmic-derivative formulas. All axiom-free; the project's one
  axiom lives in `Divisor/Axioms/AxiomHasseWeil.lean` and is imported
  only by the terminal module `Divisor/Hasse.lean`.
-/
import Divisor.Bridges.DivisorMultiplicity
import Divisor.Bridges.ChordFiberProductNormZ
import Divisor.Bridges.ChordFiberProductBarFactored
import Divisor.Bridges.ResultantLogDerivAtSplit
import Divisor.Bridges.TraceLogDeriv
import Divisor.Bridges.ChordSumEqChordFiberProductLogDeriv
