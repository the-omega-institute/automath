import Omega.Zeta.FinitePartCyclicLiftDirichletMultipleSum
import Omega.Zeta.FinitePartCyclicLiftReducedConstantClosed

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclic-lift finite-part chain from the Dirichlet-series
definition to the polylog representation, meromorphic continuation at `s = 1`, and the residue
formula.
    thm:finite-part-cyclic-lift-polylog-dirichlet-xi -/
theorem paper_etds_finite_part_cyclic_lift_polylog_dirichlet_xi
    (dirichletSeriesDefined polylogRepresentation meromorphicAtOne simplePoleAtOne
      residueFormula : Prop)
    (hSeries : dirichletSeriesDefined)
    (hPolylog : dirichletSeriesDefined -> polylogRepresentation)
    (hMeromorphic : polylogRepresentation -> meromorphicAtOne)
    (hPole : meromorphicAtOne -> simplePoleAtOne)
    (hResidue : polylogRepresentation -> residueFormula) :
    polylogRepresentation ∧ simplePoleAtOne ∧ residueFormula := by
  have hPoly : polylogRepresentation := hPolylog hSeries
  have hPoleAtOne : simplePoleAtOne := hPole (hMeromorphic hPoly)
  exact ⟨hPoly, hPoleAtOne, hResidue hPoly⟩

end Omega.Zeta
