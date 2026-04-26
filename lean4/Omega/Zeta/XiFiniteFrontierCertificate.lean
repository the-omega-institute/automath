import Omega.POM.CostOptimizationDecidable

namespace Omega.Zeta

open Omega.POM.CostOptimizationDecidableData

/-- Paper label: `thm:xi-finite-frontier-certificate`. This is the Zeta-facing restatement of the
finite bounded-slice Pareto-frontier certificate from the POM layer. -/
theorem paper_xi_finite_frontier_certificate (D : Omega.POM.CostOptimizationDecidableData) :
    D.HasFiniteComputableFrontier := by
  simpa using Omega.POM.paper_pom_cost_optimization_decidable D

end Omega.Zeta
