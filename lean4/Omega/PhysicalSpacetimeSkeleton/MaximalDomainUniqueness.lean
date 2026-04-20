import Omega.PhysicalSpacetimeSkeleton.GlobalGeometricObjects
import Omega.PhysicalSpacetimeSkeleton.TerminalAdmissibleDomain

namespace Omega.PhysicalSpacetimeSkeleton

universe u

open Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure
open TerminalAdmissibleDomainData

/-- Paper-facing uniqueness corollary for the maximal admissible domain attached to a fixed
finite compatible Lorentz family: the descended metric on the terminal quotient is unique, and
therefore the global geometric objects induced from that metric are unique as well.
    cor:physical-spacetime-maximal-domain-uniqueness -/
theorem paper_physical_spacetime_maximal_domain_uniqueness
    (D : TerminalAdmissibleDomainData) :
    (∃! g : D.terminalDomain → ℝ, ∀ i x, g (pointClass D.family i x) = D.family.metric i x) ∧
      ∃! G : GlobalGeometricObjects D.family,
        ∀ i x, G.metric (pointClass D.family i x) = D.family.metric i x := by
  have hTerminal := paper_physical_spacetime_terminal_admissible_domain D
  have hObjects := paper_physical_spacetime_global_geometric_objects D.family
  exact ⟨hTerminal.1, hObjects⟩

end Omega.PhysicalSpacetimeSkeleton
