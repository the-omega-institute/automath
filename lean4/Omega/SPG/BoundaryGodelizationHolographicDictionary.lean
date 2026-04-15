import Omega.SPG.DyadicCubicalBoundaryInjective

namespace Omega.SPG

/-- Paper: `thm:spg-boundary-godelization-holographic-dictionary`.
    If bulk objects inject into oriented boundary data and the boundary data injects into its
    Gödel code, then the composite bulk-to-code map is injective. -/
theorem paper_spg_boundary_godelization_holographic_dictionary
    {Bulk Boundary Code : Type*}
    (toBoundary : Bulk → Boundary) (toCode : Boundary → Code)
    (hBoundary : Function.Injective toBoundary)
    (hCode : Function.Injective toCode) :
    Function.Injective (toCode ∘ toBoundary) := by
  exact hCode.comp hBoundary

end Omega.SPG
