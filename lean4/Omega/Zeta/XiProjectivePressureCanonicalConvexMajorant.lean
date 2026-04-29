import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-projective-pressure-canonical-convex-majorant`. -/
theorem paper_xi_projective_pressure_canonical_convex_majorant
    (convexPressure integerLowerBound jensenChain exactInterpolation : Prop)
    (hconvex : convexPressure)
    (hlower : convexPressure → integerLowerBound)
    (hjensen : convexPressure → integerLowerBound → jensenChain)
    (hexact : jensenChain → exactInterpolation) :
    convexPressure ∧ integerLowerBound ∧ jensenChain ∧ exactInterpolation := by
  have hLower : integerLowerBound := hlower hconvex
  have hJensen : jensenChain := hjensen hconvex hLower
  exact ⟨hconvex, hLower, hJensen, hexact hJensen⟩

end Omega.Zeta
