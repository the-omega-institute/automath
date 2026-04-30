import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-boundary-support-function-root-system`. -/
theorem paper_xi_leyang_boundary_support_function_root_system {V : Type*} [Fintype V]
    (boundaryExponent supportFunction : V → Real)
    (weylWallsRecovered rootSystemRecovered : Prop)
    (hSupport : boundaryExponent = supportFunction)
    (hRecover : boundaryExponent = supportFunction → weylWallsRecovered ∧ rootSystemRecovered) :
    weylWallsRecovered ∧ rootSystemRecovered := by
  exact hRecover hSupport

end Omega.Zeta
