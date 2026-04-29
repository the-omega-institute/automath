import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-cartesian-power-joukowsky-godel-anisotropic-parabola`. -/
theorem paper_xi_cartesian_power_joukowsky_godel_anisotropic_parabola
    (tangentCLT anisotropicLimit parabolaSupport : Prop)
    (hCLT : tangentCLT)
    (hTransport : tangentCLT → anisotropicLimit)
    (hParabola : anisotropicLimit → parabolaSupport) :
    anisotropicLimit ∧ parabolaSupport := by
  exact ⟨hTransport hCLT, hParabola (hTransport hCLT)⟩

end Omega.Zeta
