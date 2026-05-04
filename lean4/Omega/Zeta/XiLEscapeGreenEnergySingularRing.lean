import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-L-escape-green-energy-singular-ring`. -/
theorem paper_xi_l_escape_green_energy_singular_ring
    (lReflectiveSquareRoot escapeEnergyDiscreteGreen escapeEnergyIntegralGreen : Prop)
    (hreflect : lReflectiveSquareRoot)
    (hdisc : lReflectiveSquareRoot -> escapeEnergyDiscreteGreen)
    (hint : escapeEnergyDiscreteGreen -> escapeEnergyIntegralGreen) :
    escapeEnergyDiscreteGreen ∧ escapeEnergyIntegralGreen := by
  have hdiscrete : escapeEnergyDiscreteGreen := hdisc hreflect
  exact ⟨hdiscrete, hint hdiscrete⟩

end Omega.Zeta
