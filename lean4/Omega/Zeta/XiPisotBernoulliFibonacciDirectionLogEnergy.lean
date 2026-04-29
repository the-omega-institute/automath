import Mathlib.Tactic
import Omega.Zeta.XiPisotBernoulliFibonacciDirectionNonrajchman

namespace Omega.Zeta

/-- Paper label: `cor:xi-pisot-bernoulli-fibonacci-direction-log-energy`. -/
theorem paper_xi_pisot_bernoulli_fibonacci_direction_log_energy
    (nontrivialFibonacciDirection fourierLimitPositive escapedFrequencySequence
      logarithmicEnergyLaw divergentSquaredEnergy : Prop)
    (hnonrajchman : nontrivialFibonacciDirection →
      fourierLimitPositive ∧ escapedFrequencySequence)
    (henergy : fourierLimitPositive → escapedFrequencySequence → logarithmicEnergyLaw)
    (hdiv : logarithmicEnergyLaw → divergentSquaredEnergy)
    (hdir : nontrivialFibonacciDirection) :
    logarithmicEnergyLaw ∧ divergentSquaredEnergy := by
  rcases hnonrajchman hdir with ⟨hfourier, hescaped⟩
  have hlog : logarithmicEnergyLaw := henergy hfourier hescaped
  exact ⟨hlog, hdiv hlog⟩

end Omega.Zeta
