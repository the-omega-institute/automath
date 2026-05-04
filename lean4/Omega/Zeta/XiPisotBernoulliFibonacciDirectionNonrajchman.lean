import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-pisot-bernoulli-fibonacci-direction-nonrajchman`. -/
theorem paper_xi_pisot_bernoulli_fibonacci_direction_nonrajchman
    (nontrivialFibonacciDirection fourierLimitPositive escapedFrequencySequence
      torusFourierSameLimit nonRajchmanWitness : Prop)
    (hlimit : nontrivialFibonacciDirection -> fourierLimitPositive)
    (hescape : nontrivialFibonacciDirection -> escapedFrequencySequence)
    (hperiodize : fourierLimitPositive -> torusFourierSameLimit)
    (hwitness :
      escapedFrequencySequence -> torusFourierSameLimit -> nonRajchmanWitness)
    (hdir : nontrivialFibonacciDirection) :
    fourierLimitPositive ∧ escapedFrequencySequence ∧ torusFourierSameLimit ∧
      nonRajchmanWitness := by
  have hfourier : fourierLimitPositive := hlimit hdir
  have hescaped : escapedFrequencySequence := hescape hdir
  have htorus : torusFourierSameLimit := hperiodize hfourier
  exact ⟨hfourier, hescaped, htorus, hwitness hescaped htorus⟩

end Omega.Zeta
