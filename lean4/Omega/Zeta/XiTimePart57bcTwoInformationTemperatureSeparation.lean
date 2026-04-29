namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part57bc-two-information-temperature-separation`. -/
theorem paper_xi_time_part57bc_two_information_temperature_separation
    (globalLowerBound localExactRate distinctMechanisms : Prop) (hGlobal : globalLowerBound)
    (hLocal : localExactRate) (hDistinct : distinctMechanisms) :
    globalLowerBound ∧ localExactRate ∧ distinctMechanisms := by
  exact ⟨hGlobal, hLocal, hDistinct⟩

end Omega.Zeta
