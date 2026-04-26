import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-partition-identifiability-ind-multiset`. The finite
identifiability conclusion is obtained from the finite-spectrum hypothesis, while the
Legendre-dual conclusion is retained as the pressure/differentiability implication. -/
theorem paper_xi_time_partition_identifiability_ind_multiset
    (finiteIndexSpectrum laplaceValuesDetermineMeasure pressureLimit differentiablePressure
      legendreSpectrum : Prop)
    (hFinite : finiteIndexSpectrum)
    (hLaplace : finiteIndexSpectrum -> laplaceValuesDetermineMeasure)
    (hPressure : pressureLimit -> differentiablePressure -> legendreSpectrum) :
    laplaceValuesDetermineMeasure ∧
      (pressureLimit -> differentiablePressure -> legendreSpectrum) := by
  exact ⟨hLaplace hFinite, hPressure⟩

end Omega.Zeta
