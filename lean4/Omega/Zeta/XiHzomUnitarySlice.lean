import Omega.Zeta.XiUnitarySliceSpectralCrossing

namespace Omega.Zeta

/-- Paper label: `cor:xi-hzom-unitary-slice`. -/
theorem paper_xi_hzom_unitary_slice (D : xi_unitary_slice_spectral_crossing_data) :
    xi_unitary_slice_spectral_crossing_statement D := by
  exact paper_xi_unitary_slice_spectral_crossing D

end Omega.Zeta
