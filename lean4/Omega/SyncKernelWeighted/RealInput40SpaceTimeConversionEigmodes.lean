import Omega.SyncKernelRealInput.RealInput40DirectionalCouplingEigs
import Omega.SyncKernelWeighted.RealInput40SpaceTimeConversionLaw

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:real-input-40-space-time-conversion-eigmodes`. On a generalized eigenmode,
the directional coupling coincides with the Rayleigh quotient `W(v)`, hence with the eigenvalue
`μ`; substituting that identity into the exact conversion law yields the eigenmode corollary. -/
theorem paper_real_input_40_space_time_conversion_eigmodes
    (D : Omega.SyncKernelWeighted.real_input_40_space_time_conversion_law_data)
    (v : Fin 2 -> Real)
    (hv : Omega.SyncKernelRealInput.real_input_40_directional_coupling_eigs_g_unit_sphere v)
    (hW :
      D.real_input_40_space_time_conversion_law_directionalCoupling =
        Omega.SyncKernelRealInput.real_input_40_directional_coupling_eigs_rayleigh v) :
    Omega.SyncKernelWeighted.real_input_40_space_time_conversion_law_statement D := by
  have hrayleigh :
      Omega.SyncKernelRealInput.real_input_40_directional_coupling_eigs_rayleigh v =
        Omega.SyncKernelRealInput.real_input_40_directional_coupling_eigs_mu :=
    (Omega.SyncKernelRealInput.paper_real_input_40_directional_coupling_eigs v hv).2
  have hcoupling :
      D.real_input_40_space_time_conversion_law_directionalCoupling =
        Omega.SyncKernelRealInput.real_input_40_directional_coupling_eigs_mu := by
    rw [hW, hrayleigh]
  simpa [hcoupling] using paper_real_input_40_space_time_conversion_law D

end Omega.SyncKernelWeighted
