import Omega.SyncKernelWeighted.FiniteRhParityGeneral

namespace Omega.SyncKernelRealInput

/-- Paper label: `cor:real-input-40-primitive-orbits-parity-cancellation`. -/
theorem paper_real_input_40_primitive_orbits_parity_cancellation
    (D : Omega.SyncKernelWeighted.finite_rh_parity_general_data) :
    D.parity_cancellation_law := by
  exact Omega.SyncKernelWeighted.paper_finite_rh_parity_general D

end Omega.SyncKernelRealInput
