import Omega.SyncKernelWeighted.RealInput40P7Branch10GaloisS10

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:real-input-40-p7-jacobian-endoZ`. -/
theorem paper_real_input_40_p7_jacobian_endoz
    (D : real_input_40_p7_branch10_galois_s10_data)
    (jacobianAbsolutelySimple endomorphismRingZ : Prop)
    (hZarhin :
      real_input_40_p7_branch10_galois_s10_statement D →
        jacobianAbsolutelySimple ∧ endomorphismRingZ) :
    jacobianAbsolutelySimple ∧ endomorphismRingZ := by
  exact hZarhin (paper_real_input_40_p7_branch10_galois_s10 D)

end Omega.SyncKernelWeighted
