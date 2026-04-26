import Omega.TypedAddressBiaxialCompletion.JensenDefectLogDerivative

namespace Omega.CircleDimension

/-- Chapter-level wrapper for the typed-address Jensen-defect log-derivative package.
    prop:cdim-jensen-defect-log-derivative -/
theorem paper_cdim_jensen_defect_log_derivative
    (D : Omega.TypedAddressBiaxialCompletion.JensenDefectLogDerivativeData) :
    Omega.TypedAddressBiaxialCompletion.jensenDefectLogDerivativeStatement D := by
  exact
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_jensen_defect_log_derivative D

end Omega.CircleDimension
