import Omega.CircleDimension.MinimalRecordAxis

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address restatement of the circle-dimension minimal-record-axis package: the admissible
continuous transversal is unique. -/
theorem paper_typed_address_biaxial_completion_unique_continuous_transversal
    (D : Omega.CircleDimension.MinimalRecordAxisData) : D.uniqueContinuousTransverse := by
  exact (Omega.CircleDimension.paper_cdim_minimal_record_axis D).2.1

end Omega.TypedAddressBiaxialCompletion
