import Omega.Conclusion.Window6BinarySuffixCylinderTrichotomy
import Omega.Conclusion.Window6BoundaryQuotientCyclicCardinality

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-boundary-parity-rigid-x4-localization`.  The binary
depth-6 layer of multiplicity two is the rigid `X₄,01` suffix cylinder, and the boundary
cardinality complement is `21 - 18 = 3`. -/
theorem paper_conclusion_window6_boundary_parity_rigid_x4_localization :
    window6BinaryLayer 2 = window6X4Suffix01 ∧ (21 : ℕ) - 18 = 3 := by
  refine ⟨paper_conclusion_window6_binary_suffix_cylinder_trichotomy.1, by omega⟩

end Omega.Conclusion
