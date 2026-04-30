import Omega.Conclusion.AnchorResidualPluckerVolume

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-anchor-residual-plucker-geometry`. -/
theorem paper_conclusion_anchor_residual_plucker_geometry (κ r : ℕ) :
    conclusion_anchor_residual_plucker_volume_plucker_volume κ r =
      conclusion_anchor_residual_plucker_volume_residual_kernel_polynomial_frame κ r := by
  exact (paper_conclusion_anchor_residual_plucker_volume κ r).1

end Omega.Conclusion
