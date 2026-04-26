import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-S3-upgrade-vtheta`. The improved affine residual input is
threaded through the uniform main and energy-coupling hypotheses to obtain the upgraded
third-trace estimate. -/
theorem paper_gm_s3_upgrade_vtheta
    (UniformMain EnergyCoupling ImprovedResidual UpgradedS3 : Prop)
    (hmain : UniformMain) (henergy : EnergyCoupling) (himproved : ImprovedResidual)
    (hderive : UniformMain -> EnergyCoupling -> ImprovedResidual -> UpgradedS3) :
    UpgradedS3 := by
  exact hderive hmain henergy himproved

end Omega.SyncKernelRealInput
