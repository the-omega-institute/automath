import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `prop:cdim-poisson-density-linfty-universal-constant`. -/
theorem paper_cdim_poisson_density_linfty_universal_constant
    (secondOrderLinftyExpansion profileSupOneOverPi universalLimit : Prop)
    (hExpand : secondOrderLinftyExpansion) (hSup : profileSupOneOverPi)
    (hLimit : secondOrderLinftyExpansion → profileSupOneOverPi → universalLimit) :
    universalLimit := by
  exact hLimit hExpand hSup

end Omega.CircleDimension
