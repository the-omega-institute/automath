import Omega.GU.JoukowskyGodelLeadingCoeffRigidity

namespace Omega.GU

/-- `cor:group-jg-monic-boundary-readout` -/
theorem paper_group_jg_monic_boundary_readout {K : Type*} [Field K] (a_n a_0 lc : K)
    (hmonic : a_n = 1) (hlc : lc = a_n * a_0) : lc = a_0 := by
  simpa [hmonic] using hlc

end Omega.GU
