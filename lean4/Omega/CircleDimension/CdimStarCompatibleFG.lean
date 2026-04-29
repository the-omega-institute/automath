import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension.CdimStarCompatibleFG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: finite torsion extensions preserve the circle dimension.
    prop:circle-dimension-phase-gate-profinite-fiber-localization-rational-winding -/
theorem paper_cdim_star_compatible_fg_seeds (r t : ℕ) :
    Omega.CircleDimension.circleDim r t = Omega.CircleDimension.circleDim r 0 :=
  Omega.CircleDimension.circleDim_finite_extension r t 0

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_cdim_star_compatible_fg_package (r t : ℕ) :
    Omega.CircleDimension.circleDim r t = Omega.CircleDimension.circleDim r 0 :=
  paper_cdim_star_compatible_fg_seeds r t

/-- Paper-facing theorem matching the exact statement from the manuscript. -/
theorem paper_cdim_star_compatible_fg (r t : ℕ) :
    Omega.CircleDimension.circleDim r t = Omega.CircleDimension.circleDim r 0 :=
  paper_cdim_star_compatible_fg_package r t

end Omega.CircleDimension.CdimStarCompatibleFG
