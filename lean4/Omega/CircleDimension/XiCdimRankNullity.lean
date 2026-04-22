import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Xi-facing wrapper of the circle-dimension rank-nullity formula. -/
theorem paper_xi_cdim_rank_nullity (f : Omega.CircleDimension.CircleDimHomData) :
    Omega.CircleDimension.circleDim f.sourceRank 0 =
      Omega.CircleDimension.circleDim f.kernelRank 0 +
        Omega.CircleDimension.circleDim f.imageRank 0 := by
  simpa using cdim_rank_nullity f

end Omega.CircleDimension
