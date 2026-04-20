import Mathlib.Tactic

namespace Omega.CircleDimension.WdimBettiAverageLaw

/-- Paper seed: the weighted dimension is the average of the boundary/body first Betti ranks
    once the relative-rank exactness identity is inserted.
    cor:cdim-wdim-betti-average-law -/
theorem paper_cdim_wdim_betti_average_law_seeds
    (rankX rankSigma rankRel wdim : ℚ)
    (hexact : rankSigma = rankX + rankRel)
    (hwdim : wdim = rankX + rankRel / 2) :
    wdim = (rankX + rankSigma) / 2 := by
  rw [hwdim, hexact]
  ring

/-- Packaged form of the Betti-average law seeds.
    cor:cdim-wdim-betti-average-law -/
theorem paper_cdim_wdim_betti_average_law_package
    (rankX rankSigma rankRel wdim : ℚ)
    (hexact : rankSigma = rankX + rankRel)
    (hwdim : wdim = rankX + rankRel / 2) :
    wdim = (rankX + rankSigma) / 2 :=
  paper_cdim_wdim_betti_average_law_seeds rankX rankSigma rankRel wdim hexact hwdim

/-- Paper-facing Betti-average law.
    cor:cdim-wdim-betti-average-law -/
theorem paper_cdim_wdim_betti_average_law
    (rankX rankSigma rankRel wdim : ℚ)
    (hexact : rankSigma = rankX + rankRel)
    (hwdim : wdim = rankX + rankRel / 2) :
    wdim = (rankX + rankSigma) / 2 :=
  paper_cdim_wdim_betti_average_law_package rankX rankSigma rankRel wdim hexact hwdim

end Omega.CircleDimension.WdimBettiAverageLaw
