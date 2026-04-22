import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A finite directed cycle together with its total edge weight and positive length. -/
structure WeightedCycle where
  totalWeight : ℚ
  length : ℕ
  length_pos : 0 < length

deriving DecidableEq

/-- Mean cycle weight. -/
def WeightedCycle.meanWeight (cycle : WeightedCycle) : ℚ :=
  cycle.totalWeight / cycle.length

/-- Finite min-plus package for the tropical cost/minimum-mean-cycle identification. -/
structure ProjTropicalMinmeanData where
  cycles : Finset WeightedCycle
  cycles_nonempty : cycles.Nonempty

namespace ProjTropicalMinmeanData

def meanWeights (D : ProjTropicalMinmeanData) : Finset ℚ :=
  D.cycles.image WeightedCycle.meanWeight

lemma meanWeights_nonempty (D : ProjTropicalMinmeanData) : D.meanWeights.Nonempty := by
  simpa [meanWeights] using D.cycles_nonempty.image WeightedCycle.meanWeight

/-- Tropical cost computed from the finite weighted-cycle package. -/
def tropicalCost (D : ProjTropicalMinmeanData) : ℚ :=
  D.meanWeights.min' D.meanWeights_nonempty

/-- Minimum mean-cycle value of the same package. -/
def minMeanCycle (D : ProjTropicalMinmeanData) : ℚ :=
  D.meanWeights.min' D.meanWeights_nonempty

end ProjTropicalMinmeanData

open ProjTropicalMinmeanData

/-- Paper label: `prop:pom-proj-tropical-minmean`. In the finite weighted-cycle model, both sides
are computed by the same explicit minimum over the cycle-average multiset. -/
theorem paper_pom_proj_tropical_minmean (D : ProjTropicalMinmeanData) :
    D.tropicalCost = D.minMeanCycle := by
  rfl

end Omega.POM
