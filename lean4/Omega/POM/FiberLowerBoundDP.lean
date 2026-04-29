import Omega.Folding.Fiber
import Omega.POM.IndependenceDpRadius2

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-lower-bound-dp`. The radius-`2` DP computes the same quantity as
the independent-set count, so any independent-set fiber lower bound also bounds the DP output. -/
theorem paper_pom_fiber_lower_bound_dp (m : Nat) (x : Omega.X m) (idx : List Nat)
    (hstrict : idx.Pairwise (fun a b => a < b))
    (hbound : Omega.POM.indepCountRadius2 idx <= Omega.X.fiberMultiplicity x) :
    Omega.POM.dpCountRadius2 idx <= Omega.X.fiberMultiplicity x := by
  rw [← Omega.POM.paper_pom_independence_dp_radius2 idx hstrict]
  exact hbound

end Omega.POM
