import Mathlib.Tactic

namespace Omega.SPG

/-- The Euler-characteristic cycle-rank expression for the first homology of a boundary
multigraph. -/
def boundaryMultigraphH1FreeRank (A X c : Int) : Int :=
  A - X + c

/-- The circle dimension of `H₁` is read off from the free rank. -/
def boundaryMultigraphH1Cdim (A X c : Int) : Int :=
  boundaryMultigraphH1FreeRank A X c

/-- Paper label: `prop:hypercube-boundary-multigraph-h1-cdim`. -/
theorem paper_hypercube_boundary_multigraph_h1_cdim (A X c : Int) :
    boundaryMultigraphH1Cdim A X c = A - X + c := by
  rfl

end Omega.SPG
