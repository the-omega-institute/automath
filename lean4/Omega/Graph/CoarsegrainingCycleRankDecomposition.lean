import Mathlib.Tactic

namespace Omega.Graph

/-- Paper label: `thm:graph-coarsegraining-cycle-rank-decomposition`. -/
theorem paper_graph_coarsegraining_cycle_rank_decomposition (k : Nat) (V E cG eIn : Int)
    (fiberRank : Fin k -> Int)
    (hEin : eIn = (V - (k : Int)) + Finset.univ.sum fiberRank) :
    (E - eIn) - (k : Int) + cG = (E - V + cG) - Finset.univ.sum fiberRank := by
  rw [hEin]
  ring

end Omega.Graph
