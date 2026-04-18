import Mathlib

namespace Omega.Folding

theorem paper_fold_gauge_anomaly_P10_leyang_linear_disjointness {alpha : Type}
    [DecidableEq alpha] (base q10 ly inter : alpha)
    (hL : inter ∈ ({base, q10} : Finset alpha))
    (hLY : inter ∈ ({base, ly} : Finset alpha))
    (hneq : q10 ≠ ly) : inter = base := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL hLY
  rcases hL with rfl | rfl
  · rfl
  · rcases hLY with hbase | hly
    · exact hbase
    · exact (hneq hly).elim

end Omega.Folding
