import Omega.OperatorAlgebra.FoldDmaxCapacityEqualsLogIndex

namespace Omega.Zeta

/-- Paper label: `cor:xi-renyi-flatness-under-momq-amplification`.
The finite-fold `Dmax`/log-index identity is preserved under `MOM_q` linear amplification. -/
theorem paper_xi_renyi_flatness_under_momq_amplification {Ω X : Type*} [Fintype Ω]
    [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X] (fold : Ω → X)
    (hfold : Function.Surjective fold) (q : ℕ) :
    (q : ℝ) * Omega.OperatorAlgebra.foldDmaxCapacity fold =
      (q : ℝ) * Real.log (Omega.OperatorAlgebra.foldLargestFiberCard fold) := by
  rw [(Omega.OperatorAlgebra.paper_op_algebra_dmax_capacity_equals_log_index fold hfold).2]

end Omega.Zeta
