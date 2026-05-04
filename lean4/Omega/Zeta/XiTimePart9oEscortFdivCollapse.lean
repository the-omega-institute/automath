import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

theorem paper_xi_time_part9o_escort_fdiv_collapse (f : ℝ → ℝ) (p q : ℝ) :
    (∑ b : Fin 2,
      (if b = 0 then 1 - p else p) *
        f ((if b = 0 then 1 - q else q) / (if b = 0 then 1 - p else p))) =
      (1 - p) * f ((1 - q) / (1 - p)) + p * f (q / p) := by
  simp [Fin.sum_univ_two]

end Omega.Zeta
