import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Subtracting the uniform baseline `1` from each fiber count removes exactly `p` points, so the
mean-centered total equals the trace correction `-a_p`. -/
theorem paper_xi_terminal_zm_elliptic_fiber_count_mean_trace (p : Nat) (a_p : Int)
    (N_p : Fin p → Nat) (hcount : (∑ y : Fin p, (N_p y : Int)) = (p : Int) - a_p) :
    (∑ y : Fin p, ((N_p y : Int) - 1)) = -a_p := by
  calc
    (∑ y : Fin p, ((N_p y : Int) - 1))
        = (∑ y : Fin p, (N_p y : Int)) - ∑ _ : Fin p, (1 : Int) := by
            rw [Finset.sum_sub_distrib]
    _ = ((p : Int) - a_p) - ∑ _ : Fin p, (1 : Int) := by rw [hcount]
    _ = ((p : Int) - a_p) - p := by simp
    _ = -a_p := by ring

end Omega.Zeta
