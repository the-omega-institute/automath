import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part9xc_serrin_ldp_vacuum (psi : Unit → ℝ) (n : ℕ) :
    Finset.sum (Finset.range n) (fun _ => psi ()) = (n : ℝ) * psi () := by
  simp

end Omega.Zeta
