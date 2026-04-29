import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62d-activated-branch-second-order-silence`. -/
theorem paper_xi_time_part62d_activated_branch_second_order_silence (h lam : ℤ)
    (hlam : lam = h + 3 * h ^ 3 - h ^ 4 + 18 * h ^ 5 - 22 * h ^ 6) :
    ∃ R : ℤ, lam - h = h ^ 3 * R := by
  subst lam
  refine ⟨3 - h + 18 * h ^ 2 - 22 * h ^ 3, ?_⟩
  ring

end Omega.Zeta
