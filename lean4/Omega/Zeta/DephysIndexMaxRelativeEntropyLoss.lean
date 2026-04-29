import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:dephys-index-max-relative-entropy-loss`. The dephysicalized relative-entropy
losses form a bounded-above set whose supremum is exactly `log indE`, because every loss is at
most `log indE` and the approximation hypothesis produces losses arbitrarily close to that bound. -/
theorem paper_dephys_index_max_relative_entropy_loss {State : Type*}
    (D : State → State → ℝ) (E : State → State) (indE : ℝ) (hind : 1 < indE)
    (hloss_nonneg : ∀ rho sigma, 0 ≤ D rho sigma - D (E rho) (E sigma))
    (hloss_le : ∀ rho sigma, D rho sigma - D (E rho) (E sigma) ≤ Real.log indE)
    (hloss_approx : ∀ eps > 0, ∃ rho sigma,
      Real.log indE - eps < D rho sigma - D (E rho) (E sigma)) :
    sSup {x : ℝ | ∃ rho sigma, x = D rho sigma - D (E rho) (E sigma)} = Real.log indE := by
  let dephys_index_max_relative_entropy_loss_S : Set ℝ :=
    {x : ℝ | ∃ rho sigma, x = D rho sigma - D (E rho) (E sigma)}
  have hnonempty : dephys_index_max_relative_entropy_loss_S.Nonempty := by
    rcases hloss_approx 1 zero_lt_one with ⟨rho, sigma, hlt⟩
    exact ⟨_, ⟨rho, sigma, rfl⟩⟩
  have hbdd : BddAbove dephys_index_max_relative_entropy_loss_S := by
    refine ⟨Real.log indE, ?_⟩
    rintro x ⟨rho, sigma, rfl⟩
    exact hloss_le rho sigma
  have hsSup_le : sSup dephys_index_max_relative_entropy_loss_S ≤ Real.log indE := by
    refine csSup_le hnonempty ?_
    rintro x ⟨rho, sigma, rfl⟩
    exact hloss_le rho sigma
  have hlog_le : Real.log indE ≤ sSup dephys_index_max_relative_entropy_loss_S := by
    by_contra hlt
    have hslt : sSup dephys_index_max_relative_entropy_loss_S < Real.log indE := lt_of_not_ge hlt
    have heps : 0 < (Real.log indE - sSup dephys_index_max_relative_entropy_loss_S) / 2 := by
      linarith
    rcases hloss_approx ((Real.log indE - sSup dephys_index_max_relative_entropy_loss_S) / 2)
      heps with ⟨rho, sigma, happrox⟩
    have hmem :
        D rho sigma - D (E rho) (E sigma) ∈ dephys_index_max_relative_entropy_loss_S :=
      ⟨rho, sigma, rfl⟩
    have hxle :
        D rho sigma - D (E rho) (E sigma) ≤ sSup dephys_index_max_relative_entropy_loss_S :=
      le_csSup hbdd hmem
    linarith
  have hEq : sSup dephys_index_max_relative_entropy_loss_S = Real.log indE :=
    le_antisymm hsSup_le hlog_le
  simpa [dephys_index_max_relative_entropy_loss_S] using hEq

end Omega.Zeta
