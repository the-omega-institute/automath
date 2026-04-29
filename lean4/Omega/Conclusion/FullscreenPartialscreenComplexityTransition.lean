import Mathlib.Tactic

namespace Omega.Conclusion

/-- Kernel rank read from the identity `ker f_S ≅ ℤ^(c(Γ_S) - 1)`. -/
def conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank
    (componentCount : ℕ) : ℕ :=
  componentCount - 1

/-- Completion cost: zero kernel gives an `O(1)` recovery bound, while positive kernel rank gives
the exact completion cost. -/
def conclusion_fullscreen_partialscreen_complexity_transition_completion_cost
    (componentCount : ℕ) : ℕ :=
  if conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount = 0 then
    1
  else
    conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount

/-- Paper label: `thm:conclusion-fullscreen-partialscreen-complexity-transition`. The kernel-rank
identity `ker f_S ≅ ℤ^(c(Γ_S) - 1)` produces the expected two-phase behavior: connected full-screen
data have constant recovery complexity, while disconnected partial screens have exact completion
cost `c(Γ_S) - 1`. -/
theorem paper_conclusion_fullscreen_partialscreen_complexity_transition (componentCount : ℕ) :
    (componentCount ≤ 1 →
      conclusion_fullscreen_partialscreen_complexity_transition_completion_cost componentCount =
        1) ∧
    (2 ≤ componentCount →
      conclusion_fullscreen_partialscreen_complexity_transition_completion_cost componentCount =
          conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount ∧
        conclusion_fullscreen_partialscreen_complexity_transition_completion_cost componentCount =
          componentCount - 1) := by
  constructor
  · intro hsmall
    have hzero :
        conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount = 0 := by
      unfold conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank
      omega
    simp [conclusion_fullscreen_partialscreen_complexity_transition_completion_cost, hzero]
  · intro hlarge
    have hne :
        conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount ≠ 0 := by
      unfold conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank
      omega
    have hcost :
        conclusion_fullscreen_partialscreen_complexity_transition_completion_cost componentCount =
          conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank componentCount := by
      simp [conclusion_fullscreen_partialscreen_complexity_transition_completion_cost, hne]
    refine ⟨?_, ?_⟩
    · exact hcost
    · simpa [conclusion_fullscreen_partialscreen_complexity_transition_kernel_rank] using hcost

end Omega.Conclusion
