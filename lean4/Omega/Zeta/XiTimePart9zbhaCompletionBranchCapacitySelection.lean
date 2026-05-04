import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The inverse golden-ratio branch weight used by the two-atom completion certificate. -/
noncomputable def xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- The normalization constant on the golden branch. -/
noncomputable def xi_time_part9zbha_completion_branch_capacity_selection_goldenKappa : ℝ :=
  (xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight + 1) ^ 3

/-- The normalization constant on the symmetric branch. -/
def xi_time_part9zbha_completion_branch_capacity_selection_halfKappa : ℝ :=
  4

/-- A concrete slope-ratio selector for the capacity curve: value `1` is reserved for the
golden branch and value `0` for every other branch. -/
noncomputable def xi_time_part9zbha_completion_branch_capacity_selection_slopeCode
    (p : ℝ) : ℕ :=
  if p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight then 1 else 0

/-- Concrete certificate data for the two-atom Mellin completion identity.

The coefficient comparison has already reduced the identity to the two possible weights,
and the two implications record the corresponding scalar normalizations.  The capacity
condition is encoded by the branch slope code, from which the golden branch is selected. -/
structure xi_time_part9zbha_completion_branch_capacity_selection_data where
  p : ℝ
  kappa : ℝ
  coefficient_branch :
    p = (1 : ℝ) / 2 ∨
      p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight
  kappa_on_half :
    p = (1 : ℝ) / 2 →
      kappa = xi_time_part9zbha_completion_branch_capacity_selection_halfKappa
  kappa_on_golden :
    p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight →
      kappa = xi_time_part9zbha_completion_branch_capacity_selection_goldenKappa
  slope_ratio_code :
    xi_time_part9zbha_completion_branch_capacity_selection_slopeCode p = 1

namespace xi_time_part9zbha_completion_branch_capacity_selection_data

/-- The completion identity leaves exactly the symmetric and golden coefficient branches. -/
def completion_branch_dichotomy
    (D : xi_time_part9zbha_completion_branch_capacity_selection_data) : Prop :=
  (D.p = (1 : ℝ) / 2 ∧
      D.kappa = xi_time_part9zbha_completion_branch_capacity_selection_halfKappa) ∨
    (D.p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight ∧
      D.kappa = xi_time_part9zbha_completion_branch_capacity_selection_goldenKappa)

/-- The encoded capacity slope ratio selects the golden branch. -/
def capacity_selects_golden_branch
    (D : xi_time_part9zbha_completion_branch_capacity_selection_data) : Prop :=
  D.p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight ∧
    D.kappa = xi_time_part9zbha_completion_branch_capacity_selection_goldenKappa

end xi_time_part9zbha_completion_branch_capacity_selection_data

open xi_time_part9zbha_completion_branch_capacity_selection_data

/-- Paper label: `thm:xi-time-part9zbha-completion-branch-capacity-selection`. -/
theorem paper_xi_time_part9zbha_completion_branch_capacity_selection
    (D : xi_time_part9zbha_completion_branch_capacity_selection_data) :
    D.completion_branch_dichotomy ∧ D.capacity_selects_golden_branch := by
  classical
  have hGolden : D.p = xi_time_part9zbha_completion_branch_capacity_selection_goldenWeight := by
    by_contra h
    have hCode :
        xi_time_part9zbha_completion_branch_capacity_selection_slopeCode D.p = 0 := by
      simp [xi_time_part9zbha_completion_branch_capacity_selection_slopeCode, h]
    rw [D.slope_ratio_code] at hCode
    norm_num at hCode
  have hKappaGolden :
      D.kappa = xi_time_part9zbha_completion_branch_capacity_selection_goldenKappa :=
    D.kappa_on_golden hGolden
  constructor
  · rcases D.coefficient_branch with hHalf | hBranchGolden
    · exact Or.inl ⟨hHalf, D.kappa_on_half hHalf⟩
    · exact Or.inr ⟨hBranchGolden, D.kappa_on_golden hBranchGolden⟩
  · exact ⟨hGolden, hKappaGolden⟩

end Omega.Zeta
