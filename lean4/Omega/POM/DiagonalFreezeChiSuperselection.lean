import Mathlib.Tactic

namespace Omega.POM

/-- The chi-superselection lower bound follows from the frozen max-fiber lower bound and
monotonicity of the escort measure. -/
theorem paper_pom_diagonal_freeze_chi_superselection {α : Type*} (ν : Set α → ℝ)
    (M C : Set α) (ε : ℝ) (hmono : ∀ {A B : Set α}, A ⊆ B → ν A ≤ ν B)
    (hMC : M ⊆ C) (hfreeze : 1 - ε ≤ ν M) : (1 - ε ≤ ν M) ∧ (1 - ε ≤ ν C) := by
  exact ⟨hfreeze, le_trans hfreeze (hmono hMC)⟩

end Omega.POM
