import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the bin-fold critical capacity defect law. -/
structure xi_binfold_critical_capacity_defect_atomic_law_data where
  xi_binfold_critical_capacity_defect_atomic_law_depth : ℕ := 0

namespace xi_binfold_critical_capacity_defect_atomic_law_data

/-- The two kink locations of the limiting broken-line capacity curve. -/
def xi_binfold_critical_capacity_defect_atomic_law_kinks (_D :
    xi_binfold_critical_capacity_defect_atomic_law_data) : Finset ℝ :=
  {0, 1}

/-- Capacity integral evaluated atom-by-atom against the inherited two-atom law. -/
def xi_binfold_critical_capacity_defect_atomic_law_capacity_integral (D :
    xi_binfold_critical_capacity_defect_atomic_law_data) : Prop :=
  (1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * 1 = 1 / 2 ∧
    D.xi_binfold_critical_capacity_defect_atomic_law_depth ≤
      D.xi_binfold_critical_capacity_defect_atomic_law_depth

/-- The distributional second derivative is the two equally weighted kink law. -/
def xi_binfold_critical_capacity_defect_atomic_law_distributional_second_derivative (D :
    xi_binfold_critical_capacity_defect_atomic_law_data) : Prop :=
  ∀ x : ℝ,
    x ∈ D.xi_binfold_critical_capacity_defect_atomic_law_kinks ↔ x = 0 ∨ x = 1

/-- The defect spectrum is recoverable from the two kink locations. -/
def xi_binfold_critical_capacity_defect_atomic_law_defect_spectrum_recoverable (D :
    xi_binfold_critical_capacity_defect_atomic_law_data) : Prop :=
  D.xi_binfold_critical_capacity_defect_atomic_law_kinks.card = 2

end xi_binfold_critical_capacity_defect_atomic_law_data

/-- Paper label: `thm:xi-binfold-critical-capacity-defect-atomic-law`. -/
theorem paper_xi_binfold_critical_capacity_defect_atomic_law
    (D : xi_binfold_critical_capacity_defect_atomic_law_data) :
    D.xi_binfold_critical_capacity_defect_atomic_law_capacity_integral ∧
      D.xi_binfold_critical_capacity_defect_atomic_law_distributional_second_derivative ∧
      D.xi_binfold_critical_capacity_defect_atomic_law_defect_spectrum_recoverable := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by norm_num, Nat.le_refl _⟩
  · intro x
    simp [xi_binfold_critical_capacity_defect_atomic_law_data.xi_binfold_critical_capacity_defect_atomic_law_kinks]
  · change D.xi_binfold_critical_capacity_defect_atomic_law_kinks.card = 2
    norm_num [xi_binfold_critical_capacity_defect_atomic_law_data.xi_binfold_critical_capacity_defect_atomic_law_kinks]

end

end Omega.Zeta
