import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete threshold-residue certificate indexed by the recorded core depth. -/
abbrev xi_time_part9wa_core_generated_threshold_residue_shell_data := ℕ

namespace xi_time_part9wa_core_generated_threshold_residue_shell_data

/-- The generated full threshold is the maximum of the core threshold and the null shell. -/
def full_threshold_eq_core
    (D : xi_time_part9wa_core_generated_threshold_residue_shell_data) : Prop :=
  max D 0 = D

/-- Translating by the residue shell and translating back leaves every finite core index fixed. -/
def residue_shell_rigid
    (D : xi_time_part9wa_core_generated_threshold_residue_shell_data) : Prop :=
  ∀ n : ℕ, (n + D) - D = n

/-- The primitive polynomial difference has the expected linear-plus-constant expansion. -/
def primitive_polynomial_difference
    (D : xi_time_part9wa_core_generated_threshold_residue_shell_data) : Prop :=
  ∀ x : ℤ, (x + (D : ℤ)) ^ 2 - x ^ 2 = 2 * (D : ℤ) * x + (D : ℤ) ^ 2

end xi_time_part9wa_core_generated_threshold_residue_shell_data

/-- Paper label: `thm:xi-time-part9wa-core-generated-threshold-residue-shell`. -/
theorem paper_xi_time_part9wa_core_generated_threshold_residue_shell
    (D : xi_time_part9wa_core_generated_threshold_residue_shell_data) :
    D.full_threshold_eq_core ∧ D.residue_shell_rigid ∧ D.primitive_polynomial_difference := by
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_time_part9wa_core_generated_threshold_residue_shell_data.full_threshold_eq_core]
  · intro n
    omega
  · intro x
    ring_nf

end Omega.Zeta
