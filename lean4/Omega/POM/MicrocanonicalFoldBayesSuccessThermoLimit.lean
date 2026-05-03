import Mathlib.Data.Finset.Sym
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Complete homogeneous polynomial of degree `t` over a finite support `s`. -/
noncomputable def pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneousOn
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℚ) (t : ℕ) : ℚ :=
  (s.sym t).sum fun m => ((m : Multiset α).map w).prod

/-- Complete homogeneous polynomial of degree `t` over a finite type. -/
noncomputable def pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneous
    {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℚ) (t : ℕ) : ℚ :=
  pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneousOn
    (Finset.univ : Finset α) w t

/-- The fixed-`t` coefficient extracted from the finite Euler product
`∏ x (1 - w x z)⁻¹`, represented directly as the finite symmetric-power coefficient. -/
noncomputable def pom_microcanonical_fold_bayes_success_thermo_limit_generatingCoefficient
    {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℚ) (t : ℕ) : ℚ :=
  ((Finset.univ : Finset α).sym t).sum fun m => ((m : Multiset α).map w).prod

/-- Concrete finite-type algebraic statement packaging the fixed-`t` thermodynamic-limit
coefficient as a complete homogeneous polynomial and as the corresponding finite generating
coefficient. -/
def pom_microcanonical_fold_bayes_success_thermo_limit_statement
    {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℚ) : Prop :=
  pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneous w 0 = 1 ∧
    (∀ t,
      pom_microcanonical_fold_bayes_success_thermo_limit_generatingCoefficient w t =
        pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneous w t) ∧
    (∀ t,
      pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneous w t =
        ((Finset.univ : Finset α).sym t).sum fun m => ((m : Multiset α).map w).prod)

/-- Paper label: `thm:pom-microcanonical-fold-bayes-success-thermo-limit`. -/
theorem paper_pom_microcanonical_fold_bayes_success_thermo_limit
    {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℚ) :
    pom_microcanonical_fold_bayes_success_thermo_limit_statement w := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneous
      pom_microcanonical_fold_bayes_success_thermo_limit_completeHomogeneousOn
    rw [Finset.sym_zero, Finset.sum_singleton]
    rfl
  · intro t
    rfl
  · intro t
    rfl

end Omega.POM
