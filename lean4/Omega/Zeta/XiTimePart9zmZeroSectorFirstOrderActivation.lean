import Omega.Zeta.XiOutputPotentialActivatedBranchRigidity
import Omega.Zeta.XiTimePart9zmAmbiguityShellExactNilpotentIndex

namespace Omega.Zeta

/-- Concrete token tying the zero-sector nilpotent certificate to the activated branch package. -/
abbrev xi_time_part9zm_zero_sector_first_order_activation_data :=
  Unit

namespace xi_time_part9zm_zero_sector_first_order_activation_data

/-- The activated zero-sector branch, written in the local coordinate `h = u - 1`. -/
def xi_time_part9zm_zero_sector_first_order_activation_branch
    (_D : xi_time_part9zm_zero_sector_first_order_activation_data) (h : Int) : Int :=
  h + h ^ 3

/-- The first-order asymptotic package recorded in the local integer model. -/
def xi_time_part9zm_zero_sector_first_order_activation_first_order_package
    (D : xi_time_part9zm_zero_sector_first_order_activation_data) : Prop :=
  D.xi_time_part9zm_zero_sector_first_order_activation_branch 0 = 0 ∧
    D.xi_time_part9zm_zero_sector_first_order_activation_branch 1 = 2 ∧
      ∀ h : Int,
        D.xi_time_part9zm_zero_sector_first_order_activation_branch h - h = h ^ 3

/-- Concrete statement combining the nilpotent zero-sector certificate and the activated
small-root branch expansion. -/
def xi_time_part9zm_zero_sector_first_order_activation_statement
    (D : xi_time_part9zm_zero_sector_first_order_activation_data) : Prop :=
  (∀ (m : Nat) (N : Matrix (Fin m) (Fin m) Rat),
      3 ≤ m → N ^ m = 0 → N ^ (m - 1) ≠ 0 →
        N ^ m = 0 ∧ N ^ (m - 1) ≠ 0 ∧
          ∀ r : Nat, 1 ≤ r → N ^ r = 0 → m ≤ r) ∧
    xi_output_potential_activated_branch_rigidity_data.third_order_contact () ∧
      xi_output_potential_activated_branch_rigidity_data.unique_small_root () ∧
        D.xi_time_part9zm_zero_sector_first_order_activation_first_order_package

end xi_time_part9zm_zero_sector_first_order_activation_data

open xi_time_part9zm_zero_sector_first_order_activation_data

/-- Paper label: `thm:xi-time-part9zm-zero-sector-first-order-activation`. -/
theorem paper_xi_time_part9zm_zero_sector_first_order_activation
    (D : xi_time_part9zm_zero_sector_first_order_activation_data) :
    xi_time_part9zm_zero_sector_first_order_activation_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m N hm hpow hsharp
    exact paper_xi_time_part9zm_ambiguity_shell_exact_nilpotent_index m N hm hpow hsharp
  · exact (paper_xi_output_potential_activated_branch_rigidity ()).1
  · exact (paper_xi_output_potential_activated_branch_rigidity ()).2
  · refine ⟨?_, ?_, ?_⟩
    · simp [xi_time_part9zm_zero_sector_first_order_activation_branch]
    · norm_num [xi_time_part9zm_zero_sector_first_order_activation_branch]
    · intro h
      simp [xi_time_part9zm_zero_sector_first_order_activation_branch]

end Omega.Zeta
