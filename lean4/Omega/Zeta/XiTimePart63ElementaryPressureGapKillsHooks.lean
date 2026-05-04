import Mathlib.Tactic
import Omega.POM.PartitionGapPositiveKillsHooks

namespace Omega.Zeta

/-- Concrete hook-channel data for the elementary pressure-gap annihilation statement. -/
structure xi_time_part63_elementary_pressure_gap_kills_hooks_data where
  Hook : Type*
  partitionGap : ℝ
  channelNonzero : Hook → Prop
  B : Hook → ℝ
  T : Hook → ℕ → ℝ
  gap_pos : 0 < partitionGap
  gap_closed_on_nonzero : ∀ lam : Hook, channelNonzero lam → partitionGap = 0
  channelNonzero_of_B_ne_zero : ∀ lam : Hook, B lam ≠ 0 → channelNonzero lam
  channelNonzero_of_T_ne_zero : ∀ (lam : Hook) (m : ℕ), T lam m ≠ 0 → channelNonzero lam

/-- Paper-facing package: every nontrivial hook has vanishing boundary and trace channels. -/
def xi_time_part63_elementary_pressure_gap_kills_hooks_statement
    (D : xi_time_part63_elementary_pressure_gap_kills_hooks_data) : Prop :=
  ∀ lam : D.Hook, D.B lam = 0 ∧ ∀ m : ℕ, D.T lam m = 0

/-- Paper label: `thm:xi-time-part63-elementary-pressure-gap-kills-hooks`. -/
theorem paper_xi_time_part63_elementary_pressure_gap_kills_hooks
    (D : xi_time_part63_elementary_pressure_gap_kills_hooks_data) :
    xi_time_part63_elementary_pressure_gap_kills_hooks_statement D := by
  have hno_channel :
      ∀ lam : D.Hook, ¬ D.channelNonzero lam :=
    Omega.POM.paper_pom_partition_gap_positive_kills_hooks D.partitionGap
      D.channelNonzero D.gap_pos D.gap_closed_on_nonzero
  intro lam
  constructor
  · by_contra hB
    exact hno_channel lam (D.channelNonzero_of_B_ne_zero lam hB)
  · intro m
    by_contra hT
    exact hno_channel lam (D.channelNonzero_of_T_ne_zero lam m hT)

end Omega.Zeta
