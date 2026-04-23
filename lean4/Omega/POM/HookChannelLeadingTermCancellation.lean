import Mathlib.Tactic
import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.POM

noncomputable section

open SchurPartitionIndex

/-- Concrete data for the hook-channel leading-term cancellation package. The Perron-pure
resonance class is modeled by a single top coefficient that appears with opposite signs in the two
partition channels. -/
structure pom_hook_channel_leading_term_cancellation_data where
  q : ℕ
  rho : ℝ
  leadingCoeff : ℝ
  leadingCoeff_nonneg : 0 ≤ leadingCoeff

/-- The resonance exponent `P(q)` attached to the hook channel. -/
def pom_hook_channel_leading_term_cancellation_P
    (D : pom_hook_channel_leading_term_cancellation_data) : ℕ :=
  D.q + 1

/-- Partition-by-partition contribution of the resonance class to the Schur trace. -/
def pom_hook_channel_leading_term_cancellation_partition_term
    (D : pom_hook_channel_leading_term_cancellation_data) :
    SchurPartitionIndex → ℝ
  | cycle => D.leadingCoeff * D.rho ^ pom_hook_channel_leading_term_cancellation_P D
  | split => -D.leadingCoeff * D.rho ^ pom_hook_channel_leading_term_cancellation_P D

/-- The top exponential coefficient before multiplying by the common Perron factor. -/
def pom_hook_channel_leading_term_cancellation_top_coefficient
    (D : pom_hook_channel_leading_term_cancellation_data) : ℝ :=
  ∑ ν, match ν with
    | cycle => D.leadingCoeff
    | split => -D.leadingCoeff

/-- The Schur trace of the resonance class after compression by partition type. -/
def pom_hook_channel_leading_term_cancellation_schur_trace
    (D : pom_hook_channel_leading_term_cancellation_data) : ℝ :=
  ∑ ν, pom_hook_channel_leading_term_cancellation_partition_term D ν

/-- Statement of the hook-channel cancellation package: Perron purity keeps the leading
coefficient nonnegative, the top coefficient cancels exactly across the two partition types, and
the compressed Schur trace therefore vanishes at the full exponential order `ρ^{P(q)}`. -/
def pom_hook_channel_leading_term_cancellation_statement
    (D : pom_hook_channel_leading_term_cancellation_data) : Prop :=
  0 ≤ D.leadingCoeff ∧
    pom_hook_channel_leading_term_cancellation_top_coefficient D = 0 ∧
    pom_hook_channel_leading_term_cancellation_schur_trace D =
      pom_hook_channel_leading_term_cancellation_top_coefficient D *
        D.rho ^ pom_hook_channel_leading_term_cancellation_P D ∧
    pom_hook_channel_leading_term_cancellation_schur_trace D = 0

/-- Paper label: `thm:pom-hook-channel-leading-term-cancellation`. Expanding the Schur trace by
partition type isolates the unique resonance exponent `P(q)`; because the Perron-pure top
coefficient appears with opposite signs in the two hook channels, the coefficient of the leading
exponential term cancels exactly. -/
theorem paper_pom_hook_channel_leading_term_cancellation
    (D : pom_hook_channel_leading_term_cancellation_data) :
    pom_hook_channel_leading_term_cancellation_statement D := by
  have hCoeff :
      pom_hook_channel_leading_term_cancellation_top_coefficient D = 0 := by
    rw [pom_hook_channel_leading_term_cancellation_top_coefficient, sum_over_schur_partition_index]
    ring
  have hTrace_factor :
      pom_hook_channel_leading_term_cancellation_schur_trace D =
        pom_hook_channel_leading_term_cancellation_top_coefficient D *
          D.rho ^ pom_hook_channel_leading_term_cancellation_P D := by
    rw [pom_hook_channel_leading_term_cancellation_schur_trace,
      pom_hook_channel_leading_term_cancellation_top_coefficient,
      sum_over_schur_partition_index, sum_over_schur_partition_index]
    simp [pom_hook_channel_leading_term_cancellation_partition_term]
  have hTrace_zero : pom_hook_channel_leading_term_cancellation_schur_trace D = 0 := by
    rw [hTrace_factor, hCoeff]
    ring
  exact ⟨D.leadingCoeff_nonneg, hCoeff, hTrace_factor, hTrace_zero⟩

end

end Omega.POM
