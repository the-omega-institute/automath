import Omega.POM.PartitionPressureKnapsack
import Omega.POM.SchurTraceFiniteLaplacePrinciple

namespace Omega.POM

open PartitionPressureKnapsackData
open pom_schur_trace_finite_laplace_principle_data

/-- Concrete data for the identity-sector collapse: the part `1` has strictly dominant
normalized pressure, and each audited Schur channel carries finite-Laplace data with nonzero
identity-sector coefficient. -/
structure pom_identity_sector_collapse_all_schur_channels_data where
  q : ℕ
  q_pos : 1 ≤ q
  P : ℕ → ℚ
  P_zero : P 0 = 0
  strict_identity :
    ∀ r : ℕ, 2 ≤ r → r ≤ q → P r / (r : ℚ) < P 1
  channelCount : ℕ
  channelLaplaceData : Fin channelCount → pom_schur_trace_finite_laplace_principle_data
  channelLeading_nonzero :
    ∀ lam : Fin channelCount,
      (channelLaplaceData lam).pom_schur_trace_finite_laplace_principle_topCoefficient ≠ 0

namespace pom_identity_sector_collapse_all_schur_channels_data

/-- The partition-pressure knapsack specialized to the identity part. -/
def knapsack (D : pom_identity_sector_collapse_all_schur_channels_data) :
    PartitionPressureKnapsackData where
  q := D.q
  hq := D.q_pos
  P := D.P
  P_zero := D.P_zero
  bestPart := 1
  bestPart_pos := by norm_num
  bestPart_le := D.q_pos
  bestPart_optimal := by
    intro r hr_pos hr_le
    by_cases h1 : r = 1
    · simp [h1]
    · have htwo : 2 ≤ r := by omega
      have hlt : D.P r / (r : ℚ) < D.P 1 := D.strict_identity r htwo hr_le
      simpa using hlt.le

/-- Multiplicity vector for the unique identity partition `(1^q)`. -/
def identityCounts (D : pom_identity_sector_collapse_all_schur_channels_data) :
    Fin (D.q + 1) → ℕ :=
  fun r => if (r : ℕ) = 1 then D.q else 0

/-- The identity partition is the unique maximizer for the specialized knapsack. -/
def identityUniqueMaximizer (D : pom_identity_sector_collapse_all_schur_channels_data) : Prop :=
  (D.knapsack.respectsBudget D.identityCounts) ∧
    D.knapsack.partitionPressure D.identityCounts = (D.q : ℚ) * D.knapsack.optimalSlope ∧
      ∀ c : Fin (D.q + 1) → ℕ, D.knapsack.respectsBudget c →
        D.knapsack.partitionPressure c = (D.q : ℚ) * D.knapsack.optimalSlope →
          c = D.identityCounts

/-- Every Schur channel satisfies the finite-Laplace dichotomy. -/
def allChannelsFiniteLaplace (D : pom_identity_sector_collapse_all_schur_channels_data) : Prop :=
  ∀ lam : Fin D.channelCount, (D.channelLaplaceData lam).finite_laplace_principle

/-- Every Schur channel has a nonzero identity-sector leading coefficient. -/
def allChannelsNonzeroLeading (D : pom_identity_sector_collapse_all_schur_channels_data) : Prop :=
  ∀ lam : Fin D.channelCount,
    (D.channelLaplaceData lam).pom_schur_trace_finite_laplace_principle_topCoefficient ≠ 0

/-- The concrete all-channel collapse package: unique identity partition, nonzero leading
coefficient in each channel, and the finite-Laplace conclusion in each channel. -/
def collapse (D : pom_identity_sector_collapse_all_schur_channels_data) : Prop :=
  D.identityUniqueMaximizer ∧ D.allChannelsNonzeroLeading ∧ D.allChannelsFiniteLaplace

lemma identityCounts_eq_singleBestPartCounts
    (D : pom_identity_sector_collapse_all_schur_channels_data) :
    D.identityCounts = D.knapsack.singleBestPartCounts := by
  funext r
  by_cases hr : (r : ℕ) = 1
  · simp [identityCounts, PartitionPressureKnapsackData.singleBestPartCounts, knapsack, hr]
  · simp [identityCounts, PartitionPressureKnapsackData.singleBestPartCounts, knapsack, hr]

lemma identity_part_unique_optimal
    (D : pom_identity_sector_collapse_all_schur_channels_data) :
    ∀ r : Fin (D.q + 1), 1 ≤ (r : ℕ) → D.knapsack.partIsOptimal r → (r : ℕ) = 1 := by
  intro r hr_pos hopt
  by_contra hne
  have htwo : 2 ≤ (r : ℕ) := by omega
  have hr_le : (r : ℕ) ≤ D.q := Nat.le_of_lt_succ r.2
  have hlt : D.P r / (r : ℚ) < D.P 1 := D.strict_identity r htwo hr_le
  have heq : D.P r / (r : ℚ) = D.P 1 := by
    simpa [PartitionPressureKnapsackData.partIsOptimal, PartitionPressureKnapsackData.optimalSlope,
      knapsack] using hopt.2
  exact (ne_of_lt hlt) heq

end pom_identity_sector_collapse_all_schur_channels_data

open pom_identity_sector_collapse_all_schur_channels_data

/-- Paper label: `cor:pom-identity-sector-collapse-all-schur-channels`. -/
theorem paper_pom_identity_sector_collapse_all_schur_channels
    (D : pom_identity_sector_collapse_all_schur_channels_data) : D.collapse := by
  have hknapsack := paper_pom_partition_pressure_knapsack D.knapsack
  rcases hknapsack with ⟨_, _, hunique⟩
  have hsingle :
      (∀ r : Fin (D.q + 1), 1 ≤ (r : ℕ) → D.knapsack.partIsOptimal r → (r : ℕ) = 1) ∧
        (1 : ℕ) ∣ D.q := by
    refine ⟨D.identity_part_unique_optimal, ⟨D.q, by simp⟩⟩
  rcases hunique hsingle with ⟨hbudget, hpressure, huniq⟩
  have hidentity : D.identityUniqueMaximizer := by
    dsimp [pom_identity_sector_collapse_all_schur_channels_data.identityUniqueMaximizer]
    rw [D.identityCounts_eq_singleBestPartCounts]
    simpa [pom_identity_sector_collapse_all_schur_channels_data.knapsack] using
      ⟨hbudget, hpressure, huniq⟩
  refine ⟨hidentity, D.channelLeading_nonzero, ?_⟩
  intro lam
  exact paper_pom_schur_trace_finite_laplace_principle (D.channelLaplaceData lam)

end Omega.POM
