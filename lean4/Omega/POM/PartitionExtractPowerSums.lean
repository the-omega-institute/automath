import Omega.POM.FiniteSampleIndistinguishabilityPowerSums

namespace Omega.POM

/-- Paper-facing extraction of the `k`-th power sum from partition statistics.
    cor:pom-partition-extract-power-sums -/
theorem paper_pom_partition_extract_power_sums {α : Type*} [DecidableEq α] [Fintype α]
    (t k : ℕ) (μ : α → ℚ) :
    k ≤ t →
      ∃ T : Finset (Finset (Fin t)) → ℚ, symmetricPartitionStatistic t μ T = samplePowerSum μ k := by
  intro hk
  refine ⟨fun σ => if σ = ({initialBlock t k hk} : Finset (Finset (Fin t))) then 1 else 0, ?_⟩
  rw [symmetricStatistic_indicator_singleton t μ (initialBlock t k hk)]
  simp [blockFamilyMass_singleton_initialBlock]

end Omega.POM
