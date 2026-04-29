import Omega.POM.ProjectionAsPartitionPrimeRegister

namespace Omega.POM

/-- Paper label: `cor:pom-partition-budget-duality`. -/
theorem paper_pom_partition_budget_duality (n : ℕ) (hn : 3 ≤ n) :
    (∀ S : Finset Nat,
        (∃ Φ : Omega.POM.Partition n → Omega.POM.PrimeRegisterElement,
            Function.Injective Φ ∧
              (∀ π, Φ π ⊆ S) ∧
              (∀ π σ, Φ (Omega.POM.partitionMeet π σ) = Φ π ∩ Φ σ)) →
          Nat.choose n 2 ≤ S.card) ∧
      (∀ π : Omega.POM.Partition n,
        Omega.POM.minimumSkeletonEdgeCount π = n - Omega.POM.blockCount π) := by
  refine ⟨paper_pom_meet_gcd_prime_budget n hn, ?_⟩
  exact paper_pom_partition_skeleton_compression n

end Omega.POM
