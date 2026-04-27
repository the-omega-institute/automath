import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.SchurVarianceGrowthRateSpectralIdentity

namespace Omega.POM

noncomputable section

open SchurPartitionIndex
open scoped BigOperators

/-- Concrete paper-facing data for the `S₂` Schur variance optimization seed. -/
abbrev pom_schur_variance_exponent_partition_optimization_Data := PUnit

namespace pom_schur_variance_exponent_partition_optimization_Data

/-- The finite visible partition set in the seed model. -/
def visible_partition_set : Finset SchurPartitionIndex := Finset.univ

/-- Nontrivial Schur channels, with the trivial/cycle channel removed. -/
def nontrivial_schur_channels : Finset SchurPartitionIndex :=
  visible_partition_set.filter fun lam => lam ≠ cycle

/-- The visible exponent attached to each Schur channel in the concrete radius-two model. -/
def partition_exponent : SchurPartitionIndex → ℝ
  | cycle => 0
  | split => Real.log 2

/-- The finite maximum over nontrivial Schur channels is attained at the split channel. -/
def finite_max_flattening : Prop :=
  split ∈ nontrivial_schur_channels ∧
    ∀ lam ∈ nontrivial_schur_channels, partition_exponent lam ≤ partition_exponent split

/-- Paper-facing optimization law for the finite `S₂` Schur seed. -/
def optimization_law (_D : pom_schur_variance_exponent_partition_optimization_Data) : Prop :=
  visible_partition_set = Finset.univ ∧
    nontrivial_schur_channels = {split} ∧
    finite_max_flattening ∧
    (∀ m : ℕ,
      Real.log (pomSchurSeedVariance 2 (m + 1)) =
        (2 * (m + 1) : ℝ) * partition_exponent split) ∧
    pomSchurSeedSpectralEnvelope 2 =
      Real.exp ((Real.log (pomSchurSeedVariance 2 1)) / 2)

end pom_schur_variance_exponent_partition_optimization_Data

open pom_schur_variance_exponent_partition_optimization_Data

/-- Paper label: `cor:pom-schur-variance-exponent-partition-optimization`.

For the finite `S₂` Schur seed, the only nontrivial channel is `split`, so the finite channel
maximum flattens to that visible exponent. The radius-two spectral identity then supplies the
variance growth exponent and the Schur spectral envelope. -/
theorem paper_pom_schur_variance_exponent_partition_optimization
    (D : pom_schur_variance_exponent_partition_optimization_Data) : D.optimization_law := by
  classical
  have hspec :=
    paper_pom_schur_variance_growth_rate_spectral_identity (show (0 : ℝ) < 2 by norm_num)
  refine ⟨rfl, ?_, ?_, ?_, hspec.2.2⟩
  · ext lam
    cases lam <;> simp [nontrivial_schur_channels, visible_partition_set]
  · refine ⟨?_, ?_⟩
    · simp [nontrivial_schur_channels, visible_partition_set]
    · intro lam hlam
      cases lam <;> simp [nontrivial_schur_channels, visible_partition_set,
        partition_exponent] at hlam ⊢
  · intro m
    simpa [partition_exponent] using hspec.2.1 m

end

end Omega.POM
