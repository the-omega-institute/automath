import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.POM

open SchurPartitionIndex
open scoped BigOperators

/-- Paper label: `thm:pom-schur-variance-decomposition`.

For the concrete `S₂` Schur--Plancherel seed, the trivial channel is exactly the class-function
average, centering kills that channel, and the remaining variance is carried by the unique
nontrivial channel. -/
theorem paper_pom_schur_variance_decomposition (m : ℝ) :
    let average := schurNormalizedChannelTrace m cycle
    let centered : SchurPartitionIndex → ℝ := fun ν => schurCycleMonomial m ν - average
    let centeredVariance := ∑ ν, (1 / schurWeight ν) * (centered ν) ^ (2 : ℕ)
    let centeredChannel : SchurPartitionIndex → ℝ :=
      fun lam => ∑ ν, (schurCharacter lam ν / schurWeight ν) * centered ν
    average = (schurCycleMonomial m cycle + schurCycleMonomial m split) / 2 ∧
      centeredChannel cycle = 0 ∧
      centeredVariance =
        ∑ lam, if lam = cycle then 0 else (centeredChannel lam / schurDegree lam) ^ (2 : ℕ) := by
  dsimp
  constructor
  · rw [schurNormalizedChannelTrace_cycle]
    simp [schurCycleMonomial]
  · constructor
    · rw [schurNormalizedChannelTrace_cycle, sum_over_schur_partition_index]
      simp [schurCharacter, schurWeight, schurCycleMonomial]
    · rw [schurNormalizedChannelTrace_cycle, sum_over_schur_partition_index]
      repeat rw [sum_over_schur_partition_index]
      simp [schurCharacter, schurDegree, schurWeight, schurCycleMonomial]
      ring

end Omega.POM
