import Mathlib.Tactic
import Omega.POM.HookChannelImpliesPartitionGapClosed
import Omega.POM.SchurVarianceDecomposition

namespace Omega.Conclusion

noncomputable section

open Omega.POM
open Omega.POM.SchurPartitionIndex
open scoped BigOperators

/-- The centered average in the conclusion-level Schur variance package. -/
def conclusion_strict_gap_forces_nonhook_schur_variance_average (m : ℝ) : ℝ :=
  Omega.POM.schurNormalizedChannelTrace m cycle

/-- The centered class function after subtracting the trivial Schur channel. -/
def conclusion_strict_gap_forces_nonhook_schur_variance_centered
    (m : ℝ) : Omega.POM.SchurPartitionIndex → ℝ :=
  fun ν => Omega.POM.schurCycleMonomial m ν -
    conclusion_strict_gap_forces_nonhook_schur_variance_average m

/-- The centered Schur-side variance. -/
def conclusion_strict_gap_forces_nonhook_schur_variance_centeredVariance
    (m : ℝ) : ℝ :=
  ∑ ν, (1 / Omega.POM.schurWeight ν) *
    (conclusion_strict_gap_forces_nonhook_schur_variance_centered m ν) ^ (2 : ℕ)

/-- The centered Schur channel transform. -/
def conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel
    (m : ℝ) : Omega.POM.SchurPartitionIndex → ℝ :=
  fun lam => ∑ ν, (Omega.POM.schurCharacter lam ν / Omega.POM.schurWeight ν) *
    conclusion_strict_gap_forces_nonhook_schur_variance_centered m ν

/-- In the `S₂` seed there are no nontrivial nonhook partitions. -/
def conclusion_strict_gap_forces_nonhook_schur_variance_isNonhook :
    Omega.POM.SchurPartitionIndex → Bool
  | cycle => false
  | split => false

/-- Paper label: `thm:conclusion-strict-gap-forces-nonhook-schur-variance`. The variance
decomposition reduces the centered energy to Schur channels, and a strict partition gap removes
the unique nontrivial hook channel in the `S₂` seed, leaving only the nonhook-filtered sum. -/
theorem paper_conclusion_strict_gap_forces_nonhook_schur_variance
    (m partitionGap : ℝ) (hNonneg : 0 ≤ partitionGap)
    (hStrictGapKillsHook :
      0 < partitionGap →
        ¬ (conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m split ≠ 0))
    (hGap : 0 < partitionGap) :
    conclusion_strict_gap_forces_nonhook_schur_variance_centeredVariance m =
      ∑ lam, if conclusion_strict_gap_forces_nonhook_schur_variance_isNonhook lam then
        (conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m lam /
            Omega.POM.schurDegree lam) ^ (2 : ℕ)
      else
        0 := by
  rcases Omega.POM.paper_pom_schur_variance_decomposition m with ⟨_, _, hVariance⟩
  have hSplitZero :
      conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m split = 0 := by
    by_contra hSplitNonzero
    have hClosed : partitionGap = 0 :=
      Omega.POM.paper_pom_hook_channel_implies_partition_gap_closed partitionGap
        (conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m split ≠ 0)
        hNonneg hStrictGapKillsHook hSplitNonzero
    linarith
  calc
    conclusion_strict_gap_forces_nonhook_schur_variance_centeredVariance m =
        ∑ lam, if lam = cycle then
          0
        else
          (conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m lam /
              Omega.POM.schurDegree lam) ^ (2 : ℕ) := by
      simpa [conclusion_strict_gap_forces_nonhook_schur_variance_average,
        conclusion_strict_gap_forces_nonhook_schur_variance_centered,
        conclusion_strict_gap_forces_nonhook_schur_variance_centeredVariance,
        conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel] using hVariance
    _ = 0 := by
      rw [Omega.POM.sum_over_schur_partition_index]
      simp [hSplitZero]
    _ = ∑ lam, if conclusion_strict_gap_forces_nonhook_schur_variance_isNonhook lam then
          (conclusion_strict_gap_forces_nonhook_schur_variance_centeredChannel m lam /
              Omega.POM.schurDegree lam) ^ (2 : ℕ)
        else
          0 := by
      rw [Omega.POM.sum_over_schur_partition_index]
      simp [conclusion_strict_gap_forces_nonhook_schur_variance_isNonhook]

end

end Omega.Conclusion
