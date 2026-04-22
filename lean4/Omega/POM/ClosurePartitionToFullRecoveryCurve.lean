import Omega.POM.CompleteHomogeneousLinearRecurrence
import Omega.POM.FiniteSampleIndistinguishabilityPowerSums
import Omega.POM.InvertWFromHomogeneousCurve

namespace Omega.POM

/-- Paper label: `thm:pom-closure-partition-to-full-recovery-curve`. -/
def pom_closure_partition_to_full_recovery_curve_statement : Prop :=
  (∀ {α : Type*} [DecidableEq α] [Fintype α] (n : ℕ) (μ ν : α → ℚ),
    partitionPatternIndistinguishable n μ ν → powerSumIndistinguishable n μ ν) ∧
  (∀ (n : ℕ) (h e e' : ℕ → ℚ), h 0 = 1 → e 0 = 1 → e' 0 = 1 →
      (∀ t < n, h (t + 1) = completeHomogeneousRecurrence e h t) →
      (∀ t < n, h (t + 1) = completeHomogeneousRecurrence e' h t) →
    ∀ t ≤ n, e t = e' t) ∧
  (∀ (e h : ℕ → ℚ), (∀ t : ℕ, h (t + 1) = completeHomogeneousRecurrence e h t) →
    (∀ t : ℕ, h (t + 1) = completeHomogeneousRecurrence e h t) ∧
      ∀ t : ℕ, h (t + 1) = completeHomogeneousRecurrence e h t)

theorem paper_pom_closure_partition_to_full_recovery_curve :
    pom_closure_partition_to_full_recovery_curve_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro α _ _ n μ ν hpart
    exact (paper_pom_finite_sample_indistinguishability_power_sums n μ ν).2.1
      ((paper_pom_finite_sample_indistinguishability_power_sums n μ ν).1 hpart)
  · intro n h e e' h0 he0 he0' hrec hrec'
    exact paper_pom_invert_w_from_homogeneous_curve n h e e' h0 he0 he0' hrec hrec'
  · intro e h hrec
    let paper_pom_closure_partition_to_full_recovery_curve_linearRecurrence : Prop :=
      ∀ t : ℕ, h (t + 1) = completeHomogeneousRecurrence e h t
    have hpack :=
      paper_pom_complete_homogeneous_linear_recurrence
        paper_pom_closure_partition_to_full_recovery_curve_linearRecurrence
        paper_pom_closure_partition_to_full_recovery_curve_linearRecurrence hrec
        (fun hlin => hlin)
    exact hpack

end Omega.POM
