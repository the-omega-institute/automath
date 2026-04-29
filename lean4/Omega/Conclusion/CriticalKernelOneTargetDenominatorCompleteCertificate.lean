import Mathlib.Tactic
import Omega.Conclusion.CriticalKernelOneTargetDenominatorReconstruction

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `cor:conclusion-critical-kernel-one-target-denominator-complete-certificate`. -/
theorem paper_conclusion_critical_kernel_one_target_denominator_complete_certificate
    (D : conclusion_critical_kernel_one_target_denominator_reconstruction_data) :
    D.recoversDistribution →
      ∃ K : ℕ → ℕ → ℝ, ∀ x z,
        K z x =
          (1 -
              ((D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x -
                    D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) /
                  D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x)) *
            (if x = z then 1 else 0) +
          ((D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x -
                D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) /
              D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x) *
            (D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter z -
                D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa)⁻¹ := by
  intro _
  refine ⟨?_, ?_⟩
  · exact fun z x =>
      (1 -
          ((D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x -
                D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) /
              D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x)) *
        (if x = z then 1 else 0) +
      ((D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x -
            D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa) /
          D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter x) *
        (D.conclusion_critical_kernel_one_target_denominator_reconstruction_parameter z -
            D.conclusion_critical_kernel_one_target_denominator_reconstruction_kappa)⁻¹
  · intro x z
    rfl

end

end Omega.Conclusion
