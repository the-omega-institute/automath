import Mathlib.NumberTheory.PrimeCounting
import Omega.Zeta.XiCRTMultistageAxisAllocationAdditiveControl

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The optimal maximum-prime cutoff supplied by the additive-control theorem. -/
noncomputable def xi_multistage_crt_axis_count_scaling_optimalCutoff
    (optimalValue : ℝ) : ℕ :=
  Nat.ceil optimalValue

/-- The required number of CRT prime axes is the prime-counting function at the cutoff. -/
noncomputable def xi_multistage_crt_axis_count_scaling_axisCount
    (optimalValue : ℝ) : ℕ :=
  Nat.primeCounting (xi_multistage_crt_axis_count_scaling_optimalCutoff optimalValue)

/-- Concrete axis-count scaling package: the count is `π(p_max*)`, and the additive-control
theorem bounds the cutoff scale by the available Chebyshev mass. -/
def xi_multistage_crt_axis_count_scaling_package
    (optimalValue cutoffMass : ℝ) : Prop :=
  xi_multistage_crt_axis_count_scaling_axisCount optimalValue =
      Nat.primeCounting (xi_multistage_crt_axis_count_scaling_optimalCutoff optimalValue) ∧
    optimalValue ≤ cutoffMass

/-- The no-parameter paper statement, with all finite-stage hypotheses explicit. -/
def xi_multistage_crt_axis_count_scaling_statement : Prop :=
  ∀ (stageCount : ℕ) (stageLogPrimeMass stageTarget greedyAllocation : Fin stageCount → ℝ)
    (chebyshevMass cutoffMass optimalValue : ℝ),
      (∀ i, stageTarget i ≤ stageLogPrimeMass i) →
        (∀ i, greedyAllocation i = stageTarget i) →
          (∑ i, stageTarget i) ≤ chebyshevMass →
            chebyshevMass ≤ cutoffMass →
              optimalValue = ∑ i, stageTarget i →
                xi_multistage_crt_axis_count_scaling_package optimalValue cutoffMass

/-- Paper label: `cor:xi-multistage-crt-axis-count-scaling`. -/
theorem paper_xi_multistage_crt_axis_count_scaling :
    xi_multistage_crt_axis_count_scaling_statement := by
  intro stageCount stageLogPrimeMass stageTarget greedyAllocation chebyshevMass cutoffMass
    optimalValue hTargetLe hGreedy hChebyshev hCutoff hOptimal
  let D : XiCRTMultistageAxisAllocationData :=
    { stageCount := stageCount
      stageLogPrimeMass := stageLogPrimeMass
      stageTarget := stageTarget
      greedyAllocation := greedyAllocation
      chebyshevMass := chebyshevMass
      cutoffMass := cutoffMass
      optimalValue := optimalValue
      target_le_stageMass := hTargetLe
      greedy_eq_target := hGreedy
      targetSum_le_chebyshev := hChebyshev
      chebyshev_le_cutoff := hCutoff
      optimalValue_eq_targetSum := hOptimal }
  have hPackage := paper_xi_crt_multistage_axis_allocation_additive_control D
  exact ⟨rfl, hPackage.2.2.2⟩

end

end Omega.Zeta
