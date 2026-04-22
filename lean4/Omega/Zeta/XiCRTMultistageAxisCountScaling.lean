import Mathlib.NumberTheory.PrimeCounting
import Omega.Zeta.XiCRTMultistageAxisAllocationAdditiveControl

open scoped BigOperators Nat.Prime

namespace Omega.Zeta

noncomputable section

/-- The cutoff scale singled out by the additive-control theorem. -/
noncomputable def xi_crt_multistage_axis_count_scaling_optimalCutoff (optimalValue : ℝ) : ℕ :=
  Nat.ceil optimalValue

/-- The minimal number of prime axes obtained by using every prime up to the optimal cutoff. -/
noncomputable def xi_crt_multistage_axis_count_scaling_minimalAxisCount (optimalValue : ℝ) : ℕ :=
  Nat.primeCounting (xi_crt_multistage_axis_count_scaling_optimalCutoff optimalValue)

/-- Concrete axis-count scaling package: the optimal axis count is the prime count up to the
chosen cutoff, and the additive-control theorem bounds that cutoff by the Chebyshev mass budget. -/
def xi_crt_multistage_axis_count_scaling_minimalAxisCountScaling
    (optimalValue cutoffMass : ℝ) : Prop :=
  xi_crt_multistage_axis_count_scaling_minimalAxisCount optimalValue =
      Nat.primeCounting (xi_crt_multistage_axis_count_scaling_optimalCutoff optimalValue) ∧
    optimalValue ≤ cutoffMass

/-- Paper label: `cor:xi-crt-multistage-axis-count-scaling`.
The additive-control theorem supplies the optimal cutoff bound, while the axis count itself is the
prime-counting function evaluated at that cutoff. -/
theorem paper_xi_crt_multistage_axis_count_scaling
    (stageCount : ℕ) (stageLogPrimeMass stageTarget greedyAllocation : Fin stageCount → ℝ)
    (chebyshevMass cutoffMass optimalValue : ℝ)
    (hTargetLe : ∀ i, stageTarget i ≤ stageLogPrimeMass i)
    (hGreedy : ∀ i, greedyAllocation i = stageTarget i)
    (hChebyshev : (∑ i, stageTarget i) ≤ chebyshevMass)
    (hCutoff : chebyshevMass ≤ cutoffMass)
    (hOptimal : optimalValue = ∑ i, stageTarget i) :
    xi_crt_multistage_axis_count_scaling_minimalAxisCountScaling optimalValue cutoffMass := by
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
