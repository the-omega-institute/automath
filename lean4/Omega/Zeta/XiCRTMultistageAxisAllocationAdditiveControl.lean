import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite-stage data for the CRT axis-allocation problem. Each stage receives a
log-prime mass budget, a target demand, and the greedy allocation is required to match the target
stage-by-stage. Chebyshev control bounds the total target mass and therefore the optimal value. -/
structure XiCRTMultistageAxisAllocationData where
  stageCount : ℕ
  stageLogPrimeMass : Fin stageCount → ℝ
  stageTarget : Fin stageCount → ℝ
  greedyAllocation : Fin stageCount → ℝ
  chebyshevMass : ℝ
  cutoffMass : ℝ
  optimalValue : ℝ
  target_le_stageMass : ∀ i, stageTarget i ≤ stageLogPrimeMass i
  greedy_eq_target : ∀ i, greedyAllocation i = stageTarget i
  targetSum_le_chebyshev : (∑ i, stageTarget i) ≤ chebyshevMass
  chebyshev_le_cutoff : chebyshevMass ≤ cutoffMass
  optimalValue_eq_targetSum : optimalValue = ∑ i, stageTarget i

namespace XiCRTMultistageAxisAllocationData

/-- Summing the disjoint stage targets is bounded by the available Chebyshev mass. -/
def lowerBoundByChebyshev (D : XiCRTMultistageAxisAllocationData) : Prop :=
  (∑ i, D.stageTarget i) ≤ D.chebyshevMass

/-- The greedy stage-by-stage construction stays within the log-prime mass budget at every stage. -/
def greedyFeasibleAllocation (D : XiCRTMultistageAxisAllocationData) : Prop :=
  ∀ i, D.greedyAllocation i ≤ D.stageLogPrimeMass i

/-- The optimal value is exactly the sum of the greedy stage allocations. -/
def optimalValueCharacterization (D : XiCRTMultistageAxisAllocationData) : Prop :=
  D.optimalValue = ∑ i, D.greedyAllocation i

/-- The Chebyshev asymptotic packages the optimal scale under the cutoff `x`. -/
def asymptoticScale (D : XiCRTMultistageAxisAllocationData) : Prop :=
  D.optimalValue ≤ D.cutoffMass

lemma greedyFeasible (D : XiCRTMultistageAxisAllocationData) : D.greedyFeasibleAllocation := by
  intro i
  rw [D.greedy_eq_target i]
  exact D.target_le_stageMass i

lemma optimalValue_eq_greedySum (D : XiCRTMultistageAxisAllocationData) :
    D.optimalValueCharacterization := by
  have hSum : (∑ i, D.greedyAllocation i) = ∑ i, D.stageTarget i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact D.greedy_eq_target i
  calc
    D.optimalValue = ∑ i, D.stageTarget i := D.optimalValue_eq_targetSum
    _ = ∑ i, D.greedyAllocation i := by simpa using hSum.symm

lemma asymptoticScale_of_chebyshev (D : XiCRTMultistageAxisAllocationData) : D.asymptoticScale := by
  calc
    D.optimalValue = ∑ i, D.stageTarget i := D.optimalValue_eq_targetSum
    _ ≤ D.chebyshevMass := D.targetSum_le_chebyshev
    _ ≤ D.cutoffMass := D.chebyshev_le_cutoff

end XiCRTMultistageAxisAllocationData

/-- Summing disjoint log-prime mass yields the Chebyshev lower bound, the greedy allocation is
feasible stage-by-stage, its total equals the optimal value, and the packaged Chebyshev asymptotic
controls the final scale.
    thm:xi-crt-multistage-axis-allocation-additive-control -/
theorem paper_xi_crt_multistage_axis_allocation_additive_control
    (D : XiCRTMultistageAxisAllocationData) :
    D.lowerBoundByChebyshev ∧ D.greedyFeasibleAllocation ∧ D.optimalValueCharacterization ∧
      D.asymptoticScale := by
  exact ⟨D.targetSum_le_chebyshev, D.greedyFeasible, D.optimalValue_eq_greedySum,
    D.asymptoticScale_of_chebyshev⟩

end Omega.Zeta
