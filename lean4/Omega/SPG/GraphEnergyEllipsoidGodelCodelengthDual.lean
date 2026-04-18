import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SPG

/-- The squared Euclidean energy of a finite real vector. -/
def graphEnergyEllipsoidEnergy {rank : ℕ} (x : Fin rank → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- The dual-coordinate readout used for the Gödel codelength bound. -/
def graphEnergyEllipsoidLogLength {rank : ℕ} (dualWeights : Fin rank → ℝ) (x : Fin rank → ℝ) : ℝ :=
  ∑ i, dualWeights i * x i

/-- The squared dual norm controlling the readout. -/
def graphEnergyEllipsoidDualBound {rank : ℕ} (dualWeights : Fin rank → ℝ) : ℝ :=
  ∑ i, dualWeights i ^ 2

/-- Membership in the concrete ellipsoid of energy budget `E`. -/
def graphEnergyInEllipsoid {rank : ℕ} (energyBudget : ℝ) (x : Fin rank → ℝ) : Prop :=
  0 ≤ energyBudget ∧ graphEnergyEllipsoidEnergy x ≤ energyBudget

private theorem graphEnergyEllipsoidDualBound_nonneg {rank : ℕ} (dualWeights : Fin rank → ℝ) :
    0 ≤ graphEnergyEllipsoidDualBound dualWeights := by
  unfold graphEnergyEllipsoidDualBound
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The dual readout of a point in the concrete graph-energy ellipsoid is bounded by the product of
the primal and dual square-root budgets. This is the finite-dimensional Cauchy-Schwarz bridge used
by the SPG single-gate spacing estimates.
    prop:graph-energy-ellipsoid-godel-codelength-dual -/
theorem paper_graph_energy_ellipsoid_godel_codelength_dual
    (rank : ℕ) (energyBudget : ℝ) (dualWeights : Fin rank → ℝ) :
    ∀ x : Fin rank → ℝ, graphEnergyInEllipsoid energyBudget x ->
      |graphEnergyEllipsoidLogLength dualWeights x| ≤
        Real.sqrt energyBudget * Real.sqrt (graphEnergyEllipsoidDualBound dualWeights) := by
  intro x hx
  rcases hx with ⟨hEnergyBudget, hxEllipsoid⟩
  have hDualNonneg : 0 ≤ graphEnergyEllipsoidDualBound dualWeights :=
    graphEnergyEllipsoidDualBound_nonneg dualWeights
  have hCS :=
    Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) dualWeights x
  have hSq :
      (graphEnergyEllipsoidLogLength dualWeights x) ^ 2 ≤
        energyBudget * graphEnergyEllipsoidDualBound dualWeights := by
    calc
      (graphEnergyEllipsoidLogLength dualWeights x) ^ 2 ≤
          graphEnergyEllipsoidDualBound dualWeights * graphEnergyEllipsoidEnergy x := by
        simpa [graphEnergyEllipsoidLogLength, graphEnergyEllipsoidDualBound,
          graphEnergyEllipsoidEnergy, mul_comm, mul_left_comm, mul_assoc] using hCS
      _ ≤ graphEnergyEllipsoidDualBound dualWeights * energyBudget := by
        exact mul_le_mul_of_nonneg_left hxEllipsoid hDualNonneg
      _ = energyBudget * graphEnergyEllipsoidDualBound dualWeights := by ring
  calc
    |graphEnergyEllipsoidLogLength dualWeights x| ≤
        Real.sqrt (energyBudget * graphEnergyEllipsoidDualBound dualWeights) :=
      Real.abs_le_sqrt hSq
    _ = Real.sqrt energyBudget * Real.sqrt (graphEnergyEllipsoidDualBound dualWeights) := by
      rw [Real.sqrt_mul hEnergyBudget]

end Omega.SPG
