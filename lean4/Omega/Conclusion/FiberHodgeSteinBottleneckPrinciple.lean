import Mathlib.Tactic
import Omega.POM.FiberHodgeSteinTensorizationGap
import Omega.POM.FiberReconstructionCartesianProduct

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The concrete path-factor list used by the conclusion-level bottleneck wrapper. -/
def conclusion_fiber_hodge_stein_bottleneck_principle_lengths : List ℕ :=
  [1, 2, 3]

/-- A one-vertex weighted graph carrying the Hodge--Stein identities used below. -/
def conclusion_fiber_hodge_stein_bottleneck_principle_graph :
    Omega.POM.FiberWeightedGraph where
  V := Fin 1
  fintypeV := inferInstance
  vertexWeight := fun _ => 1
  conductance := fun _ _ => 0

/-- The diagonal two-factor Hodge--Stein tensorization instance. -/
def conclusion_fiber_hodge_stein_bottleneck_principle_tensorData :
    Omega.POM.FiberHodgeSteinTensorizationGapData where
  G := conclusion_fiber_hodge_stein_bottleneck_principle_graph
  r := 2
  hr := by norm_num
  factorGap := fun i => if i = 0 then 2 else 5
  factorGap_ne_zero := by
    intro i
    fin_cases i <;> norm_num
  factorLoad := fun i => if i = 0 then 7 else 11

/-- Concrete statement for `thm:conclusion-fiber-hodge-stein-bottleneck-principle`. -/
def conclusion_fiber_hodge_stein_bottleneck_principle_statement : Prop :=
  Omega.POM.FiberReconstructionCartesianFactors
      conclusion_fiber_hodge_stein_bottleneck_principle_lengths ∧
    Omega.POM.fiberReconstructionCubeDimension
      conclusion_fiber_hodge_stein_bottleneck_principle_lengths =
        (conclusion_fiber_hodge_stein_bottleneck_principle_lengths.map
          fun ℓ => (ℓ + 1) / 2).sum ∧
    Omega.POM.fiberReconstructionDiameter
      conclusion_fiber_hodge_stein_bottleneck_principle_lengths =
        conclusion_fiber_hodge_stein_bottleneck_principle_lengths.sum ∧
    conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.Valid ∧
    (∀ i : Fin conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.r,
      conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.poissonSource i =
        conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.factorLoad i) ∧
    (conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.minimizerFlow =
      fun i => -conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.poissonPotential i) ∧
    conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.productSpectralGap =
      sInf (Set.range
        conclusion_fiber_hodge_stein_bottleneck_principle_tensorData.factorGap)

/-- Paper label: `thm:conclusion-fiber-hodge-stein-bottleneck-principle`. -/
theorem paper_conclusion_fiber_hodge_stein_bottleneck_principle :
    conclusion_fiber_hodge_stein_bottleneck_principle_statement := by
  have hcart := Omega.POM.paper_pom_fiber_reconstruction_cartesian_product
    conclusion_fiber_hodge_stein_bottleneck_principle_lengths
  have htensor := Omega.POM.paper_pom_fiber_hodge_stein_tensorization_gap
    conclusion_fiber_hodge_stein_bottleneck_principle_tensorData
  exact ⟨hcart.1, hcart.2.1, hcart.2.2, htensor, htensor.2.2.2.1,
    htensor.2.2.2.2.1, htensor.2.2.2.2.2⟩

end

end Omega.Conclusion
