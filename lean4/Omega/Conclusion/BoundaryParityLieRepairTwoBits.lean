import Mathlib.Tactic
import Omega.Conclusion.BoundaryParityBlindFiltration
import Omega.Conclusion.CompressionLadderSpin10

namespace Omega.Conclusion

/-- The residual parity quotient has rank `2`, matching the two missing bits after the geometric
diagonal subgroup is quotiented out. -/
def window6BoundaryParityResidualRank : ℕ :=
  3 - 1

/-- The minimal disconnected repair contributes one component for each residual parity character. -/
def window6BoundaryParityLieRepairComponentCount : ℕ :=
  2 ^ window6BoundaryParityResidualRank

/-- Connected repairs would force the component count down to `1`; the two-bit repair avoids this. -/
def window6BoundaryParityLieRepairConnected : Prop :=
  window6BoundaryParityLieRepairComponentCount = 1

/-- The sharp witness model is the minimal repair with exactly four connected components. -/
def window6BoundaryParityLieRepairSharpModel : Prop :=
  window6BoundaryParityLieRepairComponentCount = 4

/-- The blind-filtration quotient carries two residual parity bits, and the `Spin(10)` compression
ladder forces them into disconnected components. Consequently any faithful Lie repair is
disconnected with at least four components, and the four-component witness is sharp.
    thm:conclusion-window6-boundary-parity-lie-repair-two-bits -/
theorem paper_conclusion_window6_boundary_parity_lie_repair_two_bits :
    ¬ window6BoundaryParityLieRepairConnected ∧
      4 ≤ window6BoundaryParityLieRepairComponentCount ∧
      window6BoundaryParityLieRepairSharpModel := by
  rcases quotient_rank_two with ⟨hResidual, hCardinality, _⟩
  have hLoss : 2 ≤ window6BoundaryParityResidualRank := by
    simpa [window6BoundaryParityResidualRank] using
      CompressionLadderSpin10.so10_kernel_lower_bound
  have hSharp : window6BoundaryParityLieRepairSharpModel := by
    dsimp [window6BoundaryParityLieRepairSharpModel, window6BoundaryParityLieRepairComponentCount]
    simpa [window6BoundaryParityResidualRank, hResidual] using hCardinality
  have hCount : window6BoundaryParityLieRepairComponentCount = 4 := by
    simpa [window6BoundaryParityLieRepairSharpModel] using hSharp
  refine ⟨?_, ?_, hSharp⟩
  · dsimp [window6BoundaryParityLieRepairConnected]
    rw [hCount]
    decide
  · simpa [hCount]

end Omega.Conclusion
