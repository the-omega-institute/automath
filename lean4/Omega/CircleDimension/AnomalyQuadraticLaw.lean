import Mathlib.Tactic
import Omega.CircleDimension.TensorHomExtLaws

namespace Omega.CircleDimension

/-- The connected anomaly dimension keeps only the exterior-square contribution of the free
    rank. -/
def anomalyConnectedDim (freeRank torsionRank : Nat) : Nat :=
  Nat.choose (circleDim freeRank torsionRank) 2

/-- Torsion contributes only a discrete anomaly ledger. -/
def anomalyDiscretePart (_freeRank torsionRank : Nat) : Nat := torsionRank

/-- Paper-facing bookkeeping wrapper for the connected anomaly dimension:
    the connected contribution is exactly the exterior-square rank of the free part,
    hence equals `choose (cdim G) 2`, while torsion survives only in the discrete part.
    thm:cdim-anomaly-quadratic-law -/
theorem paper_cdim_anomaly_quadratic_law :
    ∀ freeRank torsionRank : Nat,
      anomalyConnectedDim freeRank torsionRank =
        Nat.choose (circleDim freeRank torsionRank) 2 ∧
      anomalyConnectedDim freeRank torsionRank = Nat.choose freeRank 2 ∧
      circleDim 0 torsionRank = 0 ∧
      anomalyDiscretePart freeRank torsionRank = anomalyDiscretePart 0 torsionRank := by
  intro freeRank torsionRank
  have hSeeds := paper_cdim_tensor_hom_ext_laws_seeds
  have hExt : circleDim 0 torsionRank = 0 := hSeeds.2 torsionRank
  refine ⟨rfl, ?_, hExt, rfl⟩
  simp [anomalyConnectedDim, circleDim]

end Omega.CircleDimension
