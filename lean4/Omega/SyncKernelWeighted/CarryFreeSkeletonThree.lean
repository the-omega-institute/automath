import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.EA.CarryFreeZetaTrichotomy
import Omega.SyncKernelWeighted.CarryFreeCoreBlock
import Omega.Zeta.DynZeta

namespace Omega.SyncKernelWeighted

private theorem sevenShiftFredholm_det (z : ℤ) :
    ((1 : Matrix (Fin 1) (Fin 1) ℤ) - z • Omega.EA.sevenShiftAdjacency).det = 1 - 7 * z := by
  rw [Matrix.det_fin_one]
  simp [Omega.EA.sevenShiftAdjacency]
  ring

private theorem threeShiftFredholm_det (z : ℤ) :
    ((1 : Matrix (Fin 1) (Fin 1) ℤ) - z • Omega.EA.threeShiftAdjacency).det = 1 - 3 * z := by
  rw [Matrix.det_fin_one]
  simp [Omega.EA.threeShiftAdjacency]
  ring

/-- Paper label: `prop:carry-free-skeleton-three`. -/
theorem paper_carry_free_skeleton_three :
    k9BlockFingerprint ∧
      k13BlockFingerprint ∧
      k21BlockFingerprint ∧
      Omega.EA.TwoStepStronglyConnected Omega.EA.sevenCarryFreeEdge ∧
      Omega.EA.TwoStepStronglyConnected Omega.EA.threeCarryFreeEdge ∧
      Omega.EA.TwoStepStronglyConnected Omega.Graph.goldenMeanGraph.edge ∧
      Omega.EA.sevenShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 7 ∧
      Omega.EA.threeShiftAdjacency.charpoly = Polynomial.X - Polynomial.C 3 ∧
      Omega.Graph.goldenMeanAdjacency.charpoly = Polynomial.X ^ 2 - Polynomial.X - 1 ∧
      (∀ z : ℤ, ((1 : Matrix (Fin 1) (Fin 1) ℤ) - z • Omega.EA.sevenShiftAdjacency).det =
        1 - 7 * z) ∧
      (∀ z : ℤ, ((1 : Matrix (Fin 1) (Fin 1) ℤ) - z • Omega.EA.threeShiftAdjacency).det =
        1 - 3 * z) ∧
      (∀ z : ℤ, (Omega.Zeta.fredholmGoldenMean z).det = 1 - z - z ^ 2) := by
  rcases paper_carry_free_core_block with ⟨hk9, hk13, hk21⟩
  rcases Omega.EA.paper_carry_free_zeta_trichotomy with
    ⟨h7conn, h3conn, hgmconn, h7char, h3char, hgmchar⟩
  refine ⟨hk9, hk13, hk21, h7conn, h3conn, hgmconn, h7char, h3char, hgmchar, ?_, ?_, ?_⟩
  · exact sevenShiftFredholm_det
  · exact threeShiftFredholm_det
  · exact Omega.Zeta.fredholmGoldenMean_det

end Omega.SyncKernelWeighted
