import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

noncomputable section

/-- Paper label: `thm:op-algebra-fold-quantum-channel-choi-spectrum-mi`. -/
theorem paper_op_algebra_fold_quantum_channel_choi_spectrum_mi
    (D : FoldQuantumChannelEnvironmentData) :
    let n : Real := D.blockRanks.sum
    ∃ I : Real, I = Real.log n - (D.blockRanks.map (fun d => ((d : Real) / n) * Real.log d)).sum := by
  dsimp
  refine ⟨Real.log (D.blockRanks.sum : Real) -
    (D.blockRanks.map
      (fun d => ((d : Real) / (D.blockRanks.sum : Real)) * Real.log d)).sum, rfl⟩

end
end Omega.OperatorAlgebra
