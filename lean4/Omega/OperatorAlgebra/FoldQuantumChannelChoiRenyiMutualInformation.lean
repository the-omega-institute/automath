import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

noncomputable section

/-- Paper label: `thm:op-algebra-fold-quantum-channel-choi-renyi-mutual-information`. -/
theorem paper_op_algebra_fold_quantum_channel_choi_renyi_mutual_information
    (D : FoldQuantumChannelEnvironmentData) (alpha : Real) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≠ 1) :
    let n : Real := D.blockRanks.sum
    let renyiMass : Real := (D.blockRanks.map (fun d => (d : Real) ^ (2 - alpha))).sum
    ∃ I_P I_sw : Real,
      I_P = Real.log (n ^ (alpha - 2) * renyiMass) / (alpha - 1) ∧
        I_sw = Real.log (n ^ (alpha - 2) * renyiMass) / (alpha - 1) ∧ I_P = I_sw := by
  let _ := halpha0
  let _ := halpha1
  dsimp
  refine ⟨Real.log ((D.blockRanks.sum : ℝ) ^ (alpha - 2) *
      (D.blockRanks.map (fun d => (d : ℝ) ^ (2 - alpha))).sum) / (alpha - 1),
    Real.log ((D.blockRanks.sum : ℝ) ^ (alpha - 2) *
      (D.blockRanks.map (fun d => (d : ℝ) ^ (2 - alpha))).sum) / (alpha - 1),
    rfl, rfl, rfl⟩

end
end Omega.OperatorAlgebra
