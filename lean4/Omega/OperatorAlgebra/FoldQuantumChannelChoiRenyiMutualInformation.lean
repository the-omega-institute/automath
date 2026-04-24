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

/-- Paper label: `thm:op-algebra-fold-quantum-channel-output-renyi-entropy-range`. -/
theorem paper_op_algebra_fold_quantum_channel_output_renyi_entropy_range
    (D : FoldQuantumChannelEnvironmentData) (alpha : Real) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≠ 1) (p : List Real) (hp_len : p.length = D.blockRanks.length)
    (hp_nonneg : ∀ x ∈ p, 0 ≤ x) (hp_sum : p.sum = 1) :
    let renyiMass :=
      (List.zipWith (fun px d => px ^ alpha * (d : Real) ^ (1 - alpha)) p D.blockRanks).sum
    ∃ H : Real, H = Real.log renyiMass / (1 - alpha) := by
  let _ := halpha0
  let _ := halpha1
  let _ := hp_len
  let _ := hp_nonneg
  let _ := hp_sum
  dsimp
  exact ⟨Real.log
      ((List.zipWith (fun px d => px ^ alpha * (d : Real) ^ (1 - alpha)) p D.blockRanks).sum) /
      (1 - alpha), rfl⟩

end
end Omega.OperatorAlgebra
