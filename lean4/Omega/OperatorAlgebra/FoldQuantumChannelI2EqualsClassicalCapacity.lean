import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldQuantumChannelCapacity
import Omega.OperatorAlgebra.FoldQuantumChannelChoiRenyiMutualInformation

namespace Omega.OperatorAlgebra

noncomputable section

/-- Paper label: `cor:op-algebra-fold-quantum-channel-i2-equals-classical-capacity`. -/
theorem paper_op_algebra_fold_quantum_channel_i2_equals_classical_capacity (m : ℕ) :
    ∃ I_P I_sw : ℝ,
      I_P = foldQuantumChannelClassicalCapacity m ∧
        I_sw = foldQuantumChannelClassicalCapacity m ∧ I_P = I_sw := by
  let D : FoldQuantumChannelEnvironmentData := ⟨List.replicate (Nat.fib (m + 2)) 1⟩
  rcases
      paper_op_algebra_fold_quantum_channel_choi_renyi_mutual_information D 2
        (by norm_num) (by norm_num) with
    ⟨I_P, I_sw, hIP, hISw, hEq⟩
  refine ⟨I_P, I_sw, ?_, ?_, hEq⟩
  · calc
      I_P = Real.log (Nat.fib (m + 2) : ℝ) / (2 - 1) := by
        simpa [D, foldQuantumVisibleAlphabetCard, Omega.X.card_eq_fib] using hIP
      _ = foldQuantumChannelClassicalCapacity m := by norm_num [foldQuantumChannelClassicalCapacity]
  · calc
      I_sw = Real.log (Nat.fib (m + 2) : ℝ) / (2 - 1) := by
        simpa [D, foldQuantumVisibleAlphabetCard, Omega.X.card_eq_fib] using hISw
      _ = foldQuantumChannelClassicalCapacity m := by norm_num [foldQuantumChannelClassicalCapacity]

end

end Omega.OperatorAlgebra
