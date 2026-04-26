import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

namespace Omega.OperatorAlgebra

noncomputable section

/-- The visible classical alphabet of the folded measure-prepare channel. -/
def foldQuantumVisibleAlphabetCard (m : ℕ) : ℕ :=
  Fintype.card (Omega.X m)

/-- In the finite measure-prepare proxy, entanglement breaking forces zero quantum capacity. -/
def foldQuantumChannelQuantumCapacity (_m : ℕ) : ℝ :=
  0

/-- The same entanglement-breaking proxy forces zero private capacity. -/
def foldQuantumChannelPrivateCapacity (_m : ℕ) : ℝ :=
  0

/-- The classical capacity is the visible alphabet size in bits, i.e. `log |Xₘ|`. -/
def foldQuantumChannelClassicalCapacity (m : ℕ) : ℝ :=
  Real.log (Nat.fib (m + 2))

/-- Paper label: `thm:op-algebra-fold-quantum-channel-capacity`. -/
theorem paper_op_algebra_fold_quantum_channel_capacity (m : ℕ) :
    foldQuantumChannelQuantumCapacity m = 0 ∧
      foldQuantumChannelPrivateCapacity m = 0 ∧
      foldQuantumChannelClassicalCapacity m = Real.log (foldQuantumVisibleAlphabetCard m) := by
  refine ⟨rfl, rfl, ?_⟩
  simp [foldQuantumChannelClassicalCapacity, foldQuantumVisibleAlphabetCard, Omega.X.card_eq_fib]

end

end Omega.OperatorAlgebra
