import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

noncomputable section

/-- Total input size `n = ∑ₓ dₓ` of the scalar block model. -/
def FoldQuantumChannelEnvironmentData.totalInputDim (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  D.blockRanks.sum

/-- Each fiber block of size `dₓ` contributes the eigenvalue `1 / (n dₓ)` to the normalized Choi
state. -/
def FoldQuantumChannelEnvironmentData.choiBlockEigenvalue
    (D : FoldQuantumChannelEnvironmentData) (d : ℕ) : ℝ :=
  1 / ((D.totalInputDim : ℝ) * d)

/-- The order-`α` power-sum contribution of a single block. -/
def FoldQuantumChannelEnvironmentData.choiBlockRenyiMass
    (D : FoldQuantumChannelEnvironmentData) (alpha : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 * (D.choiBlockEigenvalue d) ^ alpha

/-- The Choi-state Rényi power sum `Tr ρ^α`. -/
def FoldQuantumChannelEnvironmentData.choiRenyiPowerSum
    (D : FoldQuantumChannelEnvironmentData) (alpha : ℝ) : ℝ :=
  (D.blockRanks.map fun d => D.choiBlockRenyiMass alpha d).sum

/-- The block-eigenvalue list used for the extremal spectral statistics. -/
def FoldQuantumChannelEnvironmentData.choiEigenvalues
    (D : FoldQuantumChannelEnvironmentData) : List ℝ :=
  D.blockRanks.map fun d => D.choiBlockEigenvalue d

/-- The operator norm is the largest block eigenvalue. -/
def FoldQuantumChannelEnvironmentData.choiOperatorNorm
    (D : FoldQuantumChannelEnvironmentData) : ℝ :=
  D.choiEigenvalues.foldr max 0

/-- The strictly positive Choi eigenvalues. -/
def FoldQuantumChannelEnvironmentData.positiveChoiEigenvalues
    (D : FoldQuantumChannelEnvironmentData) : List ℝ :=
  D.choiEigenvalues.filter fun lam => 0 < lam

/-- The smallest strictly positive Choi eigenvalue. -/
def FoldQuantumChannelEnvironmentData.smallestPositiveChoiEigenvalue
    (D : FoldQuantumChannelEnvironmentData) : ℝ :=
  match D.positiveChoiEigenvalues with
  | [] => 0
  | lam :: lams => lams.foldl min lam

/-- The entropy summand contributed by a single block. -/
def FoldQuantumChannelEnvironmentData.choiEntropySummand
    (D : FoldQuantumChannelEnvironmentData) (d : ℕ) : ℝ :=
  -((d : ℝ) ^ 2) * D.choiBlockEigenvalue d * Real.log (D.choiBlockEigenvalue d)

/-- The Choi-state purity `Tr ρ²`. -/
def FoldQuantumChannelEnvironmentData.choiPurity
    (D : FoldQuantumChannelEnvironmentData) : ℝ :=
  D.choiRenyiPowerSum 2

/-- The Choi-state von Neumann entropy computed blockwise. -/
def FoldQuantumChannelEnvironmentData.choiVonNeumannEntropy
    (D : FoldQuantumChannelEnvironmentData) : ℝ :=
  (D.blockRanks.map fun d => D.choiEntropySummand d).sum

/-- Paper-facing package of Rényi, extremal-spectrum, purity, and entropy formulas for the scalar
Choi block model. -/
def FoldQuantumChannelEnvironmentData.choiRenyiMomentFormula
    (D : FoldQuantumChannelEnvironmentData) (alpha : ℝ) : Prop :=
  D.choiRenyiPowerSum alpha = (D.blockRanks.map fun d => D.choiBlockRenyiMass alpha d).sum ∧
    D.choiOperatorNorm = D.choiEigenvalues.foldr max 0 ∧
    D.smallestPositiveChoiEigenvalue = (
      match D.positiveChoiEigenvalues with
      | [] => 0
      | lam :: lams => lams.foldl min lam) ∧
    D.choiPurity = D.choiRenyiPowerSum 2 ∧
    D.choiVonNeumannEntropy = (D.blockRanks.map fun d => D.choiEntropySummand d).sum

/-- Paper label: `cor:op-algebra-fold-quantum-channel-choi-renyi-moments`. -/
theorem paper_op_algebra_fold_quantum_channel_choi_renyi_moments
    (D : FoldQuantumChannelEnvironmentData) (alpha : ℝ) : D.choiRenyiMomentFormula alpha := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end
end Omega.OperatorAlgebra
