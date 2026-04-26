import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiSpectrumMi
import Omega.POM.FiberIndsetFactorization

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `cor:conclusion-fold-quantum-fiber-spectrum-resource-partition`. The Fibonacci
fiber spectrum determines both the minimal environment size and the closed mutual-information
expression of the folded quantum channel. -/
theorem paper_conclusion_fold_quantum_fiber_spectrum_resource_partition
    (blocks : List (List ℕ)) :
    let fiberSizes := blocks.map fun ls => (ls.map fun ell => Nat.fib (ell + 2)).prod
    let D : Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData := ⟨fiberSizes⟩
    D.minEnvironmentDim = (fiberSizes.map fun d => d ^ 2).sum ∧
      ∃ I : ℝ,
        I = Real.log (fiberSizes.sum : ℝ) -
          (fiberSizes.map (fun d => ((d : ℝ) / (fiberSizes.sum : ℝ)) * Real.log d)).sum := by
  dsimp
  let D : Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData := ⟨blocks.map fun ls =>
    (ls.map fun ell => Nat.fib (ell + 2)).prod⟩
  constructor
  · simpa [D] using
      show D.minEnvironmentDim = (blocks.map (fun ls => (ls.map fun ell => Nat.fib (ell + 2)).prod)
          |>.map fun d => d ^ 2).sum from by
        simpa [Omega.OperatorAlgebra.FoldQuantumChannelEnvironmentData.s2Moment, D] using
          (Omega.OperatorAlgebra.paper_op_algebra_fold_quantum_channel_minimal_environment_equals_s2 D).2.2
  · simpa [D] using Omega.OperatorAlgebra.paper_op_algebra_fold_quantum_channel_choi_spectrum_mi D

end
end Omega.Conclusion
