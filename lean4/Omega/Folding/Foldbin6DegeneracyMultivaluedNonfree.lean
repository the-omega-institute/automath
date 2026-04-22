import Omega.GU.TerminalFoldbin6NoLinearKernel

namespace Omega

/-- Paper label: `cor:foldbin6-degeneracy-multivalued-nonfree`. The audited window-`6` histogram
contains nonempty fibers of sizes `2`, `3`, and `4`, so the partition is multivalued and the GU
coset obstruction rules out any linear-kernel model. -/
theorem paper_foldbin6_degeneracy_multivalued_nonfree :
    cBinFiberHist 6 2 ≠ 0 ∧ cBinFiberHist 6 3 ≠ 0 ∧ cBinFiberHist 6 4 ≠ 0 ∧
      ¬ ∃ k, Omega.GU.TerminalFoldbin6CosetModel k := by
  refine ⟨?_, ?_, ?_, Omega.GU.paper_terminal_foldbin6_no_linear_kernel⟩
  · simp [cBinFiberHist_6_2]
  · simp [cBinFiberHist_6_3]
  · simp [cBinFiberHist_6_4]

end Omega
