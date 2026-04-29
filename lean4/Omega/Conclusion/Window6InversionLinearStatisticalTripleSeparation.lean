import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence
import Omega.Conclusion.Window6NoLinearFactorization
import Omega.Folding.BinFold

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-inversion-linear-statistical-triple-separation`. -/
theorem paper_conclusion_window6_inversion_linear_statistical_triple_separation :
    (Omega.cBinFiberHist 6 2 = 8 ∧ Omega.cBinFiberHist 6 3 = 4 ∧
        Omega.cBinFiberHist 6 4 = 9) ∧
      (¬ ∃ k : ℕ, Omega.GU.TerminalFoldbin6CosetModel k) ∧
      Omega.Conclusion.conclusion_capacity_ordered_spectrum_infonce_equivalence_statement := by
  exact ⟨⟨Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.cBinFiberHist_6_4⟩,
    Omega.Conclusion.paper_conclusion_window6_no_linear_factorization,
    Omega.Conclusion.paper_conclusion_capacity_ordered_spectrum_infonce_equivalence⟩

end Omega.Conclusion
