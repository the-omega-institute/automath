import Omega.Conclusion.RealInput40BFJordanTowerSeparation

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-realinput40-full-essential-pure-zero-spectrum-stripping`. The full-to-essential
compression strips only the transient zero-spectrum tower, leaving the stable BF and
Cuntz--Krieger invariants unchanged while preserving the audited nilpotent depths. -/
theorem paper_conclusion_realinput40_full_essential_pure_zero_spectrum_stripping :
    Omega.SyncKernelWeighted.realInput40BowenFranksOrder = 1 ∧
      Omega.SyncKernelWeighted.realInput40CuntzKriegerK0Rank = 0 ∧
      Omega.SyncKernelWeighted.realInput40CuntzKriegerK1Rank = 0 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_essential_kernel_dim 3 = 11 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 5 = 31 := by
  rcases paper_conclusion_realinput40_bf_jordan_tower_separation with
    ⟨hBF, hK0, hK1, hEssential3, _, hFull5⟩
  exact ⟨hBF, hK0, hK1, hEssential3, hFull5⟩

end Omega.Conclusion
