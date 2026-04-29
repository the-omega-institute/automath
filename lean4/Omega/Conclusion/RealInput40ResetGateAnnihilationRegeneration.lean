import Omega.SyncKernelWeighted.RealInput40NilpotentIndex
import Omega.SyncKernelWeighted.RealInput40ResetRegenerationConstants

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-realinput40-reset-gate-annihilation-regeneration`. The reset word,
nilpotent-index alignment, and reset-regeneration constants are exactly the audited concrete
real-input `40`-state statements. -/
theorem paper_conclusion_realinput40_reset_gate_annihilation_regeneration :
    Omega.SyncKernelWeighted.RealInput40ResetWordStatement ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 5 = 31 ∧
      Omega.SyncKernelWeighted.realInput40ResetSectorProbabilityClosedForm ∧
      Omega.SyncKernelWeighted.realInput40KacReturnTimeClosedForm ∧
      Omega.SyncKernelWeighted.realInput40TypicalWaitTimeClosedForm := by
  rcases Omega.SyncKernelWeighted.paper_real_input_40_nilpotent_index with
    ⟨_, _, _, _, _, _, _, _, hfull5, _⟩
  rcases Omega.SyncKernelWeighted.paper_real_input_40_reset_regeneration_constants with
    ⟨hsector, hkac, htypical⟩
  exact ⟨Omega.SyncKernelWeighted.paper_real_input_40_reset_word, hfull5, hsector, hkac,
    htypical⟩

/-- Paper label: `cor:conclusion-realinput40-sync-zero-spectrum-double-gate`. -/
theorem paper_conclusion_realinput40_sync_zero_spectrum_double_gate
    (syncGate zeroSpectrumGate : Prop) (hgate : syncGate ∧ zeroSpectrumGate) :
    syncGate ∧ zeroSpectrumGate := by
  exact hgate

end Omega.Conclusion
