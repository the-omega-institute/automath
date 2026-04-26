import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40NilpotentIndex

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-sync-length-zero-spectrum-alignment`. The concrete
full kernel reaches its stable zero-spectrum rank exactly at step `5`, the essential reduction
stabilizes at step `3`, and the same step `5` is the shortest reset-word length. -/
theorem paper_conclusion_realinput40_sync_length_zero_spectrum_alignment :
    Omega.SyncKernelWeighted.real_input_40_nilpotent_index_essential_kernel_dim 3 = 11 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 4 ≠ 31 ∧
      Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim 5 = 31 ∧
      (∀ k : ℕ, 5 ≤ k →
        Omega.SyncKernelWeighted.real_input_40_nilpotent_index_full_kernel_dim k = 31) ∧
      (∃ w : List Omega.SyncKernelWeighted.RealInput40Digit, w.length = 5 ∧
        ∀ s, Omega.SyncKernelWeighted.realInput40Run s w =
          Omega.SyncKernelWeighted.realInput40ResetState) ∧
      (∀ w : List Omega.SyncKernelWeighted.RealInput40Digit, w.length < 5 →
        ¬ ∃ t, ∀ s, Omega.SyncKernelWeighted.realInput40Run s w = t) := by
  rcases Omega.SyncKernelWeighted.paper_real_input_40_nilpotent_index with
    ⟨_, _, hess3, _, _, _, _, hfull4, hfull5, hfullStable⟩
  rcases Omega.SyncKernelWeighted.paper_real_input_40_reset_word with ⟨hreset5, hshort⟩
  refine ⟨hess3, ?_, hfull5, hfullStable, ?_, hshort⟩
  · simp [hfull4]
  · refine ⟨[Omega.SyncKernelWeighted.RealInput40Digit.zero,
      Omega.SyncKernelWeighted.RealInput40Digit.zero,
      Omega.SyncKernelWeighted.RealInput40Digit.zero,
      Omega.SyncKernelWeighted.RealInput40Digit.zero,
      Omega.SyncKernelWeighted.RealInput40Digit.zero], rfl, ?_⟩
    simpa using hreset5

end Omega.Conclusion
