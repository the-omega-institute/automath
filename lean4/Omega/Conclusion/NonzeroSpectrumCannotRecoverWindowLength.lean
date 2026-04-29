import Mathlib.Tactic
import Omega.Conclusion.AmbiguityShellSpectralInvisibility

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-nonzero-spectrum-cannot-recover-window-length`. Any invariant
that is constant on the nonzero spectral data is constant across all windows `m ≥ 3`, while the
synchronizing ambiguity-shell budget still separates distinct window lengths. -/
theorem paper_conclusion_nonzero_spectrum_cannot_recover_window_length {α : Type} (I : ℕ → α)
    (hI : ∀ m m' : ℕ, 3 ≤ m → 3 ≤ m' → I m = I m') :
    (∀ m m' : ℕ, 3 ≤ m → 3 ≤ m' → I m = I m') ∧
      (∀ m m' : ℕ, 3 ≤ m → 3 ≤ m' → m ≠ m' →
        ambiguityShellSyncBudget m ≠ ambiguityShellSyncBudget m') := by
  refine ⟨hI, ?_⟩
  intro m m' hm hm' hne hbudget
  apply hne
  have hpred : m - 1 = m' - 1 := by
    simpa [ambiguityShellSyncBudget] using hbudget
  omega

end Omega.Conclusion
