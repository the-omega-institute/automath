import Omega.Folding.FoldBinSaturation

namespace Omega

/-- Paper label: `cor:fold-bin-saturation-window-density`. -/
theorem paper_fold_bin_saturation_window_density
    (windowCondition relativeWindow exponentialDecay : Prop) (hWindow : windowCondition)
    (hRatio : windowCondition → relativeWindow) (hDecay : relativeWindow → exponentialDecay) :
    windowCondition ∧ relativeWindow ∧ exponentialDecay := by
  exact ⟨hWindow, hRatio hWindow, hDecay (hRatio hWindow)⟩

end Omega
