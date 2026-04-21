import Mathlib.Tactic
import Omega.Conclusion.BinfoldCollisionScaleForcesMaxfiberDivergence

namespace Omega.Conclusion

/-- The collision-driven lower bound for the number of active nonzero Fourier modes. -/
def fourierActiveModeCountLowerBound (M Col : ℕ → ℝ) (m : ℕ) : ℝ :=
  M m * Col m - 1

/-- If the collision scale `M_m * Col_m` diverges, then the linear lower bound
`M_m * Col_m - 1` diverges as well. -/
private theorem fourierActiveModeCountLowerBound_diverges
    (M Col : ℕ → ℝ)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    NatDivergesToInfinity (fourierActiveModeCountLowerBound M Col) := by
  intro K
  obtain ⟨m, hm⟩ := hGrowth (K + 1)
  refine ⟨m, ?_⟩
  have hm' : (K : ℝ) + 1 ≤ M m * Col m := by
    simpa [binfoldCollisionScaleTerm, Nat.cast_add] using hm
  dsimp [fourierActiveModeCountLowerBound]
  linarith

/-- The nonzero Fourier support is bounded below by the collision mass minus the zero mode, so
once `M_m * Col_m` diverges the active-mode count must diverge too.
    cor:conclusion-fourier-active-mode-count-diverges -/
theorem paper_conclusion_fourier_active_mode_count_diverges
    (Nnz M Col : ℕ → ℝ)
    (hLower : ∀ m, fourierActiveModeCountLowerBound M Col m ≤ Nnz m)
    (hGrowth : NatDivergesToInfinity (binfoldCollisionScaleTerm M Col)) :
    (∀ m, M m * Col m - 1 ≤ Nnz m) ∧ NatDivergesToInfinity Nnz := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa [fourierActiveModeCountLowerBound] using hLower m
  · intro K
    obtain ⟨m, hm⟩ := fourierActiveModeCountLowerBound_diverges M Col hGrowth K
    exact ⟨m, hm.trans (hLower m)⟩

end Omega.Conclusion
