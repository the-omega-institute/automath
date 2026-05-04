import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-foldbin-sufficient-spectral-certificate-must-widen`. -/
theorem paper_conclusion_foldbin_sufficient_spectral_certificate_must_widen
    (K F : ℕ → ℕ) (gap : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (hCapture : ∀ N, ∃ m ≥ N, η * (F m : ℝ) * gap m ≤ (K m : ℝ))
    (hDiverge : ∀ B : ℝ, ∃ N, ∀ m ≥ N, B ≤ η * (F m : ℝ) * gap m) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ m ≥ N0, B ≤ (K m : ℝ) := by
  have _hη : 0 < η := hη
  intro B N0
  rcases hDiverge B with ⟨N1, hN1⟩
  rcases hCapture (max N0 N1) with ⟨m, hm, hKm⟩
  refine ⟨m, le_trans (Nat.le_max_left N0 N1) hm, ?_⟩
  exact le_trans (hN1 m (le_trans (Nat.le_max_right N0 N1) hm)) hKm

end Omega.Conclusion
