import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-binfold-single-chi2-reconstructs-fisher-lecam-geometry`. -/
theorem paper_conclusion_binfold_single_chi2_reconstructs_fisher_lecam_geometry
    (δχ φ fisher : ℝ) (q : ℕ) (hδ : δχ = (2 * φ - 3) / 5)
    (hfisher :
      fisher =
        (Real.log φ) ^ 2 * binfoldEscortTheta φ q * (1 - binfoldEscortTheta φ q)) :
    φ = (5 * δχ + 3) / 2 ∧
      binfoldEscortTheta φ q = 1 / (1 + ((5 * δχ + 3) / 2) ^ (q + 1)) ∧
      fisher =
        (Real.log ((5 * δχ + 3) / 2)) ^ 2 *
          (1 / (1 + ((5 * δχ + 3) / 2) ^ (q + 1))) *
            (1 - 1 / (1 + ((5 * δχ + 3) / 2) ^ (q + 1))) := by
  have hφ : φ = (5 * δχ + 3) / 2 := by
    nlinarith [hδ]
  refine ⟨hφ, ?_, ?_⟩
  · rw [hφ]
    rfl
  · rw [hfisher, hφ]
    rfl

end

end Omega.Conclusion
