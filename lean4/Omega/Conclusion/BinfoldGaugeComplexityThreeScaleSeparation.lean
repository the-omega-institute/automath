import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-gauge-complexity-three-scale-separation`. -/
theorem paper_conclusion_binfold_gauge_complexity_three_scale_separation
    (Xi Gamma Sigma : ℕ → ℝ) (xiLimit gammaLimit sigmaLimit : Prop) (hXi : xiLimit)
    (hGamma : gammaLimit) (hSigma : sigmaLimit)
    (hXiGamma : ∀ eps > 0, ∃ M, ∀ m ≥ M, Xi m ≤ eps * Gamma m)
    (hGammaSigma : ∀ eps > 0, ∃ M, ∀ m ≥ M, Gamma m ≤ eps * Sigma m) :
    xiLimit ∧ gammaLimit ∧ sigmaLimit ∧
      (∀ eps > 0, ∃ M, ∀ m ≥ M, Xi m ≤ eps * Gamma m) ∧
      (∀ eps > 0, ∃ M, ∀ m ≥ M, Gamma m ≤ eps * Sigma m) := by
  exact ⟨hXi, hGamma, hSigma, hXiGamma, hGammaSigma⟩

end Omega.Conclusion
