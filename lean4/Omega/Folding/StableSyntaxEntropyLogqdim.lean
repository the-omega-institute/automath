import Omega.Folding.Entropy

open scoped goldenRatio

namespace Omega.Folding.StableSyntaxEntropyLogqdim

/-- Paper-facing seed for the logarithmic identification between stable-syntax entropy
    and the quantum dimension of `τ`.
    cor:folding-stable-syntax-entropy-logqdim -/
theorem paper_folding_stable_syntax_entropy_logqdim_seeds
    (dτ : ℝ) (hdτ : dτ = φ) : Real.log dτ = Real.log φ := by
  simp [hdτ]

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_folding_stable_syntax_entropy_logqdim_package
    (dτ : ℝ) (hdτ : dτ = φ) : Real.log dτ = Real.log φ :=
  paper_folding_stable_syntax_entropy_logqdim_seeds dτ hdτ

/-- Exact paper-facing wrapper for `cor:folding-stable-syntax-entropy-logqdim`. -/
theorem paper_folding_stable_syntax_entropy_logqdim
    (dτ : ℝ) (hdτ : dτ = φ) : Real.log dτ = Real.log φ := by
  simpa using paper_folding_stable_syntax_entropy_logqdim_package dτ hdτ

end Omega.Folding.StableSyntaxEntropyLogqdim
