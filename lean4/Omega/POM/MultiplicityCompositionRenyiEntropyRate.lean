import Omega.POM.MultiplicityCompositionLogconvexLambdaq

namespace Omega.POM

noncomputable section

/-- Paper label: `prop:pom-multiplicity-composition-renyi-entropy-rate`. Unfolding the
Rényi entropy-rate proxy and the secant slope of `q ↦ log λ_q` gives the normalized
paper formula `(q log λ₁ - log λ_q) / (q - 1)`. -/
theorem paper_pom_multiplicity_composition_renyi_entropy_rate (q : ℕ) (hq : 1 < q) :
    pomMultiplicityCompositionRenyiEntropyRate q =
      (((q : ℝ) * Real.log (pomMultiplicityCompositionLambda 1)) -
        Real.log (pomMultiplicityCompositionLambda q)) / ((q : ℝ) - 1) := by
  unfold pomMultiplicityCompositionRenyiEntropyRate pomMultiplicityCompositionLambdaSecantSlope
  have hq' : (1 : ℝ) < q := by
    exact_mod_cast hq
  have hqne : (q : ℝ) - 1 ≠ 0 := by
    linarith
  field_simp [hqne]
  ring

end

end Omega.POM
