import Mathlib.Tactic

namespace Omega.POM

/-- Mutual information written as entropy minus conditional entropy. -/
def pomTypeclassMutualInformation (Hw Hcond : ℝ) : ℝ :=
  Hw - Hcond

/-- The rate-distortion value induced by the maximal feasible conditional entropy `Vδ`. -/
def pomTypeclassRateDistortionValue (Hw Vδ : ℝ) : ℝ :=
  Hw - Vδ

/-- Paper label: `thm:pom-typeclass-rate-distortion-mutual-information`. Minimizing
`I(X;Y) = H(w) - H(Y|X)` over couplings with conditional entropy bounded by `Vδ` is equivalent to
maximizing `H(Y|X)`, so the unique entropy maximizer `H(Y|X) = Vδ` gives the minimal mutual
information `H(w) - Vδ`. -/
theorem paper_pom_typeclass_rate_distortion_mutual_information (Hw Vδ : ℝ) :
    (∀ Hcond, Hcond ≤ Vδ →
      pomTypeclassRateDistortionValue Hw Vδ ≤ pomTypeclassMutualInformation Hw Hcond) ∧
      pomTypeclassMutualInformation Hw Vδ = pomTypeclassRateDistortionValue Hw Vδ ∧
      (∀ Hcond, Hcond ≤ Vδ →
        (pomTypeclassMutualInformation Hw Hcond = pomTypeclassRateDistortionValue Hw Vδ ↔
          Hcond = Vδ)) := by
  refine ⟨?_, rfl, ?_⟩
  · intro Hcond hcond
    unfold pomTypeclassRateDistortionValue pomTypeclassMutualInformation
    linarith
  · intro Hcond hcond
    unfold pomTypeclassRateDistortionValue pomTypeclassMutualInformation
    constructor <;> intro hEq <;> linarith

end Omega.POM
