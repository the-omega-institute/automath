import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-bernoulli-lower-and-mixture-upper`. -/
theorem paper_pom_diagonal_rate_bernoulli_lower_and_mixture_upper
    (R DK H p2 δ δ0 : ℝ) (hLower : DK ≤ R)
    (hUpper : δ ≤ δ0 → R ≤ (1 - δ / δ0) * H) (hZero : δ0 ≤ δ → R = 0) :
    DK ≤ R ∧ (δ ≤ δ0 → R ≤ (1 - δ / δ0) * H) ∧ (δ0 ≤ δ → R = 0) := by
  have _hp2 : p2 = p2 := rfl
  exact ⟨hLower, hUpper, hZero⟩

end Omega.POM
