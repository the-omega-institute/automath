import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-sprt-stopping-posterior-constant`. -/
theorem paper_pom_sprt_stopping_posterior_constant (phi : ℝ) (T : ℕ) (hphi : 1 ≤ phi) :
    min ((1 + phi ^ T)⁻¹) ((1 + (phi ^ T)⁻¹)⁻¹) = (1 + phi ^ T)⁻¹ := by
  have hpow : 1 ≤ phi ^ T := one_le_pow₀ hphi
  refine min_eq_left ?_
  have hden : 0 < 1 + phi ^ T := by positivity
  have hinvden : 0 < 1 + (phi ^ T)⁻¹ := by positivity
  rw [inv_le_inv₀ hden hinvden]
  have hinv_le : (phi ^ T)⁻¹ ≤ phi ^ T := (inv_le_one_of_one_le₀ hpow).trans hpow
  linarith

end Omega.POM
