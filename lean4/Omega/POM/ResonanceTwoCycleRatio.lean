import Mathlib.Tactic

namespace Omega.POM

/-- Concrete two-mode model for the resonance asymptotic. -/
def pomResonanceTerm (C1 C2 lambda1 lambda2 : ℚ) (m : ℕ) : ℚ :=
  C1 * lambda1 ^ m + C2 * lambda2 ^ m

/-- Ratio of consecutive terms in the two-mode resonance model. -/
def pomResonanceRatio (C1 C2 lambda1 lambda2 : ℚ) (m : ℕ) : ℚ :=
  pomResonanceTerm C1 C2 lambda1 lambda2 (m + 1) / pomResonanceTerm C1 C2 lambda1 lambda2 m

/-- Leading alternating correction after dividing by the Perron mode. -/
def pomResonanceMainError (A lambda1 lambda2 : ℚ) (m : ℕ) : ℚ :=
  A * (lambda2 / lambda1) ^ m

lemma pomResonanceTerm_scaled (C1 C2 lambda1 lambda2 : ℚ) (m : ℕ) (hlambda1 : lambda1 ≠ 0) :
    pomResonanceTerm C1 C2 lambda1 lambda2 m =
      lambda1 ^ m * (C1 + C2 * (lambda2 / lambda1) ^ m) := by
  have hratiopow : lambda1 ^ m * (lambda2 / lambda1) ^ m = lambda2 ^ m := by
    calc
      lambda1 ^ m * (lambda2 / lambda1) ^ m = lambda1 ^ m * (lambda2 * lambda1⁻¹) ^ m := by
        rw [div_eq_mul_inv]
      _ = lambda1 ^ m * (lambda2 ^ m * (lambda1⁻¹) ^ m) := by rw [mul_pow]
      _ = lambda2 ^ m * (lambda1 ^ m * (lambda1⁻¹) ^ m) := by ring
      _ = lambda2 ^ m * (lambda1 * lambda1⁻¹) ^ m := by rw [← mul_pow]
      _ = lambda2 ^ m * 1 ^ m := by
        congr 2
        field_simp [hlambda1]
      _ = lambda2 ^ m := by simp
  unfold pomResonanceTerm
  rw [← hratiopow]
  ring

/-- Paper label: `prop:pom-resonance-two-cycle-ratio`.

After normalizing by the Perron root `λ₁`, the two-term model has an exact ratio formula; if
`λ₂ / λ₁ < 0`, the main correction alternates sign between even and odd times. -/
theorem paper_pom_resonance_two_cycle_ratio
    (C1 C2 lambda1 lambda2 A : ℚ) (m : ℕ) (hlambda1 : lambda1 ≠ 0)
    (hden : C1 + C2 * (lambda2 / lambda1) ^ m ≠ 0) (hA : 0 ≤ A)
    (hlambda1_pos : 0 < lambda1) (hlambda2_neg : lambda2 < 0) :
    pomResonanceRatio C1 C2 lambda1 lambda2 m =
      lambda1 * (C1 + C2 * (lambda2 / lambda1) ^ (m + 1)) /
        (C1 + C2 * (lambda2 / lambda1) ^ m) ∧
      0 ≤ pomResonanceMainError A lambda1 lambda2 (2 * m) ∧
      pomResonanceMainError A lambda1 lambda2 (2 * m + 1) ≤ 0 := by
  have hpow : lambda1 ^ m ≠ 0 := pow_ne_zero m hlambda1
  have hpowSucc : lambda1 ^ (m + 1) ≠ 0 := pow_ne_zero (m + 1) hlambda1
  have htermm :
      pomResonanceTerm C1 C2 lambda1 lambda2 m =
        lambda1 ^ m * (C1 + C2 * (lambda2 / lambda1) ^ m) :=
    pomResonanceTerm_scaled C1 C2 lambda1 lambda2 m hlambda1
  have htermm1 :
      pomResonanceTerm C1 C2 lambda1 lambda2 (m + 1) =
        lambda1 ^ (m + 1) * (C1 + C2 * (lambda2 / lambda1) ^ (m + 1)) :=
    pomResonanceTerm_scaled C1 C2 lambda1 lambda2 (m + 1) hlambda1
  have hratio :
      pomResonanceRatio C1 C2 lambda1 lambda2 m =
        lambda1 * (C1 + C2 * (lambda2 / lambda1) ^ (m + 1)) /
          (C1 + C2 * (lambda2 / lambda1) ^ m) := by
    unfold pomResonanceRatio
    rw [htermm1, htermm]
    field_simp [hpow, hpowSucc, hden]
    ring
  have hratio_neg : lambda2 / lambda1 < 0 := div_neg_of_neg_of_pos hlambda2_neg hlambda1_pos
  have hratio_nonpos : lambda2 / lambda1 ≤ 0 := le_of_lt hratio_neg
  have hEvenPow : 0 ≤ (lambda2 / lambda1) ^ (2 * m) := by
    rw [pow_mul]
    positivity
  have hOddPow : (lambda2 / lambda1) ^ (2 * m + 1) ≤ 0 := by
    rw [pow_add]
    norm_num
    exact mul_nonpos_of_nonneg_of_nonpos hEvenPow hratio_nonpos
  refine ⟨hratio, ?_⟩
  refine ⟨?_, ?_⟩
  · unfold pomResonanceMainError
    exact mul_nonneg hA hEvenPow
  · unfold pomResonanceMainError
    exact mul_nonpos_of_nonneg_of_nonpos hA hOddPow

end Omega.POM
