import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete ground-layer entropy base used for the sharp one-bit threshold model. -/
def xi_real_input_ground_layer_oracle_threshold_c : ℝ := 2

/-- If the external register budget stays below one bit per step, the counting ratio against the
ground-layer model `c = 2` is at most `1`. -/
def xi_real_input_ground_layer_oracle_threshold_success_bound (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, B n ≤ n →
    ((2 : ℝ) ^ (B n)) / (xi_real_input_ground_layer_oracle_threshold_c ^ n) ≤ 1

/-- If the external register budget is at least one bit per step, the same counting ratio is at
least `1`, matching the sharp `log₂ c = 1` threshold for `c = 2`. -/
def xi_real_input_ground_layer_oracle_threshold_rate_threshold (B : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≤ B n →
    1 ≤ ((2 : ℝ) ^ (B n)) / (xi_real_input_ground_layer_oracle_threshold_c ^ n)

/-- Paper label: `thm:xi-real-input-ground-layer-oracle-threshold`. In the concrete `c = 2`
ground-layer model, the external counting ratio crosses `1` exactly at one bit per step. -/
theorem paper_xi_real_input_ground_layer_oracle_threshold (B : ℕ → ℕ) :
    xi_real_input_ground_layer_oracle_threshold_success_bound B ∧
      xi_real_input_ground_layer_oracle_threshold_rate_threshold B := by
  refine ⟨?_, ?_⟩
  · intro n hBn
    have hden : 0 < ((2 : ℝ) ^ n) := by positivity
    have hpow : (2 : ℝ) ^ (B n) ≤ (2 : ℝ) ^ n := by
      exact pow_le_pow_right₀ (by norm_num) hBn
    have hratio :
        ((2 : ℝ) ^ (B n)) / ((2 : ℝ) ^ n) ≤ ((2 : ℝ) ^ n) / ((2 : ℝ) ^ n) := by
      exact div_le_div_of_nonneg_right hpow (le_of_lt hden)
    simpa [xi_real_input_ground_layer_oracle_threshold_c] using hratio
  · intro n hBn
    have hden : 0 < ((2 : ℝ) ^ n) := by positivity
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (B n) := by
      exact pow_le_pow_right₀ (by norm_num) hBn
    have hratio :
        ((2 : ℝ) ^ n) / ((2 : ℝ) ^ n) ≤ ((2 : ℝ) ^ (B n)) / ((2 : ℝ) ^ n) := by
      exact div_le_div_of_nonneg_right hpow (le_of_lt hden)
    simpa [xi_real_input_ground_layer_oracle_threshold_c] using hratio

end Omega.SyncKernelRealInput
