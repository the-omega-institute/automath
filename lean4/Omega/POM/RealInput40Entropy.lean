import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the real-input-40 entropy wrapper: the path counts are sandwiched between
the base grammar and a constant multiplicative lift, the entropy agrees with the golden-mean
product entropy, and the spectral radius is the corresponding Perron value. -/
structure real_input_40_entropy_data where
  real_input_40_entropy_base_paths : ℕ → ℕ
  real_input_40_entropy_kernel_paths : ℕ → ℕ
  real_input_40_entropy_lift_constant : ℕ
  real_input_40_entropy_topological_entropy : ℝ
  real_input_40_entropy_spectral_radius : ℝ
  real_input_40_entropy_base_le_kernel :
    ∀ n : ℕ,
      real_input_40_entropy_base_paths n ≤ real_input_40_entropy_kernel_paths n
  real_input_40_entropy_kernel_le_lift :
    ∀ n : ℕ,
      real_input_40_entropy_kernel_paths n ≤
        real_input_40_entropy_lift_constant * real_input_40_entropy_base_paths n
  real_input_40_entropy_entropy_eq :
    real_input_40_entropy_topological_entropy = 2 * Real.log Real.goldenRatio
  real_input_40_entropy_spectral_radius_eq :
    real_input_40_entropy_spectral_radius = Real.goldenRatio ^ 2

/-- The paper-facing entropy statement records the path-count sandwich together with the entropy
and spectral-radius identities of the real-input-40 kernel. -/
def real_input_40_entropy_stmt (D : real_input_40_entropy_data) : Prop :=
  (∀ n : ℕ, D.real_input_40_entropy_base_paths n ≤ D.real_input_40_entropy_kernel_paths n) ∧
    (∀ n : ℕ,
      D.real_input_40_entropy_kernel_paths n ≤
        D.real_input_40_entropy_lift_constant * D.real_input_40_entropy_base_paths n) ∧
    D.real_input_40_entropy_topological_entropy = 2 * Real.log Real.goldenRatio ∧
    D.real_input_40_entropy_spectral_radius = Real.goldenRatio ^ 2

/-- Paper label: `prop:real-input-40-entropy`. -/
theorem paper_real_input_40_entropy (D : real_input_40_entropy_data) :
    real_input_40_entropy_stmt D := by
  exact ⟨D.real_input_40_entropy_base_le_kernel, D.real_input_40_entropy_kernel_le_lift,
    D.real_input_40_entropy_entropy_eq, D.real_input_40_entropy_spectral_radius_eq⟩

end Omega.POM
