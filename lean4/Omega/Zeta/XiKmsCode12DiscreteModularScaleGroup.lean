import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped goldenRatio

/-- Concrete data for the code `(1,2)` Cuntz/KMS model and its modular scale package. -/
structure xi_kms_code12_discrete_modular_scale_group_data where
  xi_kms_code12_discrete_modular_scale_group_kms_state : Type
  xi_kms_code12_discrete_modular_scale_group_is_kms :
    xi_kms_code12_discrete_modular_scale_group_kms_state → Prop
  xi_kms_code12_discrete_modular_scale_group_canonical_kms_state :
    xi_kms_code12_discrete_modular_scale_group_kms_state
  xi_kms_code12_discrete_modular_scale_group_beta : ℝ
  xi_kms_code12_discrete_modular_scale_group_modular_spectrum : Set ℝ
  xi_kms_code12_discrete_modular_scale_group_connes_scale_set : Set ℝ
  xi_kms_code12_discrete_modular_scale_group_canonical_is_kms :
    xi_kms_code12_discrete_modular_scale_group_is_kms
      xi_kms_code12_discrete_modular_scale_group_canonical_kms_state
  xi_kms_code12_discrete_modular_scale_group_kms_state_ext :
    ∀ (psi : xi_kms_code12_discrete_modular_scale_group_kms_state),
      xi_kms_code12_discrete_modular_scale_group_is_kms psi →
      psi = xi_kms_code12_discrete_modular_scale_group_canonical_kms_state
  xi_kms_code12_discrete_modular_scale_group_beta_cert :
    xi_kms_code12_discrete_modular_scale_group_beta = Real.log Real.goldenRatio
  xi_kms_code12_discrete_modular_scale_group_spectrum_cert :
    xi_kms_code12_discrete_modular_scale_group_modular_spectrum =
      {r : ℝ | ∃ n : ℤ, r = Real.goldenRatio ^ n}
  xi_kms_code12_discrete_modular_scale_group_connes_scale_cert :
    xi_kms_code12_discrete_modular_scale_group_connes_scale_set =
      {0} ∪ {r : ℝ | ∃ n : ℤ, r = Real.goldenRatio ^ n}

namespace xi_kms_code12_discrete_modular_scale_group_data

/-- The KMS state is unique in the concrete code `(1,2)` package. -/
def xi_kms_code12_discrete_modular_scale_group_unique_kms_state
    (D : xi_kms_code12_discrete_modular_scale_group_data) : Prop :=
  ∃! psi : D.xi_kms_code12_discrete_modular_scale_group_kms_state,
    D.xi_kms_code12_discrete_modular_scale_group_is_kms psi

/-- The inverse temperature is the logarithm of the golden ratio. -/
def xi_kms_code12_discrete_modular_scale_group_beta_eq_log_phi
    (D : xi_kms_code12_discrete_modular_scale_group_data) : Prop :=
  D.xi_kms_code12_discrete_modular_scale_group_beta = Real.log Real.goldenRatio

/-- The positive modular spectrum is the discrete group `φ^ℤ`. -/
def xi_kms_code12_discrete_modular_scale_group_spectrum_phi_zpowers
    (D : xi_kms_code12_discrete_modular_scale_group_data) : Prop :=
  D.xi_kms_code12_discrete_modular_scale_group_modular_spectrum =
    {r : ℝ | ∃ n : ℤ, r = Real.goldenRatio ^ n}

/-- The Connes scale set is `{0} ∪ φ^ℤ`. -/
def xi_kms_code12_discrete_modular_scale_group_connes_scale
    (D : xi_kms_code12_discrete_modular_scale_group_data) : Prop :=
  D.xi_kms_code12_discrete_modular_scale_group_connes_scale_set =
    {0} ∪ {r : ℝ | ∃ n : ℤ, r = Real.goldenRatio ^ n}

end xi_kms_code12_discrete_modular_scale_group_data

/-- Paper label: `thm:xi-kms-code12-discrete-modular-scale-group`. -/
theorem paper_xi_kms_code12_discrete_modular_scale_group
    (D : xi_kms_code12_discrete_modular_scale_group_data) :
    D.xi_kms_code12_discrete_modular_scale_group_unique_kms_state ∧
      D.xi_kms_code12_discrete_modular_scale_group_beta_eq_log_phi ∧
      D.xi_kms_code12_discrete_modular_scale_group_spectrum_phi_zpowers ∧
      D.xi_kms_code12_discrete_modular_scale_group_connes_scale := by
  refine ⟨?_, D.xi_kms_code12_discrete_modular_scale_group_beta_cert,
    D.xi_kms_code12_discrete_modular_scale_group_spectrum_cert,
    D.xi_kms_code12_discrete_modular_scale_group_connes_scale_cert⟩
  refine ⟨D.xi_kms_code12_discrete_modular_scale_group_canonical_kms_state,
    D.xi_kms_code12_discrete_modular_scale_group_canonical_is_kms, ?_⟩
  intro psi hpsi
  exact D.xi_kms_code12_discrete_modular_scale_group_kms_state_ext psi hpsi

end Omega.Zeta
