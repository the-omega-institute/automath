import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete canonical-system bookkeeping for spectral-flow/Maslov and entropy quantization.
The seed type indexes boundary Lagrangian parameters, while the height variable is represented by
natural truncation stages. -/
structure xi_maslov_spectralflow_entropy_quantization_data where
  xi_maslov_spectralflow_entropy_quantization_seed : Type
  xi_maslov_spectralflow_entropy_quantization_spectralFlow :
    xi_maslov_spectralflow_entropy_quantization_seed → ℕ → ℤ
  xi_maslov_spectralflow_entropy_quantization_maslovIndex :
    xi_maslov_spectralflow_entropy_quantization_seed →
      xi_maslov_spectralflow_entropy_quantization_seed → ℕ → ℤ
  xi_maslov_spectralflow_entropy_quantization_entropy :
    xi_maslov_spectralflow_entropy_quantization_seed → ℕ → ℝ
  xi_maslov_spectralflow_entropy_quantization_kappaCap : ℝ
  xi_maslov_spectralflow_entropy_quantization_kappaCap_pos :
    0 < xi_maslov_spectralflow_entropy_quantization_kappaCap
  xi_maslov_spectralflow_entropy_quantization_spectralFlow_maslov_law :
    ∀ α β T,
      xi_maslov_spectralflow_entropy_quantization_spectralFlow α T -
          xi_maslov_spectralflow_entropy_quantization_spectralFlow β T =
        xi_maslov_spectralflow_entropy_quantization_maslovIndex α β T
  xi_maslov_spectralflow_entropy_quantization_entropy_law :
    ∀ α β T,
      xi_maslov_spectralflow_entropy_quantization_entropy α T -
          xi_maslov_spectralflow_entropy_quantization_entropy β T =
        xi_maslov_spectralflow_entropy_quantization_kappaCap *
          (xi_maslov_spectralflow_entropy_quantization_spectralFlow α T -
            xi_maslov_spectralflow_entropy_quantization_spectralFlow β T : ℝ)

namespace xi_maslov_spectralflow_entropy_quantization_data

/-- The integer spectral-flow difference is the Maslov index. -/
def spectral_flow_eq_maslov
    (D : xi_maslov_spectralflow_entropy_quantization_data) : Prop :=
  ∀ α β T,
    D.xi_maslov_spectralflow_entropy_quantization_spectralFlow α T -
        D.xi_maslov_spectralflow_entropy_quantization_spectralFlow β T =
      D.xi_maslov_spectralflow_entropy_quantization_maslovIndex α β T

/-- Entropy differences occur in integral spectral-flow quanta. -/
def entropy_quantized (D : xi_maslov_spectralflow_entropy_quantization_data) : Prop :=
  ∀ α β T,
    D.xi_maslov_spectralflow_entropy_quantization_entropy α T -
        D.xi_maslov_spectralflow_entropy_quantization_entropy β T =
      D.xi_maslov_spectralflow_entropy_quantization_kappaCap *
        (D.xi_maslov_spectralflow_entropy_quantization_spectralFlow α T -
          D.xi_maslov_spectralflow_entropy_quantization_spectralFlow β T : ℝ)

end xi_maslov_spectralflow_entropy_quantization_data

open xi_maslov_spectralflow_entropy_quantization_data

/-- Paper label: `prop:xi-maslov-spectralflow-entropy-quantization`. -/
theorem paper_xi_maslov_spectralflow_entropy_quantization
    (D : xi_maslov_spectralflow_entropy_quantization_data) :
    D.spectral_flow_eq_maslov ∧ D.entropy_quantized := by
  exact ⟨D.xi_maslov_spectralflow_entropy_quantization_spectralFlow_maslov_law,
    D.xi_maslov_spectralflow_entropy_quantization_entropy_law⟩

end Omega.Zeta
