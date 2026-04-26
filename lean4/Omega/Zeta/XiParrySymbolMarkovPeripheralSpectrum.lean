import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-parry-symbol-markov-peripheral-spectrum`. -/
theorem paper_xi_parry_symbol_markov_peripheral_spectrum (φ : ℝ) (hφ0 : φ ≠ 0)
    (hφ : φ ^ 2 = φ + 1) :
    ((φ⁻¹ - 1) * (0 - 1) - (φ⁻¹)^2 = 0) ∧
      ((φ⁻¹ - (-(φ⁻¹)^2)) * (0 - (-(φ⁻¹)^2)) - (φ⁻¹)^2 = 0) := by
  constructor <;> field_simp [hφ0] <;> nlinarith [hφ]

end Omega.Zeta
