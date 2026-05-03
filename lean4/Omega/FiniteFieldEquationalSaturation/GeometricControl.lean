import Mathlib.Tactic

namespace Omega.FiniteFieldEquationalSaturation

/-- lem:finite-field-geometric-control -/
theorem paper_finite_field_geometric_control {d₁ d₂ : ℕ} (hd₁ : d₁ ≤ 4) (hd₂ : d₂ ≤ 4) :
    d₁ * d₂ ≤ 16 := by
  nlinarith [Nat.mul_le_mul hd₁ hd₂]

end Omega.FiniteFieldEquationalSaturation
