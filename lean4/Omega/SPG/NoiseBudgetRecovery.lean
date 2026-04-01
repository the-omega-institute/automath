import Mathlib.Tactic

namespace Omega.SPG

/-- Divide a positive-factor inequality through by the factor.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem le_div_of_pos_mul_le {c ε δ : ℝ} (hc : 0 < c) (h : c * ε ≤ δ) :
    ε ≤ δ / c := by
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- Rearrangement equivalence for positive factors.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem pos_mul_le_iff_le_div {c ε δ : ℝ} (hc : 0 < c) :
    c * ε ≤ δ ↔ ε ≤ δ / c := by
  constructor
  · intro h
    exact le_div_of_pos_mul_le hc h
  · intro h
    have : ε * c ≤ δ := (le_div_iff₀ hc).1 h
    simpa [mul_comm] using this

end Omega.SPG
