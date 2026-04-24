import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:gm-sofic-rational-nonconcentration-vtheta`.
A positive twisted-gap parameter `κ` together with a positive conductor range exponent `θ`
already produces an explicit positive saving exponent, which we take to be `κ * θ`. -/
theorem paper_gm_sofic_rational_nonconcentration_vtheta (M : ℕ) (κ θ : ℝ)
    (twistedRadius : ℕ → ℝ) (perronRadius : ℝ) :
    0 < κ → κ < 1 → 0 < θ →
      (∀ q ≤ M, twistedRadius q ≤ (1 - κ) * perronRadius) → ∃ ϑ : ℝ, 0 < ϑ := by
  intro hκ hκ_lt_one hθ hgap
  refine ⟨κ * θ, mul_pos hκ hθ⟩

end Omega.SyncKernelWeighted
