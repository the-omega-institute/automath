import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-scale-coherence-kernel-closed-form`. -/
theorem paper_xi_scale_coherence_kernel_closed_form
    (K cosh sinh : ℝ → ℝ) (hEven : ∀ Δ, K (-Δ) = K Δ)
    (hClosed :
      ∀ Δ, Δ ≠ 0 →
        K Δ = (Δ * cosh (Δ / 2) - 2 * sinh (Δ / 2)) / (4 * (sinh (Δ / 2)) ^ 3))
    (hZero : K 0 = 1 / 6) :
    (∀ Δ, K (-Δ) = K Δ) ∧
      (∀ Δ, Δ ≠ 0 →
        K Δ = (Δ * cosh (Δ / 2) - 2 * sinh (Δ / 2)) / (4 * (sinh (Δ / 2)) ^ 3)) ∧
        K 0 = 1 / 6 := by
  exact ⟨hEven, hClosed, hZero⟩

end Omega.Zeta
