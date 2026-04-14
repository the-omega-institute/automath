import Mathlib.Tactic

/-!
# Fiber defect scalar affine collinearity seed values

The affine function f(x) = a + b·x has constant slope b, so any two points
(x₁, f(x₁)) and (x₂, f(x₂)) are collinear with slope b. We verify the
algebraic identity and a numerical instance.
-/

namespace Omega.GU

/-- Affine collinearity: the slope of f(x) = a + b·x between any two points equals b,
    plus a numerical instance: slopes 12/4 = 3 and 28/4 = 7 with 12·7 = 28·3.
    cor:gut-fiber-defect-single-latent-affine-collinearity -/
theorem paper_gut_fiber_defect_affine_collinearity_seeds :
    (∀ a₁ b₁ _a₂ b₂ x₁ x₂ : ℤ, b₂ * (x₂ - x₁) ≠ 0 →
      (a₁ + b₁ * x₂ - (a₁ + b₁ * x₁)) * (b₂ * (x₂ - x₁)) =
      b₁ * (x₂ - x₁) * (b₂ * (x₂ - x₁))) ∧
    (3 * (5 - 1) = 12 ∧ 7 * (5 - 1) = 28 ∧ 12 * 7 = 28 * 3) := by
  exact ⟨fun _ _ _ _ _ _ _ => by ring, by omega, by omega, by omega⟩

end Omega.GU
