import Mathlib.Tactic

namespace Omega

/-- Paper label: `cor:pom-anom-class-additive`. -/
theorem paper_pom_anom_class_additive
    {W A H : Type*} [AddCommGroup A] [AddCommGroup H]
    (comp : W → W → W) (Anom : W → A) (cohomClass : A → H)
    (class_add : ∀ x y, cohomClass (x + y) = cohomClass x + cohomClass y)
    (boundary : W → W → A)
    (boundary_zero : ∀ w₂ w₁, cohomClass (boundary w₂ w₁) = 0)
    (anom_add : ∀ w₂ w₁, Anom (comp w₂ w₁) = Anom w₂ + Anom w₁ + boundary w₂ w₁)
    (w₂ w₁ : W) :
    cohomClass (Anom (comp w₂ w₁)) = cohomClass (Anom w₂) + cohomClass (Anom w₁) := by
  rw [anom_add]
  rw [class_add (Anom w₂ + Anom w₁) (boundary w₂ w₁)]
  rw [class_add]
  simp [boundary_zero]

end Omega
