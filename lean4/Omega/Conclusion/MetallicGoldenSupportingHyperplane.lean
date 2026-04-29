import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-metallic-golden-supporting-hyperplane`. -/
theorem paper_conclusion_metallic_golden_supporting_hyperplane (hZ κ : ℝ → ℝ) (βc : ℝ)
    (hmax : ∀ A : ℝ, 1 ≤ A → hZ A - βc * κ A ≤ hZ 1 - βc * κ 1)
    (hunique :
      ∀ A : ℝ, 1 ≤ A → hZ A - βc * κ A = hZ 1 - βc * κ 1 → A = 1) :
    (∀ A : ℝ, 1 ≤ A → hZ A - hZ 1 ≤ βc * (κ A - κ 1)) ∧
      (∀ A : ℝ, 1 ≤ A →
        (hZ A - hZ 1 = βc * (κ A - κ 1) ↔ A = 1)) := by
  refine ⟨?_, ?_⟩
  · intro A hA
    have hAmax := hmax A hA
    linarith
  · intro A hA
    refine ⟨?_, ?_⟩
    · intro hEq
      apply hunique A hA
      linarith
    · intro hA1
      subst A
      ring

end Omega.Conclusion
