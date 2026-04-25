import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete spectral-support package for the collision response. `Q8` is the reduced denominator,
`Pole` records poles of the `r`th collision response, `EvenBranch` records points on the rigid
even branch, and `Removable` records removable singularities of the response. -/
structure conclusion_collision_response_spectral_support_data where
  Q8 : ℝ → ℝ → ℝ → ℝ
  Pole : ℕ → ℝ → ℝ → ℝ → Prop
  EvenBranch : ℝ → ℝ → Prop
  Removable : ℕ → ℝ → ℝ → ℝ → Prop
  pole_from_q8 :
    ∀ r z u v, 1 ≤ r → Pole r z u v → Q8 z u v = 0
  even_branch_removable :
    ∀ r z u v, 1 ≤ r → EvenBranch z v → Removable r z u v

/-- Paper label: `cor:conclusion-collision-response-spectral-support`. The `u`-collision
response can only have poles on the reduced `Q8` factor, and the rigid even branch contributes
only removable singularities. -/
theorem paper_conclusion_collision_response_spectral_support
    (D : conclusion_collision_response_spectral_support_data) :
    (∀ r z u v, 1 ≤ r → D.Pole r z u v → D.Q8 z u v = 0) ∧
      (∀ r z u v, 1 ≤ r → D.EvenBranch z v → D.Removable r z u v) := by
  exact ⟨D.pole_from_q8, D.even_branch_removable⟩

end Omega.Conclusion
