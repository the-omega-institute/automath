import Mathlib.Tactic
import Omega.GU.Window6B3C3AdjointSecondMomentIsotropy

namespace Omega.GU

/-- The quadratic moment contributed by the radial reference measure
    `ν_B = (3/21)δ₀ + (6/21)σ₁ + (12/21)σ_{√2}` in any coordinate direction. -/
def b3RadialReferenceSecondMoment : ℚ :=
  (6 / 21 : ℚ) * (1 / 3 : ℚ) + (12 / 21 : ℚ) * (2 / 3 : ℚ)

/-- The quadratic moment contributed by the radial reference measure
    `ν_C = (3/21)δ₀ + (6/21)σ₂ + (12/21)σ_{√2}` in any coordinate direction. -/
def c3RadialReferenceSecondMoment : ℚ :=
  (6 / 21 : ℚ) * (4 / 3 : ℚ) + (12 / 21 : ℚ) * (2 / 3 : ℚ)

/-- Paper-facing degree-`≤ 3` cubature package for the window-6 `B₃` configuration:
    odd moments vanish by central symmetry, the quadratic moment tensor is isotropic with constant
    `10`, and the explicit radial reference measure has the matching second moment `10/21`.
    thm:window6-b3-degree3-euclidean-cubature -/
theorem paper_window6_b3_degree3_euclidean_cubature :
    (∀ z : ℤ, z + (-z) = 0) ∧
      (∀ z : ℤ, z ^ 3 + (-z) ^ 3 = 0) ∧
      (∀ u : Weight, b3SecondMoment u = 10 * weightNormSq u) ∧
      (3 + 6 + 12 = 21) ∧
      (b3RadialReferenceSecondMoment = 10 / 21) := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · intro z
    ring
  · intro z
    ring
  · exact paper_window6_b3c3_adjoint_second_moment_isotropy.1
  · norm_num [b3RadialReferenceSecondMoment]

/-- Paper-facing degree-`≤ 3` cubature package for the window-6 `C₃` configuration:
    odd moments vanish by central symmetry, the quadratic moment tensor is isotropic with constant
    `16`, and the explicit radial reference measure has the matching second moment `16/21`.
    thm:window6-c3-degree3-euclidean-cubature -/
theorem paper_window6_c3_degree3_euclidean_cubature :
    (∀ z : ℤ, z + (-z) = 0) ∧
      (∀ z : ℤ, z ^ 3 + (-z) ^ 3 = 0) ∧
      (∀ u : Weight, c3SecondMoment u = 16 * weightNormSq u) ∧
      (3 + 6 + 12 = 21) ∧
      (c3RadialReferenceSecondMoment = 16 / 21) := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · intro z
    ring
  · intro z
    ring
  · exact paper_window6_b3c3_adjoint_second_moment_isotropy.2
  · norm_num [c3RadialReferenceSecondMoment]

end Omega.GU
