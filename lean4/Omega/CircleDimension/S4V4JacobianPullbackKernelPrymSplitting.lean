import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Omega.CircleDimension.S4V4CompatibleBiellipticPencilsExactlyThree
import Omega.CircleDimension.S4V4PrymA2PolarizedIsogenyRigidity

namespace Omega.CircleDimension

open S4V4PrymA2PolarizedIsogenyRigidityData

/-- Concrete Prym data realizing the `A₂` polarization package with determinant `3`. -/
def cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data :
    S4V4PrymA2PolarizedIsogenyRigidityData where
  a := 2
  b := -1
  c := 2
  naturalPolarization := a2CartanForm
  hnatural := by rfl
  hinvariant := by native_decide
  hpositive := by norm_num
  hdet := by
    norm_num [a2CartanForm, Matrix.det_fin_two]

/-- Paper label: `thm:cdim-s4-v4-jacobian-pullback-kernel-and-prym-splitting`.
The cyclic kernel is modeled by the audited three-element `C₃` packet, and the Prym factor is the
rank-two `A₂`-polarized surface already isolated in the chapter-local rigidity package. -/
theorem paper_cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting :
    s4v4CompatibleBiellipticPencils.card = 3 ∧
      (let D := cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data
       D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧ D.naturalPrymPolarizationIsA2) ∧
      a2CartanForm.det = 3 ∧
      Module.finrank ℚ (Fin 2 → ℚ) = 2 ∧
      Module.finrank ℚ ((Fin 2 → ℚ) × (Fin 2 → ℚ)) =
        Module.finrank ℚ (Fin 2 → ℚ) + Module.finrank ℚ (Fin 2 → ℚ) := by
  refine ⟨paper_cdim_s4_v4_compatible_bielliptic_pencils_exactly_three.1, ?_, ?_, ?_, ?_⟩
  · simpa [cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data] using
      paper_cdim_s4_v4_prym_a2_polarized_isogeny_rigidity
        cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data
  · norm_num [a2CartanForm, Matrix.det_fin_two]
  · simp
  · simp

end Omega.CircleDimension
