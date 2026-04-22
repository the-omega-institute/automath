import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Omega.Zeta.AppOffcriticalRadiusCompression

namespace Omega.Zeta

noncomputable section

/-- Off-critical zero package for the comoving Jensen-defect kernel decomposition. -/
structure xi_comoving_jensen_defect_kernel_decomposition_zero_data where
  Zero : Type*
  gamma : Zero → ℝ
  delta : Zero → ℝ
  delta_pos : ∀ z, 0 < delta z
  delta_le_one : ∀ z, delta z ≤ 1
  bounded_height_finite : ∀ x0 R : ℝ, {z : Zero | |gamma z - x0| ≤ R}.Finite

/-- Squared Cayley modulus of the disk image attached to the horizontal offset `x` and
off-critical distance `delta`. -/
noncomputable def xi_comoving_jensen_defect_kernel_decomposition_cayley_image_modulus_sq
    (x delta : ℝ) : ℝ :=
  appOffcriticalModSq x delta

/-- Modulus of the same Cayley image. -/
noncomputable def xi_comoving_jensen_defect_kernel_decomposition_cayley_image_modulus
    (x delta : ℝ) : ℝ :=
  Real.sqrt (xi_comoving_jensen_defect_kernel_decomposition_cayley_image_modulus_sq x delta)

/-- Support-radius bound for a single off-critical contribution. -/
def xi_comoving_jensen_defect_kernel_decomposition_support_radius (varrho delta : ℝ) : ℝ :=
  varrho + delta

/-- Contribution of one off-critical zero to the comoving Jensen defect. Outside the support
radius the kernel is truncated to zero. -/
noncomputable def xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution
    (varrho x delta : ℝ) : ℝ :=
  if |x| < xi_comoving_jensen_defect_kernel_decomposition_support_radius varrho delta then
    max
      (Real.log
        (varrho / xi_comoving_jensen_defect_kernel_decomposition_cayley_image_modulus x delta))
      0
  else
    0

/-- Kernel form of a single off-critical contribution after rewriting the disk-zero by its Cayley
image. -/
noncomputable def xi_comoving_jensen_defect_kernel_decomposition_kernel
    (varrho delta x : ℝ) : ℝ :=
  xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution varrho x delta

/-- The zeros that contribute nontrivially to the comoving Jensen defect at `(x₀, ϱ)`. -/
def xi_comoving_jensen_defect_kernel_decomposition_support
    (D : xi_comoving_jensen_defect_kernel_decomposition_zero_data) (x0 varrho : ℝ) : Set D.Zero :=
  {z |
    xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution
        varrho (D.gamma z - x0) (D.delta z) ≠ 0}

/-- Packaging the off-critical zeros as data, each disk-zero contribution rewrites to the same
Cayley-image kernel, and for fixed `(x₀, ϱ)` only finitely many zeros contribute because the
kernel has bounded support and the zero set is finite in every bounded-height window.
    thm:xi-comoving-jensen-defect-kernel-decomposition -/
theorem paper_xi_comoving_jensen_defect_kernel_decomposition
    (D : xi_comoving_jensen_defect_kernel_decomposition_zero_data) (x0 varrho : ℝ) :
    (∀ z,
      xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution
          varrho (D.gamma z - x0) (D.delta z) =
        xi_comoving_jensen_defect_kernel_decomposition_kernel
          varrho (D.delta z) (D.gamma z - x0)) ∧
    xi_comoving_jensen_defect_kernel_decomposition_support D x0 varrho ⊆
      {z : D.Zero |
        |D.gamma z - x0| ≤
          xi_comoving_jensen_defect_kernel_decomposition_support_radius varrho 1} ∧
    (xi_comoving_jensen_defect_kernel_decomposition_support D x0 varrho).Finite := by
  have hsubset :
      xi_comoving_jensen_defect_kernel_decomposition_support D x0 varrho ⊆
        {z : D.Zero |
          |D.gamma z - x0| ≤
            xi_comoving_jensen_defect_kernel_decomposition_support_radius varrho 1} := by
    intro z hz
    have hlt :
        |D.gamma z - x0| <
          xi_comoving_jensen_defect_kernel_decomposition_support_radius varrho (D.delta z) := by
      by_contra hnotlt
      have hzero :
          xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution
              varrho (D.gamma z - x0) (D.delta z) = 0 := by
        simp [xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution, hnotlt]
      exact hz hzero
    have hdelta : D.delta z ≤ 1 := D.delta_le_one z
    dsimp [xi_comoving_jensen_defect_kernel_decomposition_support_radius] at hlt ⊢
    linarith
  refine ⟨by intro z; rfl, hsubset, ?_⟩
  exact
    (D.bounded_height_finite x0
      (xi_comoving_jensen_defect_kernel_decomposition_support_radius varrho 1)).subset hsubset

end

end Omega.Zeta
