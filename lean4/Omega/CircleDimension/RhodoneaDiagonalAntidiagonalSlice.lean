import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.CircleDimension.BiphaseAverageFiberDiagonalAntidiagonal

namespace Omega.CircleDimension

noncomputable section

/-- Rhodonea specialization of the biphase-average gate along the linear subflow
`(u, v) = ((d + n) t, (d - n) t)`. -/
def cdim_rhodonea_diagonal_antidiagonal_slice_subflow (d n t : ℝ) : ℂ :=
  cdim_biphase_average_fiber_diagonal_antidiagonal_gate ((d + n) * t) ((d - n) * t)

/-- Paper label: `cor:cdim-rhodonea-diagonal-antidiagonal-slice`.
Along the rhodonea substitution, the midpoint/difference gate collapses to the explicit
`exp(i d t) cos(n t)` factorization. The diagonal slice is recovered by `n = 0`, the
antidiagonal slice by `d = 0`, and the unit-frequency zeros repeat with period `2π`. -/
theorem paper_cdim_rhodonea_diagonal_antidiagonal_slice :
    (∀ d n t : ℝ,
      cdim_rhodonea_diagonal_antidiagonal_slice_subflow d n t =
        Complex.exp (((d * t : ℝ) : ℂ) * Complex.I) * (Real.cos (n * t) : ℂ)) ∧
    (∀ d t : ℝ,
      cdim_rhodonea_diagonal_antidiagonal_slice_subflow d 0 t =
        Complex.exp (((d * t : ℝ) : ℂ) * Complex.I)) ∧
    (∀ n t : ℝ,
      cdim_rhodonea_diagonal_antidiagonal_slice_subflow 0 n t = (Real.cos (n * t) : ℂ)) ∧
    (∀ d : ℝ, ∀ k : ℕ,
      cdim_rhodonea_diagonal_antidiagonal_slice_subflow d 1 (Real.pi / 2 + k * (2 * Real.pi)) = 0) := by
  rcases paper_cdim_biphase_average_fiber_diagonal_antidiagonal with
    ⟨hsub, _, _, _, _⟩
  have hformula : ∀ d n t : ℝ,
      cdim_rhodonea_diagonal_antidiagonal_slice_subflow d n t =
        Complex.exp (((d * t : ℝ) : ℂ) * Complex.I) * (Real.cos (n * t) : ℂ) := by
    intro d n t
    have hu : (d * t + n * t : ℝ) = (d + n) * t := by ring
    have hv : (d * t - n * t : ℝ) = (d - n) * t := by ring
    simpa [cdim_rhodonea_diagonal_antidiagonal_slice_subflow, hu, hv] using hsub (d * t) (n * t)
  refine ⟨hformula, ?_, ?_, ?_⟩
  · intro d t
    simpa using hformula d 0 t
  · intro n t
    simpa using hformula 0 n t
  · intro d k
    rw [hformula]
    have hcos : Real.cos (Real.pi / 2 + k * (2 * Real.pi)) = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using Real.cos_add_nat_mul_two_pi (Real.pi / 2) k
    simp [hcos]

end

end Omega.CircleDimension
